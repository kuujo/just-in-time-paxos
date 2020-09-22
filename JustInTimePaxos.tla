-------------------------- MODULE JustInTimePaxos --------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

\* The set of Paxos replicas
CONSTANT Replicas

\* The set of Paxos clients
CONSTANT Clients

\* The set of possible values
CONSTANT Values

\* An empty value
CONSTANT Nil

\* Request/response types
CONSTANTS
    MClientRequest,
    MClientResponse,
    MRepairRequest,
    MRepairResponse,
    MAbortRequest,
    MAbortResponse,
    MViewChangeRequest,
    MViewChangeResponse,
    MStartViewRequest

\* Replica statuses
CONSTANTS
    SNormal,
    SAborting,
    SViewChange

\* Entry types
CONSTANTS
    TValue,
    TNoOp

----

\* A sequence of replicas used for deterministic primary election
VARIABLE replicas

globalVars == <<replicas>>

\* The set of all messages on the network
VARIABLE messages

messageVars == <<messages>>

(* Local client state *)

\* Strictly increasing representation of synchronized time
VARIABLE cTime

\* The highest known view ID for a client
VARIABLE cViewID

\* The current sequence number for a client
VARIABLE cSeqNum

\* A client response buffer
VARIABLE cResps

\* A set of all commits - used for model checking
VARIABLE cCommits

clientVars == <<cTime, cViewID, cSeqNum, cResps, cCommits>>

(* Local replica state *)

\* The current status of a replica
VARIABLE rStatus

\* A replica's commit log
VARIABLE rLog

\* The current view ID for a replica
VARIABLE rViewID

\* The current sequence number for each session
VARIABLE rSeqNum

\* The highest known timestamp for all sessions
VARIABLE rTimestamp

\* The last known normal view
VARIABLE rLastViewID

\* The set of received view change responses
VARIABLE rViewChanges

\* The point (client+sequence number) in the log currently being aborted
VARIABLE rAbortPoint

\* The set of abort responses received
VARIABLE rAbortResps

replicaVars == <<rStatus, rLog, rViewID, rSeqNum, rTimestamp,
                 rLastViewID, rViewChanges, rAbortPoint, rAbortResps>>

\* A counter used to limit the state space for model checking
VARIABLE transitions

vars == <<globalVars, messageVars, clientVars, replicaVars, transitions>>

----

(*
This section provides helpers for the spec.
*)

RECURSIVE SeqFromSet(_)
SeqFromSet(S) == 
    IF S = {} THEN
        << >> 
    ELSE LET x == CHOOSE x \in S : TRUE
        IN  << x >> \o SeqFromSet(S \ {x})

Pick(S) == CHOOSE s \in S : TRUE

RECURSIVE SetReduce(_, _, _)
SetReduce(Op(_, _), S, value) == 
    IF S = {} THEN
        value
    ELSE
        LET s == Pick(S)
        IN SetReduce(Op, S \ {s}, Op(s, value)) 

Max(s) == CHOOSE x \in s : \A y \in s : x >= y

Sum(S) == LET _op(a, b) == a + b
          IN SetReduce(_op, S, 0)

IsQuorum(s) == Cardinality(s) * 2 >= Cardinality(Replicas)

Quorums == {r \in SUBSET Replicas : IsQuorum(r)}

Primary(v) == replicas[(v%Len(replicas)) + (IF v >= Len(replicas) THEN 1 ELSE 0)]

IsPrimary(r) == Primary(rViewID[r]) = r

----

(*
This section models the network.
*)

\* Send a set of messages
Sends(ms) == messages' = messages \cup ms

\* Send a message
Send(m) == Sends({m})

\* Reply to a message with a set of responses
Replies(req, resps) == messages' = (messages \cup resps) \ {req}

\* Reply to a message
Reply(req, resp) == Replies(req, {resp})

\* Discard a message
Discard(m) == messages' = messages \ {m}

----

(*
This section models client requests.
*)

\* Client 'c' sends value 'v' to all replicas
ClientRequest(c, v) ==
    /\ cTime' = cTime + 1
    /\ cSeqNum' = [cSeqNum EXCEPT ![c] = cSeqNum[c] + 1]
    /\ Sends({[src       |-> c,
               dest      |-> r,
               type      |-> MClientRequest,
               viewID    |-> cViewID[c],
               seqNum    |-> cSeqNum'[c],
               value     |-> v,
               timestamp |-> cTime'] : r \in Replicas})
    /\ UNCHANGED <<globalVars, replicaVars, cViewID, cResps, cCommits>>

\* Client 'c' handles a response 'm' from replica 'r'
HandleClientResponse(c, r, m) ==
    /\ \/ /\ m.viewID = cViewID[c]
          /\ cResps' = [cResps EXCEPT ![c] = cResps[c] \cup {m}]
          /\ LET 
                 seqNumResps == {n \in cResps[c] : n.seqNum = m.seqNum}
                 goodResps   == {n \in seqNumResps : n.viewID = cViewID[c] /\ n.succeeded}
                 isCommitted == /\ \E n \in goodResps : n.src = Primary(n.viewID)
                                /\ {n.src : n \in goodResps} \in Quorums
             IN
                 /\ \/ /\ isCommitted
                       /\ cCommits' = [cCommits EXCEPT ![c] = cCommits[c] \cup 
                             {CHOOSE n \in goodResps : n.src = Primary(n.viewID)}]
                    \/ /\ ~isCommitted
                       /\ UNCHANGED <<cCommits>>
                 /\ UNCHANGED <<cViewID, cSeqNum>>
       \/ /\ m.viewID > cViewID[c]
          /\ cViewID' = [cViewID EXCEPT ![c] = m.viewID]
          /\ cSeqNum' = [cSeqNum EXCEPT ![c] = 0]
          /\ cResps'  = [cResps  EXCEPT ![c] = {}]
          /\ UNCHANGED <<cCommits>>
       \/ /\ m.viewID < cViewID[c]
          /\ UNCHANGED <<cCommits>>
    /\ Discard(m)
    /\ UNCHANGED <<globalVars, replicaVars, cTime, cSeqNum>>

----

(*
This section models the replica protocol.
*)

\* Replica 'r' requests a repair of the client 'c' request 'm'
Repair(r, c, m) ==
    /\ Replies(m, {[src    |-> r,
                    dest   |-> d,
                    type   |-> MRepairRequest,
                    viewID |-> rViewID[r],
                    client |-> c,
                    seqNum |-> rSeqNum[r][c] + 1] : d \in Replicas})

\* Replica 'r' aborts the client 'c' request 'm'
Abort(r, c, m) ==
    /\ IsPrimary(r)
    /\ rStatus[r]   = SNormal
    /\ rStatus'     = [rStatus     EXCEPT ![r] = SAborting]
    /\ rAbortResps' = [rAbortResps EXCEPT ![r] = {}]
    /\ rAbortPoint' = [rAbortPoint EXCEPT ![r] = [client |-> c, seqNum |-> m.seqNum]]
    /\ Replies(m, {[src       |-> r,
                    dest      |-> d,
                    type      |-> MAbortRequest,
                    viewID    |-> rViewID[r],
                    client    |-> c,
                    seqNum    |-> m.seqNum,
                    timestamp |-> m.timestamp] : d \in Replicas})

\* Replica 'r' handles client 'c' request 'm'
HandleClientRequest(r, c, m) ==
    /\ rStatus[r] = SNormal
    /\ \/ /\ m.viewID = rViewID[r]
          /\ LET
                 lastIndex     == Sum({Len(rLog[r][i]) : i \in Clients})
                 index         == lastIndex + 1
                 lastTimestamp == rTimestamp[r]
                 isSequential  == m.seqNum = rSeqNum[r][c] + 1
                 isLinear      == m.timestamp > lastTimestamp
                 entry         == [type      |-> TValue, 
                                   index     |-> index,
                                   value     |-> m.value,
                                   timestamp |-> m.timestamp]
                 append(e)     == [rLog EXCEPT ![r] = [rLog[r] EXCEPT 
                                               ![c] = Append(rLog[r][c], e)]]
             IN
                \/ /\ isSequential
                   /\ isLinear
                   /\ rLog' = append(entry)
                   /\ rSeqNum' = [rSeqNum EXCEPT ![r] = [rSeqNum[r] EXCEPT ![c] = m.seqNum]]
                   /\ rTimestamp' = [rTimestamp EXCEPT ![r] = m.timestamp]
                   /\ Reply(m, [src       |-> r,
                                dest      |-> c,
                                type      |-> MClientResponse,
                                viewID    |-> rViewID[r],
                                seqNum    |-> m.seqNum,
                                index     |-> index,
                                value     |-> m.value,
                                succeeded |-> TRUE])
                   /\ UNCHANGED <<rStatus, rAbortPoint, rAbortResps>>
                \/ /\ \/ ~isSequential
                      \/ ~isLinear
                   /\ \/ /\ IsPrimary(r)
                         /\ Abort(r, c, m)
                      \/ /\ ~IsPrimary(r)
                         /\ Reply(m, [src       |-> r,
                                      dest      |-> c,
                                      type      |-> MClientResponse,
                                      viewID    |-> rViewID[r],
                                      seqNum    |-> m.seqNum,
                                      succeeded |-> FALSE])
                         /\ UNCHANGED <<rStatus, rAbortPoint, rAbortResps>>
                   /\ UNCHANGED <<rLog, rSeqNum, rTimestamp>>
       \/ /\ m.viewID < rViewID[r]
          /\ Reply(m, [src       |-> r,
                       dest      |-> c,
                       type      |-> MClientResponse,
                       viewID    |-> rViewID[r],
                       seqNum    |-> m.seqNum,
                       succeeded |-> FALSE])
          /\ UNCHANGED <<rStatus, rLog, rSeqNum, rTimestamp, rAbortPoint, rAbortResps>>
    /\ UNCHANGED <<globalVars, clientVars, rViewID, rLastViewID, rViewChanges>>

\* Replica 'r' handles replica 's' repair request 'm'
HandleRepairRequest(r, s, m) ==
    /\ m.viewID = rViewID[r]
    /\ IsPrimary(r)
    /\ rStatus[r] = SNormal
    /\ LET index == Len(rLog[r][m.client]) + 1 - (rSeqNum[r] - m.seqNum)
       IN
          /\ \/ /\ index <= Len(rLog[r][m.client])
                /\ Reply(m, [src    |-> r,
                             dest   |-> s,
                             type   |-> MRepairResponse,
                             viewID |-> rViewID[r],
                             client |-> m.client,
                             seqNum |-> m.seqNum])
                /\ UNCHANGED <<rStatus, rAbortPoint, rAbortResps>>
             \/ /\ index = Len(rLog[r][m.client]) + 1
                /\ Abort(r, m.client, m)
    /\ UNCHANGED <<globalVars, clientVars>>

\* Replica 'r' handles replica 's' repair response 'm'
HandleRepairResponse(r, s, m) ==
    /\ HandleClientRequest(r, m.client, [m EXCEPT !.src = m.client])

\* Replica 'r' handles replica 's' abort request 'm'
HandleAbortRequest(r, s, m) ==
    /\ m.viewID = rViewID[r]
    /\ rStatus[r] \in {SNormal, SAborting}
    /\ LET 
           offset == Len(rLog[r][m.client]) + 1 - (rSeqNum[r][m.client] - m.seqNum)
           entry == [type |-> TNoOp, timestamp |-> m.timestamp]
           replace(i, e) == [j \in 1..Max({Len(rLog[r][m.client]), i}) |->
                                IF j = i THEN e ELSE rLog[r][m.client][j]]
       IN
          /\ offset <= Len(rLog[r][m.client]) + 1
          /\ rLog' = replace(offset, entry)
          /\ rTimestamp' = [rTimestamp EXCEPT ![r] = Max({rTimestamp[r], m.timestamp})]
          /\ rSeqNum' = [rSeqNum EXCEPT ![r] = [rSeqNum[r] EXCEPT 
                                        ![m.client] = Max({rSeqNum[r][m.client], m.seqNum})]]
          /\ Replies(m, {[src       |-> r,
                          dest      |-> Primary(rViewID[r]),
                          type      |-> MAbortResponse,
                          viewID    |-> rViewID[r],
                          client    |-> m.client,
                          seqNum    |-> m.seqNum],
                         [src       |-> r,
                          dest      |-> m.client,
                          type      |-> MClientResponse,
                          viewID    |-> rViewID[r],
                          seqNum    |-> m.seqNum,
                          succeeded |-> FALSE]})
    /\ UNCHANGED <<globalVars, clientVars, rStatus, rAbortPoint, 
                   rAbortResps, rViewID, rLastViewID, rViewChanges>>

\* Replica 'r' handles replica 's' repair response 'm'
HandleAbortResponse(r, s, m) ==
    /\ rStatus[r] = SAborting
    /\ m.viewID = rViewID[r]
    /\ IsPrimary(r)
    /\ m.seqNum = rAbortPoint[r].seqNum
    /\ rAbortResps' = [rAbortResps EXCEPT ![r] = rAbortResps[r] \cup {m}]
    /\ LET resps == {res.src : res \in {resp \in rAbortResps'[r] :
                        /\ resp.viewID = rViewID[r]
                        /\ resp.client = rAbortPoint[r].client
                        /\ resp.seqNum = rAbortPoint[r].seqNum}}
           isQuorum == r \in resps /\ resps \in Quorums
       IN
          \/ /\ isQuorum
             /\ rStatus' = [rStatus EXCEPT ![r] = SNormal]
          \/ /\ ~isQuorum
             /\ UNCHANGED <<rStatus>>
    /\ UNCHANGED <<globalVars, messageVars, clientVars, rLog, rSeqNum, rTimestamp, 
                   rAbortPoint, rViewID, rViewChanges, rLastViewID>>

\* Replica 'r' requests a view change
ChangeView(r) ==
    /\ Sends({[src    |-> r,
               dest   |-> d,
               type   |-> MViewChangeRequest,
               viewID |-> rViewID[r] + 1] : d \in Replicas})
    /\ UNCHANGED <<globalVars, clientVars, replicaVars>>

\* Replica 'r' handles replica 's' view change request 'm'
HandleViewChangeRequest(r, s, m) ==
    /\ rViewID[r] < m.viewID
    /\ rViewID'      = [rViewID EXCEPT ![r] = m.viewID]
    /\ rStatus'      = [rStatus EXCEPT ![r] = SViewChange]
    /\ rViewChanges' = [rViewChanges EXCEPT ![r] = {}]
    /\ Reply(m, [src        |-> r,
                 dest       |-> Primary(m.viewID),
                 type       |-> MViewChangeResponse,
                 viewID     |-> m.viewID,
                 lastViewID |-> rLastViewID[r],
                 logs       |-> rLog[r]])
    /\ UNCHANGED <<globalVars, clientVars, rLog, rSeqNum, rTimestamp,  
                   rAbortPoint, rAbortResps, rLastViewID>>

\* Replica 'r' handles replica 's' view change response 'm'
HandleViewChangeResponse(r, s, m) ==
    /\ IsPrimary(r)
    /\ rViewID[r]    = m.viewID
    /\ rStatus[r]    = SViewChange
    /\ rViewChanges' = [rViewChanges EXCEPT ![r] = rViewChanges[r] \cup {m}]
    /\ LET viewChanges     == {v \in rViewChanges'[r] : v.viewID = rViewID[r]}
           viewSources     == {v.src : v \in viewChanges}
           isQuorum        == r \in viewSources /\ viewSources \in Quorums
           lastViewIDs     == {v.lastViewID : v \in viewChanges}
           lastViewID      == (CHOOSE v1 \in lastViewIDs : \A v2 \in lastViewIDs : v2 <= v1)
           lastViewChanges == {v2 \in viewChanges : v2.lastViewID = lastViewID}
           viewLogs        == [c \in Clients |-> {v1.logs[c] : v1 \in lastViewChanges}]
           mergeEnts(es)   ==
               IF es = {} \/ \E e \in es : e.type = TNoOp THEN
                   [type |-> TNoOp]
               ELSE
                   CHOOSE e \in es : e.type # TNoOp
           range(ls)       == Max({Len(l) : l \in ls})
           entries(ls, i)  == {l[i] : l \in {k \in ls : i <= Len(k)}}
           mergeLogs(ls)   == [i \in 1..range(ls) |-> mergeEnts(entries(ls, i))]
           viewLog         == [c \in Clients |-> mergeLogs(viewLogs[c])]
           viewRange       == Max({Len(viewLog[c]) : c \in Clients})
           viewTimestamp   == IF viewRange > 0 THEN
                                 Max(UNION {{l[i].timestamp : i \in DOMAIN l} :
                                                l \in {viewLog[c] : c \in Clients}})
                             ELSE 0
       IN
           \/ /\ isQuorum
              /\ Replies(m, {[src       |-> r,
                              dest      |-> d,
                              type      |-> MStartViewRequest,
                              viewID    |-> rViewID[r],
                              timestamp |-> viewTimestamp,
                              log       |-> viewLog] : d \in Replicas})
           \/ /\ ~isQuorum
              /\ Discard(m)
    /\ UNCHANGED <<globalVars, clientVars, rStatus, rViewID, rLog, rSeqNum, 
                   rTimestamp, rAbortPoint, rAbortResps, rLastViewID>>

\* Replica 'r' handles replica 's' start view request 'm'
HandleStartViewRequest(r, s, m) ==
    /\ \/ rViewID[r] < m.viewID
       \/ /\ rViewID[r] = m.viewID
          /\ rStatus[r] = SViewChange
    /\ rLog'        = [rLog        EXCEPT ![r] = m.log]
    /\ rSeqNum'     = [rSeqNum     EXCEPT ![r] = [c \in Clients |-> 0]]
    /\ rTimestamp'  = [rTimestamp  EXCEPT ![r] = m.timestamp]
    /\ rStatus'     = [rStatus     EXCEPT ![r] = SNormal]
    /\ rViewID'     = [rViewID     EXCEPT ![r] = m.viewID]
    /\ rLastViewID' = [rLastViewID EXCEPT ![r] = m.viewID]
    /\ Discard(m)
    /\ UNCHANGED <<globalVars, clientVars, rAbortPoint, rAbortResps, rViewChanges>>

----


InitMessageVars ==
    /\ messages = {}

InitClientVars ==
    /\ cTime    = 0
    /\ cViewID  = [c \in Clients |-> 1]
    /\ cSeqNum  = [c \in Clients |-> 0]
    /\ cResps   = [c \in Clients |-> {}]
    /\ cCommits = [c \in Clients |-> {}]

InitReplicaVars ==
    /\ replicas     = SeqFromSet(Replicas)
    /\ rStatus      = [r \in Replicas |-> SNormal]
    /\ rLog         = [r \in Replicas |-> [c \in Clients |-> <<>>]]
    /\ rSeqNum      = [r \in Replicas |-> [c \in Clients |-> 0]]
    /\ rTimestamp   = [r \in Replicas |-> 0]
    /\ rAbortPoint  = [r \in Replicas |-> [client |-> Nil, seqNum |-> 0]]
    /\ rAbortResps  = [r \in Replicas |-> {}]
    /\ rViewID      = [r \in Replicas |-> 1]
    /\ rLastViewID  = [r \in Replicas |-> 1]
    /\ rViewChanges = [r \in Replicas |-> {}]

Init ==
    /\ InitMessageVars
    /\ InitClientVars
    /\ InitReplicaVars
    /\ transitions = 0

----

\* The type invariant verifies that clients do not receive two commits at the 
\* same index with different values.
TypeOK ==
    \A c1, c2 \in Clients :
       \A e1 \in cCommits[c1] :
          ~\E e2 \in cCommits[c2] :
             /\ e1.index = e2.index
             /\ e1.value # e2.value

Transition == transitions' = transitions + 1

Next ==
    \/ \E c \in Clients :
          \E v \in Values :
             /\ ClientRequest(c, v)
             /\ Transition
    \/ \E r \in Replicas : 
          /\ ChangeView(r)
          /\ Transition
    \/ \E m \in messages :
          /\ m.type = MClientRequest
          /\ HandleClientRequest(m.dest, m.src, m)
          /\ Transition
    \/ \E m \in messages :
          /\ m.type = MClientResponse
          /\ HandleClientResponse(m.dest, m.src, m)
          /\ Transition
    \/ \E m \in messages :
          /\ m.type = MRepairRequest
          /\ HandleRepairRequest(m.dest, m.src, m)
          /\ Transition
    \/ \E m \in messages :
          /\ m.type = MRepairResponse
          /\ HandleRepairResponse(m.dest, m.src, m)
          /\ Transition
    \/ \E m \in messages :
          /\ m.type = MAbortRequest
          /\ HandleAbortRequest(m.dest, m.src, m)
          /\ Transition
    \/ \E m \in messages :
          /\ m.type = MAbortResponse
          /\ HandleAbortResponse(m.dest, m.src, m)
          /\ Transition
    \/ \E m \in messages :
          /\ m.type = MViewChangeRequest
          /\ HandleViewChangeRequest(m.dest, m.src, m)
          /\ Transition
    \/ \E m \in messages :
          /\ m.type = MViewChangeResponse
          /\ HandleViewChangeResponse(m.dest, m.src, m)
          /\ Transition
    \/ \E m \in messages :
          /\ m.type = MStartViewRequest
          /\ HandleStartViewRequest(m.dest, m.src, m)
          /\ Transition
    \/ \E m \in messages : Discard(m)

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Tue Sep 22 12:57:49 PDT 2020 by jordanhalterman
\* Created Fri Sep 18 22:45:21 PDT 2020 by jordanhalterman
