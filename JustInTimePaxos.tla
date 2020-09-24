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
    MClientReply,
    MRepairRequest,
    MRepairReply,
    MAbortRequest,
    MAbortReply,
    MViewChangeRequest,
    MViewChangeReply,
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

(*
Message schemas

ViewIDs == [viewID |-> n \in (1..)]

  ClientRequest
    [src       |-> c \in Clients,
     dest      |-> r \in Replicas,
     type      |-> MClientRequest,
     viewID    |-> i \in ViewIDs,
     value     |-> v \in Values,
     seqNum    |-> s \in (1..),
     timestamp |-> t \in (1..)]

  ClientReply
    [src       |-> r \in Replicas,
     dest      |-> c \in Clients,
     type      |-> MClientReply,
     viewID    |-> i \in ViewIDs,
     value     |-> v \in Values,
     seqNum    |-> s \in (1..),
     index     |-> i \in (1..),
     succeeded |-> TRUE \/ FALSE]

  RepairRequest
    [src       |-> r \in Replicas,
     dest      |-> r \in Replicas,
     type      |-> MRepairRequest,
     viewID    |-> i \in ViewIDs,
     client    |-> c \in Clients,
     seqNum    |-> s \in (1..),
     timestamp |-> t \in (1..)]

  RepairReply
    [src       |-> r \in Replicas,
     dest      |-> r \in Replicas,
     type      |-> MRepairReply,
     viewID    |-> i \in ViewIDs,
     client    |-> c \in Clients,
     seqNum    |-> s \in (1..),
     value     |-> v \in Values,
     timestamp |-> t \in (1..)]

  AbortRequest
    [src       |-> r \in Replicas,
     dest      |-> r \in Replicas,
     type      |-> MAbortRequest,
     viewID    |-> i \in ViewIDs,
     client    |-> c \in Clients,
     seqNum    |-> s \in (1..),
     timestamp |-> t \in (1..)]

  AbortReply
    [src       |-> r \in Replicas,
     dest      |-> r \in Replicas,
     type      |-> MAbortReply,
     viewID    |-> i \in ViewIDs,
     client    |-> c \in Clients,
     seqNum    |-> s \in (1..)]

  ViewChangeRequest
    [src        |-> r \in Replicas,
     dest       |-> r \in Replicas,
     type       |-> MViewChangeRequest,
     viewID     |-> i \in ViewIDs]
  
  ViewChangeReply
    [src        |-> r \in Replicas,
     dest       |-> r \in Replicas,
     type       |-> MViewChangeReply,
     viewID     |-> i \in ViewIDs,
     lastViewID |-> i \in (1..),
     log        |-> [c \in Clients |-> [
                       i \in 1..(1..) |-> [
                           value |-> v \in Values, 
                           timestamp |-> (1..)]]]]
  
  StartViewRequest
    [src       |-> r \in Replicas,
     dest      |-> r \in Replicas,
     type      |-> MStartViewRequest,
     viewID    |-> i \in ViewIDs,
     timestamp |-> t \in (1..),
     log        |-> [c \in Clients |-> [
                       i \in 1..(1..) |-> [
                           value |-> v \in Values, 
                           timestamp |-> (1..)]]]]
*)

----

\* A sequence of replicas used for deterministic primary election
VARIABLE replicas

globalVars == <<replicas>>

\* The set of all messages on the network
VARIABLE messages

\* The total number of messages sent
VARIABLE messageCount

messageVars == <<messages, messageCount>>

(* Local client state *)

\* Strictly increasing representation of synchronized time
VARIABLE cTime

\* The highest known view ID for a client
VARIABLE cViewID

\* The current sequence number for a client
VARIABLE cSeqNum

\* A client response buffer
VARIABLE cReps

\* A set of all commits - used for model checking
VARIABLE cCommits

clientVars == <<cTime, cViewID, cSeqNum, cReps, cCommits>>

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
VARIABLE rAbortReps

replicaVars == <<rStatus, rLog, rViewID, rSeqNum, rTimestamp,
                 rLastViewID, rViewChanges, rAbortPoint, rAbortReps>>

vars == <<globalVars, messageVars, clientVars, replicaVars>>

----

(*
This section provides helpers for the spec.
*)

\* Creates a sequence from set 'S'
RECURSIVE SeqFromSet(_)
SeqFromSet(S) == 
    IF S = {} THEN
        << >> 
    ELSE LET x == CHOOSE x \in S : TRUE
        IN  << x >> \o SeqFromSet(S \ {x})

\* Selects an element of set 'S'
Pick(S) == CHOOSE s \in S : TRUE

RECURSIVE SetReduce(_, _, _)
SetReduce(Op(_, _), S, value) == 
    IF S = {} THEN
        value
    ELSE
        LET s == Pick(S)
        IN SetReduce(Op, S \ {s}, Op(s, value)) 

\* Computes the greatest vlue in set 'S'
Max(S) == CHOOSE x \in S : \A y \in S : x >= y

\* Computes the sum of numbers in set 'S'
Sum(S) == LET _op(a, b) == a + b
          IN SetReduce(_op, S, 0)

\* A boolean indicating whether the given set is a quorum
IsQuorum(s) == Cardinality(s) * 2 >= Cardinality(Replicas)

\* The set of all quorums
Quorums == {r \in SUBSET Replicas : IsQuorum(r)}

\* The primary for view 'v'
Primary(v) == replicas[(v%Len(replicas)) + (IF v >= Len(replicas) THEN 1 ELSE 0)]

\* A boolean indicating whether replica 'r' is the primary for the current view
IsPrimary(r) == Primary(rViewID[r]) = r

----

(*
This section models the network.
*)

\* Send a set of messages
Sends(ms) ==
    /\ messages'     = messages \cup ms
    /\ messageCount' = messageCount + Cardinality(ms)

\* Send a message
Send(m) == Sends({m})

\* Reply to a message with a set of responses
Replies(req, reps) == 
    /\ messages'     = (messages \cup reps) \ {req}
    /\ messageCount' = messageCount + Cardinality(reps)

\* Reply to a message
Reply(req, resp) == Replies(req, {resp})

\* Discard a message
Discard(m) == 
    /\ messages'     = messages \ {m}
    /\ messageCount' = messageCount + 1

----

(*
This section models client requests.
*)

\* Client 'c' sends value 'v' to all replicas
\* Client requests are ordered globally using physical timestamps and locally (within
\* the client) using client sequence numbers. Sequence numbers are sequential and unique
\* within each view.
\* When the client sends a request is generates a new timestamp. Physical timestamps
\* are modeled here as a strictly increasing global clock simulating synchronized 
\* system clocks. The sequence number for the client is also incremented and sent
\* with the request.
ClientRequest(c, v) ==
    /\ cTime'   = cTime + 1
    /\ cSeqNum' = [cSeqNum EXCEPT ![c] = cSeqNum[c] + 1]
    /\ Sends({[src       |-> c,
               dest      |-> r,
               type      |-> MClientRequest,
               viewID    |-> cViewID[c],
               seqNum    |-> cSeqNum'[c],
               value     |-> v,
               timestamp |-> cTime'] : r \in Replicas})
    /\ UNCHANGED <<globalVars, replicaVars, cViewID, cReps, cCommits>>

\* Client 'c' handles a response 'm' from replica 'r'
\* When a response is received by the client, if the client is still in the request
\* view it can process the response. The client is responsible for determining commitment
\* by counting responses for each sequence number. Once a response is received from a
\* majority of the replicas including the primary replica, the response is committed.
\* Committed responses are stored in a history variable for checking against invariants.
HandleClientReply(c, r, m) ==
    /\ \/ /\ m.viewID = cViewID[c]
          /\ cReps' = [cReps EXCEPT ![c] = cReps[c] \cup {m}]
          /\ LET 
                 seqNumReps  == {n \in cReps[c] : n.seqNum = m.seqNum}
                 goodReps    == {n \in seqNumReps : n.viewID = cViewID[c] /\ n.succeeded}
                 isCommitted == /\ \E n \in goodReps : n.src = Primary(n.viewID)
                                /\ {n.src : n \in goodReps} \in Quorums
             IN
                 /\ \/ /\ isCommitted
                       /\ cCommits' = [cCommits EXCEPT ![c] = cCommits[c] \cup 
                             {CHOOSE n \in goodReps : n.src = Primary(n.viewID)}]
                    \/ /\ ~isCommitted
                       /\ UNCHANGED <<cCommits>>
                 /\ UNCHANGED <<cViewID, cSeqNum>>
       \/ /\ m.viewID > cViewID[c]
          /\ cViewID' = [cViewID EXCEPT ![c] = m.viewID]
          /\ cSeqNum' = [cSeqNum EXCEPT ![c] = 0]
          /\ cReps'   = [cReps   EXCEPT ![c] = {}]
          /\ UNCHANGED <<cCommits>>
       \/ /\ m.viewID < cViewID[c]
          /\ UNCHANGED <<cViewID, cSeqNum, cReps, cCommits>>
    /\ Discard(m)
    /\ UNCHANGED <<globalVars, replicaVars, cTime>>

----

(*
This section models the replica protocol.
*)

\* Replica 'r' requests a repair of the client 'c' request 'm'
Repair(r, c, m) ==
    /\ Replies(m, {[src       |-> r,
                    dest      |-> d,
                    type      |-> MRepairRequest,
                    viewID    |-> rViewID[r],
                    client    |-> c,
                    seqNum    |-> m.seqNum,
                    timestamp |-> m.timestamp] : d \in Replicas})

\* Replica 'r' aborts the client 'c' request 'm'
Abort(r, c, m) ==
    /\ IsPrimary(r)
    /\ rStatus[r]   = SNormal
    /\ rStatus'     = [rStatus     EXCEPT ![r] = SAborting]
    /\ rAbortReps'  = [rAbortReps  EXCEPT ![r] = {}]
    /\ rAbortPoint' = [rAbortPoint EXCEPT ![r] = [client |-> c, seqNum |-> m.seqNum]]
    /\ Replies(m, {[src       |-> r,
                    dest      |-> d,
                    type      |-> MAbortRequest,
                    viewID    |-> rViewID[r],
                    client    |-> c,
                    seqNum    |-> m.seqNum,
                    timestamp |-> m.timestamp] : d \in Replicas})

\* Replica 'r' handles client 'c' request 'm'
\* Client requests with a view ID not matching the replica's view are rejected.
\* Clients reset their sequence number of 
\* For requests in the correct view, the request must be sequential and linear
\* to be appended to the log. That is, the request must have a 'seqNum' that is
\* 1 + the prior 'seqNum' for the client, and the 'timestamp' must be greater
\* than all prior timestamps in the log. This is necessary to ensure the primary
\* log does not change when requests are reordered. The client can retry requests
\* that are reordered with a new sequence number and timestamp.
\* To maintain consistency within the log, a separate sequence is maintained for
\* each session (client), and each sequence number is assigned to a unique
\* position in the session log. Session logs are logically merged into a totally
\* ordered log using the request timestamps.
\* When a sequence number is skipped, the primary must commit a TNoOp entry to
\* the log. It does so by running the AbortRequest protocol.
\* When a sequence number is skipped on a non-primary replica, the replica attempts
\* to recover the request using the RepairRequest protocol.
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
                   /\ rLog'       = append(entry)
                   /\ rSeqNum'    = [rSeqNum    EXCEPT ![r] = 
                                    [rSeqNum[r] EXCEPT ![c] = m.seqNum]]
                   /\ rTimestamp' = [rTimestamp EXCEPT ![r] = m.timestamp]
                   /\ Reply(m, [src       |-> r,
                                dest      |-> c,
                                type      |-> MClientReply,
                                viewID    |-> rViewID[r],
                                seqNum    |-> m.seqNum,
                                index     |-> index,
                                value     |-> m.value,
                                succeeded |-> TRUE])
                   /\ UNCHANGED <<rStatus, rAbortPoint, rAbortReps>>
                \/ /\ \/ /\ ~isSequential
                         /\ m.seqNum > rSeqNum[r][c] + 1
                      \/ ~isLinear
                   /\ \/ /\ IsPrimary(r)
                         /\ Abort(r, c, m)
                      \/ /\ ~IsPrimary(r)
                         /\ Repair(r, c, m)
                         /\ UNCHANGED <<rStatus, rAbortPoint, rAbortReps>>
                   /\ UNCHANGED <<rLog, rSeqNum, rTimestamp>>
       \/ /\ m.viewID < rViewID[r]
          /\ Reply(m, [src       |-> r,
                       dest      |-> c,
                       type      |-> MClientReply,
                       viewID    |-> rViewID[r],
                       seqNum    |-> m.seqNum,
                       succeeded |-> FALSE])
          /\ UNCHANGED <<rStatus, rLog, rSeqNum, rTimestamp, rAbortPoint, rAbortReps>>
    /\ UNCHANGED <<globalVars, clientVars, rViewID, rLastViewID, rViewChanges>>

\* Replica 'r' handles replica 's' repair request 'm'
\* When a repair request is received, if the requested sequence number is in the session
\* log, the entry is returned. Otherwise, the primary aborts the request.
HandleRepairRequest(r, s, m) ==
    /\ m.viewID = rViewID[r]
    /\ IsPrimary(r)
    /\ rStatus[r] = SNormal
    /\ LET offset == Len(rLog[r][m.client]) - (rSeqNum[r][m.client] - m.seqNum)
       IN
          \/ /\ offset <= Len(rLog[r][m.client])
             /\ Reply(m, [src       |-> r,
                          dest      |-> s,
                          type      |-> MRepairReply,
                          viewID    |-> rViewID[r],
                          client    |-> m.client,
                          seqNum    |-> m.seqNum,
                          value     |-> rLog[r][m.client][offset].value,
                          timestamp |-> rLog[r][m.client][offset].timestamp])
             /\ UNCHANGED <<rStatus, rAbortPoint, rAbortReps>>
          \/ /\ offset = Len(rLog[r][m.client]) + 1
             /\ Abort(r, m.client, m)
    /\ UNCHANGED <<globalVars, clientVars, rLog, rSeqNum, rTimestamp, rViewID, rLastViewID, rViewChanges>>

\* Replica 'r' handles replica 's' repair response 'm'
\* Repair responses are handled like client requests.
HandleRepairReply(r, s, m) ==
    HandleClientRequest(r, m.client, [m EXCEPT !.src = m.client])

\* Replica 'r' handles replica 's' abort request 'm'
\* If the aborted sequence number is in the session log, the entry is replaced with
\* a no-op entry. If the sequence number can be appebded to the log, it is.
HandleAbortRequest(r, s, m) ==
    /\ m.viewID = rViewID[r]
    /\ rStatus[r] \in {SNormal, SAborting}
    /\ LET 
           offset == Len(rLog[r][m.client]) - (rSeqNum[r][m.client] - m.seqNum)
           entry  == [type |-> TNoOp, value |-> Nil, timestamp |-> 0]
       IN
          /\ \/ /\ offset <= Len(rLog[r][m.client])
                /\ rLog' = [rLog EXCEPT ![r] = [
                            rLog[r] EXCEPT ![m.client] = [
                            rLog[r][m.client] EXCEPT ![offset] = [
                            rLog[r][m.client][offset] EXCEPT !.type = TNoOp]]]]
                /\ UNCHANGED <<rTimestamp, rSeqNum>>
             \/ /\ offset = Len(rLog[r][m.client]) + 1
                /\ rLog' = [rLog EXCEPT ![r] = [
                            rLog[r] EXCEPT ![m.client] = 
                               Append(rLog[r][m.client], entry)]]
                /\ rTimestamp' = [rTimestamp EXCEPT ![r] = Max({rTimestamp[r], m.timestamp})]
                /\ rSeqNum'    = [rSeqNum    EXCEPT ![r] = [
                                  rSeqNum[r] EXCEPT ![m.client] = m.seqNum]]
          /\ Replies(m, {[src       |-> r,
                          dest      |-> Primary(rViewID[r]),
                          type      |-> MAbortReply,
                          viewID    |-> rViewID[r],
                          client    |-> m.client,
                          seqNum    |-> m.seqNum],
                         [src       |-> r,
                          dest      |-> m.client,
                          type      |-> MClientReply,
                          viewID    |-> rViewID[r],
                          seqNum    |-> m.seqNum,
                          succeeded |-> FALSE]})
    /\ UNCHANGED <<globalVars, clientVars, rStatus, rAbortPoint, 
                   rAbortReps, rViewID, rLastViewID, rViewChanges>>

\* Replica 'r' handles replica 's' repair response 'm'
HandleAbortReply(r, s, m) ==
    /\ rStatus[r] = SAborting
    /\ m.viewID = rViewID[r]
    /\ IsPrimary(r)
    /\ m.seqNum = rAbortPoint[r].seqNum
    /\ rAbortReps' = [rAbortReps EXCEPT ![r] = rAbortReps[r] \cup {m}]
    /\ LET reps == {res.src : res \in {resp \in rAbortReps'[r] :
                        /\ resp.viewID = rViewID[r]
                        /\ resp.client = rAbortPoint[r].client
                        /\ resp.seqNum = rAbortPoint[r].seqNum}}
           isQuorum == r \in reps /\ reps \in Quorums
       IN
          \/ /\ isQuorum
             /\ rStatus' = [rStatus EXCEPT ![r] = SNormal]
          \/ /\ ~isQuorum
             /\ UNCHANGED <<rStatus>>
    /\ UNCHANGED <<globalVars, messageVars, clientVars, rLog, rSeqNum, rTimestamp, 
                   rAbortPoint, rViewID, rViewChanges, rLastViewID>>

\* Replica 'r' requests a view change
\* The view change is requested by sending a ViewChangeRequest to each replica.
ChangeView(r) ==
    /\ Sends({[src    |-> r,
               dest   |-> d,
               type   |-> MViewChangeRequest,
               viewID |-> rViewID[r] + 1] : d \in Replicas})
    /\ UNCHANGED <<globalVars, clientVars, replicaVars>>

\* Replica 'r' handles replica 's' view change request 'm'
\* Replicas respond to ViewChangeRequests with the contents of their logs
\* for reconciliation. When a new view change is requested, the replica updates
\* its ViewID and transitions to the ViewChange status to block writes during
\* the transition.
HandleViewChangeRequest(r, s, m) ==
    /\ rViewID[r] < m.viewID
    /\ rViewID'      = [rViewID      EXCEPT ![r] = m.viewID]
    /\ rStatus'      = [rStatus      EXCEPT ![r] = SViewChange]
    /\ rViewChanges' = [rViewChanges EXCEPT ![r] = {}]
    /\ Reply(m, [src        |-> r,
                 dest       |-> Primary(m.viewID),
                 type       |-> MViewChangeReply,
                 viewID     |-> m.viewID,
                 lastViewID |-> rLastViewID[r],
                 log        |-> rLog[r]])
    /\ UNCHANGED <<globalVars, clientVars, rLog, rSeqNum, rTimestamp,  
                   rAbortPoint, rAbortReps, rLastViewID>>

\* Replica 'r' handles replica 's' view change response 'm'
\* ViewChangeReplys are handled by the primary for the new view. Once
\* responses are received from a majority of the replicas including the new
\* primary, the logs received from each replica are merged together to form
\* the log for the new view. For each known session, the logs from each replica
\* are merged by comparing each entry and keeping all non-empty sequential
\* entries in the quorum. An updated timestamp is calculated from the reconciled
\* log, and a StartViewRequest containing the new logs is sent to each replica.
HandleViewChangeReply(r, s, m) ==
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
           viewLogs        == [c \in Clients |-> {v1.log[c] : v1 \in lastViewChanges}]
           mergeEnts(es)   ==
               IF es = {} \/ \E e \in es : e.type = TNoOp THEN
                   CHOOSE e \in es : e.type = TNoOp
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
                   rTimestamp, rAbortPoint, rAbortReps, rLastViewID>>

\* Replica 'r' handles replica 's' start view request 'm'
\* If the view is new, the replica updates its logs and session state from the request.
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
    /\ UNCHANGED <<globalVars, clientVars, rAbortPoint, rAbortReps, rViewChanges>>

----


InitMessageVars ==
    /\ messages     = {}
    /\ messageCount = 0

InitClientVars ==
    /\ cTime    = 0
    /\ cViewID  = [c \in Clients |-> 1]
    /\ cSeqNum  = [c \in Clients |-> 0]
    /\ cReps    = [c \in Clients |-> {}]
    /\ cCommits = [c \in Clients |-> {}]

InitReplicaVars ==
    /\ replicas     = SeqFromSet(Replicas)
    /\ rStatus      = [r \in Replicas |-> SNormal]
    /\ rLog         = [r \in Replicas |-> [c \in Clients |-> <<>>]]
    /\ rSeqNum      = [r \in Replicas |-> [c \in Clients |-> 0]]
    /\ rTimestamp   = [r \in Replicas |-> 0]
    /\ rAbortPoint  = [r \in Replicas |-> [client |-> Nil, seqNum |-> 0]]
    /\ rAbortReps   = [r \in Replicas |-> {}]
    /\ rViewID      = [r \in Replicas |-> 1]
    /\ rLastViewID  = [r \in Replicas |-> 1]
    /\ rViewChanges = [r \in Replicas |-> {}]

Init ==
    /\ InitMessageVars
    /\ InitClientVars
    /\ InitReplicaVars

----

\* The type invariant verifies that clients do not receive two commits at the 
\* same index with different values.
TypeOK ==
    \A c1, c2 \in Clients :
       \A e1 \in cCommits[c1] :
          ~\E e2 \in cCommits[c2] :
             /\ e1.index = e2.index
             /\ e1.value # e2.value

Next ==
    \/ \E c \in Clients :
          \E v \in Values :
             /\ ClientRequest(c, v)
    \/ \E r \in Replicas : 
          /\ ChangeView(r)
    \/ \E m \in messages :
          /\ m.type = MClientRequest
          /\ HandleClientRequest(m.dest, m.src, m)
    \/ \E m \in messages :
          /\ m.type = MClientReply
          /\ HandleClientReply(m.dest, m.src, m)
    \/ \E m \in messages :
          /\ m.type = MRepairRequest
          /\ HandleRepairRequest(m.dest, m.src, m)
    \/ \E m \in messages :
          /\ m.type = MRepairReply
          /\ HandleRepairReply(m.dest, m.src, m)
    \/ \E m \in messages :
          /\ m.type = MAbortRequest
          /\ HandleAbortRequest(m.dest, m.src, m)
    \/ \E m \in messages :
          /\ m.type = MAbortReply
          /\ HandleAbortReply(m.dest, m.src, m)
    \/ \E m \in messages :
          /\ m.type = MViewChangeRequest
          /\ HandleViewChangeRequest(m.dest, m.src, m)
    \/ \E m \in messages :
          /\ m.type = MViewChangeReply
          /\ HandleViewChangeReply(m.dest, m.src, m)
    \/ \E m \in messages :
          /\ m.type = MStartViewRequest
          /\ HandleStartViewRequest(m.dest, m.src, m)
    \/ \E m \in messages : 
          /\ Discard(m)
          /\ UNCHANGED <<globalVars, clientVars, replicaVars>>

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Thu Sep 24 10:56:11 PDT 2020 by jordanhalterman
\* Created Fri Sep 18 22:45:21 PDT 2020 by jordanhalterman
