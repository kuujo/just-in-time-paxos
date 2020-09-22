-------------------------- MODULE JustInTimePaxos --------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

\* The set of Paxos replicas
CONSTANT Replicas

\* The set of Paxos clients
CONSTANT Clients

\* An empty value
CONSTANT Nil

\* Client request/response types+
CONSTANTS
    MWriteRequest,
    MWriteResponse,
    MReadRequest,
    MReadResponse

\* Server request/response types
CONSTANTS
    MRepairRequest,
    MRepairResponse,
    MAbortRequest,
    MAbortResponse,
    MViewChangeRequest,
    MViewChangeResponse,
    MStartViewRequest

\* Replica roles
CONSTANTS
    SNormal,
    SAborting,
    SViewChange

\* Entry types
CONSTANTS
    TValue,
    TNoOp

----

VARIABLE replicas

globalVars == <<replicas>>

VARIABLE messages

messageVars == <<messages>>

VARIABLE cTime

VARIABLE cViewID

VARIABLE cSeqNum

VARIABLE cResps

VARIABLE cWrites

VARIABLE cReads

clientVars == <<cTime, cViewID, cSeqNum, cResps, cWrites, cReads>>

VARIABLE rStatus

VARIABLE rLog

VARIABLE rViewID

VARIABLE rSeqNum

VARIABLE rLastView

VARIABLE rViewChanges

VARIABLE rAbortSeqNum

VARIABLE rAbortResps

replicaVars == <<rStatus, rLog, rViewID, rSeqNum, rLastView, rViewChanges, rAbortSeqNum, rAbortResps>>

VARIABLE transitions

vars == <<globalVars, messageVars, clientVars, replicaVars, transitions>>

----

\* Helpers

RECURSIVE SeqFromSet(_)
SeqFromSet(S) == 
  IF S = {} THEN << >> 
  ELSE LET x == CHOOSE x \in S : TRUE
       IN  << x >> \o SeqFromSet(S \ {x})

Max(s) == CHOOSE x \in s : \A y \in s : x >= y

IsQuorum(s) == Cardinality(s) * 2 >= Cardinality(Replicas)

Quorums == {r \in SUBSET Replicas : IsQuorum(r)}

Primary(v) == replicas[(v%Len(replicas)) + (IF v >= Len(replicas) THEN 1 ELSE 0)]

IsPrimary(r) == Primary(rViewID[r]) = r

Replace(l, i, x) == [j \in 1..Max({Len(l), i}) |-> IF j = i THEN x ELSE l[j]]

----

\* Messaging helpers

Sends(ms) == messages' = messages \cup ms

Send(m) == Sends({m})

Replies(req, resps) == messages' = (messages \cup resps) \ {req}

Reply(req, resp) == Replies(req, {resp})

Discard(m) == messages' = messages \ {m}

----

Write(c) ==
    /\ cTime' = cTime + 1
    /\ cSeqNum' = [cSeqNum EXCEPT ![c] = cSeqNum[c] + 1]
    /\ Sends({[src       |-> c,
               dest      |-> r,
               type      |-> MWriteRequest,
               viewID    |-> cViewID[c],
               seqNum  |-> cSeqNum'[c],
               timestamp |-> cTime'] : r \in Replicas})
    /\ UNCHANGED <<globalVars, replicaVars, cViewID, cResps, cWrites, cReads>>

Read(c) ==
    /\ Sends({[src       |-> c,
               dest      |-> r,
               type      |-> MReadRequest,
               viewID    |-> cViewID[c]] : r \in Replicas})
    /\ UNCHANGED <<globalVars, replicaVars, cTime, cSeqNum, cResps, cWrites, cReads>>

HandleWriteResponse(c, r, m) ==
    /\ \/ /\ m.viewID = cViewID[c]
          /\ IF m.seqNum \notin DOMAIN cResps[c][r] THEN
                cResps' = [cResps EXCEPT ![c] = [cResps[c] EXCEPT ![r] = cResps[c][r] @@ (m.seqNum :> m)]]
             ELSE
                cResps' = [cResps EXCEPT ![c] = [cResps[c] EXCEPT ![r] = [cResps[c][r] EXCEPT ![m.seqNum] = m]]]
          /\ LET 
                 allResps    == {cResps[c][r][r1] : r1 \in {r2 \in Replicas : r2 \in DOMAIN cResps[c][r]}}
                 isCommitted == {r1.src : r1 \in {r2 \in allResps : r2.succeeded}} \in Quorums
             IN
                 /\ \/ /\ isCommitted
                       /\ cWrites' = [cWrites EXCEPT ![c] = cWrites[c] \cup {m}]
                    \/ /\ ~isCommitted
                       /\ UNCHANGED <<cWrites>>
                 /\ UNCHANGED <<cViewID, cSeqNum>>
       \/ /\ m.viewID > cViewID[c]
          /\ cViewID' = [cViewID EXCEPT ![c] = m.viewID]
          /\ cSeqNum' = [cSeqNum EXCEPT ![c] = 0]
          /\ cResps'  = [cResps  EXCEPT ![c] = [i \in Replicas |-> {}]]
          /\ UNCHANGED <<cWrites>>
       \/ /\ m.viewID < cViewID[c]
          /\ UNCHANGED <<cWrites>>
    /\ Discard(m)
    /\ UNCHANGED <<globalVars, replicaVars, cTime, cSeqNum, cReads>>

HandleReadResponse(c, r, m) ==
    /\ \/ /\ m.viewID = cViewID[c]
          /\ cReads' = [cReads EXCEPT ![c] = cReads[c] \cup {m}]
          /\ UNCHANGED <<cViewID, cSeqNum>>
       \/ /\ m.viewID > cViewID[c]
          /\ cViewID' = [cViewID EXCEPT ![c] = m.viewID]
          /\ cSeqNum' = [cSeqNum EXCEPT ![c] = 0]
          /\ UNCHANGED <<cReads>>
       \/ /\ m.viewID < cViewID[c]
          /\ UNCHANGED <<cViewID, cSeqNum, cReads>>
    /\ Discard(m)
    /\ UNCHANGED <<globalVars, replicaVars, cTime, cSeqNum, cResps, cWrites>>

----

\* Server request/response handling

Repair(r, c, m) ==
    /\ Replies(m, {[src    |-> r,
                    dest   |-> d,
                    type   |-> MRepairRequest,
                    viewID |-> rViewID[r],
                    client |-> c,
                    seqNum |-> rSeqNum[r][c] + 1] : d \in Replicas})

Abort(r, c, m) ==
    /\ IsPrimary(r)
    /\ rStatus[r]    = SNormal
    /\ rStatus'      = [rStatus      EXCEPT ![r] = SAborting]
    /\ rAbortResps'  = [rAbortResps  EXCEPT ![r] = [rAbortResps[r] EXCEPT ![c] = {}]]
    /\ rAbortSeqNum' = [rAbortSeqNum EXCEPT ![r] = [rAbortSeqNum[r] EXCEPT ![c] = m.seqNum]]
    /\ Replies(m, {[src    |-> r,
                    dest   |-> d,
                    type   |-> MAbortRequest,
                    viewID |-> rViewID[r],
                    client |-> c,
                    seqNum |-> m.seqNum] : d \in Replicas})

HandleWriteRequest(r, c, m) ==
    /\ rStatus[r] = SNormal
    /\ \/ /\ m.viewID = rViewID[r]
          /\ LET
                 isSequential == m.seqNum = rSeqNum[r][c] + 1
                 isLinear     == \A i \in DOMAIN rLog[r] : \A e \in rLog[r][i] : m.timestamp > e.timestamp
             IN
                \/ /\ isSequential
                   /\ isLinear
                   /\ rLog' = [rLog    EXCEPT ![r] = [
                               rLog[r] EXCEPT ![c] = 
                                   Append(rLog[r][c], [type      |-> TValue, 
                                                       value     |-> m.value,
                                                       timestamp |-> m.timestamp])]]
                   /\ rSeqNum' = [rSeqNum EXCEPT ![r] = [rSeqNum[r] EXCEPT ![c] = m.seqNum]]
                   /\ Reply(m, [src       |-> r,
                                dest      |-> c,
                                type      |-> MWriteResponse,
                                seqNum    |-> m.seqNum,
                                viewID    |-> rViewID[r],
                                succeeded |-> TRUE])
                \/ /\ \/ ~isSequential
                      \/ ~isLinear
                   /\ \/ /\ IsPrimary(r)
                         /\ Abort(r, c, m)
                      \/ /\ ~IsPrimary(r)
                         /\ Reply(m, [src       |-> r,
                                      dest      |-> c,
                                      type      |-> MWriteResponse,
                                      seqNum    |-> m.seqNum,
                                      viewID    |-> rViewID[r],
                                      succeeded |-> FALSE])
                   /\ UNCHANGED <<rLog>>
       \/ /\ m.viewID < rViewID[r]
          /\ Reply(m, [src       |-> r,
                       dest      |-> c,
                       type      |-> MWriteResponse,
                       seqNum    |-> m.seqNum,
                       viewID    |-> rViewID[r],
                       succeeded |-> FALSE])
          /\ UNCHANGED <<rLog>>
    /\ UNCHANGED <<globalVars, clientVars, rStatus, rViewID, rLastView, rViewChanges>>

HandleReadRequest(r, c, m) ==
    /\ rStatus[r] = SNormal
    /\ Len(rLog[r]) > 0
    /\ Reply(m, [src       |-> r,
                 dest      |-> c,
                 type      |-> MReadResponse,
                 viewID    |-> rViewID[r],
                 primary   |-> IsPrimary(r),
                 index     |-> Len(rLog[r]),
                 checksum  |-> rLog[r][Len(rLog[r])].checksum,
                 succeeded |-> TRUE])
    /\ UNCHANGED <<globalVars, clientVars, rStatus, rLog, rViewID, rLastView, rViewChanges>>

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
                /\ UNCHANGED <<rStatus, rAbortResps, rAbortSeqNum>>
             \/ /\ index = Len(rLog[r][m.client]) + 1
                /\ Abort(r, m.client, m)
    /\ UNCHANGED <<globalVars, clientVars>>

HandleRepairResponse(r, s, m) ==
    /\ HandleWriteRequest(r, m.client, [m EXCEPT !.src = m.client])

HandleAbortRequest(r, s, m) ==
    /\ m.viewID = rViewID[r]
    /\ rStatus[r] \in {SNormal, SAborting}
    /\ LET index == Len(rLog[r][m.client]) + 1 - (rSeqNum[r] - m.seqNum)
       IN
          /\ index <= Len(rLog[r][m.client]) + 1
          /\ rLog' = [rLog EXCEPT ![r] = [rLog[r] EXCEPT ![m.client] = Replace(rLog[r][m.client], index, [type |-> TNoOp])]]
          /\ \/ /\ m.seqNum > rSeqNum[r][m.client]
                /\ rSeqNum' = [rSeqNum EXCEPT ![r] = [rSeqNum[r] EXCEPT ![m.client] = m.seqNum]]
             \/ /\ m.seqNum <= rSeqNum[r][m.client]
                /\ UNCHANGED <<rSeqNum>>
          /\ Replies(m, {[src       |-> r,
                          dest      |-> Primary(rViewID[r]),
                          type      |-> MAbortResponse,
                          viewID    |-> rViewID[r],
                          seqNum    |-> m.seqNum],
                         [src       |-> r,
                          dest      |-> Primary(rViewID[r]),
                          type      |-> MWriteResponse,
                          viewID    |-> rViewID[r],
                          seqNum    |-> m.seqNum,
                          succeeded |-> FALSE]})
    /\ UNCHANGED <<globalVars, clientVars, rStatus, rViewID, rLastView, rViewChanges>>

HandleAbortResponse(r, s, m) ==
    /\ rStatus[r] = SAborting
    /\ m.viewID = rViewID[r]
    /\ IsPrimary(r)
    /\ m.seqNum = rAbortSeqNum[r][m.client]
    /\ rAbortResps' = [rAbortResps EXCEPT ![r] = [rAbortResps[r] EXCEPT ![m.client] = rAbortResps[r][m.client] \cup {m}]]
    /\ LET resps == {res.src : res \in {resp \in rAbortResps'[r][m.client] :
                                  /\ resp.viewID = rViewID[r]
                                  /\ resp.seqNum = rAbortSeqNum[r][m.client]}}
           isQuorum == r \in resps /\ resps \in Quorums
       IN
          \/ /\ isQuorum
             /\ rStatus' = [rStatus EXCEPT ![r] = [rStatus[r] EXCEPT ![m.client] = SNormal]]
          \/ /\ ~isQuorum
             /\ UNCHANGED <<rStatus>>
    /\ UNCHANGED <<globalVars, clientVars>>

ChangeView(r) ==
    /\ Sends({[src    |-> r,
               dest   |-> d,
               type   |-> MViewChangeRequest,
               viewID |-> rViewID[r] + 1] : d \in Replicas})
    /\ UNCHANGED <<globalVars, clientVars, replicaVars>>

HandleViewChangeRequest(r, s, m) ==
    /\ rViewID[r] < m.viewID
    /\ rViewID'      = [rViewID EXCEPT ![r] = m.viewID]
    /\ rStatus'      = [rStatus EXCEPT ![r] = SViewChange]
    /\ rViewChanges' = [rViewChanges EXCEPT ![r] = {}]
    /\ Reply(m, [src        |-> r,
                 dest       |-> Primary(m.viewID),
                 type       |-> MViewChangeResponse,
                 viewID     |-> m.viewID,
                 lastViewID |-> rLastView[r],
                 logs       |-> rLog[r]])
    /\ UNCHANGED <<globalVars, clientVars, rLog, rSeqNum, rAbortSeqNum, rAbortResps, rLastView>>

HandleViewChangeResponse(r, s, m) ==
    /\ IsPrimary(r)
    /\ rViewID[r]    = m.viewID
    /\ rStatus[r]    = SViewChange
    /\ rViewChanges' = [rViewChanges EXCEPT ![r] = rViewChanges[r] \cup {m}]
    /\ LET viewChanges    == {v \in rViewChanges'[r][m.client] : /\ v.viewID = rViewID[r]}
           viewSources    == {v.src : v \in viewChanges}
           isQuorum       == r \in viewSources /\ viewSources \in Quorums
           lastViews      == {v.lastViewID : v \in viewChanges}
           lastView       == (CHOOSE v1 \in lastViews : \A v2 \in lastViews : v2 <= v1)
           viewLogs       == [c \in Clients |-> {v1.logs[c] : v1 \in {v2 \in viewChanges : v2.lastView = lastView}}]
           mergeEnts(es)  ==
               IF es = {} \/ \E e \in es : r.type = TNoOp THEN
                   [type |-> TNoOp]
               ELSE
                   CHOOSE e \in es : e.type # TNoOp
           range(ls)      == Max({Len(l) : l \in ls})
           entries(ls, i) == {l[i] : l \in {k \in ls : i <= Len(k)}}
           mergeLogs(ls)  == [i \in 1..range(ls) |-> mergeEnts(entries(ls, i))]
       IN
           \/ /\ isQuorum
              /\ Replies(m, {[src    |-> r,
                              dest   |-> d,
                              type   |-> MStartViewRequest,
                              viewID |-> rViewID[r],
                              logs   |-> [c \in Clients |-> mergeLogs(viewLogs[c])]] : d \in Replicas})
           \/ /\ ~isQuorum
              /\ Discard(m)
    /\ UNCHANGED <<globalVars, clientVars, rStatus, rViewID, rLog, rSeqNum, rAbortSeqNum, rAbortResps, rLastView>>

HandleStartViewRequest(r, s, m) ==
    /\ \/ rViewID[r] < m.viewID
       \/ /\ rViewID[r] = m.viewID
          /\ rStatus[r] = SViewChange
    /\ rLog'      = [rLog      EXCEPT ![r] = m.log]
    /\ rStatus'   = [rStatus   EXCEPT ![r] = SNormal]
    /\ rViewID'   = [rViewID   EXCEPT ![r] = m.viewID]
    /\ rLastView' = [rLastView EXCEPT ![r] = m.viewID]
    /\ Discard(m)
    /\ UNCHANGED <<globalVars, clientVars, rViewChanges>>

----


InitMessageVars ==
    /\ messages = {}

InitClientVars ==
    /\ cTime      = 0
    /\ cViewID    = [c \in Clients |-> 1]
    /\ cSeqNum    = [c \in Clients |-> 0]
    /\ cResps = [c \in Clients |-> [r \in Replicas |-> [s \in {} |-> [index |-> 0, checksum |-> Nil]]]]
    /\ cWrites    = [c \in Clients |-> {}]
    /\ cReads     = [c \in Clients |-> {}]

InitReplicaVars ==
    /\ replicas     = SeqFromSet(Replicas)
    /\ rStatus      = [r \in Replicas |-> SNormal]
    /\ rLog         = [r \in Replicas |-> [c \in Clients |-> <<>>]]
    /\ rSeqNum      = [r \in Replicas |-> [c \in Clients |-> 0]]
    /\ rAbortSeqNum = [r \in Replicas |-> [c \in Clients |-> 0]]
    /\ rAbortResps  = [r \in Replicas |-> [c \in Clients |-> {}]]
    /\ rViewID      = [r \in Replicas |-> 1]
    /\ rLastView    = [r \in Replicas |-> 1]
    /\ rViewChanges = [r \in Replicas |-> {}]

Init ==
    /\ InitMessageVars
    /\ InitClientVars
    /\ InitReplicaVars
    /\ transitions = 0

----

\* The type invariant checks that no read ever reads a different value than a previous write
Inv == TRUE \* TODO

Transition == transitions' = transitions + 1

Next ==
    \/ \E c \in Clients :
          /\ Write(c)
          /\ Transition
    \/ \E c \in Clients : 
          /\ Read(c)
          /\ Transition
    \/ \E r \in Replicas : 
          /\ ChangeView(r)
          /\ Transition
    \/ \E m \in messages :
          /\ m.type = MWriteRequest
          /\ HandleWriteRequest(m.dest, m.src, m)
          /\ Transition
    \/ \E m \in messages :
          /\ m.type = MWriteResponse
          /\ HandleWriteResponse(m.dest, m.src, m)
          /\ Transition
    \/ \E m \in messages :
          /\ m.type = MReadRequest
          /\ HandleReadRequest(m.dest, m.src, m)
          /\ Transition
    \/ \E m \in messages :
          /\ m.type = MReadResponse
          /\ HandleReadResponse(m.dest, m.src, m)
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

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Tue Sep 22 05:04:13 PDT 2020 by jordanhalterman
\* Created Fri Sep 18 22:45:21 PDT 2020 by jordanhalterman
