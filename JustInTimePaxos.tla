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

ChecksumsMatch(c1, c2) ==
    /\ Len(c1) = Len(c2)
    /\ ~\E i \in DOMAIN c1 : c1[i] # c2[i]

IsCommitted(acks) ==
    \E msgs \in SUBSET acks :
       /\ {m.src    : m \in msgs} \in Quorums
       /\ \E m1 \in msgs : \A m2 \in msgs : m1.viewID = m2.viewID /\ ChecksumsMatch(m1.checksum, m2.checksum)
       /\ \E m \in msgs : m.primary

HandleWriteResponse(c, r, m) ==
    /\ ~\E w \in cWrites[c] : w.seqNum = m.seqNum
    /\ \/ /\ m.seqNum \notin DOMAIN cResps[c][r]
          /\ cResps' = [cResps EXCEPT ![c] = [cResps[c] EXCEPT ![r] = cResps[c][r] @@ (m.seqNum :> m)]]
          /\ UNCHANGED <<cWrites>>
       \/ /\ m.seqNum \in DOMAIN cResps[c][r]
          \* Do not overwrite a response from a newer view
          /\ cResps[c][r][m.seqNum].viewID <= m.viewID
          /\ cResps' = [cResps EXCEPT ![c] = [cResps[c] EXCEPT ![r] = [cResps[c][r] EXCEPT ![m.seqNum] = m]]]
          /\ LET committed == IsCommitted({cResps'[c][x][m.seqNum] : x \in {x \in Replicas : m.seqNum \in DOMAIN cResps'[c][x]}})
             IN
                \/ /\ committed
                   /\ cWrites' = [cWrites EXCEPT ![c] = cWrites[c] \cup {m}]
                \/ /\ ~committed
                   /\ UNCHANGED <<cWrites>>
    /\ Discard(m)
    /\ UNCHANGED <<globalVars, replicaVars, cTime, cSeqNum, cReads>>

HandleReadResponse(c, r, m) ==
    /\ \/ /\ m.primary
          /\ m \notin cReads[c]
          /\ cReads' = [cReads EXCEPT ![c] = cReads[c] \cup {m}]
       \/ /\ ~m.primary
          /\ UNCHANGED <<cReads>>
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
          /\ m.seqNum = rSeqNum[r][c] + 1
          /\ rLog' = [rLog EXCEPT ![r] = Append(rLog[r], m)]
          /\ rSeqNum' = [rSeqNum EXCEPT ![r] = m.seqNum]
          /\ Reply(m, [src       |-> r,
                       dest      |-> c,
                       type      |-> MWriteResponse,
                       seqNum    |-> m.seqNum,
                       viewID    |-> rViewID[r],
                       succeeded |-> TRUE])
       \/ /\ m.viewID = rViewID[r]
          /\ m.seqNum > rSeqNum[r][c] + 1
          /\ \/ /\ IsPrimary(r)
                /\ Abort(r, c, m)
             \/ /\ ~IsPrimary(r)
                /\ Repair(r, c, m)
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
    /\ \/ /\ m.seqNum <= Len(rLog[r][m.client])
          /\ Reply(m, [src    |-> r,
                       dest   |-> s,
                       type   |-> MRepairResponse,
                       viewID |-> rViewID[r],
                       client |-> m.client,
                       seqNum |-> m.seqNum])
          /\ UNCHANGED <<rStatus, rAbortResps, rAbortSeqNum>>
       \/ /\ m.seqNum = Len(rLog[r][m.client]) + 1
          /\ Abort(r, m.client, m)
    /\ UNCHANGED <<globalVars, clientVars>>

HandleRepairResponse(r, s, m) ==
    /\ HandleWriteRequest(r, m.client, [m EXCEPT !.src = m.client])

HandleAbortRequest(r, s, m) ==
    /\ m.viewID = rViewID[r]
    /\ m.seqNum <= Len(rLog[r][m.client]) + 1
    /\ rStatus[r] \in {SNormal, SAborting} 
    /\ rLog' = [rLog EXCEPT ![r] = [rLog[r] EXCEPT ![m.client] = Replace(rLog[r][m.client], m.seqNum, Nil)]]
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
                 lastNormal |-> rLastView[r],
                 log        |-> rLog[r]])
    /\ UNCHANGED <<globalVars, clientVars, rLog, rLastView>>

HandleViewChangeResponse(r, s, m) ==
    /\ IsPrimary(r)
    /\ rViewID[r]    = m.viewID
    /\ rStatus[r]    = SViewChange
    /\ rViewChanges' = [rViewChanges EXCEPT ![r] = rViewChanges[r] \cup {m}]
    /\ LET
          isViewQuorum(vs) == IsQuorum(vs) /\ \E v \in vs : v.src = r
          newViewChanges   == {v \in rViewChanges'[r] : v.viewID = rViewID[r]}
          normalViews      == {v.lastNormal : v \in newViewChanges}
          lastNormal       == CHOOSE v \in normalViews : \A v2 \in normalViews : v2 <= v
          goodLogs         == {n.log : n \in {v \in newViewChanges : v.lastNormal = lastNormal}}
          combineLogs(ls)  ==
             LET 
                indexLogs(i)           == {l \in ls : Len(l) >= i}
                indexEntries(i)        == {l[i] : l \in indexLogs(i)}
                quorumLogs(i)          == {L \in SUBSET indexLogs(i) : IsQuorum(L)}
                isCommittedEntry(i, e) == \A L \in quorumLogs(i) :
                                             \E l \in L : 
                                                ChecksumsMatch(e.checksum, l[i].checksum)
                isCommittedIndex(i)    == \E e \in indexEntries(i) : isCommittedEntry(i, e)
                commit(i)              == CHOOSE e \in indexEntries(i) : isCommittedEntry(i, e)
                maxIndex               == Max({Len(l) : l \in ls})
                committedIndexes       == {i \in 1..maxIndex : isCommittedIndex(i)}
                maxCommit              == IF Cardinality(committedIndexes) > 0 THEN Max(committedIndexes) ELSE 0
             IN
                [i \in 1..maxCommit |-> commit(i)]
       IN
          \/ /\ isViewQuorum(newViewChanges)
             /\ Replies(m, {[src    |-> r,
                             dest   |-> d,
                             type   |-> MStartViewRequest,
                             viewID |-> rViewID[r],
                             log    |-> combineLogs(goodLogs)] : d \in Replicas})
          \/ /\ ~isViewQuorum(newViewChanges)
             /\ Discard(m)
    /\ UNCHANGED <<globalVars, clientVars, rStatus, rViewID, rLog, rLastView>>

HandleStartViewRequest(r, s, m) ==
    /\ \/ rViewID[r] < m.viewID
       \/ /\ rViewID[r] = m.viewID
          /\ rStatus[r] = SViewChange
    /\ rLog'            = [rLog EXCEPT ![r] = m.log]
    /\ rStatus'         = [rStatus EXCEPT ![r] = SNormal]
    /\ rViewID'         = [rViewID EXCEPT ![r] = m.viewID]
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
Inv == 
   /\ \A c1, c2 \in Clients :
         ~\E r \in cReads[c1] :
            \E w \in cWrites[c2] : 
               /\ r.index = w.index 
               /\ ~ChecksumsMatch(r.checksum, w.checksum)
   /\ \A c1, c2 \in Clients:
         ~\E r1 \in cReads[c1] :
            \E r2 \in cReads[c2] :
               /\ r1.index = r2.index 
               /\ ~ChecksumsMatch(r1.checksum, r2.checksum)

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
\* Last modified Tue Sep 22 03:02:49 PDT 2020 by jordanhalterman
\* Created Fri Sep 18 22:45:21 PDT 2020 by jordanhalterman
