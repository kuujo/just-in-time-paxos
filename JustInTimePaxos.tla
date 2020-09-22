-------------------------- MODULE JustInTimePaxos --------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

\* The set of Paxos replicas
CONSTANT Replicas

\* The set of Paxos clients
CONSTANT Clients

\* The maximum clock interval
CONSTANT MaxClockInterval

\* An empty value
CONSTANT Nil

\* Client request/response types+
CONSTANTS
    WriteRequest,
    WriteResponse,
    ReadRequest,
    ReadResponse

\* Server request/response types
CONSTANTS
    ViewChangeRequest,
    ViewChangeResponse,
    StartViewRequest

\* Replica roles
CONSTANTS
    NormalStatus,
    ViewChangeStatus,
    RecoveringStatus

----

VARIABLE replicas

globalVars == <<replicas>>

VARIABLE messages

messageVars == <<messages>>

VARIABLE time

VARIABLE requestID

VARIABLE responses

VARIABLE writes

VARIABLE reads

clientVars == <<time, requestID, responses, writes, reads>>

VARIABLE status

VARIABLE log

VARIABLE viewID

VARIABLE lastNormalView

VARIABLE viewChanges

replicaVars == <<status, log, viewID, lastNormalView, viewChanges>>

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

IsPrimary(r) == Primary(viewID[r]) = r

----

\* Messaging helpers

Sends(ms) == messages' = messages \cup ms

Send(m) == Sends({m})

Replies(req, resps) == messages' = (messages \cup resps) \ {req}

Reply(req, resp) == Replies(req, {resp})

Discard(m) == messages' = messages \ {m}

----

Write(c) ==
    /\ time' = time + 1
    /\ requestID' = [requestID EXCEPT ![c] = requestID[c] + 1]
    /\ Sends({[src       |-> c,
               dest      |-> r,
               type      |-> WriteRequest,
               requestID |-> requestID'[c],
               timestamp |-> time'] : r \in Replicas})
    /\ UNCHANGED <<globalVars, replicaVars, responses, writes, reads>>

Read(c) ==
    /\ requestID' = [requestID EXCEPT ![c] = requestID[c] + 1]
    /\ Sends({[src       |-> c,
               dest      |-> r,
               type      |-> ReadRequest,
               requestID |-> requestID'[c]] : r \in Replicas})
    /\ UNCHANGED <<globalVars, replicaVars, time, responses, writes, reads>>

ChecksumsMatch(c1, c2) ==
    /\ Len(c1) = Len(c2)
    /\ ~\E i \in DOMAIN c1 : c1[i] # c2[i]

IsCommitted(acks) ==
    \E msgs \in SUBSET acks :
       /\ {m.src    : m \in msgs} \in Quorums
       /\ \E m1 \in msgs : \A m2 \in msgs : m1.viewID = m2.viewID /\ ChecksumsMatch(m1.checksum, m2.checksum)
       /\ \E m \in msgs : m.primary

HandleWriteResponse(c, r, m) ==
    /\ ~\E w \in writes[c] : w.requestID = m.requestID
    /\ \/ /\ m.requestID \notin DOMAIN responses[c][r]
          /\ responses' = [responses EXCEPT ![c] = [responses[c] EXCEPT ![r] = responses[c][r] @@ (m.requestID :> m)]]
          /\ UNCHANGED <<writes>>
       \/ /\ m.requestID \in DOMAIN responses[c][r]
          \* Do not overwrite a response from a newer view
          /\ responses[c][r][m.requestID].viewID <= m.viewID
          /\ responses' = [responses EXCEPT ![c] = [responses[c] EXCEPT ![r] = [responses[c][r] EXCEPT ![m.requestID] = m]]]
          /\ LET committed == IsCommitted({responses'[c][x][m.requestID] : x \in {x \in Replicas : m.requestID \in DOMAIN responses'[c][x]}})
             IN
                \/ /\ committed
                   /\ writes' = [writes EXCEPT ![c] = writes[c] \cup {m}]
                \/ /\ ~committed
                   /\ UNCHANGED <<writes>>
    /\ Discard(m)
    /\ UNCHANGED <<globalVars, replicaVars, time, requestID, reads>>

HandleReadResponse(c, r, m) ==
    /\ \/ /\ m.primary
          /\ m \notin reads[c]
          /\ reads' = [reads EXCEPT ![c] = reads[c] \cup {m}]
       \/ /\ ~m.primary
          /\ UNCHANGED <<reads>>
    /\ Discard(m)
    /\ UNCHANGED <<globalVars, replicaVars, time, requestID, responses, writes>>

----

\* Server request/response handling

HandleWriteRequest(r, c, m) ==
    /\ status[r] = NormalStatus
    /\ \/ /\ \/ Len(log[r]) = 0
             \/ /\ Len(log[r]) # 0
                /\ m.timestamp > log[r][Len(log[r])].timestamp
          /\ LET checksum == Append([i \in DOMAIN log[r] |-> log[r][i].timestamp], m.timestamp)
                 entry    == [client    |-> c,
                              requestID |-> m.requestID,
                              timestamp |-> m.timestamp,
                              checksum  |-> checksum]
             IN
                /\ log' = [log EXCEPT ![r] = Append(log[r], entry)]
                /\ Reply(m, [src       |-> r,
                             dest      |-> c,
                             type      |-> WriteResponse,
                             requestID |-> m.requestID,
                             viewID    |-> viewID[r],
                             primary   |-> IsPrimary(r),
                             index     |-> Len(log'[r]),
                             checksum  |-> log'[r][Len(log'[r])].checksum,
                             succeeded |-> TRUE])
       \/ /\ Len(log[r]) # 0
          /\ m.timestamp <= log[r][Len(log[r])].timestamp
          /\ Reply(m, [src       |-> r,
                       dest      |-> c,
                       type      |-> WriteResponse,
                       requestID |-> m.requestID,
                       viewID    |-> viewID[r],
                       primary   |-> IsPrimary(r),
                       index     |-> Len(log[r]),
                       checksum  |-> log[r][Len(log[r])].checksum,
                       succeeded |-> FALSE])
          /\ UNCHANGED <<log>>
    /\ UNCHANGED <<globalVars, clientVars, status, viewID, lastNormalView, viewChanges>>

HandleReadRequest(r, c, m) ==
    /\ status[r] = NormalStatus
    /\ Len(log[r]) > 0
    /\ Reply(m, [src       |-> r,
                 dest      |-> c,
                 type      |-> ReadResponse,
                 requestID |-> m.requestID,
                 viewID    |-> viewID[r],
                 primary   |-> IsPrimary(r),
                 index     |-> Len(log[r]),
                 checksum  |-> log[r][Len(log[r])].checksum,
                 succeeded |-> TRUE])
    /\ UNCHANGED <<globalVars, clientVars, status, log, viewID, lastNormalView, viewChanges>>

ChangeView(r) ==
    /\ Sends({[src    |-> r,
               dest   |-> d,
               type   |-> ViewChangeRequest,
               viewID |-> viewID[r] + 1] : d \in Replicas})
    /\ UNCHANGED <<globalVars, clientVars, replicaVars>>

HandleViewChangeRequest(r, s, m) ==
    /\ viewID[r] < m.viewID
    /\ viewID'      = [viewID EXCEPT ![r] = m.viewID]
    /\ status'      = [status EXCEPT ![r] = ViewChangeStatus]
    /\ viewChanges' = [viewChanges EXCEPT ![r] = {}]
    /\ Reply(m, [src        |-> r,
                 dest       |-> Primary(m.viewID),
                 type       |-> ViewChangeResponse,
                 viewID     |-> m.viewID,
                 lastNormal |-> lastNormalView[r],
                 log        |-> log[r]])
    /\ UNCHANGED <<globalVars, clientVars, log, lastNormalView>>

HandleViewChangeResponse(r, s, m) ==
    /\ IsPrimary(r)
    /\ viewID[r]    = m.viewID
    /\ status[r]    = ViewChangeStatus
    /\ viewChanges' = [viewChanges EXCEPT ![r] = viewChanges[r] \cup {m}]
    /\ LET
          isViewQuorum(vs) == IsQuorum(vs) /\ \E v \in vs : v.src = r
          newViewChanges   == {v \in viewChanges'[r] : v.viewID = viewID[r]}
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
                             type   |-> StartViewRequest,
                             viewID |-> viewID[r],
                             log    |-> combineLogs(goodLogs)] : d \in Replicas})
          \/ /\ ~isViewQuorum(newViewChanges)
             /\ Discard(m)
    /\ UNCHANGED <<globalVars, clientVars, status, viewID, log, lastNormalView>>

HandleStartViewRequest(r, s, m) ==
    /\ \/ viewID[r] < m.viewID
       \/ /\ viewID[r] = m.viewID
          /\ status[r] = ViewChangeStatus
    /\ log'            = [log EXCEPT ![r] = m.log]
    /\ status'         = [status EXCEPT ![r] = NormalStatus]
    /\ viewID'         = [viewID EXCEPT ![r] = m.viewID]
    /\ lastNormalView' = [lastNormalView EXCEPT ![r] = m.viewID]
    /\ Discard(m)
    /\ UNCHANGED <<globalVars, clientVars, viewChanges>>

----


InitMessageVars ==
    /\ messages = {}

InitClientVars ==
    /\ time = 0
    /\ requestID  = [c \in Clients |-> 0]
    /\ responses  = [c \in Clients |-> [r \in Replicas |-> [s \in {} |-> [index |-> 0, checksum |-> Nil]]]]
    /\ writes     = [c \in Clients |-> {}]
    /\ reads      = [c \in Clients |-> {}]

InitReplicaVars ==
    /\ replicas       = SeqFromSet(Replicas)
    /\ status         = [r \in Replicas |-> NormalStatus]
    /\ log            = [r \in Replicas |-> <<>>]
    /\ viewID         = [r \in Replicas |-> 1]
    /\ lastNormalView = [r \in Replicas |-> 1]
    /\ viewChanges    = [r \in Replicas |-> {}]

Init ==
    /\ InitMessageVars
    /\ InitClientVars
    /\ InitReplicaVars
    /\ transitions = 0

----

\* The type invariant checks that no read ever reads a different value than a previous write
Inv == 
   /\ \A c1, c2 \in Clients :
         ~\E r \in reads[c1] :
            \E w \in writes[c2] : 
               /\ r.index = w.index 
               /\ ~ChecksumsMatch(r.checksum, w.checksum)
   /\ \A c1, c2 \in Clients:
         ~\E r1 \in reads[c1] :
            \E r2 \in reads[c2] :
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
          /\ m.type = WriteRequest
          /\ HandleWriteRequest(m.dest, m.src, m)
          /\ Transition
    \/ \E m \in messages :
          /\ m.type = WriteResponse
          /\ HandleWriteResponse(m.dest, m.src, m)
          /\ Transition
    \/ \E m \in messages :
          /\ m.type = ReadRequest
          /\ HandleReadRequest(m.dest, m.src, m)
          /\ Transition
    \/ \E m \in messages :
          /\ m.type = ReadResponse
          /\ HandleReadResponse(m.dest, m.src, m)
          /\ Transition
    \/ \E m \in messages :
          /\ m.type = ViewChangeRequest
          /\ HandleViewChangeRequest(m.dest, m.src, m)
          /\ Transition
    \/ \E m \in messages :
          /\ m.type = ViewChangeResponse
          /\ HandleViewChangeResponse(m.dest, m.src, m)
          /\ Transition
    \/ \E m \in messages :
          /\ m.type = StartViewRequest
          /\ HandleStartViewRequest(m.dest, m.src, m)
          /\ Transition

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Tue Sep 22 01:06:09 PDT 2020 by jordanhalterman
\* Created Fri Sep 18 22:45:21 PDT 2020 by jordanhalterman
