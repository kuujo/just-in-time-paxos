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

VARIABLE globalTime

VARIABLE time

VARIABLE requestID

VARIABLE responses

VARIABLE writes

VARIABLE reads

clientVars == <<globalTime, time, requestID, responses, writes, reads>>

VARIABLE status

VARIABLE log

VARIABLE viewID

VARIABLE lastNormalView

VARIABLE viewChangeResponses

replicaVars == <<status, log, viewID, lastNormalView, viewChangeResponses>>

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

Replies(reqs, resps) == messages' = (messages \cup resps) \ reqs

Reply(req, resp) == Replies({req}, {resp})

Discard(m) == messages' = messages \ {m}

----

AdvanceTime(c) == 
    /\ globalTime' = globalTime + 1
    /\ IF time[c] < globalTime /\ globalTime - time[c] > MaxClockInterval THEN
           time' = [time EXCEPT ![c] = globalTime' - MaxClockInterval]
       ELSE
           time' = [time EXCEPT ![c] = time[c] + 1]

CurrentTime(c) == time'[c]

Write(c) ==
    /\ AdvanceTime(c)
    /\ requestID' = [requestID EXCEPT ![c] = requestID[c] + 1]
    /\ Sends({[src       |-> c,
               dest      |-> r,
               type      |-> WriteRequest,
               requestID |-> requestID'[c],
               timestamp |-> CurrentTime(c)] : r \in Replicas})
    /\ UNCHANGED <<globalVars, replicaVars, responses, writes, reads>>

Read(c) ==
    /\ requestID' = [requestID EXCEPT ![c] = requestID[c] + 1]
    /\ Sends({[src       |-> c,
               dest      |-> r,
               type      |-> ReadRequest,
               requestID |-> requestID'[c]] : r \in Replicas})
    /\ UNCHANGED <<globalVars, replicaVars, globalTime, time, responses, writes, reads>>

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
    /\ UNCHANGED <<globalVars, replicaVars, globalTime, time, requestID, reads>>

HandleReadResponse(c, r, m) ==
    /\ \/ /\ m.primary
          /\ m \notin reads[c]
          /\ reads' = [reads EXCEPT ![c] = reads[c] \cup {m}]
       \/ /\ ~m.primary
          /\ UNCHANGED <<reads>>
    /\ Discard(m)
    /\ UNCHANGED <<globalVars, replicaVars, globalTime, time, requestID, responses, writes>>

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
    /\ UNCHANGED <<globalVars, clientVars, status, viewID, lastNormalView, viewChangeResponses>>

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
    /\ UNCHANGED <<globalVars, clientVars, status, log, viewID, lastNormalView, viewChangeResponses>>

ChangeView(r) ==
    LET nextViewID == viewID[r] + 1
    IN
       /\ Primary(nextViewID) = r
       /\ status' = [status EXCEPT ![r] = ViewChangeStatus]
       /\ viewID' = [viewID EXCEPT ![r] = nextViewID]
       /\ viewChangeResponses' = [viewChangeResponses EXCEPT ![r] = {}]
       /\ Sends({[src    |-> r,
                  dest   |-> d,
                  type   |-> ViewChangeRequest,
                  viewID |-> nextViewID] : d \in Replicas})
       /\ UNCHANGED <<globalVars, clientVars, log, lastNormalView>>

HandleViewChangeRequest(r, s, m) ==
    /\ viewID[r] # m.viewID
    /\ viewID' = [viewID EXCEPT ![r] = m.viewID]
    /\ status' = [status EXCEPT ![r] = ViewChangeStatus]
    /\ viewChangeResponses' = [viewChangeResponses EXCEPT ![r] = {}]
    /\ Reply(m, [src        |-> r,
                 dest       |-> s,
                 type       |-> ViewChangeResponse,
                 viewID     |-> m.viewID,
                 lastNormal |-> lastNormalView[r],
                 log        |-> log[r]])
    /\ UNCHANGED <<globalVars, clientVars, log, lastNormalView>>

HandleViewChangeResponse(r, s, m) ==
    /\ viewID[r] = m.viewID
    /\ status[r] = ViewChangeStatus
    /\ IsPrimary(r)
    /\ viewChangeResponses' = [viewChangeResponses EXCEPT ![r] = viewChangeResponses[r] \cup {m}]
    /\ LET
          isViewQuorum(vs) == IsQuorum(vs) /\ \E v \in vs : v.src = r
          viewChanges == {n \in viewChangeResponses[r] : n.type = ViewChangeResponse /\ n.viewID = viewID[r]}
          normalViews == {n.lastNormal : n \in viewChanges}
          lastNormal == {CHOOSE v \in normalViews : \A v2 \in normalViews : v2 < v}
          goodLogs == {n.log : n \in {o \in viewChanges : o.lastNormal = lastNormal}}
          combineLogs(ls) ==
             LET 
                logsWith(i) == {l \in ls : Len(l) >= i}
                entries(i) == {l[i] : l \in logsWith(i)}
                quorums(i) == {l \in SUBSET logsWith(i) : IsQuorum(l)}
                checksums(l, i) == {e.checksum : e \in l[i]}
                isCommitted(i) == \E e \in entries(i) : \A l \in quorums(i) : e.checksum \in checksums(l, i)
                committed(i) == CHOOSE e \in entries(i) : \A l \in quorums(i) : e.checksum \in checksums(l, i)
                maxIndex == Max({Len(l) : l \in ls})
                maxCommitted == Max({i \in 1..maxIndex : isCommitted(i)})
             IN
                [i \in 1..maxCommitted |-> committed(i)]
       IN
          \/ /\ isViewQuorum(viewChanges)
             /\ Replies(m, {[src    |-> r,
                             dest   |-> d,
                             type   |-> StartViewRequest,
                             viewID |-> viewID[r],
                             log    |-> combineLogs(goodLogs)] : d \in Replicas})
          \/ /\ ~isViewQuorum(viewChanges)
             /\ Discard(m)
    /\ UNCHANGED <<globalVars, clientVars, status, viewID, log, lastNormalView>>

HandleStartViewRequest(r, s, m) ==
    /\ \/ viewID[r] < m.viewID
       \/ /\ viewID[r] = m.viewID
          /\ status[r] = ViewChangeStatus
    /\ log'    = [log EXCEPT ![r] = m.log]
    /\ status' = [status EXCEPT ![r] = NormalStatus]
    /\ viewID' = [viewID EXCEPT ![r] = m.viewID]
    /\ lastNormalView' = [lastNormalView EXCEPT ![r] = m.viewID]
    /\ Discard(m)
    /\ UNCHANGED <<globalVars, clientVars, viewChangeResponses>>

----


InitMessageVars ==
    /\ messages = {}

InitClientVars ==
    /\ globalTime = 0
    /\ time = [c \in Clients |-> 0]
    /\ requestID = [c \in Clients |-> 0]
    /\ responses = [c \in Clients |-> [r \in Replicas |-> [s \in {} |-> [index |-> 0, checksum |-> Nil]]]]
    /\ writes = [c \in Clients |-> {}]
    /\ reads = [c \in Clients |-> {}]

InitReplicaVars ==
    /\ replicas = SeqFromSet(Replicas)
    /\ status = [r \in Replicas |-> NormalStatus]
    /\ log = [r \in Replicas |-> <<>>]
    /\ viewID = [r \in Replicas |-> 1]
    /\ lastNormalView = [r \in Replicas |-> 1]
    /\ viewChangeResponses = [r \in Replicas |-> {}]

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
\* Last modified Mon Sep 21 15:12:31 PDT 2020 by jordanhalterman
\* Created Fri Sep 18 22:45:21 PDT 2020 by jordanhalterman
