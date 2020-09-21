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
                         \* SlotLookup
                         \* SlotLookupRep
                         \* GapCommit
                         \* GapCommitRep
    ViewChangeRequest,   \* ViewChangeReq
    ViewChangeResponse,  \* ViewChange
    StartViewRequest,    \* StartView
    SyncPrepareRequest,  \* SyncPrepare
    SyncPrepareResponse, \* SyncPrepareRep
    SyncCommitRequest    \* SyncCommit

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

VARIABLE viewID

VARIABLE log

replicaVars == <<status, viewID, log>>

VARIABLE transitions

vars == <<globalVars, messageVars, clientVars, replicaVars, transitions>>

----

\* Helpers

RECURSIVE SeqFromSet(_)
SeqFromSet(S) == 
  IF S = {} THEN << >> 
  ELSE LET x == CHOOSE x \in S : TRUE
       IN  << x >> \o SeqFromSet(S \ {x})

Quorums == {r \in SUBSET Replicas : Cardinality(r) * 2 > Cardinality(Replicas)}

Primary(v) == replicas[(v%Len(replicas)) + (IF v >= Len(replicas) THEN 1 ELSE 0)]

IsPrimary(r) == Primary(viewID[r]) = r

----

\* Messaging helpers

Sends(m) == messages' = messages \cup m

Send(m) == Sends({m})

Reply(req, res) == messages' = messages \cap {req, res}

Discard(m) == messages' = messages \cap {m}

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
    /\ Sends({[source    |-> c,
                      target    |-> r,
                      type      |-> WriteRequest,
                      requestID |-> requestID'[c],
                      timestamp |-> CurrentTime(c)] : r \in Replicas})
    /\ UNCHANGED <<globalVars, replicaVars, responses, writes, reads>>

Read(c) ==
    /\ requestID' = [requestID EXCEPT ![c] = requestID[c] + 1]
    /\ Sends({[source    |-> c,
                      target    |-> r,
                      type      |-> ReadRequest,
                      requestID |-> requestID'[c]] : r \in Replicas})
    /\ UNCHANGED <<globalVars, replicaVars, globalTime, time, responses, writes, reads>>

IsCommitted(acks) ==
    \E msgs \in SUBSET acks :
       /\ {m.source : m \in msgs} \in Quorums
       /\ \E m1 \in msgs : \A m2 \in msgs : m1.viewID = m2.viewID /\ m1.checksum \cap m2.checksum = {}
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
    /\ UNCHANGED <<globalVars, messageVars, replicaVars, globalTime, time, requestID, reads>>

HandleReadResponse(c, r, m) ==
    /\ \/ /\ m.primary
          /\ m \notin reads[c]
          /\ reads' = [reads EXCEPT ![c] = reads[c] \cup {m}]
       \/ /\ ~m.primary
          /\ UNCHANGED <<reads>>
    /\ Discard(m)
    /\ UNCHANGED <<globalVars, replicaVars, globalTime, time, requestID, writes>>

----

\* Server request/response handling

HandleWriteRequest(r, c, m) ==
    /\ status[r] = NormalStatus
    /\ \/ /\ \/ Len(log[r]) = 0
             \/ /\ Len(log[r]) # 0
                /\ m.timestamp > log[r][Len(log[r])].timestamp
          /\ log' = [log EXCEPT ![r] = Append(log[r], m)]
          /\ Reply(m, [source    |-> r,
                       target    |-> c,
                       type      |-> WriteResponse,
                       requestID |-> m.requestID,
                       viewID    |-> viewID[r],
                       primary   |-> IsPrimary(r),
                       index     |-> Len(log'[r]),
                       checksum  |-> {log'[r][i].timestamp : i \in DOMAIN log'[r]},
                       succeeded |-> TRUE])
       \/ /\ Len(log[r]) # 0
          /\ m.timestamp <= log[r][Len(log[r])].timestamp
          /\ Reply(m, [source    |-> r,
                       target    |-> c,
                       type      |-> WriteResponse,
                       requestID |-> m.requestID,
                       viewID    |-> viewID[r],
                       primary   |-> IsPrimary(r),
                       index     |-> Len(log[r]),
                       checksum  |-> {log[r][i].timestamp : i \in DOMAIN log[r]},
                       succeeded |-> FALSE])
          /\ UNCHANGED <<log>>
    /\ UNCHANGED <<globalVars, clientVars, status, viewID>>

HandleReadRequest(r, c, m) ==
    /\ status[r] = NormalStatus
    /\ Len(log[r]) > 0
    /\ Reply(m, [source    |-> r,
                 target    |-> c,
                 type      |-> WriteResponse,
                 requestID |-> m.requestID,
                 viewID    |-> viewID[r],
                 primary   |-> IsPrimary(r),
                 index     |-> Len(log[r]),
                 checksum  |-> {log[r][i].timestamp : i \in DOMAIN log[r]},
                 succeeded |-> TRUE])
    /\ UNCHANGED <<globalVars, clientVars, status, viewID, log>>

HandleViewChangeRequest(r, s, m) ==
    /\ FALSE
    /\ UNCHANGED <<globalVars, messageVars, clientVars, replicaVars>>

HandleViewChangeResponse(r, s, m) ==
    /\ FALSE
    /\ UNCHANGED <<globalVars, messageVars, clientVars, replicaVars>>

HandleStartViewRequest(r, s, m) ==
    /\ FALSE
    /\ UNCHANGED <<globalVars, messageVars, clientVars, replicaVars>>

HandleSyncPrepareRequest(r, s, m) ==
    /\ FALSE
    /\ UNCHANGED <<globalVars, messageVars, clientVars, replicaVars>>

HandleSyncPrepareResponse(r, s, m) ==
    /\ FALSE
    /\ UNCHANGED <<globalVars, messageVars, clientVars, replicaVars>>

HandleSyncCommitRequest(r, s, m) ==
    /\ FALSE
    /\ UNCHANGED <<globalVars, messageVars, clientVars, replicaVars>>

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
    /\ viewID = [r \in Replicas |-> 1]
    /\ log = [r \in Replicas |-> <<>>]

Init ==
    /\ InitMessageVars
    /\ InitClientVars
    /\ InitReplicaVars
    /\ transitions = 0

----

\* The type invariant checks that no read ever reads a different value than a previous write
Inv == \A c1, c2 \in Clients :
          ~\E r \in reads[c1] :
             \E w \in writes[c2] : 
                r.index = w.index /\ r.requestID # w.requestID

Next ==
    \/ \E c \in Clients :
       /\ Write(c)
       /\ transitions' = transitions + 1
    \/ \E c \in Clients : 
       /\ Read(c)
       /\ transitions' = transitions + 1
    \/ \E m \in messages :
       /\ m.type = WriteRequest
       /\ HandleWriteRequest(m.target, m.source, m)
       /\ transitions' = transitions + 1
    \/ \E m \in messages :
       /\ m.type = WriteResponse
       /\ HandleWriteResponse(m.target, m.source, m)
       /\ transitions' = transitions + 1
    \/ \E m \in messages :
       /\ m.type = ReadRequest
       /\ HandleReadRequest(m.target, m.source, m)
       /\ transitions' = transitions + 1
    \/ \E m \in messages :
       /\ m.type = ReadResponse
       /\ HandleReadResponse(m.target, m.source, m)
       /\ transitions' = transitions + 1
    \/ \E m \in messages :
       /\ m.type = ViewChangeRequest
       /\ HandleViewChangeRequest(m.target, m.source, m)
       /\ transitions' = transitions + 1
    \/ \E m \in messages :
       /\ m.type = ViewChangeResponse
       /\ HandleViewChangeResponse(m.target, m.source, m)
       /\ transitions' = transitions + 1
    \/ \E m \in messages :
       /\ m.type = StartViewRequest
       /\ HandleStartViewRequest(m.target, m.source, m)
       /\ transitions' = transitions + 1
    \/ \E m \in messages :
       /\ m.type = SyncPrepareRequest
       /\ HandleSyncPrepareRequest(m.target, m.source, m)
       /\ transitions' = transitions + 1
    \/ \E m \in messages :
       /\ m.type = SyncPrepareResponse
       /\ HandleSyncPrepareResponse(m.target, m.source, m)
       /\ transitions' = transitions + 1
    \/ \E m \in messages :
       /\ m.type = SyncCommitRequest
       /\ HandleSyncCommitRequest(m.target, m.source, m)
       /\ transitions' = transitions + 1

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Sun Sep 20 18:45:13 PDT 2020 by jordanhalterman
\* Created Fri Sep 18 22:45:21 PDT 2020 by jordanhalterman
