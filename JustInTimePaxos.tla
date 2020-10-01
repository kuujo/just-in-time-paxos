-------------------------- MODULE JustInTimePaxos --------------------------

(***************************************************************************)
(* Defines the Just-In-Time Paxos (JITPaxos) protocol.  JITPaxos is a      *)
(* variant of the Paxos consensus protocol designed for environments where *)
(* process clocks are synchronized with high precision.  The protocol      *)
(* relies on synchronized clocks to establish a global total ordering of   *)
(* events, avoiding coordination between replicas when requests arrive in  *)
(* the expected order, and reconciling requests only when they arrive out  *)
(* of order.  This allows JITPaxos to reach consensus within a single      *)
(* round trip in the normal case, falling back to traditional replication  *)
(* strategies only when required.                                          *)
(*                                                                         *)
(* JITPaxos uses a view-based approach to elect a primary and reconcile    *)
(* logs across views.  Views are identified by a monotonically increasing, *)
(* globally unique view ID.  Each view deterministically assigns a quorum, *)
(* and within the quorum a primary replica responsible for executing       *)
(* client requests and reconciling inconsistencies in the logs of the      *)
(* remaining replicas.  JITPaxos replicas to not coordinate with each      *)
(* other in the normal case.  Clients send timestamped requests in         *)
(* parallel to every replica in the view's quorum.  When a replica         *)
(* receives a client request, if the request is received in chronological  *)
(* order, it's appended to the replica's log.  If a request is received    *)
(* out of order (i.e.  the request timestamp is less than the last         *)
(* timestamp in the replica's log), the request is rejected by the         *)
(* replica.  Clients are responsible for identifying inconsistencies in    *)
(* the quorum's logs and initiating the reconciliation protocol.  To help  *)
(* clients identify inconsistencies, replicas return a checksum            *)
(* representing the contents of the log up to the request point with each  *)
(* client reply.  If a client's request is received out of chronological   *)
(* order, or if the checksums provided by the quorum do not match, the     *)
(* client must initiate the reconcilitation protocol to reconcile the      *)
(* inconsistencies in the quorum's logs.                                   *)
(*                                                                         *)
(* When requests are received out-of-order, the reconciliation protocol    *)
(* works to re-order requests using the view's primary as a reference.     *)
(* When a client initiates the reconciliation protocol for an inconsistent *)
(* replica, the replica stops accepting client requests and sends a repair *)
(* request to the primary.  The primary responds with the subset of the    *)
(* log not yet reconciled on the replica, and the replica replaces the     *)
(* out-of-order entries in its log.  Once the replica's log has been       *)
(* reconciled with the primary, it can acknowledge the reconciled request  *)
(* and begin accepting requests again.  Once a client has reconciled all   *)
(* the divergent replicas and has received acknowledgement from each of    *)
(* the replicas in the quorum, the request can be committed.               *)
(*                                                                         *)
(* View primaries and quorums are evenly distributed amongst view IDs.     *)
(* View changes can be initiated to change the primary or the set of       *)
(* replicas in the quorum.  When a view change is initiated, each replica  *)
(* sends its log to the primary for the initiated view.  Once the primary  *)
(* has received logs from a majority of replicas, it initializes the view  *)
(* with the log from the most recent in-sync replica, broadcasting the log *)
(* to its peers.  The use of quorums to determine both the commitment of a *)
(* request and the initialization of new views ensures that each view log  *)
(* contains all prior committed requests.                                  *)
(***************************************************************************)

EXTENDS Naturals, Reals, Sequences, FiniteSets, TLC

\* The set of JITPaxos replicas
CONSTANT Replicas

\* The set of JITPaxos clients
CONSTANT Clients

\* The set of possible values
CONSTANT Values

\* An empty value
CONSTANT Nil

\* Request/response types
CONSTANTS
    MClientRequest,
    MClientReply,
    MReconcileRequest,
    MReconcileReply,
    MRepairRequest,
    MRepairReply,
    MViewChangeRequest,
    MViewChangeReply,
    MStartViewRequest

\* Replica statuses
CONSTANTS
    SInSync,
    SRepair,
    SViewChange
----

(***************************************************************************)
(* This section specifies the message types and schemas used in this spec. *)
(*                                                                         *)
(* ReqIDs == [c \in Clients |-> i \in (1..)]                               *)
(*                                                                         *)
(* ViewIDs == [r \in Replicas |-> i \in (1..)]                             *)
(*                                                                         *)
(* Logs == [r \in Replicas |-> [i \in (1..) |-> Value]]                    *)
(*                                                                         *)
(* Indexes == [r \in Replicas |-> i \in (1..)]                             *)
(*                                                                         *)
(* Timestamps == [r \in Replicas |-> i \in (1..)]                          *)
(*                                                                         *)
(* Checksums == [r \in Replicas |-> [i \in (1..) |-> t \in Timestamps]]    *)
(*                                                                         *)
(*   ClientRequest                                                         *)
(*     [ src       |-> c \in Clients,                                      *)
(*       dest      |-> r \in Replicas,                                     *)
(*       type      |-> MClientRequest,                                     *)
(*       viewID    |-> i \in ViewIDs,                                      *)
(*       reqID     |-> i \in ReqIDs,                                       *)
(*       value     |-> v \in Values,                                       *)
(*       timestamp |-> t \in Timestamps ]                                  *)
(*                                                                         *)
(*   ClientReply                                                           *)
(*     [ src       |-> r \in Replicas,                                     *)
(*       dest      |-> c \in Clients,                                      *)
(*       req       |-> (ClientRequest),                                    *)
(*       type      |-> MClientReply,                                       *)
(*       viewID    |-> i \in ViewIDs,                                      *)
(*       index     |-> i \in Indexes,                                      *)
(*       checksum  |-> c \in Checksums,                                    *)
(*       value     |-> v \in Values,                                       *)
(*       timestamp |-> t \in Timestamps,                                   *)
(*       succeeded |-> TRUE \/ FALSE ]                                     *)
(*                                                                         *)
(*   ReconcileRequest                                                      *)
(*     [ src    |-> c \in Clients,                                         *)
(*       dest   |-> r \in Replicas,                                        *)
(*       type   |-> MReconcileRequest,                                     *)
(*       viewID |-> i \in ViewIDs,                                         *)
(*       reqID  |-> i \in ReqIDs,                                          *)
(*       index  |-> i \in Indexes ]                                        *)
(*                                                                         *)
(*   ReconcileReply                                                        *)
(*     [ src       |-> r \in Replicas,                                     *)
(*       dest      |-> c \in Clients,                                      *)
(*       req       |-> (ClientRequest),                                    *)
(*       type      |-> MReconcileReply,                                    *)
(*       viewID    |-> i \in ViewIDs,                                      *)
(*       index     |-> i \in Indexes,                                      *)
(*       checksum  |-> c \in Checksums,                                    *)
(*       value     |-> v \in Values,                                       *)
(*       timestamp |-> t \in Timestamps,                                   *)
(*       succeeded |-> TRUE \/ FALSE ]                                     *)
(*                                                                         *)
(*   RepairRequest                                                         *)
(*     [ src    |-> r \in Replicas,                                        *)
(*       dest   |-> r \in Replicas,                                        *)
(*       req    |-> (ClientRequest),                                       *)
(*       type   |-> MRepairRequest,                                        *)
(*       viewID |-> i \in ViewIDs,                                         *)
(*       index  |-> i \in Indexes ]                                        *)
(*                                                                         *)
(*   RepairReply                                                           *)
(*     [ src    |-> r \in Replicas,                                        *)
(*       dest   |-> r \in Replicas,                                        *)
(*       req    |-> (ClientRequest),                                       *)
(*       type   |-> MRepairReply,                                          *)
(*       viewID |-> i \in ViewIDs,                                         *)
(*       index  |-> i \in Indexes,                                         *)
(*       log    |-> l \in Logs ]                                           *)
(*                                                                         *)
(*   ViewChangeRequest                                                     *)
(*     [ src    |-> r \in Replicas,                                        *)
(*       dest   |-> r \in Replicas,                                        *)
(*       type   |-> MViewChangeRequest,                                    *)
(*       viewID |-> i \in ViewIDs ]                                        *)
(*                                                                         *)
(*   ViewChangeReply                                                       *)
(*     [ src       |-> r \in Replicas,                                     *)
(*       dest      |-> r \in Replicas,                                     *)
(*       type      |-> MViewChangeReply,                                   *)
(*       viewID    |-> i \in ViewIDs,                                      *)
(*       logViewID |-> i \in ViewIDs,                                      *)
(*       log       |-> l \in Logs ]                                        *)
(*                                                                         *)
(*   StartViewRequest                                                      *)
(*     [ src    |-> r \in Replicas,                                        *)
(*       dest   |-> r \in Replicas,                                        *)
(*       type   |-> MStartViewRequest,                                     *)
(*       viewID |-> i \in ViewIDs,                                         *)
(*       log    |-> l \in Logs ]                                           *)
(***************************************************************************)

----

\* The set of all messages on the network
VARIABLE messages

\* The total number of messages sent
VARIABLE messageCount

\* The total number of steps executed
VARIABLE stepCount

messageVars == <<messages, messageCount, stepCount>>

(* Local client state *)

\* Strictly increasing representation of synchronized time
VARIABLE cTime

\* The highest known view ID for a client
VARIABLE cViewID

\* Client request IDs
VARIABLE cReqID

\* A client response buffer
VARIABLE cReps

\* A set of all commits - used for model checking
VARIABLE cCommits

clientVars == <<cTime, cViewID, cReqID, cReps, cCommits>>

(* Local replica state *)

\* The current status of a replica
VARIABLE rStatus

\* The current view ID for a replica
VARIABLE rViewID

\* A replica's commit log
VARIABLE rLog

\* A replica's sync index
VARIABLE rSyncIndex

\* The view ID for the log
VARIABLE rLogViewID

\* The set of view change replies
VARIABLE rViewChangeReps

replicaVars == <<rStatus, rViewID, rLog, rSyncIndex, rLogViewID, rViewChangeReps>>

vars == <<messageVars, clientVars, replicaVars>>

----

(*
This section provides utilities for implementing the spec.
*)

\* Creates a sequence from set 'S'
RECURSIVE SeqFromSet(_)
SeqFromSet(S) == 
    IF S = {} THEN
        << >> 
    ELSE LET x == CHOOSE x \in S : TRUE
        IN  << x >> \o SeqFromSet(S \ {x})

RECURSIVE SetReduce(_, _, _)
SetReduce(Op(_, _), S, value) == 
    IF S = {} THEN
        value
    ELSE
        LET s == CHOOSE s \in S : TRUE
        IN SetReduce(Op, S \ {s}, Op(s, value)) 

\* Computes the greatest vlue in set 'S'
Max(S) == CHOOSE x \in S : \A y \in S : x >= y

\* Computes the sum of numbers in set 'S'
Sum(S) == LET _op(a, b) == a + b
          IN SetReduce(_op, S, 0)

\* The values of a sequence
Range(s) == {s[i] : i \in DOMAIN s}

----

(*
This section provides helpers for the protocol.
*)

\* A sorted sequence of replicas
replicas == SeqFromSet(Replicas)

\* The primary index for view 'v'
PrimaryIndex(v) == (v%Len(replicas)) + (IF v >= Len(replicas) THEN 1 ELSE 0)

\* The primary for view 'v'
Primary(v) == replicas[PrimaryIndex(v)]

\* Quorum is the quorum for a given view
Quorum(v) ==
    LET
        quorumSize == Len(replicas) \div 2 + 1
        index(i)   == PrimaryIndex(v) + (i - 1)
        member(i)  == IF index(i) > Len(replicas) THEN replicas[index(i)%Len(replicas)] ELSE replicas[index(i)]
    IN 
        {member(i) : i \in 1..quorumSize}

\* A boolean indicating whether the given set is a quorum
IsQuorum(S) == Cardinality(S) * 2 >= Cardinality(Replicas)

\* A boolean indicating whether the given set is a quorum that includes the given replica
IsLocalQuorum(r, S) == IsQuorum(S) /\ r \in S

----

(*
This section models the network.
*)

\* Send a set of messages
Sends(ms) ==
    /\ messages'     = messages \cup ms
    /\ messageCount' = messageCount + Cardinality(ms)
    /\ stepCount'    = stepCount + 1

\* Send a message
Send(m) == Sends({m})

\* Ack a message
Ack(m) == 
    /\ messages'     = messages \ {m}
    /\ messageCount' = messageCount + 1
    /\ stepCount'    = stepCount + 1

\* Ack a message and send a set of messages
AckAndSends(m, ms) == 
    /\ messages'     = (messages \cup ms) \ {m}
    /\ messageCount' = messageCount + Cardinality(ms)
    /\ stepCount'    = stepCount + 1

\* Ack and send a message
AckAndSend(m, n) == AckAndSends(m, {n})

\* Reply to a message with a set of responses
Replies(req, reps) == AckAndSends(req, reps)

\* Reply to a message
Reply(req, resp) == AckAndSend(req, resp)

----

(*
This section models client requests.
*)

\* Client 'c' sends value 'v' to all replicas
ClientRequest(c, v) ==
    /\ cTime' = cTime + 1
    /\ cReqID' = [cReqID EXCEPT ![c] = cReqID[c] + 1]
    /\ Sends({[src       |-> c,
               dest      |-> r,
               type      |-> MClientRequest,
               viewID    |-> cViewID[c],
               reqID     |-> cReqID'[c],
               value     |-> v,
               timestamp |-> cTime'] : r \in Quorum(cViewID[c])})
    /\ UNCHANGED <<replicaVars, cViewID, cReps, cCommits>>

\* Client 'c' handles a response 'm' from replica 'r'
HandleClientReply(c, r, m) ==
       \* If the reply view ID does not match the request view ID, update the client's view.
    /\ \/ /\ m.viewID # m.req.viewID
          /\ \/ /\ cViewID[c] < m.viewID
                /\ cViewID' = [cViewID EXCEPT ![c] = m.viewID]
             \/ /\ cViewID[c] >= m.viewID
                /\ UNCHANGED <<cViewID>>
          /\ Ack(m)
          /\ UNCHANGED <<cReps, cCommits>>
       \* If the request and reply views match and the reply view matches the client's view,
       \* aggregate the replies for the associated client request.
       \/ /\ m.viewID = m.req.viewID
          /\ m.viewID = cViewID[c]
          /\ \/ /\ m.succeeded
                /\ cReps' = [cReps EXCEPT ![c] = 
                                (cReps[c] \ {n \in cReps[c] : /\ n.src       = m.src 
                                                              /\ n.viewID    = cViewID[c]
                                                              /\ n.req.reqID = m.req.reqID 
                                                              /\ ~n.succeeded}) \cup {m}]
             \/ /\ ~m.succeeded
                /\ ~\E n \in cReps[c] : /\ n.src       = m.src 
                                        /\ n.viewID    = cViewID[c]
                                        /\ n.req.reqID = m.req.reqID
                                        /\ n.succeeded
                /\ cReps' = [cReps EXCEPT ![c] = cReps[c] \cup {m}]
          /\ LET reps        == {n \in cReps'[c] : /\ n.viewID    = cViewID[c] 
                                                   /\ n.req.reqID = m.req.reqID}
                 isQuorum    == {n.src : n \in {n \in reps : n.succeeded}} = Quorum(cViewID[c])
                 isCommitted == /\ \A n \in reps : n.succeeded
                                /\ Cardinality({n.checksum : n \in reps}) = 1
                 hasPrimary  == \E n \in reps : n.src = Primary(cViewID[c]) /\ n.succeeded
             IN
                 \* If a quorum of successful replies have been received and the checksums
                 \* match, add the primary reply to commits.
                 \/ /\ isQuorum
                    /\ isCommitted
                    /\ LET commit == CHOOSE n \in reps : n.src = Primary(cViewID[c])
                       IN cCommits' = [cCommits EXCEPT ![c] = cCommits[c] \cup {commit}]
                    /\ Ack(m)
                 \* If some reply failed or was returned with an incorrect checksum,
                 \* send a ReconcileRequest to the inconsistent node to force it to
                 \* reconcile its log with the primary's log.
                 \/ /\ ~isCommitted
                    /\ \/ /\ hasPrimary
                          /\ LET primaryRep == CHOOSE n \in reps : /\ n.src = Primary(cViewID[c]) 
                                                                   /\ n.succeeded
                                 retryReps  == {n \in reps :
                                                  /\ n.src      # Primary(cViewID[c]) 
                                                  /\ n.checksum # primaryRep.checksum}
                             IN AckAndSends(m, {[src    |-> c,
                                                 dest   |-> r,
                                                 type   |-> MReconcileRequest,
                                                 viewID |-> cViewID[c],
                                                 reqID  |-> m.req.reqID,
                                                 index  |-> primaryRep.index] : n \in retryReps})
                       \/ /\ ~hasPrimary
                          /\ Ack(m)
                    /\ UNCHANGED <<cCommits>>
                 \* If a quorum has not yet been reached, wait for more replies.
                 \/ /\ ~isQuorum
                    /\ isCommitted
                    /\ Ack(m)
                    /\ UNCHANGED <<cCommits>>
          /\ UNCHANGED <<cViewID>>
    /\ UNCHANGED <<replicaVars, cTime, cReqID>>

HandleReconcileReply(c, r, m) == HandleClientReply(c, r, m)

----

(*
This section models the replica protocol.
*)

\* Replica 'r' handles client 'c' request 'm'
HandleClientRequest(r, c, m) ==
    \* Client requests can only be handled if the replica is in-sync.
    /\ rStatus[r] = SInSync
       \* If the client's view matches the replica's view, process the client's request.
    /\ \/ /\ m.viewID = rViewID[r]
          /\ LET lastTimestamp == Max({rLog[r][i].timestamp : i \in DOMAIN rLog[r]} \cup {0})
             IN
                   \* If the request timestamp is greater than the highest log timestamp,
                   \* append the entry to the log and return a successful response with
                   \* the appended entry index.
                /\ \/ /\ m.timestamp > lastTimestamp
                      /\ rLog' = [rLog EXCEPT ![r] = 
                                     Append(rLog[r], [value     |-> m.value,
                                                      timestamp |-> m.timestamp])]
                      /\ Reply(m, [src       |-> r,
                                   dest      |-> c,
                                   req       |-> m,
                                   type      |-> MClientReply,
                                   viewID    |-> rViewID[r],
                                   index     |-> Len(rLog'[r]),
                                   checksum  |-> rLog'[r],
                                   value     |-> m.value,
                                   timestamp |-> m.timestamp,
                                   succeeded |-> TRUE])
                   \* If the request timestamp matches the highest log timestamp, treat the
                   \* request as a duplicate. Return a successful response indicating the
                   \* entry was appended.
                   \/ /\ m.timestamp = lastTimestamp
                      /\ Reply(m, [src       |-> r,
                                   dest      |-> c,
                                   req       |-> m,
                                   type      |-> MClientReply,
                                   viewID    |-> rViewID[r],
                                   index     |-> Len(rLog[r]),
                                   checksum  |-> rLog[r],
                                   value     |-> m.value,
                                   timestamp |-> m.timestamp,
                                   succeeded |-> TRUE])
                      /\ UNCHANGED <<rLog>>
                   \* If the request timestamp is less than the highest log timestamp,
                   \* reject the request.
                   \/ /\ m.timestamp < lastTimestamp
                      /\ Reply(m, [src       |-> r,
                                   dest      |-> c,
                                   req       |-> m,
                                   type      |-> MClientReply,
                                   viewID    |-> rViewID[r],
                                   index     |-> Len(rLog[r]),
                                   checksum  |-> rLog[r],
                                   value     |-> m.value,
                                   timestamp |-> m.timestamp,
                                   succeeded |-> FALSE])
                      /\ UNCHANGED <<rLog>>
          /\ UNCHANGED <<rViewID, rStatus, rViewChangeReps>>
       \* If the client's view is greater than the replica's view, reject the client's
       \* request with the outdated view ID and enter the view change protocol.
       \/ /\ m.viewID > rViewID[r]
          /\ rViewID'         = [rViewID         EXCEPT ![r] = m.viewID]
          /\ rStatus'         = [rStatus         EXCEPT ![r] = SViewChange]
          /\ rViewChangeReps' = [rViewChangeReps EXCEPT ![r] = {}]
          /\ Replies(m, {[src       |-> r,
                          dest      |-> c,
                          req       |-> m,
                          type      |-> MClientReply,
                          viewID    |-> rViewID[r],
                          succeeded |-> FALSE],
                         [src       |-> r,
                          dest      |-> Primary(m.viewID),
                          type      |-> MViewChangeReply,
                          viewID    |-> m.viewID,
                          logViewID |-> rLogViewID[r],
                          log       |-> rLog[r]]})
          /\ UNCHANGED <<rLog>>
       \* If the client's view is less than the replica's view, reject the client's request
       \* with the updated view ID to force the client to retry.
       \/ /\ m.viewID < rViewID[r]
          /\ Reply(m, [src       |-> r,
                       dest      |-> c,
                       req       |-> m,
                       type      |-> MClientReply,
                       viewID    |-> rViewID[r],
                       succeeded |-> FALSE])
          /\ UNCHANGED <<rViewID, rStatus, rLog, rViewChangeReps>>
    /\ UNCHANGED <<clientVars, rLogViewID, rSyncIndex>>

HandleReconcileRequest(r, c, m) == 
    /\ rStatus[r] = SInSync
    /\ rViewID[r] = m.viewID
    /\ \/ /\ rSyncIndex[r] >= m.index
          /\ Reply(m, [src       |-> r,
                       dest      |-> c,
                       req       |-> m,
                       type      |-> MReconcileReply,
                       viewID    |-> rViewID[r],
                       index     |-> m.index,
                       checksum  |-> [i \in 1..m.index |-> rLog[r][i]],
                       value     |-> rLog[r][m.index].value,
                       timestamp |-> rLog[r][m.index].timestamp,
                       succeeded |-> TRUE])
          /\ UNCHANGED <<rStatus>>
       \/ /\ rSyncIndex[r] < m.index
          /\ Primary(rViewID[r]) # r
          /\ rStatus' = [rStatus EXCEPT ![r] = SRepair]
          /\ AckAndSend(m, [src    |-> r,
                            dest   |-> Primary(rViewID[r]),
                            req    |-> m,
                            type   |-> MRepairRequest,
                            viewID |-> rViewID[r],
                            index  |-> m.index])
    /\ UNCHANGED <<clientVars, rViewID, rLog, rLogViewID, rSyncIndex, rViewChangeReps>>

HandleRepairRequest(r, s, m) ==
    /\ rStatus[r] = SInSync
    /\ rViewID[r] = m.viewID
    /\ Primary(rViewID[r]) = r
    /\ Reply(m, [src    |-> r,
                 dest   |-> s,
                 req    |-> m.req,
                 type   |-> MRepairReply,
                 viewID |-> rViewID[r],
                 index  |-> m.index,
                 log    |-> [i \in 1..m.index |-> rLog[r][i]]])
    /\ UNCHANGED <<clientVars, replicaVars>>

HandleRepairReply(r, s, m) == 
    /\ rStatus[r] = SRepair
    /\ rViewID[r] = m.viewID
    /\ rStatus'    = [rStatus    EXCEPT ![r] = SInSync]
    /\ rLog'       = [rLog       EXCEPT ![r] = m.log \o SubSeq(rLog[r], Len(m.log), Len(rLog[r]))]
    /\ rSyncIndex' = [rSyncIndex EXCEPT ![r] = Len(rLog'[r])]
    /\ Reply(m, [src       |-> r,
                 dest      |-> m.req.src,
                 req       |-> m.req,
                 type      |-> MReconcileReply,
                 viewID    |-> rViewID[r],
                 index     |-> m.index,
                 checksum  |-> m.log,
                 value     |-> m.log[m.index].value,
                 timestamp |-> m.log[m.index].timestamp,
                 succeeded |-> TRUE])
    /\ UNCHANGED <<clientVars, rViewID, rLogViewID, rViewChangeReps>>

\* Replica 'r' requests a view change
ChangeView(r) ==
    /\ Sends({[src    |-> r,
               dest   |-> d,
               type   |-> MViewChangeRequest,
               viewID |-> rViewID[r] + 1] : d \in Replicas})
    /\ UNCHANGED <<clientVars, replicaVars>>

\* Replica 'r' handles replica 's' view change request 'm'
HandleViewChangeRequest(r, s, m) ==
    /\ \/ /\ rViewID[r] < m.viewID
          /\ rViewID'         = [rViewID         EXCEPT ![r] = m.viewID]
          /\ rStatus'         = [rStatus         EXCEPT ![r] = SViewChange]
          /\ rViewChangeReps' = [rViewChangeReps EXCEPT ![r] = {}]
          /\ Reply(m, [src       |-> r,
                       dest      |-> Primary(m.viewID),
                       type      |-> MViewChangeReply,
                       viewID    |-> m.viewID,
                       logViewID |-> rLogViewID[r],
                       log       |-> rLog[r]])
       \/ /\ rViewID[r] >= m.viewID
          /\ Ack(m)
          /\ UNCHANGED <<rViewID, rStatus, rViewChangeReps>>
    /\ UNCHANGED <<clientVars, rLog, rLogViewID, rSyncIndex>>

\* Replica 'r' handles replica 's' view change reply 'm'
HandleViewChangeReply(r, s, m) ==
    \* The view change protocol is run by the primary for the view.
    /\ Primary(m.viewID) = r
    /\ rViewID[r] = m.viewID
    /\ rStatus[r] = SViewChange
    /\ rViewChangeReps' = [rViewChangeReps EXCEPT ![r] = rViewChangeReps[r] \cup {m}]
    /\ LET viewChanges == {v \in rViewChangeReps'[r] : v.viewID = rViewID[r]}
       IN
           \* In order to ensure the new view is initialized with the latest view,
           \* a quorum of view change replies must be received to guarantee the last
           \* activated view is present in the set of replies.
           \* If view change replies have been received from a majority of the replicas,
           \* initialize the view using the log from the highest activated view.
           \/ /\ IsLocalQuorum(r, {v.src : v \in viewChanges})
              /\ LET latestViewID == Max({v.logViewID : v \in viewChanges})
                     latestChange == CHOOSE v \in viewChanges : 
                                         /\ v.logViewID = latestViewID 
                                         /\ v.src \in Quorum(latestViewID)
                 IN AckAndSends(m, {[src    |-> r,
                                     dest   |-> d,
                                     type   |-> MStartViewRequest,
                                     viewID |-> rViewID[r],
                                     log    |-> latestChange.log] : d \in Replicas})
           \* If view change replies have not yet been received from a quorum, record
           \* the view change reply and discard the message.
           \/ /\ ~IsLocalQuorum(r, {v.src : v \in viewChanges})
              /\ Ack(m)
    /\ UNCHANGED <<clientVars, rStatus, rViewID, rLog, rLogViewID, rSyncIndex>>

\* Replica 'r' handles replica 's' start view request 'm'
HandleStartViewRequest(r, s, m) ==
    \* To activate a view, the replica must either not know of the view or already
    \* be participating in the view change protocol for the view.
    /\ \/ rViewID[r] < m.viewID
       \/ /\ rViewID[r] = m.viewID
          /\ rStatus[r] = SViewChange
    \* If the replica is part of the quorum for the activated view, update the log
    \* and record the activated view for use in the view change protocol.
    /\ \/ /\ r \in Quorum(m.viewID)
          /\ rLog'       = [rLog       EXCEPT ![r] = m.log]
          /\ rLogViewID' = [rLogViewID EXCEPT ![r] = m.viewID]
          /\ rSyncIndex' = [rSyncIndex EXCEPT ![r] = Len(m.log)]
       \/ /\ r \notin Quorum(m.viewID)
          /\ UNCHANGED <<rLog, rLogViewID, rSyncIndex>>
    \* Update the replica's view ID and status and clean up view change state.
    /\ rViewID' = [rViewID EXCEPT ![r] = m.viewID]
    /\ rStatus' = [rStatus EXCEPT ![r] = SInSync]
    /\ LET viewChanges == {v \in rViewChangeReps[r] : v.viewID = rViewID[r]}
       IN  rViewChangeReps' = [rViewChangeReps EXCEPT ![r] = rViewChangeReps[r] \ viewChanges]
    /\ Ack(m)
    /\ UNCHANGED <<clientVars>>

----

InitMessageVars ==
    /\ messages     = {}
    /\ messageCount = 0
    /\ stepCount    = 0

InitClientVars ==
    /\ cTime    = 0
    /\ cViewID  = [c \in Clients |-> 1]
    /\ cReqID   = [c \in Clients |-> 0]
    /\ cReps    = [c \in Clients |-> {}]
    /\ cCommits = [c \in Clients |-> {}]

InitReplicaVars ==
    /\ rStatus         = [r \in Replicas |-> SInSync]
    /\ rViewID         = [r \in Replicas |-> 1]
    /\ rLog            = [r \in Replicas |-> <<>>]
    /\ rSyncIndex      = [r \in Replicas |-> 0]
    /\ rLogViewID      = [r \in Replicas |-> 1]
    /\ rViewChangeReps = [r \in Replicas |-> {}]

Init ==
    /\ InitMessageVars
    /\ InitClientVars
    /\ InitReplicaVars

----

(*
This section specifies the invariants for the protocol.
*)

\* The linearizability invariant verifies that once a client has received matching
\* acks from a quorum and committed a value, thereafter the value is always present 
\* at the committed index on all in-sync replicas.
Linearizability == 
    \A c \in Clients :
       \A e \in cCommits[c] :
          ~\E r \in Replicas :
             /\ rStatus[r] = SInSync
             /\ rViewID[r] >= e.viewID
             /\ r \in Quorum(rViewID[r])
             /\ rLog[r][e.index].value # e.value

----

NextClientRequest == 
    \E c \in Clients :
       \E v \in Values :
          ClientRequest(c, v)

NextChangeView ==
    \E r \in Replicas : 
       ChangeView(r)

NextHandleClientRequest ==
    \E m \in messages :
       /\ m.type = MClientRequest
       /\ HandleClientRequest(m.dest, m.src, m)

NextHandleClientReply ==
    \E m \in messages :
       /\ m.type = MClientReply
       /\ HandleClientReply(m.dest, m.src, m)

NextHandleReconcileRequest ==
    \E m \in messages :
       /\ m.type = MReconcileRequest
       /\ HandleReconcileRequest(m.dest, m.src, m)

NextHandleReconcileReply ==
    \E m \in messages :
       /\ m.type = MReconcileReply
       /\ HandleReconcileReply(m.dest, m.src, m)

NextHandleRepairRequest ==
    \E m \in messages :
       /\ m.type = MRepairRequest
       /\ HandleRepairRequest(m.dest, m.src, m)

NextHandleRepairReply ==
    \E m \in messages :
       /\ m.type = MRepairReply
       /\ HandleRepairReply(m.dest, m.src, m)

NextHandleViewChangeRequest ==
    \E m \in messages :
       /\ m.type = MViewChangeRequest
       /\ HandleViewChangeRequest(m.dest, m.src, m)

NextHandleViewChangeReply ==
    \E m \in messages :
       /\ m.type = MViewChangeReply
       /\ HandleViewChangeReply(m.dest, m.src, m)

NextHandleStartViewRequest ==
    \E m \in messages :
       /\ m.type = MStartViewRequest
       /\ HandleStartViewRequest(m.dest, m.src, m)

NextDropMessage ==
    \E m \in messages :
       /\ Ack(m)
       /\ UNCHANGED <<clientVars, replicaVars>>

Next ==
    \/ NextClientRequest
    \/ NextChangeView
    \/ NextHandleClientRequest
    \/ NextHandleClientReply
    \/ NextHandleReconcileRequest
    \/ NextHandleReconcileReply
    \/ NextHandleRepairRequest
    \/ NextHandleRepairReply
    \/ NextHandleViewChangeRequest
    \/ NextHandleViewChangeReply
    \/ NextHandleStartViewRequest
    \/ NextDropMessage

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Wed Sep 30 18:02:32 PDT 2020 by jordanhalterman
\* Created Fri Sep 18 22:45:21 PDT 2020 by jordanhalterman
