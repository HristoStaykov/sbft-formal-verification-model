//#title Host protocol
//#desc Define the host state machine here: message type, state machine for executing one
//#desc host's part of the protocol.

// See exercise01.dfy for an English design of the protocol.

include "network.s.dfy"
include "cluster_config.s.dfy"
include "messages.dfy"

module Replica {
  import opened Library
  import opened HostIdentifiers
  import opened Messages
  import Network
  import ClusterConfig
                     
  type PrepareProofSet = set<Message> 
  predicate PrepareProofSetWF(ps:PrepareProofSet) {
      && forall x | x in ps :: x.Prepare?
  }

  type CommitProofSet = set<Message>
  predicate CommitProofSetWF(cs:CommitProofSet) {
      && forall x | x in cs :: x.Commit?
  }

  type PrePreparesRcvd = imap<SequenceID, Option<Message>>
  predicate PrePreparesRcvdWF(prePreparesRcvd:PrePreparesRcvd) {
    && FullImap(prePreparesRcvd)
    && (forall x | x in prePreparesRcvd && prePreparesRcvd[x].Some? :: prePreparesRcvd[x].value.PrePrepare?)
  }

  predicate FullImap<K(!new),V>(im:imap<K,V>) {
    forall k :: k in im
  }

  // The Working Window data structure. Here Replicas keep the PrePrepare from the Primary
  // and the votes from all peers. Once a Client Operation is committed by a given Replica
  // to a specific Sequence ID (the Replica has collected the necessary quorum of votes from
  // peers) the Client Operation is inserted in the committedClientOperations as appropriate.
  datatype WorkingWindow = WorkingWindow(
    committedClientOperations:imap<SequenceID, Option<ClientOperation>>,
    prePreparesRcvd:PrePreparesRcvd,
    preparesRcvd:imap<SequenceID, PrepareProofSet>,
    commitsRcvd:imap<SequenceID, CommitProofSet>
  ) {
    predicate WF()
    {
      && FullImap(committedClientOperations)
      && FullImap(preparesRcvd)
      && FullImap(commitsRcvd)
      && PrePreparesRcvdWF(prePreparesRcvd)
      && (forall seqID | seqID in preparesRcvd :: PrepareProofSetWF(preparesRcvd[seqID]))
      && (forall seqID | seqID in commitsRcvd :: CommitProofSetWF(commitsRcvd[seqID]))
    }
  }

  // Define your Host protocol state machine here.
  datatype Constants = Constants(myId:HostId, clusterConfig:ClusterConfig.Constants) {
    // host constants coupled to DistributedSystem Constants:
    // DistributedSystem tells us our id so we can recognize inbound messages.
    predicate WF() {
      && clusterConfig.WF()
      && myId < clusterConfig.N()
    }

    predicate Configure(id:HostId, clusterConf:ClusterConfig.Constants) {
      && myId == id
      && clusterConfig == clusterConf
    }
  }


  datatype Variables = Variables(
    view:nat,
    viewIsActive:bool,
    workingWindow:WorkingWindow
  ) {
    predicate WF(c:Constants)
    {
      && c.WF()
      && workingWindow.WF()
    }
  }

  function CurrentPrimary(c:Constants, v:Variables) : nat 
    requires c.WF()
  {
    v.view % c.clusterConfig.N()
  }

  // Predicate that describes what is needed and how we mutate the state v into v' when SendPrePrepare
  // Action is taken. We use the "binding" variable msgOps through which we send/recv messages.
  predicate SendPrePrepare(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>)
  {
    && v.WF(c)
    && msgOps.IsSend()
    && CurrentPrimary(c, v) == c.myId
    && var msg := msgOps.send.value;
    && msg.PrePrepare? // We have a liveness bug here, we need some state that says for the client which operation ID-s we have executed
    && v == v'
  }

  // For clarity here we have extracted all preconditions that must hold for a Replica to accept a PrePrepare
  predicate IsValidPrePrepareToAccept(c:Constants, v:Variables, p:Message)
  {
    && v.WF(c)
    && v.viewIsActive
    && p.view == v.view
    && p.PrePrepare?
    && p.sender == CurrentPrimary(c, v)
    && v.workingWindow.prePreparesRcvd[p.seqID].None?
  }

  // Predicate that describes what is needed and how we mutate the state v into v' when RecvPrePrepare
  // Action is taken. We use the "binding" variable msgOps through which we send/recv messages. In this 
  // predicate we need to reflect in our next state that we have received the PrePrepare message.
  predicate RecvPrePrepare(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>)
  {
    && v.WF(c)
    && msgOps.IsRecv()
    && var msg := msgOps.recv.value;
    && IsValidPrePrepareToAccept(c, v, msg)
    && v' == v.(workingWindow := 
                v.workingWindow.(prePreparesRcvd := 
                                 v.workingWindow.prePreparesRcvd[msg.seqID := Some(msg)]))
  }

  // For clarity here we have extracted all preconditions that must hold for a Replica to accept a Prepare
  predicate IsValidPrepareToAccept(c:Constants, v:Variables, p:Message)
  {
    && v.WF(c)
    && v.viewIsActive
    && p.view == v.view
    && p.Prepare?
    && v.workingWindow.prePreparesRcvd[p.seqID].Some?
    && v.workingWindow.prePreparesRcvd[p.seqID].value.clientOp == p.clientOp
    && (forall x | x in v.workingWindow.preparesRcvd[p.seqID] && x.seqID == p.seqID :: x.sender != p.sender)
  }

  // Predicate that describes what is needed and how we mutate the state v into v' when RecvPrepare
  // Action is taken. We use the "binding" variable msgOps through which we send/recv messages. In this 
  // predicate we need to reflect in our next state that we have received the Prepare message.
  predicate RecvPrepare(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>)
  {
    && v.WF(c)
    && msgOps.IsRecv()
    && var msg := msgOps.recv.value;
    && IsValidPrepareToAccept(c, v, msg)
    && v' == v.(workingWindow := 
                v.workingWindow.(preparesRcvd := 
                                 v.workingWindow.preparesRcvd[msg.seqID := 
                                 v.workingWindow.preparesRcvd[msg.seqID] + {msg}]))
  }

  // 
  predicate IsValidCommitToAccept(c:Constants, v:Variables, p:Message)
  {
    && v.WF(c)
    && v.viewIsActive
    && p.view == v.view
    && p.Prepare?
    && v.workingWindow.prePreparesRcvd[p.seqID].Some?
    && v.workingWindow.prePreparesRcvd[p.seqID].value.clientOp == p.clientOp
    && (forall x | x in v.workingWindow.commitsRcvd[p.seqID] && x.seqID == p.seqID :: x.sender != p.sender)
  }

  predicate RecvCommit(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>)
  {
    && v.WF(c)
    && msgOps.IsRecv()
    && var msg := msgOps.recv.value;
    && IsValidCommitToAccept(c, v, msg)
    && v' == v.(workingWindow := 
               v.workingWindow.(commitsRcvd :=
                                 v.workingWindow.commitsRcvd[msg.seqID :=
                                 v.workingWindow.commitsRcvd[msg.seqID] + {msg}]))
  }

  predicate QuorumOfCommits(c:Constants, v:Variables, seqID:SequenceID) {
    && v.WF(c)
    && |v.workingWindow.commitsRcvd[seqID]| >= c.clusterConfig.AgreementQuorum()
  }

  predicate DoCommit(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>, seqID:SequenceID)
  {
    && v.WF(c)
    && QuorumOfPrepares(c, v, seqID)
    && QuorumOfCommits(c, v, seqID)
    && v.workingWindow.prePreparesRcvd[seqID].Some?
    && var msg := v.workingWindow.prePreparesRcvd[seqID].value;
    && v' == v.(workingWindow := 
               v.workingWindow.(committedClientOperations :=
                                 v.workingWindow.committedClientOperations[msg.seqID := Some(msg.clientOp)]))
  }

  predicate QuorumOfPrepares(c:Constants, v:Variables, seqID:SequenceID)
  {
    && v.WF(c)
    && |v.workingWindow.preparesRcvd[seqID]| >= c.clusterConfig.AgreementQuorum()
  }

  // Predicate that describes what is needed and how we mutate the state v into v' when SendPrepare
  // Action is taken. We use the "binding" variable msgOps through which we send/recv messages. In this 
  // predicate we do not mutate the next state, relying on the fact that messages will be broadcast
  // and we will be able to receive our own message and store it as described in the RecvPrepare predicate.
  predicate SendPrepare(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>, seqID:SequenceID)
  {
    && v.WF(c)
    && msgOps.IsSend()
    && v.viewIsActive
    && v.workingWindow.prePreparesRcvd[seqID].Some?
    && msgOps.send == Some(Prepare(c.myId, v.view, seqID, v.workingWindow.prePreparesRcvd[seqID].value.clientOp))
    && v' == v
  }

  // Predicate that describes what is needed and how we mutate the state v into v' when SendCommit
  // Action is taken. We use the "binding" variable msgOps through which we send/recv messages. In this 
  // predicate we do not mutate the next state, relying on the fact that messages will be broadcast
  // and we will be able to receive our own message and store it as described in the RecvCommit predicate.
  predicate SendCommit(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>, seqID:SequenceID)
  {
    && v.WF(c)
    && msgOps.IsSend()
    && v.viewIsActive
    && QuorumOfPrepares(c, v, seqID)
    && v.workingWindow.prePreparesRcvd[seqID].Some?
    && msgOps.send == Some(Commit(c.myId, v.view, seqID, v.workingWindow.prePreparesRcvd[seqID].value.clientOp))
    && v' == v
  }
  
  predicate Init(c:Constants, v:Variables) {
    && v.view == 0
    && v.viewIsActive == true
    && (forall seqID | seqID in v.workingWindow.committedClientOperations
                :: v.workingWindow.committedClientOperations[seqID].None?)
    && (forall seqID | seqID in v.workingWindow.prePreparesRcvd
                :: v.workingWindow.prePreparesRcvd[seqID].None?)
    && (forall seqID | seqID in v.workingWindow.preparesRcvd :: v.workingWindow.preparesRcvd[seqID] == {})
    && (forall seqID | seqID in v.workingWindow.commitsRcvd :: v.workingWindow.commitsRcvd[seqID] == {})
  }

  // JayNF
  datatype Step =
    //| RecvClientOperation()
    | SendPrePrepareStep()
    | RecvPrePrepareStep()
    | SendPrepareStep(seqID:SequenceID)
    | RecvPrepareStep()
    | SendCommitStep(seqID:SequenceID)
    | RecvCommitStep()
    | DoCommitStep(seqID:SequenceID)
    //| Execute(seqID:SequenceID)
    //| SendReplyToClient(seqID:SequenceID)

  predicate NextStep(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>, step: Step) {
    match step
       case SendPrePrepareStep() => SendPrePrepare(c, v, v', msgOps)
       case RecvPrePrepareStep => RecvPrePrepare(c, v, v', msgOps)
       case SendPrepareStep(seqID) => SendPrepare(c, v, v', msgOps, seqID)
       case RecvPrepareStep => RecvPrepare(c, v, v', msgOps)
       case SendCommitStep(seqID) => SendCommit(c, v, v', msgOps, seqID)
       case RecvCommitStep() => RecvCommit(c, v, v', msgOps)
       case DoCommitStep(seqID) => DoCommit(c, v, v', msgOps, seqID)
  }

  predicate Next(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>) {
    exists step :: NextStep(c, v, v', msgOps, step)
  }
}
