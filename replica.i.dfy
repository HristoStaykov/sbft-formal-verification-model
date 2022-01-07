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
                     
  type PrepareProofSet = map<HostId, Network.Message<Message>> 
  predicate PrepareProofSetWF(c:Constants, ps:PrepareProofSet)
    requires c.WF()
  {
      && forall x | x in ps :: && ps[x].payload.Prepare? 
                               && c.clusterConfig.IsReplica(ps[x].sender)
  }

  type CommitProofSet = map<HostId, Network.Message<Message>>
  predicate CommitProofSetWF(c:Constants, cs:CommitProofSet)
    requires c.WF()
  {
      && forall x | x in cs :: && cs[x].payload.Commit?
                               && c.clusterConfig.IsReplica(cs[x].sender)
  }

  type PrePreparesRcvd = imap<SequenceID, Option<Network.Message<Message>>>
  predicate PrePreparesRcvdWF(prePreparesRcvd:PrePreparesRcvd) {
    && FullImap(prePreparesRcvd)
    && (forall x | x in prePreparesRcvd && prePreparesRcvd[x].Some? :: prePreparesRcvd[x].value.payload.PrePrepare?)
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
    predicate WF(c:Constants)
      requires c.WF()
    {
      && FullImap(committedClientOperations)
      && FullImap(preparesRcvd)
      && FullImap(commitsRcvd)
      && PrePreparesRcvdWF(prePreparesRcvd)
      && (forall seqID | seqID in preparesRcvd :: PrepareProofSetWF(c, preparesRcvd[seqID]))
      && (forall seqID | seqID in commitsRcvd :: CommitProofSetWF(c, commitsRcvd[seqID]))
    }
  }

  // Define your Host protocol state machine here.
  datatype Constants = Constants(myId:HostId, clusterConfig:ClusterConfig.Constants) {
    // host constants coupled to DistributedSystem Constants:
    // DistributedSystem tells us our id so we can recognize inbound messages.
    // clusterSize is in clusterConfig.
    predicate WF() {
      && clusterConfig.WF()
      && clusterConfig.IsReplica(myId)
    }

    predicate Configure(id:HostId, clusterConf:ClusterConfig.Constants) {
      && myId == id
      && clusterConfig == clusterConf
    }
  }

  datatype ViewChangeMsgs = ViewChangeMsgs(msgs:set<Network.Message<Message>>) {
    predicate WF(c:Constants) {
      && c.WF()
      && (forall msg | msg in msgs :: && msg.payload.ViewChangeMsg?
                                      && c.clusterConfig.IsReplica(msg.sender))
    }
  }

  datatype Variables = Variables(
    view:ViewNum,
    workingWindow:WorkingWindow,
    viewChangeMsgsRecvd:ViewChangeMsgs
  ) {
    predicate WF(c:Constants)
    {
      && c.WF()
      && workingWindow.WF(c)
      && viewChangeMsgsRecvd.WF(c)
    }
  }

  function CurrentPrimary(c:Constants, v:Variables) : nat 
    requires v.WF(c)
  {
    v.view % c.clusterConfig.N()
  }

  predicate HaveSufficientVCMsgsToMoveTo(c:Constants, v:Variables, newView:ViewNum)
    requires v.WF(c)
  {
    && var relevantVCMsgs := set vcMsg | && vcMsg in v.viewChangeMsgsRecvd.msgs 
                                         && vcMsg.payload.newView >= newView;
    && |relevantVCMsgs| >= c.clusterConfig.ByzantineSafeQuorum() //F+1
    && (exists vcMsg :: vcMsg in relevantVCMsgs && vcMsg.payload.newView == newView)
  }

  predicate HasCollectedProofMyViewIsAgreed(c:Constants, v:Variables) {
    && v.WF(c)
    && var vcMsgsForMyView := set msg | && msg in v.viewChangeMsgsRecvd.msgs 
                                        && msg.payload.newView == v.view;
    && ( || v.view == 0 // View 0 is active initially therefore it is initially agreed.
         || |vcMsgsForMyView| >= c.clusterConfig.AgreementQuorum())
  }

  predicate ViewIsActive(c:Constants, v:Variables) {
    && v.WF(c)
    && var vcMsgsForHigherView := set msg | && msg in v.viewChangeMsgsRecvd.msgs
                                            && msg.payload.newView > v.view;
    && var vcMsgsForMyView := set msg | && msg in v.viewChangeMsgsRecvd.msgs 
                                        && msg.payload.newView == v.view;
    && var haveMyVCMsg := exists myVCMsg :: && myVCMsg in v.viewChangeMsgsRecvd.msgs
                                            && myVCMsg.sender == c.myId
                                            && myVCMsg.payload.newView == v.view;
    && |vcMsgsForHigherView| < c.clusterConfig.ByzantineSafeQuorum() //F+1
    && ( || v.view == 0 // View 0 is active initially. There are no View Change messages for it.
         || (haveMyVCMsg && |vcMsgsForMyView| >= c.clusterConfig.AgreementQuorum())) //2F+1
    // TODO: take in account NewViewMsg once we have it in the model

  }

  // Predicate that describes what is needed and how we mutate the state v into v' when SendPrePrepare
  // Action is taken. We use the "binding" variable msgOps through which we send/recv messages.
  predicate SendPrePrepare(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>)
  {
    && v.WF(c)
    && msgOps.IsSend()
    && CurrentPrimary(c, v) == c.myId
    && var msg := msgOps.send.value;
    && msg.payload.PrePrepare? // We have a liveness bug here, we need some state that says for the client which operation ID-s we have executed
    && v == v'
  }

  // For clarity here we have extracted all preconditions that must hold for a Replica to accept a PrePrepare
  predicate IsValidPrePrepareToAccept(c:Constants, v:Variables, msg:Network.Message<Message>)
  {
    && v.WF(c)
    && msg.payload.PrePrepare?
    && c.clusterConfig.IsReplica(msg.sender)
    && ViewIsActive(c, v)
    && msg.payload.view == v.view
    && msg.sender == CurrentPrimary(c, v)
    && v.workingWindow.prePreparesRcvd[msg.payload.seqID].None?
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
                                 v.workingWindow.prePreparesRcvd[msg.payload.seqID := Some(msg)]))
  }

  // For clarity here we have extracted all preconditions that must hold for a Replica to accept a Prepare
  predicate IsValidPrepareToAccept(c:Constants, v:Variables, msg:Network.Message<Message>)
  {
    && v.WF(c)
    && msg.payload.Prepare?
    && c.clusterConfig.IsReplica(msg.sender)
    && ViewIsActive(c, v)
    && msg.payload.view == v.view
    && v.workingWindow.prePreparesRcvd[msg.payload.seqID].Some?
    && v.workingWindow.prePreparesRcvd[msg.payload.seqID].value.payload.clientOp == msg.payload.clientOp
    && msg.sender !in v.workingWindow.preparesRcvd[msg.payload.seqID] // We stick to the first vote from a peer.
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
                                 v.workingWindow.preparesRcvd[msg.payload.seqID := 
                                 v.workingWindow.preparesRcvd[msg.payload.seqID][msg.sender := msg]]))
  }

  // 
  predicate IsValidCommitToAccept(c:Constants, v:Variables, msg:Network.Message<Message>)
  {
    && v.WF(c)
    && msg.payload.Commit?
    && c.clusterConfig.IsReplica(msg.sender)
    && ViewIsActive(c, v)
    && msg.payload.view == v.view
    && v.workingWindow.prePreparesRcvd[msg.payload.seqID].Some?
    && v.workingWindow.prePreparesRcvd[msg.payload.seqID].value.payload.clientOp == msg.payload.clientOp
    && msg.sender !in v.workingWindow.commitsRcvd[msg.payload.seqID] // We stick to the first vote from a peer.
  }

  predicate RecvCommit(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>)
  {
    && v.WF(c)
    && msgOps.IsRecv()
    && var msg := msgOps.recv.value;
    && IsValidCommitToAccept(c, v, msg)
    && v' == v.(workingWindow := 
               v.workingWindow.(commitsRcvd :=
                                 v.workingWindow.commitsRcvd[msg.payload.seqID := 
                                 v.workingWindow.commitsRcvd[msg.payload.seqID][msg.sender := msg]]))
  }

  predicate QuorumOfCommits(c:Constants, v:Variables, seqID:SequenceID) {
    && v.WF(c)
    && |v.workingWindow.commitsRcvd[seqID]| >= c.clusterConfig.AgreementQuorum()
  }

  predicate DoCommit(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>, seqID:SequenceID)
  {
    && v.WF(c)
    && msgOps.NoSendRecv()
    && QuorumOfPrepares(c, v, seqID)
    && QuorumOfCommits(c, v, seqID)
    && v.workingWindow.prePreparesRcvd[seqID].Some?
    && var msg := v.workingWindow.prePreparesRcvd[seqID].value;
    && v' == v.(workingWindow := 
               v.workingWindow.(committedClientOperations :=
                                 v.workingWindow.committedClientOperations[msg.payload.seqID := Some(msg.payload.clientOp)]))
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
    && ViewIsActive(c, v)
    && v.workingWindow.prePreparesRcvd[seqID].Some?
    && msgOps.send == Some(Network.Message(c.myId,
                                       Prepare(v.view, 
                                               seqID,
                                               v.workingWindow.prePreparesRcvd[seqID].value.payload.clientOp)))
    && assert msgOps.send.value.payload.Prepare?; true
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
    && ViewIsActive(c, v)
    && QuorumOfPrepares(c, v, seqID)
    && v.workingWindow.prePreparesRcvd[seqID].Some?
    && msgOps.send == Some(Network.Message(c.myId,
                                     Commit(v.view,
                                            seqID,
                                            v.workingWindow.prePreparesRcvd[seqID].value.payload.clientOp)))
    && assert msgOps.send.value.payload.Commit?; true

    && v' == v
  }

  predicate LeaveView(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>, newView:ViewNum) {
    && v.WF(c)
    && msgOps.NoSendRecv()
    // We can only leave a view we have collected at least 2F+1 View 
    // Change messages for in viewChangeMsgsRecvd or View is 0.
    && (|| (HasCollectedProofMyViewIsAgreed(c, v) && newView == v.view + 1)
        || HaveSufficientVCMsgsToMoveTo(c, v, newView))
    && var vcMsg := Network.Message(c.myId, ViewChangeMsg(newView, ExtractCertificatesFromWorkingWindow(c, v)));
    && (forall seqID :: seqID in vcMsg.payload.certificates ==> 
           (|| vcMsg.payload.certificates[seqID].empty()
            || (&& vcMsg.payload.certificates[seqID].valid() 
                && |vcMsg.payload.certificates[seqID].votes| >= c.clusterConfig.AgreementQuorum())))
    && v' == v.(view := newView)
              .(viewChangeMsgsRecvd := v.viewChangeMsgsRecvd.(msgs := v.viewChangeMsgsRecvd.msgs + {vcMsg}))
  }

  function ExtractCertificatesFromWorkingWindow(c:Constants, v:Variables) : imap<SequenceID, PreparedCertificate> //TODO refactor after Checkpoint is added.
    requires v.WF(c)
  {
    imap seqID | seqID in v.workingWindow.preparesRcvd :: ExtractCertificateForSeqID(c, v, seqID)
  }

  function ExtractCertificateForSeqID(c:Constants, v:Variables, seqID:SequenceID) : PreparedCertificate
    requires v.WF(c)
  {
    if |v.workingWindow.preparesRcvd[seqID].Keys| < c.clusterConfig.AgreementQuorum() 
    then PreparedCertificate({})
    else PreparedCertificate(v.workingWindow.preparesRcvd[seqID].Values)
  }

  predicate SendViewChangeMsg(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>)
  {
    && v.WF(c)
    && msgOps.IsSend()
    && var msg := msgOps.send.value;
    && msg.payload.ViewChangeMsg?
    && msg.payload.newView <= v.view
    && msg.sender == c.myId
    && msg in v.viewChangeMsgsRecvd.msgs
  }
  
  predicate Init(c:Constants, v:Variables) {
    && v.view == 0
    && (forall seqID | seqID in v.workingWindow.committedClientOperations
                :: v.workingWindow.committedClientOperations[seqID].None?)
    && (forall seqID | seqID in v.workingWindow.prePreparesRcvd
                :: v.workingWindow.prePreparesRcvd[seqID].None?)
    && (forall seqID | seqID in v.workingWindow.preparesRcvd :: v.workingWindow.preparesRcvd[seqID] == map[])
    && (forall seqID | seqID in v.workingWindow.commitsRcvd :: v.workingWindow.commitsRcvd[seqID] == map[])
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
    | LeaveViewStep(newView:ViewNum)
    | SendViewChangeMsgStep()

  predicate NextStep(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>, step: Step) {
    match step
       case SendPrePrepareStep() => SendPrePrepare(c, v, v', msgOps)
       case RecvPrePrepareStep => RecvPrePrepare(c, v, v', msgOps)
       case SendPrepareStep(seqID) => SendPrepare(c, v, v', msgOps, seqID)
       case RecvPrepareStep => RecvPrepare(c, v, v', msgOps)
       case SendCommitStep(seqID) => SendCommit(c, v, v', msgOps, seqID)
       case RecvCommitStep() => RecvCommit(c, v, v', msgOps)
       case DoCommitStep(seqID) => DoCommit(c, v, v', msgOps, seqID)
       case LeaveViewStep(newView) => LeaveView(c, v, v', msgOps, newView)
       case SendViewChangeMsgStep() => SendViewChangeMsg(c, v, v', msgOps)
  }

  predicate Next(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>) {
    exists step :: NextStep(c, v, v', msgOps, step)
  }
}
