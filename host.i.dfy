//#title Host protocol
//#desc Define the host state machine here: message type, state machine for executing one
//#desc host's part of the protocol.

// See exercise01.dfy for an English design of the protocol.

include "network.s.dfy"
include "cluster_config.s.dfy"

module Host {
  import opened Library
  import opened HostIdentifiers
  import Network
  import ClusterConfig
  type ClientOperation(!new, ==)
  type SequenceID = nat

  // Define your Message datatype here.
  datatype Message = | PrePrepare(sender:HostId, view:nat, seqID:SequenceID, clientOp:ClientOperation)
                     | Prepare(sender:HostId, view:nat, seqID:SequenceID, clientOp:ClientOperation)
                     | Commit(sender:HostId, view:nat, seqID:SequenceID, clientOp:ClientOperation)
                     
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
    // TODO(jonh): get rid of ValidHosts; move hostCount in here instead.
    predicate WF() {
      && clusterConfig.WF()
      && myId < clusterConfig.clusterSize
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

  function CurentPrimary(c:Constants, v:Variables) : nat 
    requires c.WF()
  {
    v.view % c.clusterConfig.clusterSize
  }

  predicate SendPrePrepare(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>)
  {
    && v.WF(c)
    && msgOps.recv.None?
    && msgOps.send.Some?
    && var msg := msgOps.send.value;
    && msg.PrePrepare? // We have a liveness bug here, we need some state that says for the client which operation ID-s we have executed
  }

  predicate RecvPrePrepareEnabled(c:Constants, v:Variables, p:Message)
  {
    && v.WF(c)
    && v.viewIsActive
    && p.view == v.view
    && p.PrePrepare?
    && p.sender == CurentPrimary(c, v)
    && v.workingWindow.prePreparesRcvd[p.seqID].None?
  }

  predicate RecvPrePrepare(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>)
  {
    && msgOps.recv.Some?
    && msgOps.send.None?
    && var msg := msgOps.recv.value;
    && RecvPrePrepareEnabled(c, v, msg)
    && v' == v.(workingWindow := 
                v.workingWindow.(prePreparesRcvd := 
                                 v.workingWindow.prePreparesRcvd[msg.seqID := Some(msg)]))
  }

  predicate RecvPrepareEnabled(c:Constants, v:Variables, p:Message)
  {
    && v.WF(c)
    && v.viewIsActive
    && p.view == v.view
    && p.Prepare?
    && v.workingWindow.prePreparesRcvd[p.seqID].Some?
    && v.workingWindow.prePreparesRcvd[p.seqID].value.clientOp == p.clientOp
    && (forall x | x in v.workingWindow.preparesRcvd[p.seqID] && x.seqID == p.seqID :: x.sender != p.sender)
  }

  predicate RecvPrepare(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>)
  {
    && msgOps.recv.Some?
    && msgOps.send.None?
    && var msg := msgOps.recv.value;
    && RecvPrepareEnabled(c, v, msg)
    && v' == v.(workingWindow := 
                v.workingWindow.(preparesRcvd := 
                                 v.workingWindow.preparesRcvd[msg.seqID := 
                                 v.workingWindow.preparesRcvd[msg.seqID] + {msg}]))
  }

  predicate QuorumOfPrepares(c:Constants, v:Variables, seqID:SequenceID)
  {
    && v.WF(c)
    && |v.workingWindow.preparesRcvd[seqID]| >= c.clusterConfig.AgreementQuorum()
  }

  predicate SendPrepare(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>, seqID:SequenceID)
  {
    && v.WF(c)
    && msgOps.recv.None?
    && v.viewIsActive
    && v.workingWindow.prePreparesRcvd[seqID].Some?
    && msgOps.send == Some(Prepare(c.myId, v.view, seqID, v.workingWindow.prePreparesRcvd[seqID].value.clientOp))
    && v' == v
    // && v' == v.(workingWindow := 
    //             v.workingWindow.(preparesRcvd := 
    //                              v.workingWindow.preparesRcvd[seqID := 
    //                              v.workingWindow.preparesRcvd[seqID] + {msgOps.send.value}]))
  }

  predicate SendCommit(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>, seqID:SequenceID)
  {
    && v.WF(c)
    && msgOps.recv.None?
    && v.viewIsActive
    && QuorumOfPrepares(c, v, seqID)
    && v.workingWindow.prePreparesRcvd[seqID].Some?
    && msgOps.send == Some(Commit(c.myId, v.view, seqID, v.workingWindow.prePreparesRcvd[seqID].value.clientOp))
    && v' == v.(workingWindow := 
                v.workingWindow.(commitsRcvd := 
                                 v.workingWindow.commitsRcvd[seqID := 
                                 v.workingWindow.commitsRcvd[seqID] + {msgOps.send.value}]))
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
    //| RecvCommitStep()
    //| DoCommit(seqID:SequenceID)
    //| Execute(seqID:SequenceID)
    //| SendReplyToClient(seqID:SequenceID)

  predicate NextStep(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>, step: Step) {
    match step
       case SendPrePrepareStep() => SendPrePrepare(c, v, v', msgOps)
       case RecvPrePrepareStep => RecvPrePrepare(c, v, v', msgOps)
       case SendPrepareStep(seqID) => SendPrepare(c, v, v', msgOps, seqID)
       case RecvPrepareStep => RecvPrepare(c, v, v', msgOps)
       case SendCommitStep(seqID) => SendCommit(c, v, v', msgOps, seqID)
  }

  predicate Next(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>) {
    exists step :: NextStep(c, v, v', msgOps, step)
  }
}
