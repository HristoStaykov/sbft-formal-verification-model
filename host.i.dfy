//#title Host protocol
//#desc Define the host state machine here: message type, state machine for executing one
//#desc host's part of the protocol.

// See exercise01.dfy for an English design of the protocol.

include "network.s.dfy"

module Host {
  import opened Library
  import opened HostIdentifiers
  import Network
  type ClientOperation(!new, ==)
  type SequenceID = nat

  // Define your Message datatype here.
  datatype Message = | PrePrepare(sender:HostId, view:nat, seqID:SequenceID, clientOp:ClientOperation)
                     | Prepare(sender:HostId, view:nat, seqID:SequenceID, clientOp:ClientOperation)
                     | Commit(sender:HostId, view:nat, seqID:SequenceID, clientOp:ClientOperation)
                     
  type PrepareProofSet = map<HostId, Message>
  type CommitProofSet = map<HostId, Message>
  datatype WorkingWindow = WorkingWindow(
    committedClientOperations:map<SequenceID, ClientOperation>,
    preparesRcvd:map<SequenceID, PrepareProofSet>,
    commitsRcvd:map<SequenceID, CommitProofSet>
  )

  // Define your Host protocol state machine here.
  datatype Constants = Constants(myId:HostId, clusterSize:nat) {
    // host constants coupled to DistributedSystem Constants:
    // DistributedSystem tells us our id so we can recognize inbound messages.
    // TODO(jonh): get rid of ValidHosts; move hostCount in here instead.
    predicate GroupWF(id:HostId, replcasCount:nat) {
      && myId == id
      && replcasCount >= 4
      && clusterSize == replcasCount
    }
  }


  datatype Variables = Variables(
    view:nat,
    viewIsActive:bool,
    workingWindow:WorkingWindow
  )

  function CurentPrimary(v:Variables, c:Constants) : nat 
    requires c.clusterSize >= 4
  {
    v.view % c.clusterSize
  }

  predicate AcceptPrePrepare(p:Message, v:Variables, c:Constants)
    requires c.clusterSize >= 4
  {
    && p.PrePrepare?
    && p.sender == CurentPrimary(v, c)
    && p.view == v.view
    && p.sender !in v.workingWindow.preparesRcvd[p.seqID]
    //&& forall k | k in v.preparesRcvd[p.seqID] :: k != p.sender
  }

  predicate Init(c:Constants, v:Variables) {
    && v.view == 0
    && v.viewIsActive == true
  }

  // JayNF
  datatype Step =
    | SomeStep

  predicate NextStep(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>, step: Step) {
    match step
       case SomeStep => true
  }

  predicate Next(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>) {
    exists step :: NextStep(c, v, v', msgOps, step)
  }
}
