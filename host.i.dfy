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
                     
  type PrepareProofSet = set<Message> 
  predicate PrepareProofSetWF(ps:PrepareProofSet) {
      && forall x | x in ps :: x.PrePrepare? || x.Prepare?
  }

  type CommitProofSet = set<Message>
  predicate CommitProofSetWF(cs:CommitProofSet) {
      && forall x | x in cs :: x.Commit?
  }

  datatype WorkingWindow = WorkingWindow(
    committedClientOperations:imap<SequenceID, Option<ClientOperation>>,
    preparesRcvd:imap<SequenceID, PrepareProofSet>,
    commitsRcvd:imap<SequenceID, CommitProofSet>
  ) {
      // TODO: K(!new)
      // predicate FullImap<K,V>(im:imap<K,V>) {
      //   forall k :: k in im
      // }
  }

  // Define your Host protocol state machine here.
  datatype Constants = Constants(myId:HostId, clusterSize:nat) {
    // host constants coupled to DistributedSystem Constants:
    // DistributedSystem tells us our id so we can recognize inbound messages.
    // TODO(jonh): get rid of ValidHosts; move hostCount in here instead.
    predicate WF() {
      && clusterSize >= 4
      && myId < clusterSize
    }

    predicate Configure(id:HostId, replcasCount:nat) {
      && myId == id
      && clusterSize == replcasCount
    }
  }


  datatype Variables = Variables(
    view:nat,
    viewIsActive:bool,
    workingWindow:WorkingWindow
  )

  function CurentPrimary(c:Constants, v:Variables) : nat 
    requires c.WF()
  {
    v.view % c.clusterSize
  }

  predicate RecvPrePrepareEnabled(c:Constants, v:Variables, p:Message)
  {
    && c.WF()
    && v.viewIsActive
    && p.view == v.view
    && p.PrePrepare?
    && p.sender == CurentPrimary(c, v)
    && (forall x | x in v.workingWindow.preparesRcvd[p.seqID] && x.seqID == p.seqID :: x.sender != p.sender)
  }

  predicate RecvPrePrepare(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>)
  {
    && msgOps.recv.Some?
    && msgOps.send.None?
    && var msg := msgOps.recv.value;
    && RecvPrePrepareEnabled(c, v, msg)
    && v' == v.(workingWindow := 
                v.workingWindow.(preparesRcvd := 
                                 v.workingWindow.preparesRcvd[msg.seqID := 
                                 v.workingWindow.preparesRcvd[msg.seqID] + {msg}]))
  }

  predicate SendPrepare(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>)
  {
    && c.WF()
    && msgOps.recv.None?
    && v.viewIsActive
    && exists seqID | seqID in v.workingWindow.preparesRcvd :: 
              exists message | message in v.workingWindow.preparesRcvd[seqID] && message.PrePrepare? :: 
                  msgOps.send == Some(Prepare(c.myId, v.view, seqID, message.clientOp))
                  && v' == v.(workingWindow := 
                           v.workingWindow.(preparesRcvd := 
                                 v.workingWindow.preparesRcvd[seqID := 
                                 v.workingWindow.preparesRcvd[seqID] + {msgOps.send.value}]))
  }
  
  predicate Init(c:Constants, v:Variables) {
    && v.view == 0
    && v.viewIsActive == true
    && (forall seqID | seqID in v.workingWindow.committedClientOperations
                :: v.workingWindow.committedClientOperations[seqID].None?)
    && (forall seqID | seqID in v.workingWindow.preparesRcvd :: v.workingWindow.preparesRcvd[seqID] == {})
    && (forall seqID | seqID in v.workingWindow.commitsRcvd :: v.workingWindow.commitsRcvd[seqID] == {})
  }

  // JayNF
  datatype Step =
// Recvs:
    | RecvPrePrepareStep()
// Sends:
    | SendPrepareStep()

  predicate NextStep(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>, step: Step) {
    match step
       case RecvPrePrepareStep => RecvPrePrepare(c, v, v, msgOps)
       case SendPrepareStep => SendPrepare(c, v, v, msgOps)
  }

  predicate Next(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>) {
    exists step :: NextStep(c, v, v', msgOps, step)
  }
}
