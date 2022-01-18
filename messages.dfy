include "network.s.dfy"

module Messages {
  import opened HostIdentifiers
  import Network

  type SequenceID = nat
  type ViewNum = nat

  datatype ClientOperation = ClientOperation(sender:HostId, timestamp:nat)

  datatype PreparedCertificate = PreparedCertificate(votes:set<Network.Message<Message>>) {
    function prototype() : Message 
      requires |votes| > 0
    {
      var prot :| prot in votes;
      prot.payload
    }
    predicate valid() {
      && |votes| > 0
      && prototype().Prepare?
      && (forall v | v in votes :: v.payload == prototype()) // messages have to be votes that match eachother by the prototype 
      && (forall v1, v2 | && v1 in votes
                          && v2 in votes
                          && v1 != v2
                            :: v1.sender != v2.sender) // unique senders
    }
    predicate empty() {
      && |votes| == 0
    }
  }

  datatype ViewChangeMsgsSelectedByPrimary = ViewChangeMsgsSelectedByPrimary(msgs:set<Network.Message<Message>>) {
    predicate valid(view:ViewNum, quorumSize:nat) {
      && |msgs| > 0
      && (forall v | v in msgs :: && v.payload.ViewChangeMsg? 
                                  && v.payload.newView == view) // All the ViewChange messages have to be for the same View. 
      && (forall v1, v2 | && v1 in msgs
                          && v2 in msgs
                          && v1 != v2
                            :: v1.sender != v2.sender) // unique senders
      && |msgs| == quorumSize
    }
  }

  // Define your Message datatype here.
  datatype Message = | PrePrepare(view:ViewNum, seqID:SequenceID, clientOp:ClientOperation)
                     | Prepare(view:ViewNum, seqID:SequenceID, clientOp:ClientOperation)
                     | Commit(view:ViewNum, seqID:SequenceID, clientOp:ClientOperation)
                     | ClientRequest(clientOp:ClientOperation)
                     | ViewChangeMsg(newView:ViewNum, certificates:imap<SequenceID, PreparedCertificate>) // omitting last stable because we don't have checkpointing yet.
                     | NewViewMsg(newView:ViewNum, vcMsgs:ViewChangeMsgsSelectedByPrimary)
  // ToDo: ClientReply
}