include "network.s.dfy"

module Messages {
  import opened HostIdentifiers

  type SequenceID = nat

  datatype ClientOperation = ClientOperation(sender:HostId, timestamp:nat)

  // Define your Message datatype here.
  datatype Message = | PrePrepare(view:nat, seqID:SequenceID, clientOp:ClientOperation)
                     | Prepare(view:nat, seqID:SequenceID, clientOp:ClientOperation)
                     | Commit(view:nat, seqID:SequenceID, clientOp:ClientOperation)
                     | ClientRequest(clientOp:ClientOperation)

  // ToDo: ClientReply
}