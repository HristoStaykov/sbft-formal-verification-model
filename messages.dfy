include "network.s.dfy"

module Messages {
  import opened HostIdentifiers

  type SequenceID = nat
  
  type ClientOperation(!new, ==)

      // Define your Message datatype here.
  datatype Message = | PrePrepare(sender:HostId, view:nat, seqID:SequenceID, clientOp:ClientOperation)
                     | Prepare(sender:HostId, view:nat, seqID:SequenceID, clientOp:ClientOperation)
                     | Commit(sender:HostId, view:nat, seqID:SequenceID, clientOp:ClientOperation)
}