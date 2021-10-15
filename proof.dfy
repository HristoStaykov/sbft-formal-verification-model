
include "distributed_system.s.dfy"

module SafetySpec {
  import opened HostIdentifiers
  import DistributedSystem

  // No two hosts think they hold the lock simulatneously.
  predicate Safety(c:DistributedSystem.Constants, v:DistributedSystem.Variables) {
    false // Replace this placeholder with an appropriate safety condition: no two clients hold
  }
}

module Proof {
  import opened HostIdentifiers
  import Host
  import opened DistributedSystem
  import opened SafetySpec

  // Here's a predicate that will be very useful in constructing inviariant conjuncts.
  predicate CommitAgreement(c:Constants, v:Variables) {
    && (forall msg1, msg2 | 
        && msg1 in v.network.sentMsgs 
        && msg2 in v.network.sentMsgs 
        && msg1.seqID == msg2.seqID
        && msg1.Commit?
        && msg2.Commit?
        :: msg1 == msg2)
  }


  predicate Inv(c: Constants, v:Variables) {
    && CommitAgreement(c, v)
  }

  function getAllPreparesForSeqID(c: Constants, v:Variables, seqID:Host.SequenceID) : set<Host.Message> 
  {
    set msg | && msg in v.network.sentMsgs 
                 && msg.Prepare?
                 && msg.seqID == seqID 
  }

  predicate QuorumOfPreparesInNetwork(c: Constants, v:Variables, seqID:Host.SequenceID) {
    && |getAllPreparesForSeqID()| >= Host.AgreementQuorum()
  }

  lemma WlogCommitAgreement(c: Constants, v:Variables, v':Variables, step:Step, h_step:Host.Step,
                            old_msg:Host.Message, new_msg:Host.Message)
    requires NextStep(c, v, v', step)
    requires  var h_c := c.hosts[step.id];
              var h_v := v.hosts[step.id];
              var h_v' := v'.hosts[step.id];
              && Host.NextStep(h_c, h_v, h_v', step.msgOps, h_step)
              && h_step.SendCommitStep?
              && Host.SendCommit(h_c, h_v, h_v', step.msgOps, h_step.seqID)
              
    requires Inv(c, v)
    ensures old_msg == new_msg
  {
    assert QuorumOfPreparesInNetwork(h_c, h_v, h_step.seqID, old_msg.clientOp);
    assert QuorumOfPreparesInNetwork(h_c, h_v, h_step.seqID, new_msg.clientOp);
  }

  lemma InvariantNext(c: Constants, v:Variables, v':Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
  {
    var step :| NextStep(c, v, v', step);
    var h_c := c.hosts[step.id];
    var h_v := v.hosts[step.id];
    var h_v' := v'.hosts[step.id];
    var h_step :| Host.NextStep(h_c, h_v, h_v', step.msgOps, h_step);
    match h_step
      case SendPrePrepareStep() => { assert Inv(c, v'); }
      case RecvPrePrepareStep => { assert Inv(c, v'); }
      case SendPrepareStep(seqID) => { assert Inv(c, v'); }
      case RecvPrepareStep => { assert Inv(c, v'); }
      case SendCommitStep(seqID) => {
        forall msg1, msg2 | 
          && msg1 in v'.network.sentMsgs 
          && msg2 in v'.network.sentMsgs 
          && msg1.seqID == msg2.seqID
          && msg1.Commit?
          && msg2.Commit?
          ensures msg1 == msg2 {
            if(msg1 in v.network.sentMsgs && msg2 in v.network.sentMsgs) {
              assert msg1 == msg2;
            } else if(msg1 !in v.network.sentMsgs && msg2 !in v.network.sentMsgs) {
              assert msg1 == msg2;
            } else if(msg1 in v.network.sentMsgs && msg2 !in v.network.sentMsgs) {
              WlogCommitAgreement(c, v, v', step, h_step, msg1, msg2);
              assert msg1 == msg2;
            } else if(msg1 !in v.network.sentMsgs && msg2 in v.network.sentMsgs) {
              WlogCommitAgreement(c, v, v', step, h_step, msg2, msg1);
              assert msg1 == msg2;
            } else {
              assert false;
            }
            
          }
          assert Inv(c, v'); 
      }

  }

  lemma InvariantInductive(c: Constants, v:Variables, v':Variables)
    ensures Init(c, v) ==> Inv(c, v)
    ensures Inv(c, v) && Next(c, v, v') ==> Inv(c, v')
    //ensures Inv(c, v) ==> Safety(c, v)
  {
    if Inv(c, v) && Next(c, v, v') {
      InvariantNext(c, v, v');
    }
  }
}
