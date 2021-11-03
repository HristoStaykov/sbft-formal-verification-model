include "library/Library.dfy"
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
  import Library

  // Here's a predicate that will be very useful in constructing inviariant conjuncts.
  predicate RecordedPrePreparesRecvdCameFromNetwork(c:Constants, v:Variables) {
    && v.WF(c)
    && (forall hostIdx, seqID | 
              && ValidHostId(hostIdx)
              && assert Library.TriggerKeyInFullImap(seqID, v.hosts[hostIdx].workingWindow.prePreparesRcvd);
                v.hosts[hostIdx].workingWindow.prePreparesRcvd[seqID].Some? 
                :: v.hosts[hostIdx].workingWindow.prePreparesRcvd[seqID].value in v.network.sentMsgs)
  }

  predicate RecordedPreparesRecvdCameFromNetwork(c:Constants, v:Variables, observer:HostId) {
    && v.WF(c)
    && ValidHostId(observer)
    && (forall sender, seqID | 
              && ValidHostId(sender)
              && assert Library.TriggerKeyInFullImap(seqID, v.hosts[observer].workingWindow.preparesRcvd);
                sender in v.hosts[observer].workingWindow.preparesRcvd[seqID]
                :: v.hosts[observer].workingWindow.preparesRcvd[seqID][sender] in v.network.sentMsgs)
  }

  predicate RecordedPreparesInAllHostsRecvdCameFromNetwork(c:Constants, v:Variables) {
    && v.WF(c)
    && (forall observer | 
            && ValidHostId(observer)
                :: RecordedPreparesRecvdCameFromNetwork(c, v, observer))
  }

  predicate EveryCommitMsgIsSupportedByAQuorumOfPrepares(c:Constants, v:Variables) {
    && v.WF(c)
    && (forall commitMsg | commitMsg in v.network.sentMsgs && commitMsg.Commit? ::
          QuorumOfPreparesInNetwork(c, v, commitMsg.seqID) )
  }

  predicate HonestReplicasLockOnCommitForGivenView(c:Constants, v:Variables) {
    && (forall msg1, msg2 | 
        && msg1 in v.network.sentMsgs 
        && msg2 in v.network.sentMsgs 
        && msg1.seqID == msg2.seqID
        && msg1.sender == msg2.sender
        && msg1.Commit?
        && msg2.Commit?
        :: msg1 == msg2)
  }


  predicate Inv(c: Constants, v:Variables) {
    && RecordedPrePreparesRecvdCameFromNetwork(c, v)
    && RecordedPreparesInAllHostsRecvdCameFromNetwork(c, v)
    && EveryCommitMsgIsSupportedByAQuorumOfPrepares(c, v)
    && HonestReplicasLockOnCommitForGivenView(c, v)
  }

  function getAllPreparesForSeqID(c: Constants, v:Variables, seqID:Host.SequenceID) : set<Host.Message> 
  {
    set msg | && msg in v.network.sentMsgs 
              && msg.Prepare?
              && msg.seqID == seqID
  }

  function setOfSendersForMsgs(msgs:set<Host.Message>) : set<HostIdentifiers.HostId> {
    //set sender | sender in AllHosts() && (exists msg | msg in msgs :: msg.sender == sender)
    set msg | msg in msgs :: msg.sender
  }

  predicate QuorumOfPreparesInNetwork(c:Constants, v:Variables, seqID:Host.SequenceID) {
    && v.WF(c)
    && var prepares := getAllPreparesForSeqID(c, v, seqID);
    && |setOfSendersForMsgs(prepares)| >= c.clusterConfig.AgreementQuorum()
    //&& (forall prepare | prepare in prepares :: prepare.clientOp == clientOperation)
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
    requires old_msg in v.network.sentMsgs && old_msg in v'.network.sentMsgs
    requires new_msg !in v.network.sentMsgs && new_msg in v'.network.sentMsgs
    requires && old_msg.seqID == new_msg.seqID
             && old_msg.sender == new_msg.sender
             && old_msg.Commit?
             && new_msg.Commit?

    requires Inv(c, v)
    ensures old_msg == new_msg
  {
    assert QuorumOfPreparesInNetwork(c, v, h_step.seqID);
    assert QuorumOfPreparesInNetwork(c, v, h_step.seqID);
    assert old_msg == new_msg;
  }

  predicate NoNewCommits(c: Constants, v:Variables, v':Variables)
  {
    && (forall msg | msg in v'.network.sentMsgs && msg.Commit? :: msg in v.network.sentMsgs)
  }

  lemma QuorumOfPreparesInNetworkMonotonic(c: Constants, v:Variables, v':Variables, step:Step, h_step:Host.Step)
    requires NextStep(c, v, v', step)
    requires var h_c := c.hosts[step.id];
             var h_v := v.hosts[step.id];
             var h_v' := v'.hosts[step.id];
             Host.NextStep(h_c, h_v, h_v', step.msgOps, h_step)
    ensures NoNewCommits(c, v, v')
             ==> (forall seqID | QuorumOfPreparesInNetwork(c, v, seqID)
                                        :: QuorumOfPreparesInNetwork(c, v', seqID))
  {
    forall seqID | QuorumOfPreparesInNetwork(c, v, seqID)
                                  ensures QuorumOfPreparesInNetwork(c, v', seqID)
    {
      var senders := setOfSendersForMsgs(getAllPreparesForSeqID(c, v, seqID));
      var senders' := setOfSendersForMsgs(getAllPreparesForSeqID(c, v', seqID));
      Library.SubsetCardinality(senders, senders');
    }
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
    QuorumOfPreparesInNetworkMonotonic(c, v, v', step, h_step);
    match h_step
      case SendPrePrepareStep() => { assert Inv(c, v'); }
      case RecvPrePrepareStep => { assert Inv(c, v'); }
      case SendPrepareStep(seqID) => { assert Inv(c, v'); }
      case RecvPrepareStep => { assert Inv(c, v'); }
      case SendCommitStep(seqID) => {
        // HonestReplicasLockOnACommitForAGiveView
        forall msg1, msg2 | 
          && msg1 in v'.network.sentMsgs 
          && msg2 in v'.network.sentMsgs 
          && msg1.seqID == msg2.seqID
          && msg1.sender == msg2.sender
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
          // A prove of EveryCommitMsgIsSupportedByAQuorumOfPrepares
          forall commitMsg | commitMsg in v'.network.sentMsgs && commitMsg.Commit? ensures 
            QuorumOfPreparesInNetwork(c, v', commitMsg.seqID) {
            if(commitMsg in v.network.sentMsgs) {
              // This is another example of QuorumOfPreparesInNetworkMonotonic but with a sent Commit.
              var senders := setOfSendersForMsgs(getAllPreparesForSeqID(c, v, commitMsg.seqID));
              var senders' := setOfSendersForMsgs(getAllPreparesForSeqID(c, v', commitMsg.seqID));
              Library.SubsetCardinality(senders, senders');
              assert QuorumOfPreparesInNetwork(c, v', commitMsg.seqID);
            } else {
              //|v.workingWindow.preparesRcvd[seqID]| >= c.clusterConfig.AgreementQuorum()
              var prepares := getAllPreparesForSeqID(c, v, commitMsg.seqID);
              var prepares' := getAllPreparesForSeqID(c, v', commitMsg.seqID);
              calc {
                |setOfSendersForMsgs(prepares')|;
                == {assume false;} |setOfSendersForMsgs(prepares)|;
                >= { 
                  var bigSet := setOfSendersForMsgs(prepares);
                  var smallSet := h_v.workingWindow.preparesRcvd[commitMsg.seqID].Keys;
                  forall sender | sender in smallSet
                    ensures sender in bigSet {
                    var msg := h_v.workingWindow.preparesRcvd[commitMsg.seqID][sender];
                    assert msg in prepares by {
                      var observer := step.id;
                      var seqID := commitMsg.seqID;
                      assert Library.TriggerKeyInFullImap(seqID, v.hosts[observer].workingWindow.preparesRcvd);
                      assert ValidHostId(sender);
                      assert sender in v.hosts[observer].workingWindow.preparesRcvd[seqID];
                      assert RecordedPreparesRecvdCameFromNetwork(c, v, observer);
                      assert v.hosts[observer].workingWindow.preparesRcvd[seqID][sender] in v.network.sentMsgs;
                    }
                    assert sender in bigSet by {
                      assume false;
                    }
                  }
                  Library.SubsetCardinality(smallSet, bigSet);
                  assert |smallSet| <= |bigSet|;
                }
                |h_v.workingWindow.preparesRcvd[commitMsg.seqID].Keys|;
                >= h_c.clusterConfig.AgreementQuorum();
                == c.clusterConfig.AgreementQuorum();
              }

              assert QuorumOfPreparesInNetwork(c, v', commitMsg.seqID);
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
