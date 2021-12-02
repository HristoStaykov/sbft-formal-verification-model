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
  import Replica
  import opened DistributedSystem
  import opened SafetySpec
  import Library

  predicate IsHonestReplica(c:Constants, hostId:HostId) 
  {
    && c.WF()
    && c.clusterConfig.IsReplica(hostId)
  }

  // Here's a predicate that will be very useful in constructing invariant conjuncts.
  predicate RecordedPrePreparesRecvdCameFromNetwork(c:Constants, v:Variables) {
    && v.WF(c)
    && (forall replicaIdx, seqID | 
              && IsHonestReplica(c, replicaIdx)
              && assert Library.TriggerKeyInFullImap(seqID, v.hosts[replicaIdx].replicaVariables.workingWindow.prePreparesRcvd);
                v.hosts[replicaIdx].replicaVariables.workingWindow.prePreparesRcvd[seqID].Some? 
                :: v.hosts[replicaIdx].replicaVariables.workingWindow.prePreparesRcvd[seqID].value in v.network.sentMsgs)
  }

  predicate RecordedPreparesRecvdCameFromNetwork(c:Constants, v:Variables, observer:HostId)
  {
    && v.WF(c)
    && IsHonestReplica(c, observer)
    && (forall sender, seqID | 
              && assert Library.TriggerKeyInFullImap(seqID, v.hosts[observer].replicaVariables.workingWindow.preparesRcvd);
                sender in v.hosts[observer].replicaVariables.workingWindow.preparesRcvd[seqID]
                :: (&& var msg := v.hosts[observer].replicaVariables.workingWindow.preparesRcvd[seqID][sender];
                    && msg in v.network.sentMsgs
                    && msg.sender == sender
                    && msg.seqID == seqID)) // The key we stored matches what is in the msg
  }

  predicate RecordedPreparesInAllHostsRecvdCameFromNetwork(c:Constants, v:Variables) {
    && v.WF(c)
    && (forall observer | 
            && IsHonestReplica(c, observer)
                :: RecordedPreparesRecvdCameFromNetwork(c, v, observer))
  }

  predicate EveryCommitMsgIsSupportedByAQuorumOfPrepares(c:Constants, v:Variables) {
    && v.WF(c)
    && (forall commitMsg | && commitMsg in v.network.sentMsgs 
                           && commitMsg.Commit? 
                           && IsHonestReplica(c, commitMsg.sender)
          :: QuorumOfPreparesInNetwork(c, v, commitMsg.view, commitMsg.seqID, commitMsg.clientOp) )
  }

  predicate HonestReplicasLockOnPrepareForGivenView(c: Constants, v:Variables)
  {
    && (forall msg1, msg2 | 
        && msg1 in v.network.sentMsgs 
        && msg2 in v.network.sentMsgs 
        && msg1.Prepare?
        && msg2.Prepare?
        && msg1.view == msg2.view
        && msg1.seqID == msg2.seqID
        && msg1.sender == msg2.sender
        && IsHonestReplica(c, msg1.sender)
        :: msg1 == msg2)
  }

  predicate {:opaque} HonestReplicasLockOnCommitForGivenView(c:Constants, v:Variables) {
    && (forall msg1, msg2 | 
        && msg1 in v.network.sentMsgs 
        && msg2 in v.network.sentMsgs 
        && msg1.Commit?
        && msg2.Commit?
        && msg1.view == msg2.view
        && msg1.seqID == msg2.seqID
        && msg1.sender == msg2.sender
        && IsHonestReplica(c, msg1.sender)
        :: msg1 == msg2)
  }

  predicate {:opaque} CommitMsgsFromHonestSendersAgree(c:Constants, v:Variables) {
    && (forall msg1, msg2 | 
        && msg1 in v.network.sentMsgs 
        && msg2 in v.network.sentMsgs 
        && msg1.Commit?
        && msg2.Commit?
        && msg1.view == msg2.view
        && msg1.seqID == msg2.seqID
        && IsHonestReplica(c, msg1.sender)
        && IsHonestReplica(c, msg2.sender)
        :: msg1.clientOp == msg2.clientOp)
  }

  predicate RecordedPreparesHaveValidSenderID(c:Constants, v:Variables) {
    && v.WF(c)
    && (forall replicaIdx, seqID, sender |
          && IsHonestReplica(c, replicaIdx)
          && var prepareMap := v.hosts[replicaIdx].replicaVariables.workingWindow.preparesRcvd;
          && seqID in prepareMap
          && sender in prepareMap[seqID]
          :: && v.hosts[replicaIdx].replicaVariables.workingWindow.preparesRcvd[seqID][sender].sender == sender
             && c.clusterConfig.IsReplica(sender)
        )
  }

  predicate RecordedPreparesClientOpsMatchPrePrepare(c:Constants, v:Variables) {
    && v.WF(c)
    && (forall replicaIdx, seqID, sender |
          && IsHonestReplica(c, replicaIdx)
          && var prepareMap := v.hosts[replicaIdx].replicaVariables.workingWindow.preparesRcvd;
          && seqID in prepareMap
          && sender in prepareMap[seqID]
          :: && v.hosts[replicaIdx].replicaVariables.workingWindow.prePreparesRcvd[seqID].Some?
             && v.hosts[replicaIdx].replicaVariables.workingWindow.preparesRcvd[seqID][sender].clientOp
                == v.hosts[replicaIdx].replicaVariables.workingWindow.prePreparesRcvd[seqID].value.clientOp)
  }

  predicate {:opaque} RecordedCommitsClientOpsMatchPrePrepare(c:Constants, v:Variables) {
    && v.WF(c)
    && (forall replicaIdx, seqID, sender |
          && IsHonestReplica(c, replicaIdx)
          && var commitMap := v.hosts[replicaIdx].replicaVariables.workingWindow.commitsRcvd;
          && seqID in commitMap
          && sender in commitMap[seqID]
          :: && v.hosts[replicaIdx].replicaVariables.workingWindow.prePreparesRcvd[seqID].Some?
             && v.hosts[replicaIdx].replicaVariables.workingWindow.commitsRcvd[seqID][sender].clientOp 
             == v.hosts[replicaIdx].replicaVariables.workingWindow.prePreparesRcvd[seqID].value.clientOp)
  }

  predicate {:opaque} EveryCommitIsSupportedByRecordedPrepares(c:Constants, v:Variables) {
    && v.WF(c)
    && (forall commitMsg | && commitMsg in v.network.sentMsgs
                           && commitMsg.Commit?
                           && IsHonestReplica(c, commitMsg.sender)
          :: && Replica.QuorumOfPrepares(c.hosts[commitMsg.sender].replicaConstants, 
                                         v.hosts[commitMsg.sender].replicaVariables, 
                                         commitMsg.seqID))
  }

  predicate {:opaque} EveryCommitClientOpMatchesRecordedPrePrepare(c:Constants, v:Variables) {
    && v.WF(c)
    && (forall commitMsg | && commitMsg in v.network.sentMsgs
                           && commitMsg.Commit?
                           && IsHonestReplica(c, commitMsg.sender)
          :: && var recordedPrePrepare := 
                v.hosts[commitMsg.sender].replicaVariables.workingWindow.prePreparesRcvd[commitMsg.seqID];
             && recordedPrePrepare.Some?
             && commitMsg.clientOp == recordedPrePrepare.value.clientOp)
  }

  predicate RecordedPreparesMatchHostView(c:Constants, v:Variables) {
    && v.WF(c)
    && (forall observer, seqID, sender | 
                           && IsHonestReplica(c, observer)
                           && c.clusterConfig.IsReplica(sender)
                           && var replicaVars := v.hosts[observer].replicaVariables;
                           && seqID in replicaVars.workingWindow.preparesRcvd
                           && sender in replicaVars.workingWindow.preparesRcvd[seqID]
                :: && var replicaVars := v.hosts[observer].replicaVariables;
                   && replicaVars.view == replicaVars.workingWindow.preparesRcvd[seqID][sender].view)
  }

  predicate SentPreparesMatchRecordedPrePrepareIfHostInSameView(c:Constants, v:Variables) {
    && v.WF(c)
    && (forall prepare | 
                && prepare in v.network.sentMsgs
                && prepare.Prepare?
                && IsHonestReplica(c, prepare.sender)
                && prepare.view == v.hosts[prepare.sender].replicaVariables.view
                  :: && v.hosts[prepare.sender].replicaVariables.workingWindow.prePreparesRcvd[prepare.seqID].Some?
                     && v.hosts[prepare.sender].replicaVariables.workingWindow.prePreparesRcvd[prepare.seqID].value.clientOp
                        == prepare.clientOp)
  }

  // predicate PrePreparesCarrySameClientOpsForGivenSeqID(c:Constants, v:Variables)
  // {
  //   && v.WF(c)
  //   && (forall prePrepare1, prePrepare2 | && prePrepare1 in v.network.sentMsgs
  //                                         && prePrepare2 in v.network.sentMsgs
  //                                         && prePrepare1.PrePrepare?
  //                                         && prePrepare2.PrePrepare?
  //                                         && prePrepare1.sender == prePrepare2.sender
  //                                         && prePrepare1.seqID == prePrepare2.seqID
  //                                         && IsHonestReplica(c, prePrepare1.sender)
  //                                       :: prePrepare1 == prePrepare2)
  // }

  predicate Inv(c: Constants, v:Variables) {
    //&& PrePreparesCarrySameClientOpsForGivenSeqID(c, v)
    && RecordedPreparesHaveValidSenderID(c, v)
    && SentPreparesMatchRecordedPrePrepareIfHostInSameView(c, v)
    && RecordedPrePreparesRecvdCameFromNetwork(c, v)
    && RecordedPreparesInAllHostsRecvdCameFromNetwork(c, v)
    && RecordedPreparesMatchHostView(c, v)
    && EveryCommitMsgIsSupportedByAQuorumOfPrepares(c, v)
    && RecordedPreparesClientOpsMatchPrePrepare(c, v)
    && RecordedCommitsClientOpsMatchPrePrepare(c, v)
    && EveryCommitIsSupportedByRecordedPrepares(c, v)
    && EveryCommitClientOpMatchesRecordedPrePrepare(c, v)
    && HonestReplicasLockOnPrepareForGivenView(c, v)
    && HonestReplicasLockOnCommitForGivenView(c, v)
    && CommitMsgsFromHonestSendersAgree(c, v)
  }

  function sentPreparesForSeqID(c: Constants, v:Variables, view:nat, seqID:Messages.SequenceID,
                                  clientOp:Messages.ClientOperation) : set<Messages.Message> 
    requires v.WF(c)
  {
    set msg | && msg in v.network.sentMsgs 
              && msg.Prepare?
              && msg.view == view
              && msg.seqID == seqID
              && msg.clientOp == clientOp
              && msg.sender in getAllReplicas(c)
  }

  function sendersOf(msgs:set<Messages.Message>) : set<HostIdentifiers.HostId> {
    set msg | msg in msgs :: msg.sender
  }

  predicate QuorumOfPreparesInNetwork(c:Constants, v:Variables, view:nat, seqID:Messages.SequenceID, 
                                      clientOp:Messages.ClientOperation) {
    && v.WF(c)
    && var prepares := sentPreparesForSeqID(c, v, view, seqID, clientOp);
    && |sendersOf(prepares)| >= c.clusterConfig.AgreementQuorum()
    //&& (forall prepare | prepare in prepares :: prepare.clientOp == clientOperation)
  }

  predicate NoNewCommits(c: Constants, v:Variables, v':Variables)
  {
    && (forall msg | msg in v'.network.sentMsgs && msg.Commit? :: msg in v.network.sentMsgs)
  }

  lemma WlogCommitAgreement(c: Constants, v:Variables, v':Variables, step:Step,
                            msg1:Messages.Message, msg2:Messages.Message)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires msg1 in v'.network.sentMsgs 
    requires msg2 in v'.network.sentMsgs 
    requires msg1.Commit?
    requires msg2.Commit?
    requires msg1.view == msg2.view
    requires msg1.seqID == msg2.seqID
    requires msg1 in v.network.sentMsgs
    requires msg2 !in v.network.sentMsgs
    requires IsHonestReplica(c, msg1.sender)
    requires IsHonestReplica(c, msg2.sender)
    ensures msg1.clientOp == msg2.clientOp
  {
    //h_step:Replica.Step
    var prepares1 := sentPreparesForSeqID(c, v, msg1.view, msg1.seqID, msg1.clientOp);
    var senders1 := sendersOf(prepares1);
    assert |senders1| >= c.clusterConfig.AgreementQuorum();

    var h_c := c.hosts[step.id].replicaConstants;
    var h_v := v.hosts[step.id].replicaVariables;
    var h_v' := v'.hosts[step.id].replicaVariables;
    var h_step :| Replica.NextStep(h_c, h_v, h_v', step.msgOps, h_step);

    var senders2 := h_v.workingWindow.preparesRcvd[h_step.seqID].Keys;
    assert |senders2| >= c.clusterConfig.AgreementQuorum();

    forall prepare | prepare in prepares1 ensures prepare.sender in getAllReplicas(c) {
      
    }
    assert senders2 <= getAllReplicas(c);
    var equivocatingHonestSender := FindQuorumIntersection(c, senders1, senders2);
    var equivocatingPrepare1 := Messages.Prepare(equivocatingHonestSender, msg1.view,
                                        msg1.seqID, msg1.clientOp);
    var equivocatingPrepare2 := Messages.Prepare(equivocatingHonestSender, msg2.view,
                                        msg2.seqID, msg2.clientOp);
    assert equivocatingPrepare1 in v.network.sentMsgs;
    assert equivocatingPrepare1.Prepare?;
    assert equivocatingPrepare1.seqID == msg1.seqID;
    assert equivocatingPrepare1.clientOp == msg1.clientOp;

    assert equivocatingPrepare1 in prepares1;
    assert equivocatingPrepare1 in v.network.sentMsgs;

    assert equivocatingPrepare2 == h_v.workingWindow.preparesRcvd[h_step.seqID][equivocatingHonestSender];
    // by {
      // var wwMsg := h_v.workingWindow.preparesRcvd[h_step.seqID][equivocatingHonestSender];
      // assert equivocatingPrepare2.view == h_v.view;
      // assert wwMsg.view == equivocatingPrepare2.view;
      // assert wwMsg.clientOp == equivocatingPrepare2.clientOp;
      // assert wwMsg.seqID == equivocatingPrepare2.seqID;
      // assert wwMsg.sender == equivocatingPrepare2
    // };

    assert RecordedPreparesRecvdCameFromNetwork(c, v, step.id);

    assert equivocatingPrepare2 in v.network.sentMsgs;

    if(msg1.clientOp != msg2.clientOp) {

    }
  }

  function GetKReplicas(k:nat) : (hosts:set<HostIdentifiers.HostId>)
    ensures |hosts| == k
    ensures forall host | host in hosts :: 0 <= host < k
  {
    if k == 0 then {}
    else GetKReplicas(k-1) + {k - 1}
  }

  function getAllReplicas(c: Constants) : (hostsSet:set<HostIdentifiers.HostId>)
    requires c.WF()
    ensures |hostsSet| == c.clusterConfig.N()
  {
    GetKReplicas(c.clusterConfig.N())
  }

  lemma FindQuorumIntersection(c: Constants, senders1:set<HostIdentifiers.HostId>, senders2:set<HostIdentifiers.HostId>) 
    returns (common:HostIdentifiers.HostId)
    requires c.WF()
    requires |senders1| >= c.clusterConfig.AgreementQuorum()//TODO: rename hosts
    requires |senders2| >= c.clusterConfig.AgreementQuorum()
    requires senders1 <= getAllReplicas(c)
    requires senders2 <= getAllReplicas(c)
    ensures IsHonestReplica(c, common)
    ensures common in senders1
    ensures common in senders2
  {
    var f := c.clusterConfig.F();
    var n := c.clusterConfig.N();

    assert 2 * f + 1 <= |senders1|;
    assert 2 * f + 1 <= |senders2|;

    var commonSenders := senders1 * senders2;
    if(|commonSenders| < f + 1) {
      calc {
        n;
        == (3 * f) + 1;
        == 2*f+1 + 2*f+1 - (f+1);
        < |senders1| + |senders2| - |senders1*senders2|;
        == |senders1 + senders2|; 
        <= {
          assert senders1 + senders2 <= getAllReplicas(c);
          Library.SubsetCardinality(senders1 + senders2, getAllReplicas(c));
        }
        n;
      }
      assert false; // Proof by contradiction.
    }
    assert f + 1 <= |commonSenders|;


    var honestReplicas := set sender | 0 <= sender < n && IsHonestReplica(c, sender);
    var commonHonest := commonSenders * honestReplicas;
    assert 1 <= |commonHonest|;

    var result :| result in commonHonest;
    common := result;
  }

  lemma ProofCommitMsgsFromHonestSendersAgree(c: Constants, v:Variables, v':Variables, step:Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    ensures CommitMsgsFromHonestSendersAgree(c, v')
  {
    reveal_CommitMsgsFromHonestSendersAgree();
    forall msg1, msg2 | 
      && msg1 in v'.network.sentMsgs 
      && msg2 in v'.network.sentMsgs 
      && msg1.Commit?
      && msg2.Commit?
      && msg1.view == msg2.view
      && msg1.seqID == msg2.seqID
      && IsHonestReplica(c, msg1.sender)
      && IsHonestReplica(c, msg2.sender)
      ensures msg1.clientOp == msg2.clientOp {
        if(msg1 in v.network.sentMsgs && msg2 in v.network.sentMsgs) {
          assert msg1.clientOp == msg2.clientOp;
        } else if(msg1 !in v.network.sentMsgs && msg2 !in v.network.sentMsgs) {
          assert msg1.clientOp == msg2.clientOp;
        } else if(msg1 in v.network.sentMsgs && msg2 !in v.network.sentMsgs) {
          WlogCommitAgreement(c, v, v', step, msg1, msg2);
          assert msg1.clientOp == msg2.clientOp;
        } else if(msg1 !in v.network.sentMsgs && msg2 in v.network.sentMsgs) {
          WlogCommitAgreement(c, v, v', step, msg2, msg1);
          assert msg1.clientOp == msg2.clientOp;
        } else {
          assert false;
        }
      }
  }

  lemma CommitMsgStability(c: Constants, v:Variables, v':Variables, step:Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    ensures RecordedCommitsClientOpsMatchPrePrepare(c, v')
    ensures EveryCommitIsSupportedByRecordedPrepares(c, v')
    ensures EveryCommitClientOpMatchesRecordedPrePrepare(c, v')
    ensures HonestReplicasLockOnCommitForGivenView(c, v')
    ensures EveryCommitMsgIsSupportedByAQuorumOfPrepares(c, v')
    ensures CommitMsgsFromHonestSendersAgree(c, v')
  {
    ProofEveryCommitMsgIsSupportedByAQuorumOfPrepares(c, v, v', step);
    reveal_RecordedCommitsClientOpsMatchPrePrepare();
    reveal_EveryCommitIsSupportedByRecordedPrepares();
    reveal_EveryCommitClientOpMatchesRecordedPrePrepare();
    reveal_HonestReplicasLockOnCommitForGivenView();
    ProofCommitMsgsFromHonestSendersAgree(c, v, v', step);
  }

  lemma QuorumOfPreparesInNetworkMonotonic(c: Constants, v:Variables, v':Variables, step:Step, h_step:Replica.Step)
    requires NextStep(c, v, v', step)
    requires c.clusterConfig.IsReplica(step.id)
    requires var h_c := c.hosts[step.id].replicaConstants;
             var h_v := v.hosts[step.id].replicaVariables;
             var h_v' := v'.hosts[step.id].replicaVariables;
             Replica.NextStep(h_c, h_v, h_v', step.msgOps, h_step)
    ensures (forall view, seqID, clientOp | QuorumOfPreparesInNetwork(c, v, view, seqID, clientOp)
                                        :: QuorumOfPreparesInNetwork(c, v', view, seqID, clientOp))
  {
    forall view, seqID, clientOp | QuorumOfPreparesInNetwork(c, v, view, seqID, clientOp)
                                  ensures QuorumOfPreparesInNetwork(c, v', view, seqID, clientOp)
    {
      var senders := sendersOf(sentPreparesForSeqID(c, v, view, seqID, clientOp));
      var senders' := sendersOf(sentPreparesForSeqID(c, v', view, seqID, clientOp));
      Library.SubsetCardinality(senders, senders');
    }
  }

  lemma ProofEveryCommitMsgIsSupportedByAQuorumOfPrepares(c: Constants, v:Variables, v':Variables, step:Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    ensures EveryCommitMsgIsSupportedByAQuorumOfPrepares(c, v')
  {
    // A proof of EveryCommitMsgIsSupportedByAQuorumOfPrepares,
    // by selecting an arbitrary commitMsg instance
    forall commitMsg | && commitMsg in v'.network.sentMsgs 
                       && commitMsg.Commit? 
                       && IsHonestReplica(c, commitMsg.sender) ensures 
      QuorumOfPreparesInNetwork(c, v', commitMsg.view, commitMsg.seqID, commitMsg.clientOp) {
      if(commitMsg in v.network.sentMsgs) { // the commitMsg has been sent in a previous step
        // In this case, the proof is trivial - we just need to "teach" Dafny about subset cardinality
        var senders := sendersOf(sentPreparesForSeqID(c, v, commitMsg.view, commitMsg.seqID, commitMsg.clientOp));
        var senders' := sendersOf(sentPreparesForSeqID(c, v', commitMsg.view, commitMsg.seqID, commitMsg.clientOp));
        Library.SubsetCardinality(senders, senders');
      } else { // the commitMsg is being sent in the current step
        var prepares := sentPreparesForSeqID(c, v, commitMsg.view, commitMsg.seqID, commitMsg.clientOp);
        var prepares' := sentPreparesForSeqID(c, v', commitMsg.view, commitMsg.seqID, commitMsg.clientOp);
        assert prepares == prepares'; // Trigger (hint) - sending a commitMsg does not affect the set of prepares
        
        // Prove that the prepares in the working window are a subset of the prepares in the network:
        var prepareSendersFromNetwork := sendersOf(prepares);
        var h_v := v.hosts[step.id];
        var prepareSendersInWorkingWindow := h_v.replicaVariables.workingWindow.preparesRcvd[commitMsg.seqID].Keys;
        assert (forall sender | sender in prepareSendersInWorkingWindow 
                              :: && var msg := h_v.replicaVariables.workingWindow.preparesRcvd[commitMsg.seqID][sender];
                                 && msg in v.network.sentMsgs);
        assert (forall sender | sender in prepareSendersInWorkingWindow 
                              :: sender in prepareSendersFromNetwork); //Trigger for subset operator
        Library.SubsetCardinality(prepareSendersInWorkingWindow, prepareSendersFromNetwork);
      }
    }
  }

  lemma SendersAreAlwaysFewerThanMessages(msgs:set<Messages.Message>)
    ensures |sendersOf(msgs)| <= |msgs|
  {
    if |msgs| > 0 {
      var sender :| sender in sendersOf(msgs);
      var msgsFromSender := set msg | && msg in msgs 
                                      && msg.sender == sender;
      var subMsgs := msgs - msgsFromSender;
      SendersAreAlwaysFewerThanMessages(subMsgs);
      Library.SubsetCardinality(sendersOf(subMsgs), sendersOf(msgs) - {sender});
      assert sendersOf(msgs) - {sender} == sendersOf(subMsgs); // Trigger
    }
  }

  lemma WlogCommitSingleHostConsistency(c: Constants, v:Variables, v':Variables, step:Step, h_step:Replica.Step,
                            old_msg:Messages.Message, new_msg:Messages.Message)
    requires NextStep(c, v, v', step)
    requires IsHonestReplica(c, step.id)
    requires  var h_c := c.hosts[step.id].replicaConstants;
              var h_v := v.hosts[step.id].replicaVariables;
              var h_v' := v'.hosts[step.id].replicaVariables;
              && Replica.NextStep(h_c, h_v, h_v', step.msgOps, h_step)
              && h_step.SendCommitStep?
              && Replica.SendCommit(h_c, h_v, h_v', step.msgOps, h_step.seqID)
    requires old_msg in v.network.sentMsgs && old_msg in v'.network.sentMsgs
    requires new_msg !in v.network.sentMsgs && new_msg in v'.network.sentMsgs
    requires && old_msg.Commit?
             && new_msg.Commit?
             && old_msg.seqID == new_msg.seqID
             && old_msg.view == new_msg.view
             && old_msg.sender == new_msg.sender

    requires Inv(c, v)
    ensures old_msg == new_msg
  {
    var h_c := c.hosts[step.id].replicaConstants;
    var h_v := v.hosts[step.id].replicaVariables;
    var h_v' := v'.hosts[step.id].replicaVariables;
    QuorumOfPreparesInNetworkMonotonic(c, v, v', step, h_step);
    assert QuorumOfPreparesInNetwork(c, v', old_msg.view, old_msg.seqID, old_msg.clientOp);
    assert Replica.QuorumOfPrepares(h_c, h_v, new_msg.seqID);
    var recordedPreparesSenders := h_v.workingWindow.preparesRcvd[new_msg.seqID].Keys;
    assert |recordedPreparesSenders| >= c.clusterConfig.AgreementQuorum();
    var prepares := sentPreparesForSeqID(c, v, new_msg.view, new_msg.seqID, new_msg.clientOp);
    assert recordedPreparesSenders <= sendersOf(prepares) by {
      forall sender | sender in recordedPreparesSenders ensures sender in sendersOf(prepares) {
        var msg := h_v.workingWindow.preparesRcvd[new_msg.seqID][sender];
        assert msg.sender == sender;
        assert msg.seqID == new_msg.seqID;
        assert msg.clientOp == new_msg.clientOp;
        assert msg in v.network.sentMsgs;
        assert msg in prepares;
      }
    }

    var prepares' := sentPreparesForSeqID(c, v', new_msg.view, new_msg.seqID, new_msg.clientOp);
    Library.SubsetCardinality(prepares, prepares');

    assert forall sender | sender in h_v.workingWindow.preparesRcvd[new_msg.seqID]
                         :: h_v.workingWindow.preparesRcvd[new_msg.seqID][sender].clientOp == new_msg.clientOp;

    assert h_v.workingWindow.prePreparesRcvd[new_msg.seqID].value.clientOp == new_msg.clientOp;

    assert Replica.QuorumOfPrepares(h_c, h_v, old_msg.seqID);

    assert h_v.workingWindow.prePreparesRcvd[old_msg.seqID].value.clientOp == old_msg.clientOp by {
      reveal_EveryCommitClientOpMatchesRecordedPrePrepare();
    }

    assert forall sender | sender in h_v.workingWindow.preparesRcvd[old_msg.seqID]
                         :: h_v.workingWindow.preparesRcvd[old_msg.seqID][sender].clientOp == old_msg.clientOp;

    Library.SubsetCardinality(recordedPreparesSenders, sendersOf(prepares));
    assert |sendersOf(prepares)| >= c.clusterConfig.AgreementQuorum();
    SendersAreAlwaysFewerThanMessages(prepares);
    assert |prepares| >= |sendersOf(prepares)|;
    assert |prepares| >= c.clusterConfig.AgreementQuorum();
    assert QuorumOfPreparesInNetwork(c, v', new_msg.view, new_msg.seqID, new_msg.clientOp);

    assert old_msg.seqID == new_msg.seqID;
    assert old_msg.Commit? && new_msg.Commit?;
    assert old_msg.sender == new_msg.sender;
    assert old_msg.view == new_msg.view;
    assert old_msg.clientOp == new_msg.clientOp;

    assert old_msg == new_msg;
  }

  predicate SentCommitIsEnabled(c: Constants, v:Variables, v':Variables,
                                step:Step, h_step:Replica.Step)
  {
    && Inv(c, v)
    && NextStep(c, v, v', step)
    && IsHonestReplica(c, step.id)
    && var h_c := c.hosts[step.id].replicaConstants;
    && var h_v := v.hosts[step.id].replicaVariables;
    && var h_v' := v'.hosts[step.id].replicaVariables;
    && Replica.NextStep(h_c, h_v, h_v', step.msgOps, h_step)
    && h_step.SendCommitStep?
    && Replica.SendCommit(h_c, h_v, h_v', step.msgOps, h_step.seqID)
  }

  // lemma HonestReplicasLockOnCommitForGivenViewLemma(c: Constants, v:Variables, v':Variables, 
  //                                                   step:Step, h_step:Replica.Step)
  //   requires SentCommitIsEnabled(c, v, v', step, h_step)
  //   ensures HonestReplicasLockOnCommitForGivenView(c, v')
  // {
  //   reveal_HonestReplicasLockOnCommitForGivenView();
  //   forall msg1, msg2 | 
  //     && msg1 in v'.network.sentMsgs 
  //     && msg2 in v'.network.sentMsgs 
  //     && msg1.Commit?
  //     && msg2.Commit?
  //     && msg1.view == msg2.view
  //     && msg1.seqID == msg2.seqID
  //     && msg1.sender == msg2.sender
  //     && IsHonestReplica(c, msg1.sender)
  //     ensures msg1 == msg2 {
  //       if(msg1 in v.network.sentMsgs && msg2 in v.network.sentMsgs) {
  //         assert msg1 == msg2;
  //       } else if(msg1 !in v.network.sentMsgs && msg2 !in v.network.sentMsgs) {
  //         assert msg1 == msg2;
  //       } else if(msg1 in v.network.sentMsgs && msg2 !in v.network.sentMsgs) {
  //         WlogCommitSingleHostConsistency(c, v, v', step, h_step, msg1, msg2);
  //         assert msg1 == msg2;
  //       } else if(msg1 !in v.network.sentMsgs && msg2 in v.network.sentMsgs) {
  //         WlogCommitSingleHostConsistency(c, v, v', step, h_step, msg2, msg1);
  //         assert msg1 == msg2;
  //       } else {
  //         assert false;
  //       }
  //     }
  // }

  predicate SendClientOperationIsEnabled(c: Constants, v:Variables, v':Variables,
                                         step:Step, h_step:Client.Step)
  {
    && Inv(c, v)
    && NextStep(c, v, v', step)
    && c.clusterConfig.IsClient(step.id)
    && var h_c := c.hosts[step.id].clientConstants;
    && var h_v := v.hosts[step.id].clientVariables;
    && var h_v' := v'.hosts[step.id].clientVariables;
    && Client.NextStep(h_c, h_v, h_v', step.msgOps, h_step)
    && h_step.SendClientOperationStep?
    && Client.SendClientOperation(h_c, h_v, h_v', step.msgOps)
  }

  lemma SendClientOperationPreservesInv(c: Constants, v:Variables, v':Variables, 
                                   step:Step, h_step:Client.Step)
    requires SendClientOperationIsEnabled(c, v, v', step, h_step)
    ensures Inv(c, v')
  {
    CommitMsgStability(c, v, v', step);
  }

  predicate SendPrePrepareIsEnabled(c: Constants, v:Variables, v':Variables,
                                    step:Step, h_step:Replica.Step)
  {
    && Inv(c, v)
    && NextStep(c, v, v', step)
    && IsHonestReplica(c, step.id)
    && var h_c := c.hosts[step.id].replicaConstants;
    && var h_v := v.hosts[step.id].replicaVariables;
    && var h_v' := v'.hosts[step.id].replicaVariables;
    && Replica.NextStep(h_c, h_v, h_v', step.msgOps, h_step)
    && h_step.SendPrePrepareStep?
    && Replica.SendPrePrepare(h_c, h_v, h_v', step.msgOps)
  }

  lemma SendPrePrepareStepPreservesInv(c: Constants, v:Variables, v':Variables, 
                                       step:Step, h_step:Replica.Step)
    requires SendPrePrepareIsEnabled(c, v, v', step, h_step)
    ensures Inv(c, v')
  {
    CommitMsgStability(c, v, v', step);
  }

  predicate SendPrepareIsEnabled(c: Constants, v:Variables, v':Variables,
                                    step:Step, h_step:Replica.Step)
  {
    && Inv(c, v)
    && NextStep(c, v, v', step)
    && IsHonestReplica(c, step.id)
    && var h_c := c.hosts[step.id].replicaConstants;
    && var h_v := v.hosts[step.id].replicaVariables;
    && var h_v' := v'.hosts[step.id].replicaVariables;
    && Replica.NextStep(h_c, h_v, h_v', step.msgOps, h_step)
    && h_step.SendPrepareStep?
    && Replica.SendPrepare(h_c, h_v, h_v', step.msgOps, h_step.seqID)
  }

  lemma SendPrepareStepPreservesInv(c: Constants, v:Variables, v':Variables, 
                                       step:Step, h_step:Replica.Step)
    requires SendPrepareIsEnabled(c, v, v', step, h_step)
    ensures Inv(c, v')
  {
    CommitMsgStability(c, v, v', step);
  }

  predicate RecvPrePrepareIsEnabled(c: Constants, v:Variables, v':Variables,
                                    step:Step, h_step:Replica.Step)
  {
    && Inv(c, v)
    && NextStep(c, v, v', step)
    && IsHonestReplica(c, step.id)
    && var h_c := c.hosts[step.id].replicaConstants;
    && var h_v := v.hosts[step.id].replicaVariables;
    && var h_v' := v'.hosts[step.id].replicaVariables;
    && Replica.NextStep(h_c, h_v, h_v', step.msgOps, h_step)
    && h_step.RecvPrePrepareStep?
    && Replica.RecvPrePrepare(h_c, h_v, h_v', step.msgOps)
  }

  lemma RecvPrePrepareStepPreservesInv(c: Constants, v:Variables, v':Variables, 
                                   step:Step, h_step:Replica.Step)
    requires RecvPrePrepareIsEnabled(c, v, v', step, h_step)
    ensures Inv(c, v')
  {
    CommitMsgStability(c, v, v', step);
  }

  predicate RecvPrepareIsEnabled(c: Constants, v:Variables, v':Variables,
                                step:Step, h_step:Replica.Step)
  {
    && Inv(c, v)
    && NextStep(c, v, v', step)
    && IsHonestReplica(c, step.id)
    && var h_c := c.hosts[step.id].replicaConstants;
    && var h_v := v.hosts[step.id].replicaVariables;
    && var h_v' := v'.hosts[step.id].replicaVariables;
    && Replica.NextStep(h_c, h_v, h_v', step.msgOps, h_step)
    && h_step.RecvPrepareStep?
    && Replica.RecvPrepare(h_c, h_v, h_v', step.msgOps)
  }

  lemma RecvPrepareStepPreservesInv(c: Constants, v:Variables, v':Variables, 
                                   step:Step, h_step:Replica.Step)
    requires RecvPrepareIsEnabled(c, v, v', step, h_step)
    ensures Inv(c, v')
  {
    CommitMsgStability(c, v, v', step);
  }

  predicate RecvCommitIsEnabled(c: Constants, v:Variables, v':Variables,
                                step:Step, h_step:Replica.Step)
  {
    && Inv(c, v)
    && NextStep(c, v, v', step)
    && IsHonestReplica(c, step.id)
    && var h_c := c.hosts[step.id].replicaConstants;
    && var h_v := v.hosts[step.id].replicaVariables;
    && var h_v' := v'.hosts[step.id].replicaVariables;
    && Replica.NextStep(h_c, h_v, h_v', step.msgOps, h_step)
    && h_step.RecvCommitStep?
    && Replica.RecvCommit(h_c, h_v, h_v', step.msgOps)
  }

  lemma RecvCommitStepPreservesInv(c: Constants, v:Variables, v':Variables, 
                                   step:Step, h_step:Replica.Step)
    requires RecvCommitIsEnabled(c, v, v', step, h_step)
    ensures Inv(c, v')
  {
    CommitMsgStability(c, v, v', step);
  }

  predicate DoCommitIsEnabled(c: Constants, v:Variables, v':Variables,
                                step:Step, h_step:Replica.Step)
  {
    && Inv(c, v)
    && NextStep(c, v, v', step)
    && IsHonestReplica(c, step.id)
    && var h_c := c.hosts[step.id].replicaConstants;
    && var h_v := v.hosts[step.id].replicaVariables;
    && var h_v' := v'.hosts[step.id].replicaVariables;
    && Replica.NextStep(h_c, h_v, h_v', step.msgOps, h_step)
    && h_step.DoCommitStep?
    && Replica.DoCommit(h_c, h_v, h_v', step.msgOps, h_step.seqID)
  }

  lemma DoCommitStepPreservesInv(c: Constants, v:Variables, v':Variables, 
                                   step:Step, h_step:Replica.Step)
    requires DoCommitIsEnabled(c, v, v', step, h_step)
    ensures Inv(c, v')
  {
    CommitMsgStability(c, v, v', step);
  }

  lemma SendCommitStepPreservesInv(c: Constants, v:Variables, v':Variables, 
                                   step:Step, h_step:Replica.Step)
    requires SentCommitIsEnabled(c, v, v', step, h_step)
    ensures Inv(c, v')
  {
    CommitMsgStability(c, v, v', step);
    // forall commitMsg | && commitMsg in v'.network.sentMsgs 
    //                    && commitMsg.Commit? 
    //                    && IsHonestReplica(c, commitMsg.sender)
    //   ensures QuorumOfPreparesInNetwork(c, v', commitMsg.seqID, commitMsg.clientOp)
    //   {
    //     if(commitMsg !in v.network.sentMsgs) {
    //       var h_v := v.hosts[step.id].replicaVariables;
    //       var senders := h_v.workingWindow.preparesRcvd[commitMsg.seqID].Keys;
    //       var senders' := sendersOf(sentPreparesForSeqID(c, v', commitMsg.seqID, commitMsg.clientOp));
    //       assert forall sender | sender in senders :: sender in senders'; //Trigger.
    //       Library.SubsetCardinality(senders, senders');
    //     }
    //   }
  }

  lemma InvariantNext(c: Constants, v:Variables, v':Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
  {
    var step :| NextStep(c, v, v', step);

    ProofEveryCommitMsgIsSupportedByAQuorumOfPrepares(c, v, v', step);

    if (c.clusterConfig.IsReplica(step.id))
    {
      var h_c := c.hosts[step.id].replicaConstants;
      var h_v := v.hosts[step.id].replicaVariables;
      var h_v' := v'.hosts[step.id].replicaVariables;
      var h_step :| Replica.NextStep(h_c, h_v, h_v', step.msgOps, h_step);
      
      //QuorumOfPreparesInNetworkMonotonic(c, v, v', step, h_step); // not part of the proof yet
      
      match h_step
        case SendPrePrepareStep() => {
          SendPrePrepareStepPreservesInv(c, v, v', step, h_step);
        }
        case RecvPrePrepareStep => {
          RecvPrePrepareStepPreservesInv(c, v, v', step, h_step);
        }
        case SendPrepareStep(seqID) => {
          SendPrepareStepPreservesInv(c, v, v', step, h_step);
        }
        case RecvPrepareStep => { 
          RecvPrepareStepPreservesInv(c, v, v', step, h_step);
        }
        case SendCommitStep(seqID) => {
          SendCommitStepPreservesInv(c, v, v', step, h_step);
        }
        case RecvCommitStep() => {
          RecvCommitStepPreservesInv(c, v, v', step, h_step);
        }
        case DoCommitStep(seqID) => { 
          DoCommitStepPreservesInv(c, v, v', step, h_step);
        }
    } else if (c.clusterConfig.IsClient(step.id)) {

      var h_c := c.hosts[step.id].clientConstants;
      var h_v := v.hosts[step.id].clientVariables;
      var h_v' := v'.hosts[step.id].clientVariables;
      var h_step :| Client.NextStep(h_c, h_v, h_v', step.msgOps, h_step);

      match h_step
        case SendClientOperationStep() => {
          SendClientOperationPreservesInv(c, v, v', step, h_step);
        }

    } else {
      assert false; // Should not be possible
    }
  }

  lemma InvariantInductive(c: Constants, v:Variables, v':Variables)
    ensures Init(c, v) ==> Inv(c, v)
    ensures Inv(c, v) && Next(c, v, v') ==> Inv(c, v')
    //ensures Inv(c, v) ==> Safety(c, v)
  {
    if Init(c, v) {
      reveal_RecordedCommitsClientOpsMatchPrePrepare();
      reveal_EveryCommitIsSupportedByRecordedPrepares();
      reveal_EveryCommitClientOpMatchesRecordedPrePrepare();
      reveal_HonestReplicasLockOnCommitForGivenView();
      reveal_CommitMsgsFromHonestSendersAgree();
      assert Inv(c, v);
    }
    if Inv(c, v) && Next(c, v, v') {
      InvariantNext(c, v, v');
    }
  }
}
