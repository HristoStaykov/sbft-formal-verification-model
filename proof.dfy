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
    && c.IsReplica(hostId)
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
          :: QuorumOfPreparesInNetwork(c, v, commitMsg.seqID, commitMsg.clientOp) )
  }

  predicate HonestReplicasLockOnCommitForGivenView(c:Constants, v:Variables) {
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

  predicate RecordedCommitsClientOpsMatchPrePrepare(c:Constants, v:Variables) {
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

  predicate EveryCommitIsSupportedByRecordedPrepares(c:Constants, v:Variables) {
    && v.WF(c)
    && (forall commitMsg | && commitMsg in v.network.sentMsgs
                           && commitMsg.Commit?
                           && IsHonestReplica(c, commitMsg.sender)
          :: && Replica.QuorumOfPrepares(c.hosts[commitMsg.sender].replicaConstants, 
                                         v.hosts[commitMsg.sender].replicaVariables, 
                                         commitMsg.seqID))
  }

  predicate EveryCommitClientOpMatchesRecordedPrePrepare(c:Constants, v:Variables) {
    && v.WF(c)
    && (forall commitMsg | && commitMsg in v.network.sentMsgs
                           && commitMsg.Commit?
                           && IsHonestReplica(c, commitMsg.sender)
          :: && var recordedPrePrepare := 
                v.hosts[commitMsg.sender].replicaVariables.workingWindow.prePreparesRcvd[commitMsg.seqID]; 
             && recordedPrePrepare.Some?
             && commitMsg.clientOp == recordedPrePrepare.value.clientOp)
  }

  predicate Inv(c: Constants, v:Variables) {
    && RecordedPrePreparesRecvdCameFromNetwork(c, v)
    && RecordedPreparesInAllHostsRecvdCameFromNetwork(c, v)
    && EveryCommitMsgIsSupportedByAQuorumOfPrepares(c, v)
    && RecordedPreparesClientOpsMatchPrePrepare(c, v)
    && RecordedCommitsClientOpsMatchPrePrepare(c, v)
    && EveryCommitIsSupportedByRecordedPrepares(c, v)
    && EveryCommitClientOpMatchesRecordedPrePrepare(c, v)
    && HonestReplicasLockOnCommitForGivenView(c, v)
  }

  function sentPreparesForSeqID(c: Constants, v:Variables, seqID:Messages.SequenceID,
                                  clientOp:Messages.ClientOperation) : set<Messages.Message> 
  {
    set msg | && msg in v.network.sentMsgs 
              && msg.Prepare?
              && msg.seqID == seqID
              && msg.clientOp == clientOp
  }

  function sendersOf(msgs:set<Messages.Message>) : set<HostIdentifiers.HostId> {
    set msg | msg in msgs :: msg.sender
  }

  predicate QuorumOfPreparesInNetwork(c:Constants, v:Variables, seqID:Messages.SequenceID, 
                                      clientOp:Messages.ClientOperation) {
    && v.WF(c)
    && var prepares := sentPreparesForSeqID(c, v, seqID, clientOp);
    && |sendersOf(prepares)| >= c.clusterConfig.AgreementQuorum()
    //&& (forall prepare | prepare in prepares :: prepare.clientOp == clientOperation)
  }

  predicate NoNewCommits(c: Constants, v:Variables, v':Variables)
  {
    && (forall msg | msg in v'.network.sentMsgs && msg.Commit? :: msg in v.network.sentMsgs)
  }

  lemma QuorumOfPreparesInNetworkMonotonic(c: Constants, v:Variables, v':Variables, step:Step, h_step:Replica.Step)
    requires NextStep(c, v, v', step)
    requires c.IsReplica(step.id)
    requires var h_c := c.hosts[step.id].replicaConstants;
             var h_v := v.hosts[step.id].replicaVariables;
             var h_v' := v'.hosts[step.id].replicaVariables;
             Replica.NextStep(h_c, h_v, h_v', step.msgOps, h_step)
    ensures (forall seqID, clientOp | QuorumOfPreparesInNetwork(c, v, seqID, clientOp)
                                        :: QuorumOfPreparesInNetwork(c, v', seqID, clientOp))
  {
    forall seqID, clientOp | QuorumOfPreparesInNetwork(c, v, seqID, clientOp)
                                  ensures QuorumOfPreparesInNetwork(c, v', seqID, clientOp)
    {
      var senders := sendersOf(sentPreparesForSeqID(c, v, seqID, clientOp));
      var senders' := sendersOf(sentPreparesForSeqID(c, v', seqID, clientOp));
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
      QuorumOfPreparesInNetwork(c, v', commitMsg.seqID, commitMsg.clientOp) {
      if(commitMsg in v.network.sentMsgs) { // the commitMsg has been sent in a previous step
        // In this case, the proof is trivial - we just need to "teach" Dafny about subset cardinality
        var senders := sendersOf(sentPreparesForSeqID(c, v, commitMsg.seqID, commitMsg.clientOp));
        var senders' := sendersOf(sentPreparesForSeqID(c, v', commitMsg.seqID, commitMsg.clientOp));
        Library.SubsetCardinality(senders, senders');
      } else { // the commitMsg is being sent in the current step
        var prepares := sentPreparesForSeqID(c, v, commitMsg.seqID, commitMsg.clientOp);
        var prepares' := sentPreparesForSeqID(c, v', commitMsg.seqID, commitMsg.clientOp);
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

  lemma WlogCommitAgreement(c: Constants, v:Variables, v':Variables, step:Step, h_step:Replica.Step,
                            old_msg:Messages.Message, new_msg:Messages.Message)
    requires NextStep(c, v, v', step)
    requires c.IsReplica(step.id)
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
    assert QuorumOfPreparesInNetwork(c, v', old_msg.seqID, old_msg.clientOp);
    assert Replica.QuorumOfPrepares(h_c, h_v, new_msg.seqID);
    var recordedPreparesSenders := h_v.workingWindow.preparesRcvd[new_msg.seqID].Keys;
    assert |recordedPreparesSenders| >= c.clusterConfig.AgreementQuorum();
    var prepares := sentPreparesForSeqID(c, v, new_msg.seqID, new_msg.clientOp);
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

    var prepares' := sentPreparesForSeqID(c, v, new_msg.seqID, new_msg.clientOp);
    Library.SubsetCardinality(prepares, prepares');

    assert forall sender | sender in h_v.workingWindow.preparesRcvd[new_msg.seqID]
                         :: h_v.workingWindow.preparesRcvd[new_msg.seqID][sender].clientOp == new_msg.clientOp;

    assert h_v.workingWindow.prePreparesRcvd[new_msg.seqID].value.clientOp == new_msg.clientOp;

    assert Replica.QuorumOfPrepares(h_c, h_v, old_msg.seqID);

    assert h_v.workingWindow.prePreparesRcvd[old_msg.seqID].value.clientOp == old_msg.clientOp;

    assert forall sender | sender in h_v.workingWindow.preparesRcvd[old_msg.seqID]
                         :: h_v.workingWindow.preparesRcvd[old_msg.seqID][sender].clientOp == old_msg.clientOp;

    Library.SubsetCardinality(recordedPreparesSenders, sendersOf(prepares));
    assert |sendersOf(prepares)| >= c.clusterConfig.AgreementQuorum();
    SendersAreAlwaysFewerThanMessages(prepares);
    assert |prepares| >= |sendersOf(prepares)|;
    assert |prepares| >= c.clusterConfig.AgreementQuorum();
    assert QuorumOfPreparesInNetwork(c, v', new_msg.seqID, new_msg.clientOp);

    assert old_msg.seqID == new_msg.seqID;
    assert old_msg.Commit? && new_msg.Commit?;
    assert old_msg.sender == new_msg.sender;
    assert old_msg.view == new_msg.view;
    assert old_msg.clientOp == new_msg.clientOp;

    assert old_msg == new_msg;
  }

  lemma HonestReplicasLockOnCommitForGivenViewLemma(c: Constants, v:Variables, v':Variables, 
                                                    step:Step, h_step:Replica.Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires c.IsReplica(step.id)
    requires  var h_c := c.hosts[step.id].replicaConstants;
              var h_v := v.hosts[step.id].replicaVariables;
              var h_v' := v'.hosts[step.id].replicaVariables;
              && Replica.NextStep(h_c, h_v, h_v', step.msgOps, h_step)
              && h_step.SendCommitStep?
              && Replica.SendCommit(h_c, h_v, h_v', step.msgOps, h_step.seqID)
    ensures HonestReplicasLockOnCommitForGivenView(c, v')
  {
    forall msg1, msg2 | 
      && msg1 in v'.network.sentMsgs 
      && msg2 in v'.network.sentMsgs 
      && msg1.Commit?
      && msg2.Commit?
      && msg1.view == msg2.view
      && msg1.seqID == msg2.seqID
      && msg1.sender == msg2.sender
      && IsHonestReplica(c, msg1.sender)
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
  }

  lemma InvariantNext(c: Constants, v:Variables, v':Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
  {
    var step :| NextStep(c, v, v', step);

    ProofEveryCommitMsgIsSupportedByAQuorumOfPrepares(c, v, v', step);

    if (c.IsReplica(step.id))
    {
      var h_c := c.hosts[step.id].replicaConstants;
      var h_v := v.hosts[step.id].replicaVariables;
      var h_v' := v'.hosts[step.id].replicaVariables;
      var h_step :| Replica.NextStep(h_c, h_v, h_v', step.msgOps, h_step);
      
      //QuorumOfPreparesInNetworkMonotonic(c, v, v', step, h_step); // not part of the proof yet
      
      match h_step
        case SendPrePrepareStep() => { assert Inv(c, v'); }
        case RecvPrePrepareStep => { assert Inv(c, v'); }
        case SendPrepareStep(seqID) => { assert Inv(c, v'); }
        case RecvPrepareStep => { assert Inv(c, v'); }
        case SendCommitStep(seqID) => {
          HonestReplicasLockOnCommitForGivenViewLemma(c, v, v', step, h_step);
          assert Inv(c, v');
        }
        case RecvCommitStep() => { assert Inv(c, v'); }
        case DoCommitStep(seqID) => { assert Inv(c, v'); }
    } else if (c.IsClient(step.id)) {

      var h_c := c.hosts[step.id].clientConstants;
      var h_v := v.hosts[step.id].clientVariables;
      var h_v' := v'.hosts[step.id].clientVariables;
      var h_step :| Client.NextStep(h_c, h_v, h_v', step.msgOps, h_step);

      match h_step
        case SendClientOperationStep() => { assert Inv(c, v'); }

    } else {
      assert false; // Should not be possible
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
