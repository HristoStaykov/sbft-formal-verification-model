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

  // Here's a predicate that will be very useful in constructing inviariant conjuncts.
  predicate RecordedPrePreparesRecvdCameFromNetwork(c:Constants, v:Variables) {
    && v.WF(c)
    && (forall replicaIdx, seqID | 
              && c.IsReplica(replicaIdx)
              && assert Library.TriggerKeyInFullImap(seqID, v.hosts[replicaIdx].replicaVariables.workingWindow.prePreparesRcvd);
                v.hosts[replicaIdx].replicaVariables.workingWindow.prePreparesRcvd[seqID].Some? 
                :: v.hosts[replicaIdx].replicaVariables.workingWindow.prePreparesRcvd[seqID].value in v.network.sentMsgs)
  }

  predicate RecordedPreparesRecvdCameFromNetwork(c:Constants, v:Variables, observer:HostId)
  {
    && v.WF(c)
    && c.IsReplica(observer)
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
            && c.IsReplica(observer)
                :: RecordedPreparesRecvdCameFromNetwork(c, v, observer))
  }

  predicate EveryCommitMsgIsSupportedByAQuorumOfPrepares(c:Constants, v:Variables) {
    && v.WF(c)
    && (forall commitMsg | commitMsg in v.network.sentMsgs && commitMsg.Commit? ::
          QuorumOfPreparesInNetwork(c, v, commitMsg.seqID, commitMsg.clientOp) )
  }

  predicate HonestReplicasLockOnCommitForGivenView(c:Constants, v:Variables) {
    && (forall msg1, msg2 | 
        && msg1 in v.network.sentMsgs 
        && msg2 in v.network.sentMsgs 
        && msg1.Commit?
        && msg2.Commit?
        && msg1.seqID == msg2.seqID
        && msg1.sender == msg2.sender
        :: msg1 == msg2)
  }

  predicate RecordedPreparesClientOpsMatchPrePrepare(c:Constants, v:Variables) {
    && v.WF(c)
    && (forall replicaIdx, seqID, sender |
          && c.IsReplica(replicaIdx)
          && var prepareMap := v.hosts[replicaIdx].replicaVariables.workingWindow.preparesRcvd;
          && seqID in prepareMap
          && sender in prepareMap[seqID]
          :: && v.hosts[replicaIdx].replicaVariables.workingWindow.prePreparesRcvd[seqID].Some?         
             && v.hosts[replicaIdx].replicaVariables.workingWindow.preparesRcvd[seqID][sender].clientOp 
             == v.hosts[replicaIdx].replicaVariables.workingWindow.prePreparesRcvd[seqID].value.clientOp)
  }

  predicate Inv(c: Constants, v:Variables) {
    && RecordedPrePreparesRecvdCameFromNetwork(c, v)
    && RecordedPreparesInAllHostsRecvdCameFromNetwork(c, v)
    && EveryCommitMsgIsSupportedByAQuorumOfPrepares(c, v)
    && RecordedPreparesClientOpsMatchPrePrepare(c, v)
    && HonestReplicasLockOnCommitForGivenView(c, v)
  }

  function getAllPreparesForSeqID(c: Constants, v:Variables, seqID:Messages.SequenceID,
                                  clientOp:Messages.ClientOperation) : set<Messages.Message> 
  {
    set msg | && msg in v.network.sentMsgs 
              && msg.Prepare?
              && msg.seqID == seqID
              && msg.clientOp == clientOp
  }

  function setOfSendersForMsgs(msgs:set<Messages.Message>) : set<HostIdentifiers.HostId> {
    //set sender | sender in AllHosts() && (exists msg | msg in msgs :: msg.sender == sender)
    set msg | msg in msgs :: msg.sender
  }

  predicate QuorumOfPreparesInNetwork(c:Constants, v:Variables, seqID:Messages.SequenceID, 
                                      clientOp:Messages.ClientOperation) {
    && v.WF(c)
    && var prepares := getAllPreparesForSeqID(c, v, seqID, clientOp);
    && |setOfSendersForMsgs(prepares)| >= c.clusterConfig.AgreementQuorum()
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
      var senders := setOfSendersForMsgs(getAllPreparesForSeqID(c, v, seqID, clientOp));
      var senders' := setOfSendersForMsgs(getAllPreparesForSeqID(c, v', seqID, clientOp));
      Library.SubsetCardinality(senders, senders');
    }
  }

  lemma ProofEveryCommitMsgIsSupportedByAQuorumOfPrepares(c: Constants, v:Variables, v':Variables, step:Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    ensures EveryCommitMsgIsSupportedByAQuorumOfPrepares(c, v')
  {
    // A proof of EveryCommitMsgIsSupportedByAQuorumOfPrepares
    forall commitMsg | commitMsg in v'.network.sentMsgs && commitMsg.Commit? ensures 
      QuorumOfPreparesInNetwork(c, v', commitMsg.seqID, commitMsg.clientOp) {
      if(commitMsg in v.network.sentMsgs) {
        // Adding some basic facts to help Dafny - otherwise this is trivial
        var senders := setOfSendersForMsgs(getAllPreparesForSeqID(c, v, commitMsg.seqID, commitMsg.clientOp));
        var senders' := setOfSendersForMsgs(getAllPreparesForSeqID(c, v', commitMsg.seqID, commitMsg.clientOp));
        Library.SubsetCardinality(senders, senders');
      } else {
        var prepares := getAllPreparesForSeqID(c, v, commitMsg.seqID, commitMsg.clientOp);
        var prepares' := getAllPreparesForSeqID(c, v', commitMsg.seqID, commitMsg.clientOp);
        assert prepares == prepares'; // Trigger (hint)
        
        var prepareSendersFromNetwork := setOfSendersForMsgs(prepares);
        var h_v := v.hosts[step.id];
        var prepareSendersInWorkingWindow := h_v.replicaVariables.workingWindow.preparesRcvd[commitMsg.seqID].Keys;
        assert (forall sender | sender in prepareSendersInWorkingWindow 
                              :: && var msg := h_v.replicaVariables.workingWindow.preparesRcvd[commitMsg.seqID][sender];
                                 && msg in v.network.sentMsgs);
        forall sender | sender in prepareSendersInWorkingWindow 
                              ensures sender in prepareSendersFromNetwork {
          var msg := h_v.replicaVariables.workingWindow.preparesRcvd[commitMsg.seqID][sender];
          assert msg in v.network.sentMsgs;
          assert msg.seqID == commitMsg.seqID;
          assert msg.clientOp == commitMsg.clientOp;
          assert msg in prepares;
          assert msg.sender in prepareSendersFromNetwork;
        } //Trigger for subset operator
        Library.SubsetCardinality(prepareSendersInWorkingWindow, prepareSendersFromNetwork);
      }
    }
  }

  predicate ReplicaInternalMsg(msg:Messages.Message)
  {
    || msg.PrePrepare?
    || msg.Prepare?
    || msg.Commit?
  }

  lemma SendersAreAlwaysFewerThanMessages(msgs:set<Messages.Message>)
    ensures |setOfSendersForMsgs(msgs)| <= |msgs|
  {
    if |msgs| > 0 {
      var sender :| sender in setOfSendersForMsgs(msgs);
      var msgsFromSender := set msg | && msg in msgs 
                                      && msg.sender == sender;
      var subMsgs := msgs - msgsFromSender;
      SendersAreAlwaysFewerThanMessages(subMsgs);
      Library.SubsetCardinality(setOfSendersForMsgs(subMsgs), setOfSendersForMsgs(msgs) - {sender});
      assert setOfSendersForMsgs(msgs) - {sender} == setOfSendersForMsgs(subMsgs); // Trigger
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
    requires old_msg in v.network.sentMsgs && old_msg in v'.network.sentMsgs && ReplicaInternalMsg(old_msg)
    requires new_msg !in v.network.sentMsgs && new_msg in v'.network.sentMsgs && ReplicaInternalMsg(new_msg)
    requires && old_msg.seqID == new_msg.seqID
             && old_msg.sender == new_msg.sender
             && old_msg.Commit?
             && new_msg.Commit?

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
    var prepares := getAllPreparesForSeqID(c, v, new_msg.seqID, new_msg.clientOp);
    assert recordedPreparesSenders <= setOfSendersForMsgs(prepares) by {
      forall sender | sender in recordedPreparesSenders ensures sender in setOfSendersForMsgs(prepares) {
        var msg := h_v.workingWindow.preparesRcvd[new_msg.seqID][sender];
        assert msg.sender == sender;
        assert msg.seqID == new_msg.seqID;
        assert msg.clientOp == new_msg.clientOp;
        assert msg in v.network.sentMsgs;
        assert msg in prepares;
      }
    }
    Library.SubsetCardinality(recordedPreparesSenders, setOfSendersForMsgs(prepares));
    assert |setOfSendersForMsgs(prepares)| >= c.clusterConfig.AgreementQuorum();
    SendersAreAlwaysFewerThanMessages(prepares);
    assert |prepares| >= |setOfSendersForMsgs(prepares)|;
    assert |prepares| >= c.clusterConfig.AgreementQuorum();
    assert QuorumOfPreparesInNetwork(c, v', new_msg.seqID, new_msg.clientOp);
    assert old_msg == new_msg;
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
          // HonestReplicasLockOnACommitForAGiveView
          forall msg1, msg2 | 
            && msg1 in v'.network.sentMsgs 
            && msg2 in v'.network.sentMsgs 
            && msg1.Commit?
            && msg2.Commit?
            && msg1.seqID == msg2.seqID
            && msg1.sender == msg2.sender
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
