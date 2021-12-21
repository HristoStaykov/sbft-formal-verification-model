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
  import opened Library

  predicate IsHonestReplica(c:Constants, hostId:HostId) 
  {
    && c.WF()
    && c.clusterConfig.IsReplica(hostId)
  }

  type Frame = Network.Message<Messages.Message>

  // Just a shorthand to reduce a repetitive requires stanza
  predicate RVValid(c:Constants, v:Variables, replicaIdx: HostId)
  {
    && v.WF(c)
    && c.clusterConfig.IsReplica(replicaIdx)
  }

  // TODO opaque only this thing to hide its map selects
  function {:opaque} ReplicaVariables(c:Constants, v:Variables, replicaIdx: HostId) : Replica.Variables
    requires RVValid(c, v, replicaIdx)
  {
    v.hosts[replicaIdx].replicaVariables
  }

  function PrepreparesRcvdMap(c:Constants, v:Variables, replicaIdx: HostId) : imap<Messages.SequenceID, Option<Frame>>
    requires RVValid(c, v, replicaIdx)
  {
    ReplicaVariables(c, v, replicaIdx).workingWindow.prePreparesRcvd
  }

  function {:opaque} PrepreparesRcvd(c:Constants, v:Variables, replicaIdx: HostId, seqID: Messages.SequenceID) : Option<Frame>
    requires RVValid(c, v, replicaIdx)
  {
    assert Library.TriggerKeyInFullImap(seqID, v.hosts[replicaIdx].replicaVariables.workingWindow.prePreparesRcvd);
    PrepreparesRcvdMap(c, v, replicaIdx)[seqID]
  }

  function PreparesRcvdMap(c:Constants, v:Variables, replicaIdx: HostId) : imap<Messages.SequenceID, Replica.PrepareProofSet>
    requires RVValid(c, v, replicaIdx)
  {
    ReplicaVariables(c, v, replicaIdx).workingWindow.preparesRcvd
  }

  function {:opaque} PreparesRcvd(c:Constants, v:Variables, replicaIdx: HostId, seqID: Messages.SequenceID) : Replica.PrepareProofSet
    requires RVValid(c, v, replicaIdx)
  {
    assert Library.TriggerKeyInFullImap(seqID, v.hosts[replicaIdx].replicaVariables.workingWindow.preparesRcvd);
    PreparesRcvdMap(c, v, replicaIdx)[seqID]
  }

  function {:opaque} PreparesRcvdFrom(c:Constants, v:Variables, replicaIdx: HostId, seqID: Messages.SequenceID, sender: HostId) : Frame
    requires RVValid(c, v, replicaIdx)
  {
    PreparesRcvd(c, v, replicaIdx, seqID)[sender]
  }

  function CommitsRcvdMap(c:Constants, v:Variables, replicaIdx: HostId) : imap<Messages.SequenceID, Replica.CommitProofSet>
    requires RVValid(c, v, replicaIdx)
  {
    ReplicaVariables(c, v, replicaIdx).workingWindow.preparesRcvd
  }

  function {:opaque} CommitsRcvd(c:Constants, v:Variables, replicaIdx: HostId, seqID: Messages.SequenceID) : Replica.CommitProofSet
    requires RVValid(c, v, replicaIdx)
  {
    assert Library.TriggerKeyInFullImap(seqID, v.hosts[replicaIdx].replicaVariables.workingWindow.preparesRcvd);
    CommitsRcvdMap(c, v, replicaIdx)[seqID]
  }

  function {:opaque} CommitsRcvdFrom(c:Constants, v:Variables, replicaIdx: HostId, seqID: Messages.SequenceID, sender: HostId) : Frame
    requires RVValid(c, v, replicaIdx)
  {
    CommitsRcvd(c, v, replicaIdx, seqID)[sender]
  }

  function View(c:Constants, v:Variables, replicaIdx: HostId) : nat
    requires RVValid(c, v, replicaIdx)
  {
    ReplicaVariables(c, v, replicaIdx).view
  }

  // Here's a predicate that will be very useful in constructing invariant conjuncts.
  predicate RecordedPrePreparesRecvdCameFromNetwork(c:Constants, v:Variables) {
    && v.WF(c)
    && (forall replicaIdx, seqID | 
              && IsHonestReplica(c, replicaIdx)
              && PrepreparesRcvd(c, v, replicaIdx, seqID).Some?
                :: PrepreparesRcvd(c, v, replicaIdx, seqID).value in v.network.sentMsgs)
  }

  predicate RecordedPreparesRecvdCameFromNetwork(c:Constants, v:Variables, observer:HostId)
  {
    && v.WF(c)
    && IsHonestReplica(c, observer)
    && (forall sender, seqID | 
                sender in PreparesRcvd(c, v, observer, seqID)
                :: (&& var msg := PreparesRcvd(c, v, observer, seqID)[sender];
                    && msg in v.network.sentMsgs
                    && msg.sender == sender
                    && msg.payload.seqID == seqID)) // The key we stored matches what is in the msg
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
                           && commitMsg.payload.Commit? 
                           && IsHonestReplica(c, commitMsg.sender)
          :: QuorumOfPreparesInNetwork(c, v, commitMsg.payload.view, 
                                       commitMsg.payload.seqID, commitMsg.payload.clientOp) )
  }

  predicate HonestReplicasLockOnPrepareForGivenView(c: Constants, v:Variables)
  {
    && (forall msg1, msg2 | 
        && msg1 in v.network.sentMsgs 
        && msg2 in v.network.sentMsgs 
        && msg1.payload.Prepare?
        && msg2.payload.Prepare?
        && msg1.payload.view == msg2.payload.view
        && msg1.payload.seqID == msg2.payload.seqID
        && msg1.sender == msg2.sender
        && IsHonestReplica(c, msg1.sender)
        :: msg1 == msg2)
  }

  predicate /*{:opaque}*/ HonestReplicasLockOnCommitForGivenView(c:Constants, v:Variables) {
    && (forall msg1, msg2 | 
        && msg1 in v.network.sentMsgs 
        && msg2 in v.network.sentMsgs 
        && msg1.payload.Commit?
        && msg2.payload.Commit?
        && msg1.payload.view == msg2.payload.view
        && msg1.payload.seqID == msg2.payload.seqID
        && msg1.sender == msg2.sender
        && IsHonestReplica(c, msg1.sender)
        :: msg1 == msg2)
  }

  predicate /*{:opaque}*/ CommitMsgsFromHonestSendersAgree(c:Constants, v:Variables) {
    && (forall msg1, msg2 | 
        && msg1 in v.network.sentMsgs 
        && msg2 in v.network.sentMsgs 
        && msg1.payload.Commit?
        && msg2.payload.Commit?
        && msg1.payload.view == msg2.payload.view
        && msg1.payload.seqID == msg2.payload.seqID
        && IsHonestReplica(c, msg1.sender)
        && IsHonestReplica(c, msg2.sender)
        :: msg1.payload.clientOp == msg2.payload.clientOp)
  }

  predicate RecordedPreparesHaveValidSenderID(c:Constants, v:Variables) {
    && v.WF(c)
    && (forall replicaIdx, seqID, sender |
          && IsHonestReplica(c, replicaIdx)
          && var prepareMap := PreparesRcvdMap(c, v, replicaIdx);
          && seqID in prepareMap 
          && sender in prepareMap[seqID]
          :: && PreparesRcvdFrom(c, v, replicaIdx, seqID, sender).sender == sender
             && c.clusterConfig.IsReplica(sender)
        )
  }

  predicate RecordedPreparesClientOpsMatchPrePrepare(c:Constants, v:Variables) {
    && v.WF(c)
    && (forall replicaIdx, seqID, sender |
          && IsHonestReplica(c, replicaIdx)
          && var prepareMap := PreparesRcvdMap(c, v, replicaIdx);
          && seqID in prepareMap
          && sender in prepareMap[seqID]
          :: && PrepreparesRcvd(c, v, replicaIdx, seqID).Some?
             && PreparesRcvdFrom(c, v, replicaIdx, seqID, sender).payload.clientOp 
                == PrepreparesRcvd(c, v, replicaIdx, seqID).value.payload.clientOp)
  }

  predicate /*{:opaque}*/ RecordedCommitsClientOpsMatchPrePrepare(c:Constants, v:Variables) {
    && v.WF(c)
    && (forall replicaIdx, seqID, sender |
          && IsHonestReplica(c, replicaIdx)
          && var commitMap := CommitsRcvdMap(c, v, replicaIdx);
          && seqID in commitMap
          && sender in commitMap[seqID]
          :: && PrepreparesRcvd(c, v, replicaIdx, seqID).Some?
             && CommitsRcvdFrom(c, v, replicaIdx, seqID, sender).payload.clientOp 
                == PrepreparesRcvd(c, v, replicaIdx, seqID).value.payload.clientOp)
  }

  predicate /*{:opaque}*/ EveryCommitIsSupportedByRecordedPrepares(c:Constants, v:Variables) {
    && v.WF(c)
    && (forall commitMsg | && commitMsg in v.network.sentMsgs
                           && commitMsg.payload.Commit?
                           && IsHonestReplica(c, commitMsg.sender)
          :: && Replica.QuorumOfPrepares(c.hosts[commitMsg.sender].replicaConstants, 
                                         v.hosts[commitMsg.sender].replicaVariables, 
                                         commitMsg.payload.seqID))
  }

  predicate /*{:opaque}*/ EveryCommitClientOpMatchesRecordedPrePrepare(c:Constants, v:Variables) {
    && v.WF(c)
    && (forall commitMsg | && commitMsg in v.network.sentMsgs
                           && commitMsg.payload.Commit?
                           && IsHonestReplica(c, commitMsg.sender)
          :: && var recordedPrePrepare := PrepreparesRcvd(c, v, commitMsg.sender, commitMsg.payload.seqID);
             && recordedPrePrepare.Some?
             && commitMsg.payload.clientOp == recordedPrePrepare.value.payload.clientOp)
  }

  predicate RecordedPreparesMatchHostView(c:Constants, v:Variables) {
    && v.WF(c)
    && (forall observer, seqID, sender | 
                           && IsHonestReplica(c, observer)
                           && c.clusterConfig.IsReplica(sender)
                           && var replicaVars := v.hosts[observer].replicaVariables;
                           && seqID in PreparesRcvdMap(c, v, observer)
                           && sender in PreparesRcvd(c, v, observer, seqID)
                :: ReplicaVariables(c, v, observer).view == PreparesRcvdFrom(c, v, observer, seqID, sender).payload.view)
  }

  predicate SentPreparesMatchRecordedPrePrepareIfHostInSameView(c:Constants, v:Variables) {
    && v.WF(c)
    && (forall prepare | 
                && prepare in v.network.sentMsgs
                && prepare.payload.Prepare?
                && IsHonestReplica(c, prepare.sender)
                && prepare.payload.view == ReplicaVariables(c, v, prepare.sender).view
                  :: && PrepreparesRcvd(c, v, prepare.sender, prepare.payload.seqID).Some?
                     && PrepreparesRcvd(c, v, prepare.sender, prepare.payload.seqID).value.payload.clientOp
                        == prepare.payload.clientOp)
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
                                  clientOp:Messages.ClientOperation) : set<Network.Message<Messages.Message>> 
    requires v.WF(c)
  {
    set msg | && msg in v.network.sentMsgs 
              && msg.payload.Prepare?
              && msg.payload.view == view
              && msg.payload.seqID == seqID
              && msg.payload.clientOp == clientOp
              && msg.sender in getAllReplicas(c)
  }

  function sendersOf(msgs:set<Network.Message<Messages.Message>>) : set<HostIdentifiers.HostId> {
    set msg | msg in msgs :: msg.sender
  }

  predicate QuorumOfPreparesInNetwork(c:Constants, v:Variables, view:nat, seqID:Messages.SequenceID, 
                                      clientOp:Messages.ClientOperation) {
    && v.WF(c)
    && var prepares := sentPreparesForSeqID(c, v, view, seqID, clientOp);
    && |sendersOf(prepares)| >= c.clusterConfig.AgreementQuorum()
    //&& (forall prepare | prepare in prepares :: prepare.clientOp == clientOperation)
  }

  lemma WlogCommitAgreement(c: Constants, v:Variables, v':Variables, step:Step,
                            msg1:Network.Message<Messages.Message>, msg2:Network.Message<Messages.Message>)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    requires msg1 in v'.network.sentMsgs 
    requires msg2 in v'.network.sentMsgs 
    requires msg1.payload.Commit?
    requires msg2.payload.Commit?
    requires msg1.payload.view == msg2.payload.view
    requires msg1.payload.seqID == msg2.payload.seqID
    requires msg1 in v.network.sentMsgs
    requires msg2 !in v.network.sentMsgs
    requires IsHonestReplica(c, msg1.sender)
    requires IsHonestReplica(c, msg2.sender)
    ensures msg1.payload.clientOp == msg2.payload.clientOp
  {
    var prepares1 := sentPreparesForSeqID(c, v, msg1.payload.view, msg1.payload.seqID, msg1.payload.clientOp);
    var senders1 := sendersOf(prepares1);
    assert |senders1| >= c.clusterConfig.AgreementQuorum();

    var h_c := c.hosts[step.id].replicaConstants;
    var h_v := v.hosts[step.id].replicaVariables;
    var h_v' := v'.hosts[step.id].replicaVariables;
    var h_step :| Replica.NextStep(h_c, h_v, h_v', step.msgOps, h_step);

    var senders2 := h_v.workingWindow.preparesRcvd[h_step.seqID].Keys;
    assert |senders2| >= c.clusterConfig.AgreementQuorum();

    var equivocatingHonestSender := FindQuorumIntersection(c, senders1, senders2);
  }

  function GetKReplicas(c:Constants, k:nat) : (hosts:set<HostIdentifiers.HostId>)
    requires c.WF()
    requires k <= c.clusterConfig.N()
    ensures |hosts| == k
    ensures forall host :: host in hosts <==> 0 <= host < k
    ensures forall host | host in hosts :: c.clusterConfig.IsReplica(host)
  {
    if k == 0 then {}
    else GetKReplicas(c, k-1) + {k - 1}
  }

  function getAllReplicas(c: Constants) : (hostsSet:set<HostIdentifiers.HostId>)
    requires c.WF()
    ensures |hostsSet| == c.clusterConfig.N()
    ensures forall host :: host in hostsSet <==> c.clusterConfig.IsReplica(host)
  {
    GetKReplicas(c, c.clusterConfig.N())
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
    ////reveal_CommitMsgsFromHonestSendersAgree();
    forall msg1, msg2 | 
      && msg1 in v'.network.sentMsgs 
      && msg2 in v'.network.sentMsgs 
      && msg1.payload.Commit?
      && msg2.payload.Commit?
      && msg1.payload.view == msg2.payload.view
      && msg1.payload.seqID == msg2.payload.seqID
      && IsHonestReplica(c, msg1.sender)
      && IsHonestReplica(c, msg2.sender)
      ensures msg1.payload.clientOp == msg2.payload.clientOp {
        if(msg1 in v.network.sentMsgs && msg2 in v.network.sentMsgs) {
          assert msg1.payload.clientOp == msg2.payload.clientOp;
        } else if(msg1 !in v.network.sentMsgs && msg2 !in v.network.sentMsgs) {
          assert msg1.payload.clientOp == msg2.payload.clientOp;
        } else if(msg1 in v.network.sentMsgs && msg2 !in v.network.sentMsgs) {
          WlogCommitAgreement(c, v, v', step, msg1, msg2);
          assert msg1.payload.clientOp == msg2.payload.clientOp;
        } else if(msg1 !in v.network.sentMsgs && msg2 in v.network.sentMsgs) {
          WlogCommitAgreement(c, v, v', step, msg2, msg1);
          assert msg1.payload.clientOp == msg2.payload.clientOp;
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
    //reveal_RecordedCommitsClientOpsMatchPrePrepare();
    //reveal_EveryCommitIsSupportedByRecordedPrepares();
    //reveal_EveryCommitClientOpMatchesRecordedPrePrepare();
    //reveal_HonestReplicasLockOnCommitForGivenView();
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
                       && commitMsg.payload.Commit?
                       && IsHonestReplica(c, commitMsg.sender) ensures 
      QuorumOfPreparesInNetwork(c, v', commitMsg.payload.view, commitMsg.payload.seqID, commitMsg.payload.clientOp) {
      if(commitMsg in v.network.sentMsgs) { // the commitMsg has been sent in a previous step
        // In this case, the proof is trivial - we just need to "teach" Dafny about subset cardinality
        var senders := sendersOf(sentPreparesForSeqID(c, v, commitMsg.payload.view, 
                                                      commitMsg.payload.seqID, commitMsg.payload.clientOp));
        var senders' := sendersOf(sentPreparesForSeqID(c, v', commitMsg.payload.view,
                                                      commitMsg.payload.seqID, commitMsg.payload.clientOp));
        Library.SubsetCardinality(senders, senders');
      } else { // the commitMsg is being sent in the current step
        var prepares := sentPreparesForSeqID(c, v, commitMsg.payload.view,
                                             commitMsg.payload.seqID, commitMsg.payload.clientOp);
        var prepares' := sentPreparesForSeqID(c, v', commitMsg.payload.view, 
                                             commitMsg.payload.seqID, commitMsg.payload.clientOp);
        assert prepares == prepares'; // Trigger (hint) - sending a commitMsg does not affect the set of prepares
        
        // Prove that the prepares in the working window are a subset of the prepares in the network:
        var prepareSendersFromNetwork := sendersOf(prepares);
        var h_v := v.hosts[step.id];
        var prepareSendersInWorkingWindow := PreparesRcvd(c, v, step.id, commitMsg.payload.seqID).Keys;
        assert (forall sender | sender in prepareSendersInWorkingWindow 
                              :: PreparesRcvdFrom(c, v, step.id, commitMsg.payload.seqID, sender) in v.network.sentMsgs);
        assert (forall sender | sender in prepareSendersInWorkingWindow 
                              :: sender in prepareSendersFromNetwork); //Trigger for subset operator
        Library.SubsetCardinality(prepareSendersInWorkingWindow, prepareSendersFromNetwork);
      }
    }
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
      //reveal_RecordedCommitsClientOpsMatchPrePrepare();
      //reveal_EveryCommitIsSupportedByRecordedPrepares();
      //reveal_EveryCommitClientOpMatchesRecordedPrePrepare();
      //reveal_HonestReplicasLockOnCommitForGivenView();
      //reveal_CommitMsgsFromHonestSendersAgree();
      assert Inv(c, v);
    }
    if Inv(c, v) && Next(c, v, v') {
      InvariantNext(c, v, v');
    }
  }
}
