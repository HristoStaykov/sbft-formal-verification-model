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
              //&& ValidHostId(replicaIdx)
              && c.IsReplica(replicaIdx)
              && assert Library.TriggerKeyInFullImap(seqID, v.hosts[replicaIdx].replicaVariables.workingWindow.prePreparesRcvd);
                v.hosts[replicaIdx].replicaVariables.workingWindow.prePreparesRcvd[seqID].Some? 
                :: v.hosts[replicaIdx].replicaVariables.workingWindow.prePreparesRcvd[seqID].value in v.network.sentMsgs)
  }

  predicate RecordedPreparesRecvdCameFromNetwork(c:Constants, v:Variables, observer:HostId)
  {
    && v.WF(c)
    //&& ValidHostId(observer)
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
            //&& ValidHostId(observer)
            && c.IsReplica(observer)
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
        && msg1.Commit?
        && msg2.Commit?
        && msg1.seqID == msg2.seqID
        && msg1.sender == msg2.sender
        :: msg1 == msg2)
  }


  predicate Inv(c: Constants, v:Variables) {
    && RecordedPrePreparesRecvdCameFromNetwork(c, v)
    && RecordedPreparesInAllHostsRecvdCameFromNetwork(c, v)
    && EveryCommitMsgIsSupportedByAQuorumOfPrepares(c, v)
    //&& HonestReplicasLockOnCommitForGivenView(c, v)
  }

  function getAllPreparesForSeqID(c: Constants, v:Variables, seqID:Messages.SequenceID) : set<Messages.Message> 
  {
    set msg | && msg in v.network.sentMsgs 
              && msg.Prepare?
              && msg.seqID == seqID
  }

  function setOfSendersForMsgs(msgs:set<Messages.Message>) : set<HostIdentifiers.HostId> {
    //set sender | sender in AllHosts() && (exists msg | msg in msgs :: msg.sender == sender)
    set msg | msg in msgs :: msg.sender
  }

  predicate QuorumOfPreparesInNetwork(c:Constants, v:Variables, seqID:Messages.SequenceID) {
    && v.WF(c)
    && var prepares := getAllPreparesForSeqID(c, v, seqID);
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

  lemma ProofEveryCommitMsgIsSupportedByAQuorumOfPrepares(c: Constants, v:Variables, v':Variables, step:Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    ensures EveryCommitMsgIsSupportedByAQuorumOfPrepares(c, v')
  {
    // A proof of EveryCommitMsgIsSupportedByAQuorumOfPrepares
    forall commitMsg | commitMsg in v'.network.sentMsgs && commitMsg.Commit? ensures 
      QuorumOfPreparesInNetwork(c, v', commitMsg.seqID) {
      if(commitMsg in v.network.sentMsgs) {
        // Adding some basic facts to help Dafny - otherwise this is trivial
        var senders := setOfSendersForMsgs(getAllPreparesForSeqID(c, v, commitMsg.seqID));
        var senders' := setOfSendersForMsgs(getAllPreparesForSeqID(c, v', commitMsg.seqID));
        Library.SubsetCardinality(senders, senders');
      } else {
        var prepares := getAllPreparesForSeqID(c, v, commitMsg.seqID);
        var prepares' := getAllPreparesForSeqID(c, v', commitMsg.seqID);
        assert prepares == prepares'; // Trigger (hint)
        
        var prepareSendersFromNetwork := setOfSendersForMsgs(prepares);
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

  lemma InvariantNext(c: Constants, v:Variables, v':Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
  {
    var step :| NextStep(c, v, v', step);

    if (c.IsReplica(step.id))
    {
      var h_c := c.hosts[step.id].replicaConstants;
      var h_v := v.hosts[step.id].replicaVariables;
      var h_v' := v'.hosts[step.id].replicaVariables;
      var h_step :| Replica.NextStep(h_c, h_v, h_v', step.msgOps, h_step);
      QuorumOfPreparesInNetworkMonotonic(c, v, v', step, h_step);
      match h_step
        case SendPrePrepareStep() => { assert Inv(c, v'); }
        case RecvPrePrepareStep => { assert Inv(c, v'); }
        case SendPrepareStep(seqID) => { assert Inv(c, v'); }
        case RecvPrepareStep => { assert Inv(c, v'); }
        case SendCommitStep(seqID) => {
          ProofEveryCommitMsgIsSupportedByAQuorumOfPrepares(c, v, v', step);
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
        case SendClientOperationStep() => { 
          ProofEveryCommitMsgIsSupportedByAQuorumOfPrepares(c, v, v', step);
          assert Inv(c, v');  
        }

    } else {
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
