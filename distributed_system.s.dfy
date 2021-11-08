//#title DistributedSystem
//#desc DO NOT EDIT THIS FILE! It's a trusted file that specifies how hosts interact
//#desc with one another over the network.

include "replica.i.dfy"
include "cluster_config.s.dfy"
include "messages.dfy"


// Before we get here, caller must define a type Message that we'll
// use to instantiate network.s.dfy.

module DistributedSystem {
  import opened HostIdentifiers
  import opened Messages
  import ClusterConfig
  import Replica
  import Network

  datatype Constants = Constants(
    replicas:seq<Replica.Constants>,
    network:Network.Constants,
    clusterConfig:ClusterConfig.Constants) {
    predicate WF() {
      && clusterConfig.WF()
      && |replicas| == NumHosts()
      && clusterConfig.N() == NumHosts()
      && (forall id | ValidHostId(id) :: replicas[id].Configure(id, clusterConfig))  // every host knows its id (and ids are unique)
    }
  }

  datatype Variables = Variables(
    replicas:seq<Replica.Variables>,
    network:Network.Variables<Message>) {
    predicate WF(c: Constants) {
      && c.WF()
      && |replicas| == |c.replicas|
    }
  }

  predicate Init(c:Constants, v:Variables) {
    && v.WF(c)
    && (forall id | ValidHostId(id) :: Replica.Init(c.replicas[id], v.replicas[id]))
    && Network.Init(c.network, v.network)
  }

  // JayNF
  datatype Step = Step(id:HostId, msgOps: Network.MessageOps<Message>)

  predicate NextStep(c:Constants, v:Variables, v':Variables, step: Step) {
    && v.WF(c)
    && v'.WF(c)
    && ValidHostId(step.id)
    && Replica.Next(c.replicas[step.id], v.replicas[step.id], v'.replicas[step.id], step.msgOps)
    && (forall other | ValidHostId(other) && other != step.id :: v'.replicas[other] == v.replicas[other])
    && Network.Next(c.network, v.network, v'.network, step.msgOps)
  }

  predicate Next(c:Constants, v:Variables, v':Variables) {
    exists step :: NextStep(c, v, v', step)
  }
}
