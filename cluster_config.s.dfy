module ClusterConfig {

  datatype Constants = Constants(
    clusterSize:nat
  ) {
    predicate WF() {
      && clusterSize >= 4
    }

    function F() : nat // Max faulty tolerated
      requires WF()
    {
      (clusterSize - 1) / 3
    }

    function AgreementQuorum() : nat 
      requires WF()
    {
      2 * F() + 1
    }
  }
}