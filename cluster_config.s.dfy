module ClusterConfig {

  datatype Constants = Constants(
    maxByzantineFaultyReplicas:nat
  ) {

    predicate WF()
    {
      maxByzantineFaultyReplicas > 0 // Require non-trivial BFT system
    }

    function F() : nat
      requires WF()
    {
      maxByzantineFaultyReplicas
    }

    function ByzantineSafeQuorum() : nat
      requires WF()
    {
      F() + 1
    }

    function N() : nat  // BFT Cluster Size
      requires WF()
    {
      3 * F() + 1
    }

    function AgreementQuorum() : nat
      requires WF()
    {
      2 * F() + 1
    }
  }
}