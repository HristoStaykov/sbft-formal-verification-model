module ClusterConfig {

  datatype Constants = Constants(
    maxByzantineFaultyReplicas:nat,
    numClients:nat
  ) {

    predicate WF()
    {
      && maxByzantineFaultyReplicas > 0 // Require non-trivial BFT system
      && numClients > 0
    }

    function ClusterSize() : nat
      requires WF()
    {
      N() + numClients
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

    function N() : nat  // BFT Replica Size
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