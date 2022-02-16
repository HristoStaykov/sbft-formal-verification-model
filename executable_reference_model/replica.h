#pragma once
#include "cluster_config.h"
#include "messages.h"

namespace Replica {
using namespace Messages;

struct Constants {
  HostId myId;
  ClusterConfig::Constants clusterConfig;
  Constants(HostId id, ClusterConfig::Constants c) : myId(id), clusterConfig(c) {}
  bool WF() {
    return clusterConfig.WF()
        && clusterConfig.IsReplica(myId);
  }
  void Configure(HostId id, ClusterConfig::Constants clusterConf) {
    myId = id;
    clusterConfig = clusterConf;
  }
};

using PrepareProofSet = map<HostId, NetworkMessage>;
bool PrepareProofSetWF(Constants c, PrepareProofSet ps) {
  bool result = true;
  for(const auto& x : ps) {
    const auto pval = std::get_if<Prepare>(&x.second.payload);
    if(!pval || !c.clusterConfig.IsReplica(x.second.sender)) {
      result = false;
    }
  }
  return result;
}

using CommitProofSet = map<HostId, NetworkMessage>;
bool CommitProofSetWF(Constants c, PrepareProofSet cs) {
  bool result = true;
  for(const auto& x : cs) {
    const auto pval = std::get_if<Commit>(&x.second.payload);
    if(!pval || !c.clusterConfig.IsReplica(x.second.sender)) {
      result = false;
    }
  }
  return result;
}

using PrePreparesRcvd = map<SequenceID, NetworkMessage>;
bool PrePreparesRcvdWF(PrePreparesRcvd prePreparesRcvd) {
  bool result = true;
  for(const auto& x : prePreparesRcvd) {
    const auto pval = std::get_if<PrePrepare>(&x.second.payload);
    if(!pval) {
      result = false;
    }
  }
  return result;
}

struct WorkingWindow {
  map<SequenceID, OperationWrapper> committedClientOperations;
  PrePreparesRcvd prePreparesRcvd;
  map<SequenceID, PrepareProofSet> preparesRcvd;
  map<SequenceID, CommitProofSet> commitsRcvd;
  bool WF(Constants c) {
    bool result = true;
    for(const auto& element : preparesRcvd) {
      if(!PrepareProofSetWF(c, preparesRcvd[element.first])) {
        result = false;
        break;
      }
    }
    for(const auto& element : commitsRcvd) {
      if(!CommitProofSetWF(c, commitsRcvd[element.first])) {
        result = false;
        break;
      }
    }
    return result;
  }
};

struct Variables {
  ViewNum view;
  WorkingWindow workingWindow;
  bool WF(Constants c) {
    return c.WF() && workingWindow.WF(c);
  }
};

nat PrimaryForView(Constants c, ViewNum view)
{
  if(!c.WF()) throw std::runtime_error(__PRETTY_FUNCTION__);
  return view % c.clusterConfig.N();
}

nat CurrentPrimary(Constants c, Variables v)
{
  if(!v.WF(c)) throw std::runtime_error(__PRETTY_FUNCTION__);
  return PrimaryForView(c, v.view);
}

bool ViewIsActive(Constants c, Variables v) {
  return true;
}

bool IsValidPrePrepareToAccept(Constants c, Variables v, NetworkMessage msg)
{
  bool result = v.WF(c)
       && std::get_if<PrePrepare>(&msg.payload)
       && c.clusterConfig.IsReplica(msg.sender)
       && ViewIsActive(c, v)
       && std::get_if<PrePrepare>(&msg.payload)->view == v.view
       && msg.sender == CurrentPrimary(c, v)
       && v.workingWindow.prePreparesRcvd.find(std::get_if<PrePrepare>(&msg.payload)->seqID) 
          == v.workingWindow.prePreparesRcvd.end();
      // TODO: revisit View Change is introduced.

  return result;
}

bool RecvPrePrepare(Constants c, const Variables& v, Variables& vNext, const NetworkMessage& msgRecv, NetworkMessage& msgSend) {
  if(IsValidPrePrepareToAccept(c, v, msgRecv)) {
    vNext = v;
    vNext.workingWindow.prePreparesRcvd[std::get_if<PrePrepare>(&msgRecv.payload)->seqID] = msgRecv;
    return true;
  }
  return false;
}

}