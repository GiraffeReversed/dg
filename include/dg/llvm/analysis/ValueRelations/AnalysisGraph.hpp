#ifndef _DG_LLVM_ANALYSIS_GRAPH_HPP_
#define _DG_LLVM_ANALYSIS_GRAPH_HPP_

#include <llvm/IR/Module.h>

#include "GraphBuilder.hpp"
#include "GraphAnalyzer.hpp"

#ifndef NDEBUG
#include "getValName.h"
#endif

namespace dg {
namespace analysis {
namespace vr {

class AnalysisGraph {

    const llvm::Module& module;

    // VRLocation corresponding to the state of the program BEFORE executing the instruction
    std::map<const llvm::Instruction *, VRLocation *> locationMapping;
    std::map<const llvm::BasicBlock *, std::unique_ptr<VRBBlock>> blockMapping;

public:
    AnalysisGraph(const llvm::Module& M) : module(M) {
        GraphBuilder gb(module, locationMapping, blockMapping);
        gb.build();
        
        GraphAnalyzer ga(module, locationMapping, blockMapping);
        ga.analyze();
    }

    const std::map<const llvm::BasicBlock *, std::unique_ptr<VRBBlock>>& getBlockMapping() const {
        return blockMapping;
    }
};

} // namespace vr
} // namespace analysis
} // namespace dg

#endif // _DG_LLVM_ANALYSIS_GRAPH_HPP_
