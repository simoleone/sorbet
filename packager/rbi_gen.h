#ifndef SORBET_PACKAGER_RBI_GEN_H
#define SORBET_PACKAGER_RBI_GEN_H
#include "ast/ast.h"
#include "core/packages/PackageInfo.h"

namespace sorbet::packager {
/**
 * Generates an RBI file for the given package's exports.
 */
class RBIGenerator final {
public:
    static void run(core::GlobalState &gs, std::vector<ast::ParsedFile> packageFiles, std::string outputDir,
                    WorkerPool &workers);
};
} // namespace sorbet::packager

#endif // SORBET_PACKAGER_RBI_GEN_H
