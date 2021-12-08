#include "packager/rbi_gen.h"
#include "absl/synchronization/blocking_counter.h"
#include "common/FileOps.h"
#include "common/concurrency/ConcurrentQueue.h"
#include "core/GlobalState.h"
#include "main/pipeline/pipeline.h"
#include "packager/packager.h"

using namespace std;
namespace sorbet::packager {
namespace {

class Indent;

class Output final {
private:
    friend class Indent;

    fmt::memory_buffer out;
    int indent = 0;
    std::string tabStr = "";

    void resetTabString() {
        tabStr = string(indent * 2, ' ');
    }

    void tab() {
        indent++;
        resetTabString();
    }

    void untab() {
        indent--;
        resetTabString();
    }

public:
    template <typename... T> void println(fmt::format_string<T...> fmt, T &&...args) {
        fmt::format_to(std::back_inserter(out), tabStr);
        fmt::format_to(std::back_inserter(out), fmt, args...);
        fmt::format_to(std::back_inserter(out), "\n");
    }

    void println(string_view arg) {
        fmt::format_to(std::back_inserter(out), tabStr);
        std::copy(arg.begin(), arg.end(), std::back_inserter(out));
        fmt::format_to(std::back_inserter(out), "\n");
    }

    string toString() {
        return fmt::to_string(out);
    }
};

class Indent {
private:
    Output &out;

public:
    Indent(Output &out) : out(out) {
        out.tab();
    }
    ~Indent() {
        out.untab();
    }
};

// TODO: copied from lsp_helpers.cc. Move to a common utils package.
// TODO: Respect indentation.
core::TypePtr getResultType(const core::GlobalState &gs, const core::TypePtr &type, core::SymbolRef inWhat,
                            core::TypePtr receiver, const core::TypeConstraint *constr) {
    auto resultType = type;
    if (core::is_proxy_type(receiver)) {
        receiver = receiver.underlying(gs);
    }
    if (core::isa_type<core::AppliedType>(receiver)) {
        auto &applied = core::cast_type_nonnull<core::AppliedType>(receiver);
        /* instantiate generic classes */
        resultType =
            core::Types::resultTypeAsSeenFrom(gs, resultType, inWhat.enclosingClass(gs), applied.klass, applied.targs);
    }
    if (!resultType) {
        resultType = core::Types::untypedUntracked();
    }
    if (receiver) {
        resultType = core::Types::replaceSelfType(gs, resultType, receiver); // instantiate self types
    }
    if (constr) {
        resultType = core::Types::instantiate(gs, resultType, *constr); // instantiate generic methods
    }
    return resultType;
}

// iff a sig has more than this many parameters, then print it as a multi-line sig.
constexpr int MAX_PRETTY_SIG_ARGS = 4;
// iff a `def` would be this wide or wider, expand it to be a multi-line def.
constexpr int MAX_PRETTY_WIDTH = 80;

string prettySigForMethod(const core::GlobalState &gs, core::MethodRef method, const core::TypePtr &receiver,
                          core::TypePtr retType, const core::TypeConstraint *constraint) {
    ENFORCE(method.exists());
    ENFORCE(method.data(gs)->dealias(gs) == method);
    // handle this case anyways so that we don't crash in prod when this method is mis-used
    if (!method.exists()) {
        return "";
    }

    if (!retType) {
        retType = getResultType(gs, method.data(gs)->resultType, method, receiver, constraint);
    }
    string methodReturnType =
        (retType == core::Types::void_()) ? "void" : absl::StrCat("returns(", retType.show(gs), ")");
    vector<string> typeAndArgNames;
    vector<string> typeArguments;

    vector<string> flags;
    auto sym = method.data(gs);
    string sigCall = "sig";
    if (sym->isFinalMethod()) {
        sigCall = "sig(:final)";
    }
    if (sym->isAbstract()) {
        flags.emplace_back("abstract");
    }
    if (sym->isOverridable()) {
        flags.emplace_back("overridable");
    }
    if (sym->isOverride()) {
        flags.emplace_back("override");
    }
    for (auto targ : method.data(gs)->typeArguments()) {
        auto ta = targ.asTypeArgumentRef();
        typeArguments.emplace_back(absl::StrCat(":", ta.data(gs)->name.show(gs)));
    }
    for (auto &argSym : method.data(gs)->arguments()) {
        // Don't display synthetic arguments (like blk).
        if (!argSym.isSyntheticBlockArgument()) {
            typeAndArgNames.emplace_back(absl::StrCat(
                argSym.argumentName(gs), ": ", getResultType(gs, argSym.type, method, receiver, constraint).show(gs)));
        }
    }

    string flagString = "";
    if (!flags.empty()) {
        flagString = fmt::format("{}.", fmt::join(flags, "."));
    }
    string typeParamsString = "";
    if (!typeArguments.empty()) {
        typeParamsString = fmt::format("type_parameters({}).", fmt::join(typeArguments, ", "));
    }
    string paramsString = "";
    if (!typeAndArgNames.empty()) {
        paramsString = fmt::format("params({}).", fmt::join(typeAndArgNames, ", "));
    }

    auto oneline =
        fmt::format("{} {{{}{}{}{}}}", sigCall, flagString, typeParamsString, paramsString, methodReturnType);
    if (oneline.size() <= MAX_PRETTY_WIDTH && typeAndArgNames.size() <= MAX_PRETTY_SIG_ARGS) {
        return oneline;
    }

    if (!flags.empty()) {
        flagString = fmt::format("{}\n  .", fmt::join(flags, "\n  ."));
    }
    if (!typeArguments.empty()) {
        typeParamsString = fmt::format("type_parameters({})\n  .", fmt::join(typeArguments, ", "));
    }
    if (!typeAndArgNames.empty()) {
        paramsString = fmt::format("params(\n    {}\n  )\n  .", fmt::join(typeAndArgNames, ",\n    "));
    }
    return fmt::format("{} do\n  {}{}{}{}\nend", sigCall, flagString, typeParamsString, paramsString, methodReturnType);
}

string prettyDefForMethod(const core::GlobalState &gs, core::MethodRef method) {
    ENFORCE(method.exists());
    // handle this case anyways so that we don't crash in prod when this method is mis-used
    if (!method.exists()) {
        return "";
    }
    auto methodData = method.data(gs);

    string visibility = "";
    if (methodData->isMethodPrivate()) {
        visibility = "private ";
    } else if (methodData->isMethodProtected()) {
        visibility = "protected ";
    }

    auto methodNameRef = methodData->name;
    ENFORCE(methodNameRef.exists());
    string methodName = "???";
    if (methodNameRef.exists()) {
        methodName = methodNameRef.toString(gs);
    }
    string methodNamePrefix = "";
    if (methodData->owner.exists() && methodData->owner.isClassOrModule() &&
        methodData->owner.asClassOrModuleRef().data(gs)->attachedClass(gs).exists()) {
        methodNamePrefix = "self.";
    }
    vector<string> prettyArgs;
    const auto &arguments = methodData->dealias(gs).asMethodRef().data(gs)->arguments();
    ENFORCE(!arguments.empty(), "Should have at least a block arg");
    for (const auto &argSym : arguments) {
        // Don't display synthetic arguments (like blk).
        if (argSym.isSyntheticBlockArgument()) {
            continue;
        }
        string prefix = "";
        string suffix = "";
        if (argSym.flags.isRepeated) {
            if (argSym.flags.isKeyword) {
                prefix = "**"; // variadic keyword args
            } else {
                prefix = "*"; // rest args
            }
        } else if (argSym.flags.isKeyword) {
            if (argSym.flags.isDefault) {
                suffix = ": …"; // optional keyword (has a default value)
            } else {
                suffix = ":"; // required keyword
            }
        } else if (argSym.flags.isBlock) {
            prefix = "&";
        } else if (argSym.flags.isDefault) {
            suffix = "=…";
        }
        prettyArgs.emplace_back(fmt::format("{}{}{}", prefix, argSym.argumentName(gs), suffix));
    }

    string argListPrefix = "";
    string argListSeparator = "";
    string argListSuffix = "";
    if (prettyArgs.size() > 0) {
        argListPrefix = "(";
        argListSeparator = ", ";
        argListSuffix = ")";
    }

    auto result = fmt::format("{}def {}{}{}{}{}", visibility, methodNamePrefix, methodName, argListPrefix,
                              fmt::join(prettyArgs, argListSeparator), argListSuffix);
    if (prettyArgs.size() > 0 && result.length() >= MAX_PRETTY_WIDTH) {
        argListPrefix = "(\n  ";
        argListSeparator = ",\n  ";
        argListSuffix = "\n)";
        result = fmt::format("{}def {}{}{}{}{}", visibility, methodNamePrefix, methodName, argListPrefix,
                             fmt::join(prettyArgs, argListSeparator), argListSuffix);
    }
    return result;
}

core::ClassOrModuleRef lookupFQN(const core::GlobalState &gs, const vector<core::NameRef> &fqn) {
    core::ClassOrModuleRef scope = core::Symbols::root();
    for (auto name : fqn) {
        auto result = scope.data(gs)->findMember(gs, name);
        if (!result.exists() || !result.isClassOrModule()) {
            return core::Symbols::noClassOrModule();
        }
        scope = result.asClassOrModuleRef();
    }
    return scope;
}

class RBIExporter final {
private:
    const core::GlobalState &gs;
    const core::packages::PackageInfo &pkg;
    const core::ClassOrModuleRef pkgNamespace;
    const UnorderedSet<core::ClassOrModuleRef> &pkgNamespaces;
    Output out;

    // copied from variance.cc
    string showVariance(core::TypeMemberRef tm) {
        if (tm.data(gs)->isFixed()) {
            auto &lambdaParam = core::cast_type_nonnull<core::LambdaParam>(tm.data(gs)->resultType);
            return absl::StrCat("fixed: ", lambdaParam.upperBound.toString(gs));
        }

        switch (tm.data(gs)->variance()) {
            case core::Variance::CoVariant:
                return ":out";
            case core::Variance::Invariant:
                return ":invariant";
            case core::Variance::ContraVariant:
                return ":in";
        }
    }

    string typeDeclaration(const core::TypePtr &type) {
        if (core::isa_type<core::AliasType>(type)) {
            auto alias = core::cast_type_nonnull<core::AliasType>(type);
            return alias.symbol.show(gs);
        } else {
            return absl::StrCat("T.let(T.unsafe(nil), ", type.toString(gs), ")");
        }
    }

    bool shouldSkipMember(core::NameRef name) {
        if (name.kind() == core::NameKind::UNIQUE) {
            return true;
        }

        return name == core::Names::singleton() || name == core::Names::Constants::AttachedClass() ||
               name == core::Names::attached();
    }

    void emit(core::ClassOrModuleRef klass) {
        if (pkgNamespaces.contains(klass) && klass != pkgNamespace) {
            // We don't emit class definitions for items defined in other packages.
            return;
        }

        cerr << "Emitting " << klass.show(gs) << "\n";
        vector<core::ClassOrModuleRef> klassesToEmit;
        // Class definition line
        auto defType = klass.data(gs)->isClassOrModuleClass() ? "class" : "module";
        auto fullName = klass.show(gs);
        string superClassString;
        if (klass.data(gs)->superClass().exists()) {
            superClassString = absl::StrCat(" < ", klass.data(gs)->superClass().show(gs));
        }
        out.println("{} {}{}", defType, fullName, superClassString);

        {
            Indent indent(out);

            // Mixins (include/extend)
            for (auto mixin : klass.data(gs)->mixins()) {
                auto isSingleton = mixin.data(gs)->isSingletonClass(gs);
                auto keyword = isSingleton ? "extend"sv : "include"sv;
                out.println("{} {}", keyword, mixin.show(gs));
            }

            // Members
            core::MethodRef initializeMethod;
            vector<core::FieldRef> pendingFields;
            for (auto &[name, member] : klass.data(gs)->membersStableOrderSlow(gs)) {
                if (shouldSkipMember(name)) {
                    continue;
                }

                switch (member.kind()) {
                    case core::SymbolRef::Kind::ClassOrModule: {
                        // Emit later.
                        cerr << name.show(gs) << "\n";
                        klassesToEmit.emplace_back(member.asClassOrModuleRef());
                        break;
                    }
                    case core::SymbolRef::Kind::TypeMember: {
                        emit(member.asTypeMemberRef());
                        break;
                    }
                    case core::SymbolRef::Kind::TypeArgument: {
                        ENFORCE(false, "classes should never contain type arguments");
                        break;
                    }
                    case core::SymbolRef::Kind::Method: {
                        if (name == core::Names::initialize()) {
                            // Defer outputting until we gather fields.
                            initializeMethod = member.asMethodRef();
                        } else {
                            emit(member.asMethodRef());
                        }
                        break;
                    }
                    case core::SymbolRef::Kind::FieldOrStaticField: {
                        auto field = member.asFieldRef();
                        if (field.data(gs)->isField()) {
                            pendingFields.emplace_back(field);
                        } else {
                            emit(field);
                        }
                        break;
                    }
                }
            }

            maybeEmitInitialized(initializeMethod, pendingFields);

            auto singleton = klass.data(gs)->lookupSingletonClass(gs);
            if (singleton.exists()) {
                for (auto &[name, member] : singleton.data(gs)->membersStableOrderSlow(gs)) {
                    if (shouldSkipMember(name)) {
                        continue;
                    }

                    switch (member.kind()) {
                        case core::SymbolRef::Kind::ClassOrModule: {
                            cerr << name.show(gs) << "\n";
                            klassesToEmit.emplace_back(member.asClassOrModuleRef());
                            break;
                        }
                        case core::SymbolRef::Kind::TypeMember: {
                            emit(member.asTypeMemberRef());
                            break;
                        }
                        case core::SymbolRef::Kind::TypeArgument: {
                            ENFORCE(false, "classes should never contain type arguments");
                            break;
                        }
                        case core::SymbolRef::Kind::Method: {
                            emit(member.asMethodRef());
                            break;
                        }
                        case core::SymbolRef::Kind::FieldOrStaticField: {
                            auto field = member.asFieldRef();
                            if (field.data(gs)->isField()) {
                                pendingFields.emplace_back(field);
                            } else {
                                emit(field);
                            }
                            break;
                        }
                    }
                }
            }
        }

        out.println("end");

        for (auto klassToEmit : klassesToEmit) {
            emit(klassToEmit);
        }
    }

    void emit(core::MethodRef method) {
        if (method.data(gs)->name == core::Names::staticInit()) {
            return;
        }

        if (method.data(gs)->hasSig()) {
            out.println(prettySigForMethod(gs, method, nullptr, method.data(gs)->resultType, nullptr));
        }
        out.println(prettyDefForMethod(gs, method) + "; end");
    }

    void maybeEmitInitialized(core::MethodRef method, const std::vector<core::FieldRef> &fields) {
        if (fields.empty() && !method.exists()) {
            return;
        }
        string methodDef;
        if (method.exists()) {
            if (method.data(gs)->hasSig()) {
                out.println(prettySigForMethod(gs, method, nullptr, method.data(gs)->resultType, nullptr));
            }
            methodDef = prettyDefForMethod(gs, method);
        } else {
            out.println("sig {void}");
            methodDef = "def initialize";
        }

        if (fields.empty()) {
            out.println(methodDef + "; end");
        } else {
            out.println(methodDef);
            {
                Indent indent(out);
                for (auto field : fields) {
                    emit(field);
                }
            }
            out.println("end");
        }
    }
    void emit(core::FieldRef field) {
        if (field.data(gs)->isStaticField()) {
            // Static field
            const auto &resultType = field.data(gs)->resultType;
            out.println("{} = {}", field.data(gs)->name.show(gs), typeDeclaration(resultType));
        } else {
            out.println("{} = {}", field.data(gs)->name.show(gs), typeDeclaration(field.data(gs)->resultType));
        }
    }

    void emit(core::TypeMemberRef tm) {
        if (tm.data(gs)->name == core::Names::Constants::AttachedClass()) {
            return;
        }
        out.println("{} = type_member({})", tm.data(gs)->name.show(gs), showVariance(tm));
    }

public:
    RBIExporter(const core::GlobalState &gs, const core::packages::PackageInfo &pkg,
                const UnorderedSet<core::ClassOrModuleRef> &pkgNamespaces)
        : gs(gs), pkg(pkg), pkgNamespace(lookupFQN(gs, pkg.fullName())), pkgNamespaces(pkgNamespaces) {}

    void emit() {}

    string toString() {
        return out.toString();
    }
};
} // namespace

void RBIGenerator::run(core::GlobalState &gs, vector<ast::ParsedFile> packageFiles, string outputDir,
                       WorkerPool &workers) {
    absl::BlockingCounter threadBarrier(std::max(workers.size(), 1));
    // Populate package database.
    Packager::findPackages(gs, workers, move(packageFiles));

    const auto &packageDB = gs.packageDB();

    auto &packages = packageDB.packages();
    auto inputq = make_shared<ConcurrentBoundedQueue<core::NameRef>>(packages.size());

    UnorderedSet<core::ClassOrModuleRef> packageNamespaces;
    for (auto package : packages) {
        auto &pkg = gs.packageDB().getPackageInfo(package);
        auto packageNamespace = lookupFQN(gs, pkg.fullName());
        ENFORCE(packageNamespace.exists());
        packageNamespaces.insert(packageNamespace);
        inputq->push(move(package), 1);
    }

    const core::GlobalState &rogs = gs;
    workers.multiplexJob("RBIGenerator", [inputq, outputDir, &threadBarrier, &rogs, &packageNamespaces]() {
        core::NameRef job;
        for (auto result = inputq->try_pop(job); !result.done(); result = inputq->try_pop(job)) {
            auto &pkg = rogs.packageDB().getPackageInfo(job);
            ENFORCE(pkg.exists());
            auto outputFile = absl::StrCat(outputDir, "/", pkg.mangledName().show(rogs), ".rbi");
            RBIExporter exporter(rogs, pkg, packageNamespaces);

            // TODO: Test package RBIs.
            FileOps::write(outputFile, exporter.toString());
        }
        threadBarrier.DecrementCount();
    });
    // Wait for threads to complete destructing the trees.
    threadBarrier.Wait();
}
} // namespace sorbet::packager