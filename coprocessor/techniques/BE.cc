/***********************************************************************[BE.cc]
Copyright (c) 2021, Anton Reinhard, LGPL v2, see LICENSE
**************************************************************************************************/

#include "coprocessor/techniques/BE.h"
#include "coprocessor/CoprocessorTypes.h"
#include "coprocessor/ScopedDecisionLevel.h"
#include "coprocessor/techniques/BackboneSimplification.h"
#include "coprocessor/techniques/Probing.h"
#include "coprocessor/techniques/Propagation.h"
#include "riss/core/SolverTypes.h"

#ifdef CADICAL
#include <cadical.hpp>
#endif

#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <map>

using namespace Riss;

namespace {
    inline std::string groupingToString(Coprocessor::GROUPED group) {
        switch (group) {
        case Coprocessor::GROUPED::NOT:
            return "none";
        case Coprocessor::GROUPED::CONJUNCTIVE:
            return "conjunction";
        case Coprocessor::GROUPED::DISJUNCTIVE:
            return "disjunction";
        default:
            return "unknown";
        }
    }
}

namespace Coprocessor {

    BE::BE(CP3Config& _config, ClauseAllocator& _ca, ThreadController& _controller, CoprocessorData& _data, Propagation& _propagation,
           Probing& _probing, BackboneSimplification& _backboneSimpl, Solver& _solver)
        : Technique(_config, _ca, _controller)
        , data(_data)
        , propagation(_propagation)
        , probing(_probing)
        , backboneSimpl(_backboneSimpl)
        , solver(_solver)
        , nVar(solver.nVars())
        , maxRes(_config.opt_be_maxres)
        , conflictBudget(_config.opt_be_nconf)
        , grouped(static_cast<GROUPED>((int)_config.opt_be_grouping))
        , groupSize(_config.opt_be_ngrouping)
        , varUsed(solver.nVars(), false)
        , nDeletedVars(0)
        , copyTime(0)
        , bipartitionTime(0)
        , eliminationTime(0)
        , eliminationTime2(0)
        , occurrenceSimplTime(0)
        , solverTime(0)
        , subsumptionTime(0)
        , getResTime(0)
        , nSolverCalls(0)
        , eliminatedVars(0)
        , nTopLevelIterations(0)
        , nSubsumption(0)
        , nGetRes(0)
        , nOccurrencesRemoved(0)
        , dirtyCache(false) {
    }

    void BE::giveMoreSteps() {
    }

    void BE::destroy() {
#ifndef CADICAL
        delete solverconfig;
        delete cp3config;
#endif
        delete ownSolver;        
    }

    void BE::printStatistics(std::ostream& stream) {
        stream << "c [STAT] BE solver signature: " << solverSignature << "\n";
        stream << "c [STAT] BE maxres: " << maxRes << "\n";
        stream << "c [STAT] BE nConf: " << conflictBudget << "\n";
        stream << "c [STAT] BE deleted variables: " << nDeletedVars << "\n";
        stream << "c [STAT] BE bipartitionTime: " << bipartitionTime << "\n";
        stream << "c [STAT] BE eliminationTime: " << eliminationTime << "\n";
        stream << "c [STAT] BE occurrenceSimplTime: " << occurrenceSimplTime << "\n";
        stream << "c [STAT] BE occurrences removed: " << nOccurrencesRemoved << "\n";
        stream << "c [STAT] BE solverTime: " << solverTime << "\n";
        stream << "c [STAT] BE nSolverCalls: " << nSolverCalls << "\n";
        stream << "c [STAT] BE elimination candidates: " << eliminationCandidates << "\n";
        stream << "c [STAT] BE no. top level iterations: " << nTopLevelIterations << "\n";
        int usedVars = 0;
        for (const auto& it : varUsed) {
            if (bool(it))
                ++usedVars;
        }
        stream << "c [STAT] BE used variables: " << usedVars << "\n";
        stream.flush();
    }

    void BE::reset() {
        destroy();
        outputVariables.clear();
        copyTime = 0;
        bipartitionTime = 0;
        eliminationTime = 0;
        occurrenceSimplTime = 0;
        eliminationCandidates = 0;
        eliminatedVars = 0;
        nOccurrencesRemoved = 0;
    }

    bool BE::process() {
        static bool ran = false;

        if (ran) {
            return false;
        }

        if (grouped == GROUPED::NOT) {
            groupSize = 1;
        }

        computeBipartition();

        eliminate();

        data.sortClauseLists();

        ran = true;

        static bool first = true;
        if (first) {
            printStatistics(std::cerr);
            first = false;
        }

        return eliminatedVars != 0;
    }

    void BE::computeBipartition() {
        std::cout << "c Starting Bipartition" << std::endl;

        copySolver();

        assert(solver.decisionLevel() == 0 && "Only use bipartition computation on decision level 0");

        MethodTimer timer(&bipartitionTime);

        // line 1 - get the backbone and set it as output variables. this includes all units
        auto& backbone = backboneSimpl.getBackbone();
        inOutVariables.resize(solver.nVars(), InputOutputState::UNCONFIRMED);
        for (const auto& lit : backbone) {
            inOutVariables[var(lit)] = InputOutputState::BACKBONE;
        }

        // line 2
        std::vector<Var> vars;
        vars.reserve(solver.nVars());
        for (auto i = 0; i < solver.nVars(); ++i) {
            vars.emplace_back(i);
        }
        std::sort(vars.begin(), vars.end(), [&](const Var& a, const Var& b) {
            return data[a] < data[b];
        });
        std::queue<Var> varQueue;
        for (const auto& v : vars) {
            if (varUsed[v]) {
                varQueue.push(v);
            }
        }

        // line 3

        // line 4
        int lookedAtVars = 0;
        int groupBudget = varQueue.size();
        const int usedVars = varQueue.size();
        while (!varQueue.empty()) {
            if (grouped != GROUPED::NOT && lookedAtVars >= groupBudget) {
                // decrease group size
                groupSize /= 2;

                // reset budget
                groupBudget = varQueue.size();
                lookedAtVars = 0;

                std::cout << "Decreasing group size to " << groupSize << ", " << groupBudget << " variables left" << std::endl;

                if (groupSize == 1) {
                    grouped = GROUPED::NOT;
                }
            }

            // assemble current group
            std::vector<Var> group;
            for (auto i = 0; i < groupSize && !varQueue.empty(); ++i) {
                group.emplace_back(varQueue.front());
                varQueue.pop();
                ++lookedAtVars;
            }
            if (group.empty()) {
                break;
            }

            // check definedness, let the function update the inOutVars bitmap
            isDefined(group);

            // put the group members back into the queue
            for (const auto& v : group) {
                if (inOutVariables[v] == InputOutputState::UNCONFIRMED) {
                    varQueue.push(v);
                }
                assert(!(groupSize > 1 && grouped == GROUPED::CONJUNCTIVE && (inOutVariables[v] == InputOutputState::OUTPUT || inOutVariables[v] == InputOutputState::BACKBONE)));
            }
        }

        outputVariables.reserve(backbone.size());
        for (auto i = 0; i < solver.nVars(); ++i) {
            if (inOutVariables[i] == InputOutputState::OUTPUT) { // ignore backbone variables here
                outputVariables.push_back(i);
            }
        }
        eliminationCandidates = outputVariables.size();
    }

    void BE::eliminate() {
        MethodTimer timer(&eliminationTime);

        // line 2
        std::vector<Var> retrySet = outputVariables;

        // the variables that are deleted, so they can be completely removed from the cnf
        std::vector<Var> deletedVars;

        int changedVars = 100000;
        const int minChange = 0.0001 * data.nVars() + 1;

        // line 3
        while (changedVars >= minChange) {
            std::cout << "c top level iteration...\n";
            ++nTopLevelIterations;

            // line 4
            outputVariables = retrySet;
            retrySet.clear();
            changedVars = 0;

            // line 5
            // vivification on output variables
            probing.process();
            if (probing.appliedSomething()) {
                // invalidate numRes cache
                dirtyCache = true;
            }

            // line 6
            while (!outputVariables.empty()) {
                Riss::Var x;
                {
                    MethodTimer timer(&eliminationTime2);

                    // line 7
                    // select one of the output Variables that minimizes possible resolvents
                    std::size_t minIndex = 0;
                    int minRes = std::numeric_limits<int>::max();
                    for (std::size_t i = 0; i < outputVariables.size(); ++i) {
                        auto nRes = numRes(outputVariables[i]);
                        if (nRes < minRes) {
                            minRes = nRes;
                            minIndex = i;
                        }
                    }
                    x = outputVariables[minIndex];

                    // line 8
                    // remove selected variable from the set
                    outputVariables.erase(outputVariables.begin() + minIndex);
                }

                // line 9
                // occurrence simplification on x
                occurrenceSimpl(mkLit(x, false));
                occurrenceSimpl(mkLit(x, true));

                // line 10
                if (numRes(x) > maxRes) {
                    // line 11
                    // put back to maybe reconsider later
                    // at this point all other ones will also have too many resolvents
                    retrySet.reserve(outputVariables.size());
                    for (const auto& var : outputVariables) {
                        retrySet.emplace_back(var);
                    }
                    outputVariables.clear();

                } else {
                    // line 13
                    // compute resolvents into set R
                    auto R = getResolvents(x);

                    // TODO: it would probably be faster if getResolvents() and subsume() were working together
                    // run subsumption on R
                    subsume(R);

                    // line 14
                    // if number of clauses in formula without x + ||R|| is less than current number of clauses
                    auto posXClauses = getClausesContaining(mkLit(x, false));
                    auto negXClauses = getClausesContaining(mkLit(x, true));
                    // we can assume that these don't overlap

                    if (posXClauses.size() + negXClauses.size() > R.size()) {
                        // actually do the elimination now
                        for (const auto& clause : posXClauses) {
                            ca[clause].mark(1);
                            ca[clause].set_delete(true);
                            data.removedClause(clause);
                        }

                        for (const auto& clause : negXClauses) {
                            ca[clause].mark(1);
                            ca[clause].set_delete(true);
                            data.removedClause(clause);
                        }

                        data.lits.clear();
                        // add clauses from R
                        for (auto& c : R) {
                            if (c.size() == 1) {
                                std::cout << "Unit clause resolved!!" << std::endl;
                            }
                            assert(!c.empty());
                            for (const auto& l : c) {
                                data.lits.emplace_back(l);
                            }

                            Riss::CRef newClause = ca.alloc(data.lits, false);
                            ca[newClause].sort();
                            data.addClause(newClause);
                            data.getClauses().push(newClause);

                            data.lits.clear();
                        }

                        // add unit clause with x to fix it, otherwise we double the number of solutions
                        data.lits.emplace_back(mkLit(x));
                        Riss::CRef newClause = ca.alloc(data.lits, false);
                        data.addClause(newClause);
                        data.getClauses().push(newClause);

                        data.lits.clear();

                        // line 16
                        // something happened, so retrying might yield new results, also invalidate numRes cache
                        ++changedVars;
                        dirtyCache = true;
                        ++eliminatedVars;

                        deletedVars.emplace_back(x);
                    } else {
                        // line 18
                        // reconsider later
                        retrySet.emplace_back(x);
                    }
                }
            }
        }
        nDeletedVars = deletedVars.size();
    }

    void BE::isDefined(const std::vector<Var>& vars) {
        // put "vars" as output variables temporarily
        for (const auto& v : vars) {
            inOutVariables[v] = InputOutputState::OUTPUT;
        }

        // every new variable made from existing ones will just get nVars added to themselves
        // this way no collisions can happen

        Riss::vec<Lit> assumptions;

        auto add_assumption = [&](Riss::Lit l){
#if defined(CADICAL)
            ownSolver->assume((var(l) + 1) * (sign(l) ? -1 : 1));
#else
            assumptions.push(l);
#endif
        };

        // add assumption sZ for every UNCONFIRMED or INPUT variable ("vars" variables are output at this point)
        for (auto i = 1; i < nVar; ++i) {
            if (inOutVariables[i] == InputOutputState::INPUT || inOutVariables[i] == InputOutputState::UNCONFIRMED) {
                add_assumption(mkLit(i + (2 * nVar)));
                // sZ and sZ' exclude each other, might as well tell the solver
                add_assumption(mkLit(i + (3 * nVar), true));
            }
        }

        // add x and ~xprime unit clauses (breaking symmetry)
        if (groupSize == 1) {
            assert(vars.size() == 1);
            add_assumption(mkLit(vars[0]));
            add_assumption(mkLit(vars[0] + nVar, true));
        } else {
            // can't (or at least shouldn't) break symmetry with a larger group
            for (const auto& v : vars) {
                // use the sZ' (+ nvars * 3)
                add_assumption(mkLit(v + (2 * nVar), true));
                add_assumption(mkLit(v + (3 * nVar)));
            }
        }

        ++nSolverCalls;
        Riss::lbool res;

        // now set conflict budget
#if defined(CADICAL)
        ownSolver->limit("conflicts", conflictBudget);

        {
            MethodTimer timer(&solverTime);
            switch (ownSolver->solve()) {
            case 0:
                res = l_Undef;
                break;
            case 10:
                res = l_True;
                break;
            case 20:
                res = l_False;
                break;
            }
        }
#else
        ownSolver->setConfBudget(conflictBudget);
        ownSolver->assumptions.clear();

        {
            MethodTimer timer(&solverTime);
            res = ownSolver->solveLimited(assumptions);
        }
#endif

        if (groupSize == 1) {
            if (res == l_False) {
                // it's defined
                // the variable is already set as output so nothing to be done
                return;
            }
            if (res == l_True || res == l_Undef) {
                // it's not defined or ran out of time
                inOutVariables[vars[0]] = InputOutputState::INPUT;
                return;
            }
        }

        // group size > 1
        if (grouped == GROUPED::CONJUNCTIVE) {
            if (res == l_False || res == l_Undef) {
                // did not find information, reset to unknown
                for (const auto& v : vars) {
                    inOutVariables[v] = InputOutputState::UNCONFIRMED;
                }
                return;
            }

            if (res == l_True) {
                // none of the variables are defined -> all are input
                for (const auto& v : vars) {
                    inOutVariables[v] = InputOutputState::INPUT;
                }
                std::cout << "c Yay, removed " << vars.size() << " variables at once" << std::endl;
                return;
            }
        }

        if (grouped == GROUPED::DISJUNCTIVE) {
            if (res == l_False) {
                // all are defined -> all are output
                for (const auto& v : vars) {
                    inOutVariables[v] = InputOutputState::OUTPUT;
                }
                return;
            }

            if (res == l_True) {
                // at least one variable is not defined -> find which
#if defined(CADICAL)
                for (const auto& v : vars) {
                    if (ownSolver->val(v + 1 + nVar * 3)) {
                        inOutVariables[v] = InputOutputState::INPUT;
                    } else {
                        inOutVariables[v] = InputOutputState::UNCONFIRMED;
                    }
                }
#else
                auto& model = ownSolver->model;
                for (const auto& v : vars) {
                    if (model[v + nVar * 3] == l_True) {
                        inOutVariables[v] = InputOutputState::INPUT;
                    } else {
                        inOutVariables[v] = InputOutputState::UNCONFIRMED;
                    }
                }
#endif
                return;
            }
        }
    }

    void BE::copySolver() {
        MethodTimer timer(&copyTime);

        // -- copy the solver --
        // register variables
        // 1 * nVar for original variables
        // 2 * nVar for sigma prime
        // 3 * nVar for the s_z variables from the paper (s_z true makes z == z')
        // 4 * nVar for extra s_z' variables -> (s_z true makes z != z') -> needed for literal grouping
        int nVars = nVar * ((groupSize >= 1) ? 4 : 3);
#if defined(CADICAL)
        ownSolver = new CaDiCaL::Solver();

        for (std::size_t i = 0; i < data.getClauses().size(); ++i) {
            const auto& clause = ca[data.getClauses()[i]];
            for (int j = 0; j < clause.size(); ++j) {
                varUsed[var(clause[j])] = true;
                ownSolver->add((var(clause[j]) + 1) * (sign(clause[j]) ? -1 : 1));
            }
            ownSolver->add(0);  // end clause

            for (int j = 0; j < clause.size(); ++j) {
                ownSolver->add((var(clause[j]) + nVar + 1) * (sign(clause[j]) ? -1 : 1));
            }
            ownSolver->add(0);
        }

        for (int var = 1; var < solver.nVars() + 1; ++var) {
            if (!varUsed[var - 1]) {
                // no need to do this for unused variables
                continue;
            }

            // z is var
            const auto z = var;
            const auto zP = var + nVar;
            const auto sZ = var + 2 * nVar;
            // z' is var + nVar
            // s_z is var + 2 * nVar
            // add two clauses:
            // clause (~sZ, ~z, zP)
            ownSolver->add(-sZ);
            ownSolver->add(-z);
            ownSolver->add(zP);
            ownSolver->add(0);
            
            // clause (~sZ, z, ~zP)
            ownSolver->add(-sZ);
            ownSolver->add(z);
            ownSolver->add(-zP);
            ownSolver->add(0);

            if (groupSize >= 1) {
                // add two extra clauses for literal grouping
                const auto sZP = var + nVar * 3;
                // clause (~sZ', z, zP)
                ownSolver->add(-sZP);
                ownSolver->add(z);
                ownSolver->add(zP);
                ownSolver->add(0);
                // clause (~sZ', ~z, ~zP)
                ownSolver->add(-sZP);
                ownSolver->add(-z);
                ownSolver->add(-zP);
                ownSolver->add(0);
            }
        }
#else

        // init the solver
        solverconfig = new Riss::CoreConfig("");
        cp3config = new Coprocessor::CP3Config("-no-backbone -no-be");
        ownSolver = new Riss::Solver(solverconfig);
        ownSolver->setPreprocessor(cp3config);

        for (auto i = 0; i < nVars; ++i) {
            ownSolver->newVar();
        }

        // copy clauses + "prime"-clauses
        Riss::vec<Lit> assembledClause;
        Riss::vec<Lit> primeClause;
        for (std::size_t i = 0; i < data.getClauses().size(); ++i) {
            const auto& clause = ca[data.getClauses()[i]];
            for (int j = 0; j < clause.size(); ++j) {
                assembledClause.push(clause[j]);
                primeClause.push(mkLit(var(clause[j]) + nVar, sign(clause[j])));
                varUsed[var(clause[j])] = true;
            }
            ownSolver->integrateNewClause(assembledClause);
            ownSolver->integrateNewClause(primeClause);
            assembledClause.clear();
            primeClause.clear();
        }

        // add 2 additional clauses for every variable
        Riss::vec<Lit> addedClause;
        for (int var = 0; var < solver.nVars(); ++var) {
            if (!varUsed[var]) {
                // no need to do this for unused variables
                continue;
            }
            // z is var
            const auto z = var;
            const auto zP = var + nVar;
            const auto sZ = var + 2 * nVar;
            // z' is var + nVar
            // s_z is var + 2 * nVar
            // add two clauses:
            // clause (~sZ, ~z, zP)
            addedClause.push(mkLit(sZ, true));
            addedClause.push(mkLit(z, true));
            addedClause.push(mkLit(zP));
            ownSolver->integrateNewClause(addedClause);
            addedClause.clear();
            // clause (~sZ, z, ~zP)
            addedClause.push(mkLit(sZ, true));
            addedClause.push(mkLit(z));
            addedClause.push(mkLit(zP, true));
            ownSolver->integrateNewClause(addedClause);
            addedClause.clear();

            if (groupSize >= 1) {
                // add two extra clauses for literal grouping
                const auto sZP = var + nVar * 3;
                // clause (~sZ', z, zP)
                addedClause.push(mkLit(sZP, true));
                addedClause.push(mkLit(z));
                addedClause.push(mkLit(zP));
                ownSolver->integrateNewClause(addedClause);
                addedClause.clear();
                // clause (~sZ', ~z, ~zP)
                addedClause.push(mkLit(sZP, true));
                addedClause.push(mkLit(z, true));
                addedClause.push(mkLit(zP, true));
                ownSolver->integrateNewClause(addedClause);
                addedClause.clear();
            }
        }
#endif
    }

    std::uint32_t BE::numRes(const Var& x) const {
        static std::map<Var, std::uint32_t> cache;

        if (dirtyCache) {
            cache.clear();
            dirtyCache = false;
        }

        if (cache.find(x) != cache.end()) {
            return cache.at(x);
        }

        // positive and negative x literal
        Lit pX = mkLit(x, false);
        Lit nX = mkLit(x, true);

        // find number of clauses where x appears positive/negative
        std::uint32_t xpos = 0;
        std::uint32_t xneg = 0;

        for (std::size_t i = 0; i < data.getClauses().size(); ++i) {
            const auto& clause = ca[data.getClauses()[i]];
            const Lit* lit = (const Lit*)(clause);
            for (int j = 0; j < clause.size(); ++j) {
                if (lit[j] == pX) {
                    ++xpos;
                    // no need to check rest of clause
                    continue;
                }
                if (lit[j] == nX) {
                    ++xneg;
                    // no need to check rest of clause
                    continue;
                }
            }
        }

        cache.emplace(x, xpos * xneg);

        // maximum number of resolvents is every clause where x appears positive with every clause where x appears negative
        return xpos * xneg;
    }

    std::vector<Riss::CRef> BE::getClausesContaining(const Lit& x) const {
        std::vector<Riss::CRef> resultClauses;

        for (std::size_t i = 0; i < data.getClauses().size(); ++i) {
            const auto& clause = ca[data.getClauses()[i]];
            const Lit* lit = (const Lit*)(clause);
            for (int j = 0; j < clause.size(); ++j) {
                if (ca[data.getClauses()[i]].mark()) {
                    continue;
                }
                if (lit[j] == x) {
                    resultClauses.emplace_back(data.getClauses()[i]);
                    // no need to check rest of clause
                    break;
                }
            }
        }

        return resultClauses;
    }

    std::vector<std::vector<Lit>> BE::getResolvents(const Var& x) const {
        MethodTimer timer(&getResTime);
        ++nGetRes;
        auto posX = mkLit(x, false);
        auto negX = mkLit(x, true);

        // get all clauses containing x and all containing ~x
        auto posClauses = this->getClausesContaining(posX);
        auto negClauses = this->getClausesContaining(negX);

        std::vector<std::vector<Lit>> resolvents;

        // iterate through the clauses containing x/~x
        for (const auto& pC : posClauses) {
            const auto& posClause = ca[pC];
            const Lit* posLit = (const Lit*)(posClause);

            for (const auto& nC : negClauses) {
                const auto& negClause = ca[nC];
                const Lit* negLit = (const Lit*)(negClause);

                resolvents.emplace_back();
                // put all literals from both clauses into the resolvent, except x and ~x respectively
                auto& resolvent = resolvents.back();

                for (std::size_t i = 0; i < posClause.size(); ++i) {
                    if (posLit[i] != posX) {
                        resolvent.emplace_back(posLit[i]);
                    }
                }
                for (std::size_t i = 0; i < negClause.size(); ++i) {
                    if (negLit[i] != negX) {
                        // need to make sure to not add duplicate lits
                        if (std::find(resolvent.begin(), resolvent.end(), negLit[i]) == resolvent.end()) {
                            resolvent.emplace_back(negLit[i]);
                        }
                    }
                }

                if (isTautology(resolvent)) {
                    resolvents.erase(resolvents.end() - 1);
                }
            }
        }

        return resolvents;
    }

    void BE::subsume(std::vector<std::vector<Lit>>& clauses) const {
        MethodTimer timer(&subsumptionTime);
        ++nSubsumption;
        // remember if something is subsumed
        std::vector<bool> isSubsumed(clauses.size(), false);

        for (std::size_t i = 0; i < clauses.size(); ++i) {
            if (isSubsumed[i]) {
                continue;
            }
            for (std::size_t j = i + 1; j < clauses.size(); ++j) {
                if (isSubsumed[j]) {
                    continue;
                }

                if (subsumes(clauses[i], clauses[j])) { // i subsumes j
                    isSubsumed[j] = true;
                    continue; // if i subsumes j, don't check if j subsumes i
                    // because if they subsume each other then they are equal, in which case we can only remove one, not both
                }
                if (subsumes(clauses[j], clauses[i])) { // j subsumes i
                    isSubsumed[i] = true;
                }
            }
        }

        // check for subsumptions by the original clauses
        for (std::size_t i = 0; i < data.getClauses().size(); ++i) {
            const auto& c = ca[data.getClauses()[i]];
            const Lit* lit = (const Lit*)(c);
            std::vector<Riss::Lit> clause;
            for (int j = 0; j < c.size(); ++j) {
                clause.emplace_back(lit[j]);
            }

            for (std::size_t j = 0; j < clauses.size(); ++j) {
                if (isSubsumed[j]) {
                    continue;
                }

                if (subsumes(clause, clauses[j])) { // i subsumes j
                    isSubsumed[j] = true;
                    continue; // if i subsumes j, don't check if j subsumes i
                    // because if they subsume each other then they are equal, in which case we can only remove one, not both
                }
            }
        }

        // make a fancy mutable lambda that keeps track of the index as internal state
        int index = 0;
        auto remover = [index, &isSubsumed](const std::vector<Riss::Lit>&) mutable {
            return isSubsumed[index++];
        };

        // give the remover lambda as reference so it isn't copied and the state is consistent
        // -> removes all clauses that were marked in isSubsumed
        // (this assumes that std::remove_if goes through the elements in clauses in order, which isn't specified in the standard)
        clauses.erase(std::remove_if(clauses.begin(), clauses.end(), std::ref(remover)), clauses.end());
    }

    void BE::occurrenceSimpl(const Lit& x) {
        MethodTimer timer(&occurrenceSimplTime);

        bool changed = false;
        auto clauses = getClausesContaining(x);

        for (auto& clause : clauses) {

            Riss::vec<Lit> assumptions;
            auto& c = ca[clause];
            c.size();

            // add assumptions for negated clause literals except x, which is positive
            for (auto i = 0; i < c.size(); ++i) {
                if (c[i] == x) {
                    assumptions.push(x);
                } else {
                    assumptions.push(~c[i]);
                }
            }

            // only use bcp -> confbudget = 0
#if defined(CADICAL)
            ownSolver->limit("conflicts", 0);
            lbool res = ownSolver->solve() == 20 ? l_False : l_True;  //only care about unsatisfiability
#else
            ownSolver->setConfBudget(0);
            ownSolver->assumptions.clear();
            lbool res = ownSolver->solveLimited(assumptions);
#endif

            ++nSolverCalls;

            if (res == l_False) {
                // unsatisfiable -> remove x from the clause
                c.remove_lit(x);

                ++nOccurrencesRemoved;
                changed = true;
            }
        }

        if (changed) {
            dirtyCache = true;
        }
    }

    bool BE::subsumes(std::vector<Lit>& a, std::vector<Lit>& b) const {
        for (const auto& litA : a) {
            bool found = false;
            for (const auto& litB : b) {
                if (litA == litB) {
                    found = true;
                    break;
                }
            }

            if (!found) {
                return false;
            }
        }
        return true;
    }

    void BE::printLitVec(const std::vector<Lit>& lits) const {
        printf("{");
        for (std::size_t i = 0; i < lits.size(); ++i) {
            if (i != 0) {
                printf(", ");
            }

            printf("%s%d", sign(lits[i]) ? "-" : "", var(lits[i]) + 1);
        }

        printf("}");
    }

    bool BE::isTautology(const std::vector<Lit>& lits) const {
        for (std::size_t i = 0; i < lits.size(); ++i) {
            for (std::size_t j = i + 1; j < lits.size(); ++j) {
                if (lits[i] == ~lits[j]) {
                    return true;
                }
            }
        }
        return false;
    }

} // namespace Coprocessor
