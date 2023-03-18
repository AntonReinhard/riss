/***********************************************************************[BackboneSimplification.cc]
Copyright (c) 2021, Anton Reinhard, LGPL v2, see LICENSE
**************************************************************************************************/

#include "coprocessor/techniques/BackboneSimplification.h"
#include "coprocessor/ScopedDecisionLevel.h"
#include "riss/core/SolverTypes.h"

#ifdef CADICAL
#include <cadical.hpp>
#endif

#include <algorithm>
#include <cmath>
#include <unordered_map>
#include <unordered_set>

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

    inline std::string sortingToString(Coprocessor::LIKELIHOOD_HEURISTIC heuristic) {
        switch (heuristic) {
        case Coprocessor::LIKELIHOOD_HEURISTIC::DIV:
            return "division";
        case Coprocessor::LIKELIHOOD_HEURISTIC::MULT:
            return "multiplication";
        default:
            return "unknown";
        }
    }

} // namespace

namespace Coprocessor {

    BackboneSimplification::BackboneSimplification(CP3Config& _config, ClauseAllocator& _ca, ThreadController& _controller, CoprocessorData& _data,
                                                   Propagation& _propagation, Solver& _solver)
        : Technique(_config, _ca, _controller)
        , data(_data)
        , propagation(_propagation)
        , solver(_solver)
        , varUsed(solver.nVars(), false)
        , noUsedVars(0)
        , ran(false)
        , dirtyCache(true)
        , conflictBudget(_config.opt_backbone_nconf)
        , likelihood_heuristic(static_cast<LIKELIHOOD_HEURISTIC>((int)_config.opt_backbone_sorting))
        , grouping(static_cast<GROUPED>((int)_config.opt_backbone_grouping))
        , nGrouping(_config.opt_backbone_ngrouping)
        , nSolve(0)
        , unitsBefore(0)
        , timedOutCalls(0)
        , crossCheckRemovedLiterals(0)
        , copyTime(0)
        , searchTime(0)
        , solverTime(0) {
    }

    void BackboneSimplification::giveMoreSteps() {
    }

    void BackboneSimplification::destroy() {
#ifndef CADICAL
        delete solverconfig;
        delete cp3config;
#endif
        delete ownSolver;
    }

    void BackboneSimplification::reset() {
        destroy();
        backbone.clear();
        ran = false;
        timedOutCalls = 0;
        crossCheckRemovedLiterals = 0;
        copyTime = 0;
        searchTime = 0;
        solverTime = 0;
        nSolve = 0;
        unitsBefore = 0;
        noUsedVars = 0;
        dirtyCache = true;
    }

    void BackboneSimplification::printStatistics(std::ostream& stream) {
        stream << "c [STAT] BACKBONE solver signature: " << solverSignature << std::endl;
        stream << "c [STAT] BACKBONE max nconf: " << conflictBudget << std::endl;
        stream << "c [STAT] BACKBONE nGrouping: " << nGrouping << std::endl;
        stream << "c [STAT] BACKBONE grouping strat: " << groupingToString(grouping) << std::endl;
        stream << "c [STAT] BACKBONE sorting strat: " << sortingToString(likelihood_heuristic) << std::endl;
        stream << "c [STAT] BACKBONE found variables: " << backbone.size() - unitsBefore << std::endl;
        stream << "c [STAT] BACKBONE units before: " << unitsBefore << std::endl;
        stream << "c [STAT] BACKBONE timed out calls: " << timedOutCalls << std::endl;
        stream << "c [STAT] BACKBONE removed literals through found model: " << crossCheckRemovedLiterals << std::endl;
        stream << "c [STAT] BACKBONE time copying: " << copyTime << std::endl;
        stream << "c [STAT] BACKBONE time searching: " << searchTime << std::endl;
        stream << "c [STAT] BACKBONE solverTime: " << solverTime << std::endl;
        stream << "c [STAT] BACKBONE solver calls: " << nSolve << std::endl;
        stream << "c [STAT] BACKBONE used variables: " << noUsedVars << std::endl;
    }

    bool BackboneSimplification::process() {
        computeBackbone();

        // add new unit clauses
        for (const Lit& l : backbone) {
            data.enqueue(l);
        }

        // propagate
        propagation.process(data, true);

        static bool first = true;
        if (first) {
            first = false;
        }

        return true;
    }

    std::vector<Lit>& BackboneSimplification::getBackbone() {
        if (!ran) {
            computeBackbone();
        }

        return backbone;
    }

    void BackboneSimplification::computeBackbone() {
        if (ran) {
            // running again on the same thing is never beneficial
            return;
        }

        // hide class' grouping and ngrouping and use local ones instead, because they may be changed
        GROUPED grouping = this->grouping;
        int nGrouping = this->nGrouping;

        // sanity check for grouping
        if (nGrouping == 1 && grouping != GROUPED::NOT) {
            std::cerr << "c nGrouping 1 only makes sense without grouping, reverting to no groups" << std::endl;
            grouping = GROUPED::NOT;
        }

        copySolver();

        MethodTimer timer(&searchTime);

        // backbone Candidate vector
        std::vector<Lit> possibleBackboneLiterals;
#if defined(CADICAL)

        int ret;
        {
            MethodTimer t(&solverTime);
            ret = ownSolver->solve();
        }

        if (ret != 10) {
            std::cerr << "c Unsatisfiable" << std::endl;
            return;
        }

        for (int32_t i = 0; i < solver.nVars(); ++i) {
            if (ownSolver->val(i + 1)) {
                possibleBackboneLiterals.emplace_back(mkLit(i, false));
            } else {
                possibleBackboneLiterals.emplace_back(mkLit(i, true));
            }
        }
#else
        // set conflict budget to infinity
        ownSolver->budgetOff();

        Riss::lbool ret;
        {
            MethodTimer t(&solverTime);
            // Compute a model
            ret = ownSolver->solveLimited({});
        }

        if (ret == l_False) {
            // if the formula is unsatisfiable the backbone is empty
            std::cerr << "c Unsatisfiable" << std::endl;
            return;
        }

        for (int32_t i = 0; i < ownSolver->model.size(); ++i) {
            assert(ownSolver->model[i] != l_Undef);
            if (ownSolver->model[i] == l_True) {
                possibleBackboneLiterals.emplace_back(mkLit(i, false));
            } else {
                possibleBackboneLiterals.emplace_back(mkLit(i, true));
            }
        }
#endif

        std::queue<Lit> litsToCheck;
        {
            // can't sort the original so make a copy and sort that
            std::vector<Lit> backboneLitsTemp;
            backboneLitsTemp.reserve(noUsedVars);

            for (const auto& lit : possibleBackboneLiterals) {
                if (varUsed[var(lit)]) {
                    backboneLitsTemp.emplace_back(lit);
                }
            }
            switch (grouping) {
            case GROUPED::CONJUNCTIVE:
                // sort unlikely first
                std::sort(backboneLitsTemp.begin(), backboneLitsTemp.end(), [this](const Lit& x, const Lit& y) {
                    return getBackboneLikelihood(var(x)) < getBackboneLikelihood(var(y));
                });
                break;
            case GROUPED::DISJUNCTIVE:
                // sort likely first
                std::sort(backboneLitsTemp.begin(), backboneLitsTemp.end(), [this](const Lit& x, const Lit& y) {
                    return getBackboneLikelihood(var(x)) > getBackboneLikelihood(var(y));
                });
                break;
            case GROUPED::NOT:
                // no need to sort
                break;
            default:
                assert(false);
            }

            // now fill the queue in the correct order
            for (const auto& lit : backboneLitsTemp) {
                litsToCheck.push(lit);
            }
        }

        Riss::vec<Lit> unitLit;

        int lookedAtVars = 0;
        int groupBudget = litsToCheck.size();
        // Main loop over the literals
        while (!litsToCheck.empty()) {
            unitLit.clear();

            const auto currentLiteral = litsToCheck.front();
            litsToCheck.pop();
            ++lookedAtVars;

            if (possibleBackboneLiterals[var(currentLiteral)].x == -1) {
                continue;
            }

            if (nGrouping > 1 && lookedAtVars > groupBudget) {
                nGrouping = nGrouping / 2;

                // reset group budget and lookedAtVars
                lookedAtVars = 0;
                groupBudget = litsToCheck.size();

                if (config.opt_verbose > 1) {
                    std::cout << "c [BB] Decreasing group size to " << nGrouping << ", " << groupBudget << " variables left" << std::endl;
                }

                if (nGrouping == 1) {
                    grouping = GROUPED::NOT;
                }
            }

#if defined(CADICAL)
            ownSolver->limit("conflicts", conflictBudget);
#else
            ownSolver->model.clear();

            // now set conflict budget
            ownSolver->setConfBudget(conflictBudget);
#endif

            // get new model
            switch (grouping) {
            case GROUPED::NOT:
                unitLit.push(~currentLiteral);
                break;
            case GROUPED::CONJUNCTIVE:
            case GROUPED::DISJUNCTIVE:
                unitLit.push(~currentLiteral);
                for (int j = 1; j < nGrouping; ++j) {
                    if (litsToCheck.empty()) {
                        break;
                    }
                    if (possibleBackboneLiterals[var(litsToCheck.front())].x == -1) {
                        litsToCheck.pop();
                        ++lookedAtVars;
                        --j;
                        continue;
                    }
                    unitLit.push(~(litsToCheck.front()));
                    litsToCheck.pop();
                    ++lookedAtVars;
                }
                break;
            }
            Riss::lbool solveResult;

            {
                MethodTimer t(&solverTime);
                ++nSolve;

#if defined(CADICAL)
                int res;
                if (grouping == GROUPED::DISJUNCTIVE && unitLit.size() > 1) {
                    // add constraint clause
                    for (auto i = 0; i < unitLit.size(); ++i) {
                        ownSolver->constrain((var(unitLit[i]) + 1) * (sign(unitLit[i]) ? -1 : 1));
                    }
                    ownSolver->constrain(0);
                    res = ownSolver->solve();
                } else {
                    // add assumptions
                    for (auto i = 0; i < unitLit.size(); ++i) {
                        ownSolver->assume((var(unitLit[i]) + 1) * (sign(unitLit[i]) ? -1 : 1));
                    }
                    res = ownSolver->solve();
                }
                switch (res) {
                case 0:
                    solveResult = l_Undef;
                    break;
                case 10:
                    solveResult = l_True;
                    break;
                case 20:
                    solveResult = l_False;
                    break;
                }
#else
                if (grouping == GROUPED::DISJUNCTIVE && unitLit.size() > 1) {
                    // for disjunctive, add a new clause with all the "units" and remove it afterwards
                    ScopedDecisionLevel dec(*ownSolver);
                    ownSolver->integrateNewClause(unitLit);
                    solveResult = ownSolver->solveLimited({});
                    // newly integrated clauses are at the end
                } else {
                    solveResult = ownSolver->solveLimited(unitLit);
                }
                ownSolver->assumptions.clear();
#endif
            }

            if (solveResult == l_False) {
                switch (grouping) {
                case GROUPED::NOT:
                    // if there's no model then the literal is in the backbone, because
                    // apparently no model exists with the literal negated
                    // use the remaining Literal for the backbone
                    backbone.push_back(currentLiteral);
                    continue;
                case GROUPED::CONJUNCTIVE:
                    // if conjunctive grouping was used, no info was gained, retry the vars again later
                    for (int k = 0; k < unitLit.size(); ++k) {
                        litsToCheck.push(~(unitLit[k]));
                    }
                    continue;
                case GROUPED::DISJUNCTIVE:
                    //  if disjunctive grouping was used, no solution means that all lits were in the backbone
                    for (int k = 0; k < unitLit.size(); ++k) {
                        backbone.push_back(~(unitLit[k]));
                    }
                    continue;
                }
            }

            if (solveResult == l_Undef) {
                // if we ran out of conflict budget just continue
                // conjunctive grouping should be faster to solve than single, so don't try again there
                if (grouping == GROUPED::DISJUNCTIVE) {
                    // for disjunctive grouping trying them alone might yield better luck
                    for (int k = 0; k < unitLit.size(); ++k) {
                        litsToCheck.push(~(unitLit[k]));
                    }
                }

                ++timedOutCalls;
                continue;
            }

            // check the model against the remaining candidates
#if defined(CADICAL)
            for (int32_t j = 0; j < solver.nVars(); ++j) {
                if (possibleBackboneLiterals[j].x == -1) {
                    continue;
                }
                // check if signs are different
                if (sign(possibleBackboneLiterals[j]) == ownSolver->val(j + 1)) {
                    possibleBackboneLiterals[j].x = -1;
                    ++crossCheckRemovedLiterals;
                }
            }
#else
            auto& model = ownSolver->model;
            for (int32_t j = 0; j < model.size(); ++j) {
                assert(model[j] != l_Undef);
                if (possibleBackboneLiterals[j].x == -1) {
                    continue;
                }
                // check if signs are different
                if (sign(possibleBackboneLiterals[j]) != (model[j] != l_True)) {
                    possibleBackboneLiterals[j].x = -1;
                    ++crossCheckRemovedLiterals;
                }
            }
#endif
        }

        ran = true;
    }

    void BackboneSimplification::copySolver() {
        MethodTimer timer(&copyTime);

#if defined(CADICAL)
        ownSolver = new CaDiCaL::Solver();

        // copy clauses
        for (std::size_t i = 0; i < solver.clauses.size(); ++i) {
            const auto& clause = ca[solver.clauses[i]];
            for (int j = 0; j < clause.size(); ++j) {
                ownSolver->add((var(clause[j]) + 1) * (sign(clause[j]) ? -1 : 1));
                varUsed[var(clause[j])] = true;
            }
            ownSolver->add(0);
        }
#else
        // init the solver
        solverconfig = new Riss::CoreConfig("");
        cp3config = new Coprocessor::CP3Config("-no-backbone -no-be");
        ownSolver = new Riss::Solver(solverconfig);
        ownSolver->setPreprocessor(cp3config);

        // -- copy the solver --
        // register variables
        for (auto i = 0; i < solver.nVars(); ++i) {
            ownSolver->newVar();
        }

        // copy clauses
        Riss::vec<Lit> assembledClause;
        for (std::size_t i = 0; i < solver.clauses.size(); ++i) {
            const auto& clause = ca[solver.clauses[i]];
            for (int j = 0; j < clause.size(); ++j) {
                assembledClause.push(clause[j]);
                varUsed[var(clause[j])] = true;
            }
            ownSolver->integrateNewClause(assembledClause);
            assembledClause.clear();
        }
#endif

        for (std::size_t i = 0; i < solver.trail.size(); ++i) {
            backbone.emplace_back(solver.trail[i]);
        }

        unitsBefore = backbone.size();

        for (const auto& it : varUsed) {
            if (bool(it))
                ++noUsedVars;
        }
    }

    double BackboneSimplification::getBackboneLikelihood(const Var x) {
        static std::unordered_map<Var, std::uint32_t> cache;

        if (!dirtyCache) {
            return cache.at(x);
        }

        cache.clear();
        cache.reserve(noUsedVars);
        dirtyCache = false;

        std::unordered_map<Var, std::uint32_t> posCache, negCache;
        for (int i = 0; i < data.nVars(); ++i) {
            posCache.emplace(i, 0);
            negCache.emplace(i, 0);
        }

        for (std::size_t i = 0; i < data.getClauses().size(); ++i) {
            const auto& clause = ca[data.getClauses()[i]];
            const Lit* lit = (const Lit*)(clause);
            for (int j = 0; j < clause.size(); ++j) {
                if (sign(lit[j]))
                    negCache[var(lit[j])]++;
                else
                    posCache[var(lit[j])]++;
            }
        }

        double likelihood = 0.;

        for (int i = 0; i < data.nVars(); ++i) {
            const auto& xneg = negCache[i];
            const auto& xpos = posCache[i];

            switch (likelihood_heuristic) {
            case LIKELIHOOD_HEURISTIC::MULT:
                if (xneg == 0 || xpos == 0)
                    likelihood = 1000000;
                else
                    likelihood = 1. / (xpos * xneg);
                break;
            case LIKELIHOOD_HEURISTIC::DIV:
                if (xneg == 0 || xpos == 0)
                    likelihood = 1000000;
                else
                    likelihood = (xpos > xneg) ? static_cast<double>(xpos) / xneg : static_cast<double>(xneg) / xpos;
                break;
            default:
                assert(false);
                break;
            }

            cache.emplace(i, likelihood);
        }

        return cache.at(x);
    }

} // namespace Coprocessor
