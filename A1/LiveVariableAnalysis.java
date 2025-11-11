/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Stmt;

import java.util.Optional;

/**
 * Implementation of classic live variable analysis.
 * 专门用于 Live variable analysis 继承自 AbstractDataflowAnalysis
 */
public class LiveVariableAnalysis extends
        AbstractDataflowAnalysis<Stmt, SetFact<Var>> {

    public static final String ID = "livevar";
    private static final Logger log = LoggerFactory.getLogger(LiveVariableAnalysis.class);

    public LiveVariableAnalysis(AnalysisConfig config) {
        super(config);
    }

    /**
     * @return backword
     */
    @Override
    public boolean isForward() {
        return false;
    }

    /**
     * @return IN[exit] = empty
     */
    @Override
    public SetFact<Var> newBoundaryFact(CFG<Stmt> cfg) {
        return new SetFact<>();
    }

    /**
     * @return IN[B] = empty
     */
    @Override
    public SetFact<Var> newInitialFact() {
        return new SetFact<>();
    }

    /**
     * ∪
     */
    @Override
    public void meetInto(SetFact<Var> fact, SetFact<Var> target) {
       target.union(fact);
    }

    /**
     * @return in = gen∪(out-kill)
     */
    @Override
    public boolean transferNode(Stmt stmt, SetFact<Var> in, SetFact<Var> out) {
        SetFact<Var> oldIn = in.copy();
        in.clear();
        in.union(out);

        Optional<Var> def = stmt.getDef().map(lValue -> {
            if (lValue instanceof Var) {
                return (Var) lValue;
            }
            return null;
        });
        if (def.isPresent()) {
            in.remove(def.get());
        }
        stmt.getUses().forEach(rValue -> {
            if (rValue instanceof Var) {
                Var var = (Var) rValue;
                in.add(var);
            }
        });
        return !in.equals(oldIn);
    }
}
