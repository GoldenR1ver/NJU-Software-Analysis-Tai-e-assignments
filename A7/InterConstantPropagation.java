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

package pascal.taie.analysis.dataflow.inter;

import org.checkerframework.checker.units.qual.A;
import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import soot.util.Cons;

import java.util.*;
import java.util.concurrent.BrokenBarrierException;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private Map<Var, HashSet<Var>> allVarAliases;

    private Map<JField, HashSet<StoreField>>  staticFieldStore;

    private Map<JField, HashSet<LoadField>>  staticFieldLoad;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);

        allVarAliases = new HashMap<>();

        for (Var base : pta.getVars()) {
            for(Var var : pta.getVars()) {
                for (Obj obj : pta.getPointsToSet(base)) {
                    if (pta.getPointsToSet(var).contains(obj)) {
                        HashSet<Var> baseAliases = allVarAliases.getOrDefault(base, new HashSet<>());
                        baseAliases.add(var);
                        allVarAliases.put(base, baseAliases);
                        break;
                    }
                }
            }
        }

        staticFieldStore = new HashMap<>();
        staticFieldLoad = new HashMap<>();
        icfg.forEach(stmt -> {
            if(stmt instanceof StoreField storeField && storeField.isStatic()) {
                JField jField = storeField.getFieldRef().resolve();
                HashSet<StoreField> storeFields = staticFieldStore.getOrDefault(jField, new HashSet<>());
                storeFields.add(storeField);
                staticFieldStore.put(jField, storeFields);
            }
            if(stmt instanceof LoadField loadField && loadField.isStatic()) {
                JField jField = loadField.getFieldRef().resolve();
                HashSet<LoadField> loadFields = staticFieldLoad.getOrDefault(jField, new HashSet<>());
                loadFields.add(loadField);
                staticFieldLoad.put(jField, loadFields);
            }
        });

    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        return out.copyFrom(in);
    }

    /**
 * Transfers dataflow facts for non-call statements (e.g., field/array accesses).
 * This method handles alias-aware constant propagation by considering points-to
 * information and static/instance field accesses.
 * 
 * @param stmt the current statement to process
 * @param in the input fact (dataflow state before the statement)
 * @param out the output fact (dataflow state after the statement)
 * @return true if the output fact changed, false otherwise
 */
@Override
protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
    // Handle LoadField statements (reading from a field)
    if (stmt instanceof LoadField loadField && ConstantPropagation.canHoldInt(loadField.getLValue())) {
        return handleLoadField(loadField, in, out);
    }
    // Handle LoadArray statements (reading from an array element)
    else if (stmt instanceof LoadArray loadArray && ConstantPropagation.canHoldInt(loadArray.getLValue())) {
        return handleLoadArray(loadArray, in, out);
    }
    // Handle StoreField statements (writing to a field)
    else if (stmt instanceof StoreField storeField) {
        return handleStoreField(storeField, in, out);
    }
    // Handle StoreArray statements (writing to an array element)
    else if (stmt instanceof StoreArray storeArray) {
        return handleStoreArray(storeArray, in, out);
    }
    // For other statement types, delegate to the base constant propagation analysis
    else {
        return cp.transferNode(stmt, in, out);
    }
}

/**
 * Handles LoadField statements by propagating constant values from possible store sites.
 * For static fields, values are collected from all stores to the same static field.
 * For instance fields, values are collected from stores via alias variables.
 * 
 * @param loadField the LoadField statement to process
 * @param in the input fact
 * @param out the output fact
 * @return true if the output fact changed
 */
private boolean handleLoadField(LoadField loadField, CPFact in, CPFact out) {
    Var lVar = loadField.getLValue(); // Target variable receiving the loaded value
    CPFact gen = new CPFact(); // Fact for generated constants from store sites
    CPFact inTmp = in.copy();  // Temporary copy of input fact for modification

    Value resValue = null; // Accumulated value from relevant store statements
    DataflowResult<Stmt, CPFact> dataflowResult = this.solver.getResult();

    if (loadField.isStatic()) {
        // Static field: collect values from all stores to the same static field
        JField field = loadField.getFieldRef().resolve();
        Set<StoreField> storeFields = staticFieldStore.getOrDefault(field, new HashSet<>());
        for (StoreField storeField : storeFields) {
            Value storeValue = dataflowResult.getOutFact(storeField).get(storeField.getRValue());
            resValue = cp.meetValue(resValue, storeValue); // Meet values to handle multiple stores
        }
    } else {
        // Instance field: collect values from stores via alias variables
        Var base = ((InstanceFieldAccess) loadField.getFieldAccess()).getBase();
        JField field = loadField.getFieldRef().resolve();
        Set<Var> aliases = allVarAliases.getOrDefault(base, new HashSet<>());
        for (Var alias : aliases) {
            for (StoreField storeField : alias.getStoreFields()) {
                if (storeField.getFieldRef().resolve() == field) {
                    Value storeValue = dataflowResult.getOutFact(storeField).get(storeField.getRValue());
                    resValue = cp.meetValue(resValue, storeValue);
                }
            }
        }
    }

    // Update output if a value was found from store sites
    if (resValue != null) {
        gen.update(lVar, resValue); // Propagate the constant to the target variable
        inTmp.remove(lVar); // Remove the old value to avoid duplication
    }

    // Combine generated facts with the modified input fact
    boolean isChange = out.copyFrom(gen);
    return out.copyFrom(inTmp) || isChange;
}

/**
 * Handles LoadArray statements by propagating constant values from store sites
 * with matching array indices. Considers alias variables and index values.
 * 
 * @param loadArray the LoadArray statement to process
 * @param in the input fact
 * @param out the output fact
 * @return true if the output fact changed
 */
private boolean handleLoadArray(LoadArray loadArray, CPFact in, CPFact out) {
    Var lVar = loadArray.getLValue(); // Target variable receiving the loaded value
    CPFact gen = new CPFact(); // Fact for generated constants from store sites
    CPFact inTmp = in.copy();  // Temporary copy of input fact for modification

    Var base = loadArray.getArrayAccess().getBase();
    Value loadIndexValue = in.get(loadArray.getArrayAccess().getIndex()); // Index value at load site
    Value resValue = null; // Accumulated value from relevant store statements
    DataflowResult<Stmt, CPFact> dataflowResult = this.solver.getResult();
    Set<Var> aliases = allVarAliases.getOrDefault(base, new HashSet<>());

    // Iterate over alias variables and their store array statements
    for (Var alias : aliases) {
        for (StoreArray storeArray : alias.getStoreArrays()) {
            Value storeIndexValue = dataflowResult.getInFact(storeArray).get(storeArray.getArrayAccess().getIndex());
            // Check if indices match: both constants with same value, or at least one is NAC
            if (isIndexMatch(loadIndexValue, storeIndexValue)) {
                Value storeValue = dataflowResult.getOutFact(storeArray).get(storeArray.getRValue());
                resValue = cp.meetValue(resValue, storeValue);
            }
        }
    }

    // Update output if a value was found from store sites
    if (resValue != null) {
        gen.update(lVar, resValue);
        inTmp.remove(lVar);
    }

    // Combine generated facts with the modified input fact
    boolean isChange = out.copyFrom(gen);
    return out.copyFrom(inTmp) || isChange;
}

/**
 * Checks if two array indices match for constant propagation purposes.
 * Indices match if both are constants with the same value, or at least one is NAC
 * (Not a Constant), which represents uncertainty.
 * 
 * @param loadIndex the index value at the load site
 * @param storeIndex the index value at the store site
 * @return true if indices are considered matching
 */
private boolean isIndexMatch(Value loadIndex, Value storeIndex) {
    return (loadIndex.isConstant() && storeIndex.isConstant() && loadIndex.getConstant() == storeIndex.getConstant()) ||
           (loadIndex.isConstant() && storeIndex.isNAC()) ||
           (loadIndex.isNAC() && storeIndex.isConstant()) ||
           (loadIndex.isNAC() && storeIndex.isNAC());
}

/**
 * Handles StoreField statements by performing base constant propagation and
 * triggering updates for dependent load statements via alias analysis.
 * 
 * @param storeField the StoreField statement to process
 * @param in the input fact
 * @param out the output fact
 * @return true if the output fact changed
 */
private boolean handleStoreField(StoreField storeField, CPFact in, CPFact out) {
    // First, perform standard constant propagation for the store
    boolean isChange = cp.transferNode(storeField, in, out);

    // If the fact changed, add dependent load statements to the worklist
    if (isChange) {
        if (storeField.isStatic()) {
            // Static field: notify all loads of the same static field
            JField field = storeField.getFieldRef().resolve();
            Set<LoadField> loadFields = staticFieldLoad.getOrDefault(field, new HashSet<>());
            for (LoadField loadField : loadFields) {
                solver.addWorkList(loadField);
            }
        } else {
            // Instance field: notify loads via alias variables
            Var base = ((InstanceFieldAccess) storeField.getFieldAccess()).getBase();
            Set<Var> aliases = allVarAliases.getOrDefault(base, new HashSet<>());
            for (Var alias : aliases) {
                for (LoadField loadField : alias.getLoadFields()) {
                    solver.addWorkList(loadField);
                }
            }
        }
    }
    return isChange;
}

/**
 * Handles StoreArray statements by performing base constant propagation and
 * triggering updates for dependent load statements via alias analysis.
 * 
 * @param storeArray the StoreArray statement to process
 * @param in the input fact
 * @param out the output fact
 * @return true if the output fact changed
 */
private boolean handleStoreArray(StoreArray storeArray, CPFact in, CPFact out) {
    // First, perform standard constant propagation for the store
    boolean isChange = cp.transferNode(storeArray, in, out);

    // If the fact changed, add dependent load statements to the worklist
    if (isChange) {
        Var base = storeArray.getArrayAccess().getBase();
        Set<Var> aliases = allVarAliases.getOrDefault(base, new HashSet<>());
        for (Var alias : aliases) {
            for (LoadArray loadArray : alias.getLoadArrays()) {
                solver.addWorkList(loadArray);
            }
        }
    }
    return isChange;
}


    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        CPFact outTmp = out.copy();
        Optional<LValue> def = edge.getSource().getDef();
        if(def.isPresent()) {
            if(def.get() instanceof Var var) {
                outTmp.remove(var);
            }
        }

        return outTmp;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        CPFact outTmp = callSiteOut.copy();
        CPFact cpFact = new CPFact();

        List<Var> params = edge.getCallee().getIR().getParams();
        if(edge.getSource() instanceof Invoke invokeStmt) {
            List<Var> args = invokeStmt.getInvokeExp().getArgs();
            for (int i = 0; i<params.size(); i++) {
                cpFact.update(params.get(i), outTmp.get(args.get(i)));
            }
        }
        return cpFact;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        CPFact cpFact = new CPFact();

        Collection<Var> returnVars = edge.getReturnVars();
        List<Value> values = returnVars.stream().map(returnOut::get).toList();
        if(values.size() > 0) {
            Value resultValue = values.get(0);
            for(int i=1; i<values.size(); i++) {
                resultValue = cp.meetValue(resultValue, values.get(i));
            }

            Optional<LValue> def = edge.getCallSite().getDef();
            if(def.isPresent() && def.get() instanceof Var sourceValue) {
                cpFact.update(sourceValue, resultValue);
            }
        }

        return cpFact;
    }
}
