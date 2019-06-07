package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;

import com.ibm.wala.analysis.typeInference.TypeInference;
import com.ibm.wala.ssa.*;
import com.ibm.wala.types.TypeName;
import com.ibm.wala.types.TypeReference;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import org.apache.bcel.classfile.Utility;

import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ClassUtils.getType;

/**
 * This visitor fills types for wala vars, by using Wala Type inference.
 */
public class StaticTypeIVisitor implements SSAInstruction.IVisitor {
    public final VarTypeTable varTypeTable;
    private IR ir;
    private Integer firstUse;
    private Integer lastDef;

    public StaticTypeIVisitor(IR ir, VarTypeTable varTypeTable, Pair<Integer, Integer> firstUseLastDef) {
        this.ir = ir;
        this.varTypeTable = varTypeTable;
        this.firstUse = firstUseLastDef.getFirst();
        this.lastDef = firstUseLastDef.getSecond();
    }

    @Override
    public void visitGoto(SSAGotoInstruction ssaGotoInstruction) {
    }

    @Override
    public void visitArrayLoad(SSAArrayLoadInstruction ins) {
        populateVars(ins, ins.getArrayRef());
        populateVars(ins, ins.getIndex());
        populateVars(ins, ins.getDef());
    }

    @Override
    public void visitArrayStore(SSAArrayStoreInstruction ins) {
        populateVars(ins, ins.getArrayRef());
        populateVars(ins, ins.getIndex());
        populateVars(ins, ins.getValue());

    }

    @Override
    public void visitBinaryOp(SSABinaryOpInstruction ins) {
        populateVars(ins, ins.getUse(0));
        populateVars(ins, ins.getUse(1));
        populateVars(ins, ins.getDef());
    }

    @Override
    public void visitUnaryOp(SSAUnaryOpInstruction ins) {
        populateVars(ins, ins.getDef());
        populateVars(ins, ins.getUse(0));
    }

    @Override
    public void visitConversion(SSAConversionInstruction ins) {
        populateVars(ins, ins.getUse(0));
        populateVars(ins, ins.getDef());

    }

    @Override
    public void visitComparison(SSAComparisonInstruction ins) {
        populateVars(ins, ins.getUse(0));
        populateVars(ins, ins.getUse(1));
        populateVars(ins, ins.getDef());

    }

    @Override
    public void visitConditionalBranch(SSAConditionalBranchInstruction ins) {
        populateVars(ins, ins.getUse(0));
        populateVars(ins, ins.getUse(1));
    }

    @Override
    public void visitSwitch(SSASwitchInstruction ins) {
        populateVars(ins, ins.getUse(0));
        populateVars(ins, ins.getDef());
    }

    @Override
    public void visitReturn(SSAReturnInstruction ins) {
        populateVars(ins, ins.getUse(0));
    }

    @Override
    public void visitGet(SSAGetInstruction ins) {
        populateVars(ins, ins.getRef());
        populateVars(ins, ins.getDef());
    }

    @Override
    public void visitPut(SSAPutInstruction ins) {
        if (ins.isStatic())
            populateVars(ins, ins.getUse(0));
        else
            populateVars(ins, ins.getUse(1));
        populateVars(ins, ins.getRef());
    }

    @Override
    public void visitInvoke(SSAInvokeInstruction ins) {

        for (int i = 0; i < ins.getNumberOfParameters(); i++) {
            populateVars(ins, ins.getUse(i));
        }

        for (int i = 0; i < ins.getNumberOfReturnValues(); i++) {
            populateVars(ins, ins.getReturnValue(i));
        }
    }

    @Override
    public void visitNew(SSANewInstruction ssaNewInstruction) {
    }

    @Override
    public void visitArrayLength(SSAArrayLengthInstruction ins) {
        populateVars(ins, ins.getArrayRef());
        populateVars(ins, ins.getDef());
    }

    @Override
    public void visitThrow(SSAThrowInstruction ssaThrowInstruction) {
    }

    @Override
    public void visitMonitor(SSAMonitorInstruction ssaMonitorInstruction) {

    }

    @Override
    public void visitCheckCast(SSACheckCastInstruction ins) {
        populateVars(ins, ins.getUse(0));
        populateVars(ins, ins.getDef());
    }

    @Override
    public void visitInstanceof(SSAInstanceofInstruction ins) {
        populateVars(ins, ins.getUse(0));
        populateVars(ins, ins.getDef());
    }

    @Override
    public void visitPhi(SSAPhiInstruction ins) {
        for (int i = 0; i < ins.getNumberOfUses(); i++) {
            populateVars(ins, ins.getUse(i));
        }
        populateVars(ins, ins.getDef());
    }

    @Override
    public void visitPi(SSAPiInstruction ssaPiInstruction) {

    }

    @Override
    public void visitGetCaughtException(SSAGetCaughtExceptionInstruction ssaGetCaughtExceptionInstruction) {
    }

    @Override
    public void visitLoadMetadata(SSALoadMetadataInstruction ssaLoadMetadataInstruction) {

    }

// SH: Used only to populate types using wala inference.

    public void populateVars(SSAInstruction ins, int var) {
        if ((varTypeTable.lookup(var) == null)
                && (var != -1)
                && (((firstUse == null || var >= firstUse) && (lastDef == null || var <= lastDef))
                //SH: case of a method region where there aren't really boundaries.
                    || ((firstUse != null && firstUse == -100) && (lastDef != null && lastDef == -100)))) {
            if (ir.getSymbolTable().isConstant(var) && ir.getSymbolTable().isNullConstant(var)) {
                varTypeTable.add(var, "int");
                return;
            }
            String type;
            TypeName typeName = null;
            TypeReference typeRef = (TypeInference.make(ir, true)).getType(var).getTypeReference();
            if (typeRef != null) typeName = typeRef.getName();
            if (typeName == null) return;
            if (typeName.isPrimitiveType()) type = Utility.signatureToString(typeName.toString());
            else {
                type = getType(typeName);
            }
//            varTypeTable.add(var, (TypeInference.make(ir, true)).getType(var).toString());
            varTypeTable.add(var, type);
        }
    }
}

