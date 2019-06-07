package gov.nasa.jpf.symbc.veritesting.ast.transformations.substitution;

import com.ibm.wala.classLoader.CallSiteReference;
import com.ibm.wala.shrikeBT.IInvokeInstruction;
import com.ibm.wala.shrikeCT.InvalidClassFileException;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.ssa.SymbolTable;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.util.strings.Atom;
import gov.nasa.jpf.symbc.VeritestingListener;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.VeritestingMain;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.JITAnalysis;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.StatisticManager;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.DynamicTable;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.SPFCases.SPFCaseList;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Uniquness.UniqueRegion;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.removeEarlyReturns.RemoveEarlyReturns;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.CreateStaticRegions;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticRegion;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.ExprVisitorAdapter;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.FixedPointAstMapVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.StmtPrintVisitor;
import gov.nasa.jpf.vm.StackFrame;
import gov.nasa.jpf.vm.ThreadInfo;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.IntConstant;
import za.ac.sun.cs.green.expr.Variable;

import java.util.*;

import static gov.nasa.jpf.symbc.VeritestingListener.printRegionDigest;
import static gov.nasa.jpf.symbc.VeritestingListener.veritestingMode;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;
import static gov.nasa.jpf.symbc.veritesting.VeritestingMain.skipRegionStrings;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ClassUtils.getSuperClassList;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.SPFToGreenExpr;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.SpfUtil.createSPFVariableForType;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.WalaUtil.makeConstantFromWala;

/**
 * The Substitution Transformation is responsible for replacing all vars with their symbolic values if found, as well as the substitution of all constant vars.
 * Substitution Transformation is done in a general way depending on the type of the StaticRegion. Mainly by allowing the substitution to replace variables with values by looking up the ValueSymbolTable, where the ValueSymbolTable is filled depending on the type of the region. If the region is not a method region, the ValueSymbolTable is filled by a priori pass where all "input" var values are discovered by inquiring SPF for their stack slot attribute. If the region is a method region then the ValueSymbolTable is filled up by the caller by filling up vars/values of the parameters.
 * In this transformation, constants are also discovered as part of the process.
 */
public class SubstitutionVisitor extends FixedPointAstMapVisitor {
    private ExprVisitorAdapter<Expression> eva;
    public final DynamicRegion dynRegion;
    public final ThreadInfo ti;
    private Exception subsExp = null;
    private StaticRegionException sre = null;
    private boolean useVarTable = false;

    /**
     * This is used to identify if a path had spfCase instruction that requires prouning the path. The flag is used
     * to stop embedding high order region along that path.
     */
    private boolean spfCasePath = false;


    public void setSomethingChanged(boolean change) {
        this.somethingChanged = change;
    }

    public boolean getChange() {
        return somethingChanged;
    }

    public void setValueSymbolTable(DynamicTable valueSymbolTable) {
        ((ExprSubstitutionVisitor) eva.theVisitor).setValueSymbolTable(valueSymbolTable);
    }

    public DynamicTable getValueSymbolTable() {
        return ((ExprSubstitutionVisitor) eva.theVisitor).getValueSymbolTable();
    }

    private SubstitutionVisitor(ThreadInfo ti, DynamicRegion dynRegion,
                                DynamicTable valueSymbolTable, boolean useVarTable) {
        super(new ExprSubstitutionVisitor(ti, dynRegion, valueSymbolTable));
        this.ti = ti;
        this.dynRegion = dynRegion;
        eva = super.eva;
        this.useVarTable = useVarTable;

    }


    @Override
    public Stmt visit(AssignmentStmt a) {
        return new AssignmentStmt(a.lhs, eva.accept(a.rhs));
    }

    @Override
    public Stmt visit(ArrayLoadInstruction c) {
        return new ArrayLoadInstruction(c.getOriginal(),
                eva.accept(c.arrayref),
                eva.accept(c.index),
                c.elementType,
                c.def);
    }

    @Override
    public Stmt visit(ArrayStoreInstruction c) {
        return new ArrayStoreInstruction(c.getOriginal(),
                eva.accept(c.arrayref),
                eva.accept(c.index),
                c.elementType,
                eva.accept(c.assignExpr));
    }

    @Override
    public Stmt visit(GetInstruction c) {
        return new GetInstruction(c.getOriginal(),
                c.def,
                eva.accept(c.ref),
                c.field);
    }

    @Override
    public Stmt visit(ArrayLengthInstruction c) {
        return new ArrayLengthInstruction(c.getOriginal(), eva.accept(c.arrayref), c.def);
    }

    @Override
    public Stmt visit(NewInstruction c) {
        spfCasePath = true;
        return new NewInstruction(c.getOriginal());
    }

    @Override
    public Stmt visit(ThrowInstruction c) {
        spfCasePath = true;
        return new ThrowInstruction(c.getOriginal());
    }


    /**
     * While visiting IfThenElse, it is responsible for resetting the spfCasePath, if on one path of its branches an SPFCase instruction was discoverd, such as throw or object creation, if this happens then along that path, there should be no high order regions inlined. And when the branch returns the flag needs to be reset and we need to explore the other side of the branch.
     *
     * @param c
     * @return
     */
    @Override
    public Stmt visit(IfThenElseStmt c) {
        Expression cond = eva.accept(c.condition);
        boolean oldSpfPath = this.spfCasePath;
        Stmt thenStmt = c.thenStmt.accept(this);
        if (!oldSpfPath && spfCasePath)
            spfCasePath = false;

        Stmt elseStmt = c.elseStmt.accept(this);
        if (!oldSpfPath && spfCasePath)
            spfCasePath = false;

        return new IfThenElseStmt(c.original, cond, thenStmt, elseStmt);
    }

    @Override
    public Stmt visit(ReturnInstruction c) {
        return new ReturnInstruction(c.getOriginal(), eva.accept(c.rhs));
    }


    @Override
    public Stmt visit(PhiInstruction c) {
        Expression[] rhs = new Expression[c.rhs.length];
        for (int i = 0; i < rhs.length; i++) {
            rhs[i] = eva.accept(c.rhs[i]);
        }
        //hack here to populate the type of the def - there is an implicit side effect.
        eva.accept(c.def);

        return new PhiInstruction(c.getOriginal(),
                c.def,
                rhs);
    }

    /**
     * Visits an InvokeInstruction by attempting to inline static method regions.
     *
     * @param c Invoke Instruction to be visited.
     * @return A new statement that might include an inlined method region for static invocations.
     */

    @Override
    public Stmt visit(InvokeInstruction c) {

        ArrayList<Expression> values = new ArrayList<Expression>();
        Expression[] params = new Expression[c.params.length];
        for (int i = 0; i < params.length; i++) {
            params[i] = eva.accept(c.params[i]);
            values.add(params[i]); // in case of non static, the first parameter needs to be de-referenced because it will refer to an object class.
        }

        InvokeInstruction newC = new InvokeInstruction(c.getOriginal(), c.result, params);

        if (!spfCasePath) {
            SSAInvokeInstruction instruction = newC.getOriginal();
            IInvokeInstruction.IDispatch invokeCode = instruction.getCallSite().getInvocationCode();
            if ((invokeCode == IInvokeInstruction.Dispatch.STATIC)
                    || (invokeCode == IInvokeInstruction.Dispatch.VIRTUAL
                    || (invokeCode == IInvokeInstruction.Dispatch.INTERFACE)
                    || (invokeCode == IInvokeInstruction.Dispatch.SPECIAL))) {

                Pair<String, StaticRegion> keyRegionPair = null;
                if (VeritestingListener.jitAnalysis) {
                    try {
                        keyRegionPair = jitFindMethodRegion(ti, newC);
                    } catch (StaticRegionException e) {
                        sre = new StaticRegionException("Cannot summarize invoke in " + instruction.toString());
                        if (firstException == null) {
                            firstException = sre;
                            skipRegionStrings.add("Cannot summarize invoke");
                            return newC;
                        }
                    }
                } else
                    keyRegionPair = findMethodRegion(ti, newC);

                if (keyRegionPair == null) //case where we couldn't grap the method region, usually because a concrete reference does not exists.
                    return newC;
                StaticRegion hgOrdStaticRegion = keyRegionPair.getSecond();
                if (hgOrdStaticRegion != null) {
                    ++StatisticManager.thisHighOrdCount;
                    String key = keyRegionPair.getFirst();

                    System.out.println("\n********** High Order Region Discovered for region: " + key + "\n");
                    System.out.println("\n---------- STARTING Inlining Transformation for region: ---------------\n" + StmtPrintVisitor.print(hgOrdStaticRegion.staticStmt) + "\n");
                    DynamicRegion uniqueHgOrdDynRegion = null;
                    try {
                        hgOrdStaticRegion = RemoveEarlyReturns.removeEarlyReturns(hgOrdStaticRegion);
                        uniqueHgOrdDynRegion = UniqueRegion.execute(hgOrdStaticRegion);

                    } catch (CloneNotSupportedException e) {
                        if (firstException == null) {
                            subsExp = e;
                            return newC;
                        }
                    } catch (StaticRegionException e) {
                        if (firstException == null) {
                            sre = e;
                            return newC;
                        }
                    } catch (InvalidClassFileException e) {
                        if (firstException == null) {
                            subsExp = e;
                            return newC;
                        }
                    }
                    DynamicTable hgOrdValueSymbolTable = new DynamicTable<Expression>("var-value table",
                            "var",
                            "value",
                            uniqueHgOrdDynRegion.slotParamTable.getKeys(),
                            values);

                    Pair<Stmt, DynamicTable> hgOrdUniqueStmtType = null;
                    try {
                        hgOrdUniqueStmtType = attemptHighOrderRegion(uniqueHgOrdDynRegion, hgOrdValueSymbolTable);
                    } catch (StaticRegionException e) {
                        if (firstException == null) {
                            sre = e;
                            return newC;
                        }
                    }
                    Stmt hgOrdStmt = hgOrdUniqueStmtType.getFirst();
                    DynamicTable hgOrdTypeTable = hgOrdUniqueStmtType.getSecond();

                    dynRegion.varTypeTable.mergeTable(hgOrdTypeTable);
                    Stmt returnStmt;
                    somethingChanged = true;
                    if (newC.result.length == 1) {
                        Pair<Stmt, Expression> stmtRetPair = getStmtRetExp(hgOrdStmt);
                        returnStmt = new AssignmentStmt(newC.result[0], stmtRetPair.getSecond());
                        return new CompositionStmt(stmtRetPair.getFirst(), returnStmt);
                    } else {
                        return getStmtRetExp(hgOrdStmt).getFirst();
                    }
                } else {
                    sre = new StaticRegionException("Cannot summarize invoke in " + instruction.toString());
                    if (firstException == null)
                        firstException = sre;
                    skipRegionStrings.add("Cannot summarize invoke");
                    return newC;
                }
            } else
                return newC;
        } else
            return newC;
    }

    /**
     * Attempts to substitute in a high order region.
     *
     * @param methodRegion          MethodRegion where the substitution is going to be attempted.
     * @param hgOrdValueSymbolTable Value symbol table for te MethodRegion, usually populated with the parameters.
     * @return A pair of substituted statement for the high order region as well as its VarTypeTable.
     */
    private Pair<Stmt, DynamicTable> attemptHighOrderRegion(
            DynamicRegion methodRegion,
            DynamicTable hgOrdValueSymbolTable) throws StaticRegionException {

        assert (methodRegion.isMethodRegion);
        hgOrdValueSymbolTable.mergeTable(fillValueSymbolTable(ti, methodRegion));
        SubstitutionVisitor visitor = new SubstitutionVisitor(ti, methodRegion, hgOrdValueSymbolTable, this.useVarTable);
        Pair highOrderPair = new Pair(methodRegion.dynStmt.accept(visitor), methodRegion.varTypeTable);
        if (!this.somethingChanged)
            this.somethingChanged = visitor.somethingChanged || (((ExprSubstitutionVisitor) visitor.eva.theVisitor).isSomethingChanged());

        return highOrderPair;
    }


    /****************** Methods for inlining method regions ******************/

    /**
     * Iterates over the Stmt to get the return statement seperated out of the reset of the statements.
     *
     * @param stmt A statement that ends with a return expression.
     * @return A pair of Statement and retrun Statment.
     */
    private Pair<Stmt, Expression> getStmtRetExp(Stmt stmt) {
        if (stmt instanceof CompositionStmt) {
            Pair<Stmt, Expression> stmtRetPair = getStmtRetExp(((CompositionStmt) stmt).s2);
            return stmtRetPair != null ? new Pair(new CompositionStmt(((CompositionStmt) stmt).s1, stmtRetPair.getFirst()), stmtRetPair.getSecond()) : new Pair(stmt, null);
        } else {
            if (stmt instanceof ReturnInstruction)
                return new Pair(SkipStmt.skip, (((ReturnInstruction) stmt).rhs));
            if ((stmt instanceof AssignmentStmt) && (((AssignmentStmt) stmt).lhs instanceof AstVarExpr))
                return new Pair(SkipStmt.skip, (((AssignmentStmt) stmt).rhs));
            else
                return null;
        }
    }

    /**
     * Attempts to find a mapping MethodRegion.
     *
     * @param c Current invoke instruction.
     * @return A pair of the key and the methodRegion if a matching could be found.
     */
    private Pair<String, StaticRegion> jitFindMethodRegion(ThreadInfo ti, InvokeInstruction c) throws StaticRegionException {


        SSAInvokeInstruction instruction = c.getOriginal();
        MethodReference methodReference = instruction.getDeclaredTarget();
        CallSiteReference site = instruction.getCallSite();


        String currClassName = null;
        if (!instruction.isStatic() && !instruction.isSpecial()) {
            if (c.params[0] instanceof IntConstant) //if the first param is a constant, then it is already a reference and it isn't in the varTypeTable, instead we need to ask SPF for it.
                currClassName = ti.getHeap().get(((IntConstant) c.params[0]).getValue()).getClassInfo().getName();
            else if (VeritestingListener.simplify &&
                    dynRegion.constantsTable != null &&
                    dynRegion.constantsTable.lookup((Variable) c.params[0]) instanceof IntConstant) { //check if we can find it in the constant table.

                IntConstant objRef = (IntConstant) dynRegion.constantsTable.lookup((Variable) c.params[0]);
                currClassName = ti.getHeap().get((objRef).getValue()).getClassInfo().getName();
            } else {
                if (useVarTable) {
                    Object type = dynRegion.varTypeTable.lookup(c.params[0]);
                    if (type != null)
                        currClassName = type.toString();
                    else
                        return null;
                } else
                    return null;
            }
        } else {
            Atom packageNameAtom = methodReference.getDeclaringClass().getName().getPackage();
            String packageName = packageNameAtom != null ? packageNameAtom.toString().replaceAll("/", ".") : null;
            currClassName = (packageName != null ? packageName + "." : "") + methodReference.getDeclaringClass().getName().getClassName().toString();
        }

        String dynamicClassName = convertToJavaName(currClassName);

/*        if (!Character.isLetterOrDigit(dynamicClassName.charAt(dynamicClassName.length() - 1))) {
            dynamicClassName = dynamicClassName.substring(0, dynamicClassName.length() - 2);
        }
        */


        ArrayList<String> classList = getSuperClassList(ti, currClassName);
        Atom methodName = methodReference.getName();
        String methodSignature = methodReference.getSignature();
        methodSignature = methodSignature.substring(methodSignature.indexOf('('));
        String key = CreateStaticRegions.constructMethodIdentifier(dynamicClassName + "." + methodName + methodSignature);
        if (veritestingMode <= 2) return new Pair(key, null);
        for (String className : classList) {
            key = CreateStaticRegions.constructMethodIdentifier(className + "." + methodName + methodSignature);
            //StaticRegion staticRegion = VeritestingMain.veriRegions.get(key);
            String jvmMethodName = methodName.toString() + methodSignature; //methodReference.getSignature();
            StaticRegion staticRegion = JITAnalysis.discoverAllClassAndGetRegion(className, jvmMethodName, key);
            if (staticRegion != null) {
                if (printRegionDigest)
                    VeritestingListener.regionDigest.append("\n" + staticRegion.staticStmt.toString());
                return new Pair(key, staticRegion);
            }
        }
        return new Pair(key, null);
    }


    /**
     * Attempts to find a mapping MethodRegion.
     *
     * @param c Current invoke instruction.
     * @return A pair of the key and the methodRegion if a matching could be found.
     */
    private Pair<String, StaticRegion> findMethodRegion(ThreadInfo ti, InvokeInstruction c) {

        SSAInvokeInstruction instruction = c.getOriginal();
        MethodReference methodReference = instruction.getDeclaredTarget();
        CallSiteReference site = instruction.getCallSite();


        String currClassName = null;
        if (!instruction.isStatic() && !instruction.isSpecial()) {
            if (c.params[0] instanceof IntConstant) //if the first param is a constant, then it is already a reference and it isn't in the varTypeTable, instead we need to ask SPF for it.
                currClassName = ti.getHeap().get(((IntConstant) c.params[0]).getValue()).getClassInfo().getName();
            else if (VeritestingListener.simplify &&
                    dynRegion.constantsTable != null &&
                    dynRegion.constantsTable.lookup((Variable) c.params[0]) instanceof IntConstant) { //check if we can find it in the constant table.

                IntConstant objRef = (IntConstant) dynRegion.constantsTable.lookup((Variable) c.params[0]);
                currClassName = ti.getHeap().get((objRef).getValue()).getClassInfo().getName();
            } else {
                if (useVarTable) {
                    Object type = dynRegion.varTypeTable.lookup(c.params[0]);
                    if (type != null)
                        currClassName = type.toString();
                    else
                        return null;
                } else
                    return null;
            }
        } else {
            Atom packageNameAtom = methodReference.getDeclaringClass().getName().getPackage();
            String packageName = packageNameAtom != null ? packageNameAtom.toString().replaceAll("/", ".") : null;
            currClassName = (packageName != null ? packageName + "." : "") + methodReference.getDeclaringClass().getName().getClassName().toString();
        }

        String dynamicClassName = currClassName;
        if (!Character.isLetterOrDigit(dynamicClassName.charAt(dynamicClassName.length() - 1))) {
            dynamicClassName = dynamicClassName.substring(0, dynamicClassName.length() - 2);
        }
        ArrayList<String> classList = getSuperClassList(ti, currClassName);
        Atom methodName = methodReference.getName();
        String methodSignature = methodReference.getSignature();
        methodSignature = methodSignature.substring(methodSignature.indexOf('('));
        String key = CreateStaticRegions.constructMethodIdentifier(dynamicClassName + "." + methodName + methodSignature);
        for (String className : classList) {
            key = CreateStaticRegions.constructMethodIdentifier(className + "." + methodName + methodSignature);
            StaticRegion staticRegion = VeritestingMain.veriRegions.get(key);
            if (staticRegion != null) {
                if (printRegionDigest)
                    VeritestingListener.regionDigest.append("\n" + staticRegion.staticStmt.toString());
                return new Pair(key, staticRegion);
            }
        }
        return new Pair(key, null);
    }


    private String convertToJavaName(String currClassName) {
        String javaName = currClassName;
        if (javaName != null) {
            if (!Character.isLetterOrDigit(javaName.charAt(javaName.length() - 1))) {
                javaName = javaName.substring(0, javaName.length() - 1);
            }
            if (javaName.charAt(0) == 'L') {
                javaName = javaName.substring(1, javaName.length());
            }

            javaName = javaName.replaceAll("/", ".");
        }
        return javaName;
    }


    /**
     * Fills out the values of all vars that could be discovered in the region.
     *
     * @param ti        Current executing thread.
     * @param dynRegion DynamicRegion for which the ValueSymbolTable is going to be created.
     * @return Populated ValueSymbolTable for variables in the static region.
     */
    private static DynamicTable fillValueSymbolTable(ThreadInfo ti, DynamicRegion dynRegion) throws StaticRegionException {

        StackFrame sf = ti.getTopFrame();

        DynamicTable valueSymbolTable = new DynamicTable("var-value table", "var", "value");
        List<Variable> regionVarSet = dynRegion.varTypeTable.getKeys();

        for (Object var : regionVarSet) {
            if (var instanceof Variable) {
                Integer slot = (Integer) dynRegion.inputTable.lookup(var);
                if ((slot != null) && (!dynRegion.isMethodRegion)) {
                    String varType = sf.getLocalVariableType(slot);
                    gov.nasa.jpf.symbc.numeric.Expression varValueExp;
                    varValueExp = (gov.nasa.jpf.symbc.numeric.Expression) sf.getLocalAttr(slot);
                    if (varValueExp == null) {
                        int varValue = sf.getLocalVariable(slot);
                        varValueExp = createSPFVariableForType(sf, varValue, varType);

                    }
                    Expression greenValue = SPFToGreenExpr(varValueExp);
                    valueSymbolTable.add(var, greenValue);

                } else { //not a stack slot var, try to check if it is a constant from wala
                    SymbolTable symbolTable = dynRegion.ir.getSymbolTable();
                    if (var instanceof WalaVarExpr)
                        if ((((WalaVarExpr) var).number > -1) && (symbolTable.isConstant(((WalaVarExpr) var).number))) {
                            Expression greenValue = makeConstantFromWala(dynRegion.ir.getSymbolTable(), ((WalaVarExpr) var).number);
                            valueSymbolTable.add(var, greenValue);
                        }
                }
            }
        }
        return valueSymbolTable;
    }


    /**
     * Executes substitution over a non-method region.
     *
     * @return A Dynamic Region that has been substituted by symbolic or concerete values for inputs as well as constants being substituted.
     */


    public DynamicRegion execute() {

        Stmt dynStmt = dynRegion.dynStmt.accept(this);
        /*if (this.sre != null) throwException(this.sre, INSTANTIATION);
        if (this.cne != null) throwException(new StaticRegionException(this.cne.getMessage()), INSTANTIATION);
        */
        this.instantiatedRegion = new DynamicRegion(dynRegion, dynStmt, new SPFCaseList(), null, null, dynRegion.earlyReturnResult);

        System.out.println("\n--------------- SUBSTITUTION TRANSFORMATION for: " + VeritestingListener.key + " ---------------\n");
        System.out.println(StmtPrintVisitor.print(dynRegion.dynStmt));
        dynRegion.slotParamTable.print();
        dynRegion.outputTable.print();
        dynRegion.varTypeTable.print();

        System.out.println("\n--------------- AFTER SUBSTITUTION TRANSFORMATION for: " + VeritestingListener.key + " ---------------\n");
        System.out.println(StmtPrintVisitor.print(instantiatedRegion.dynStmt));
        instantiatedRegion.slotParamTable.print();
        instantiatedRegion.outputTable.print();
        instantiatedRegion.varTypeTable.print();
        System.out.println("Stack output: " + dynRegion.stackOutput);

        if (!this.somethingChanged)
            this.somethingChanged = ((ExprSubstitutionVisitor) eva.theVisitor).isSomethingChanged();
        return instantiatedRegion;
    }


    public static SubstitutionVisitor create(ThreadInfo ti, DynamicRegion dynRegion, int iterationNumber, boolean useVarTable) {

        DynamicTable valueSymbolTable = null;

        SubstitutionVisitor visitor = null;
        assert (!dynRegion.isMethodRegion);
        if (iterationNumber > 1) // create an empty valueSymbolTable because really we are using substitution here as an entry to the high order region.
            valueSymbolTable = new DynamicTable("var-value table", "var", "value");
        else
            try {
                valueSymbolTable = SubstitutionVisitor.fillValueSymbolTable(ti, dynRegion);
            } catch (StaticRegionException e) {
                visitor = new SubstitutionVisitor(ti, dynRegion, valueSymbolTable, useVarTable);

                visitor.firstException = e;
                return visitor;
            }

        visitor = new SubstitutionVisitor(ti, dynRegion, valueSymbolTable, useVarTable);

        return visitor;

    }
}
