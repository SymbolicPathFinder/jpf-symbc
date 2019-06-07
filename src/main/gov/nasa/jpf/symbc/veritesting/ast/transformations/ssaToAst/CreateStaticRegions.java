package gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst;

import com.ibm.wala.cfg.Util;
import com.ibm.wala.classLoader.IBytecodeMethod;
import com.ibm.wala.shrikeCT.InvalidClassFileException;
import com.ibm.wala.ssa.*;
import com.ibm.wala.util.graph.Graph;
import com.ibm.wala.util.graph.dominators.Dominators;
import com.ibm.wala.util.graph.dominators.NumberedDominators;
import gov.nasa.jpf.symbc.VeritestingListener;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.ast.def.*;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment.SSAToStatIVisitor;
import gov.nasa.jpf.symbc.veritesting.ast.visitors.PrettyPrintVisitor;
import x10.wala.util.NatLoop;
import za.ac.sun.cs.green.expr.*;

import java.util.*;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.DONTKNOW;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.STATIC;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;
import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil.compose;
import static gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.SSAUtil.isConditionalBranch;
import static gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.SSAUtil.isLoopStart;

// TODO: MWW: In examining the debug output, it appears that the same classes and methods are visited multiple times.  Why?
// Vaibhav: In part, this happens because we visit every method three times, once for finding conditional regions, and
// twice again when we're running with VeritestingMain.methodAnalysis set to true. This is done by VeritestingMain.startAnalysis().

/**
 * This class creates our structure IR from the WALA SSA form, this is basically done by decompiling DAGs within a Java program.
 */
/*
Here we are essentially decompiling DAGs within a Java program.  The goals
        are two-fold:
        1. It should be accurate.  Any semantics violating decompilation steps
        will obviously cause SPF to misbehave
        2. It should be lightweight.  Any fixpoint algorithms may cost a lot
        in preprocessing.

         It does *not* need to be complete.  It is o.k. if 'continue's and 'break's
         cause the generation algorithm to fail; we will skip those regions.  As
         long as we aren't analyzing malware, this won't happen too often.

         One tricky bit involves figuring out the boundaries of complex 'if' conditions.

         It is not too bad; you look for "immediate self-contained subgraphs", that is,
         subgraphs where the initial node is immediately pre-dominated by the initial node
         and for the static region and whose successor nodes (up to the region terminus) are
         dominated (not necessarily immediately) by the initial node.

         For the things we want to analyze, there should be one (for if-no-else) or
         two (for if-else) of these regions.

         For if-no-else regions, it is clear what to use as the 'then' condition, but
         with if-else regions, it is not so clear.  We use the initial condition
         'then' branch to choose, but this is pretty arbitrary, and in fact WALA seems
         to reverse the if/else branches from the source code.  This is probably because
         the jump conditions are 'jump zero'.

         We create a successor map that jumps directly to these 'then' and 'else'
         elements, and generate the condition for the 'then' branch.  Thereafter, we
         can view the problem as one of nested self-contained subgraphs, which
         simplifies the rest of the region processing.

         Another tricky bit involves translating \phi instructions to \gammas.

         I keep track of the current "conditional path" at the point of the code I am translating.  This is a stack of
         (Expression x enum {Then, Else}) pairs.  For each edge between blocks in the block structure,
         I record the associated "conditional path".  So the type of this map (the blockConditionMap) is:
         (ISSABasicBlock x ISSABasicBlock) --> List of (Expression x enum {Then, Else})

         From here it is easy: I get the predecessor blocks of the block containing the \phi.  Then I look
         up the edges in the blockConditionMap.  From here, I know the condition stack leading to that
         branch.  I gather these together and make an if/then/else.

         If I see something like this:
         \phi(w2, w8, w16)

         ==> I look up predecessor blocks:
         (1, 5, 8)

         ==> I look up associated conditions from predecessor edges:
         (((c1, Then)),
         ((c1, Else), (c2, Then)),
         ((c1, Else), (c2, Else)))

         then construct an if/then/else from the result.

         Two things that make it slightly more interesting:
         1.) What about \phis for the merge of inner (nested) branches?  Since I record a stack of conditions from the beginning of the static region, I don't really want the conditions from branches that are out of scope of the inner branch.  At the meet block, I check the conditionStack depth, and remove that depth of elements from the front of each condition list.

         2.) How does one arrange subconditions in the if/then/else to minimize the size of conditions?
          This is why I keep track of whether the condition corresponds to the 'then' or 'else' branch. I do a split based on 'then' or 'else' and recursively organize the Gamma.  For example, the Gamma for the example above would be: Gamma(c1, w2, Gamma(c2, w8, w16)))

         I could do this with just the expressions, but it would be much more work to reconstruct the then and else branches (in fact I started with this and then wasted substantial time trying to rebuild the minimal ITE structure.
*/


public class CreateStaticRegions {

    private HashMap<ISSABasicBlock, Integer> seenLoopStartSet;
    private HashMap<String, StaticRegion> veritestingRegions;

    public static String constructRegionIdentifier(String methodSignature, int offset) {
        return methodSignature + "#" + offset;
    }

    /**
     * Create the key of a conditional region, by using the name as well as the bytecode offset of the last instruction in the first block that starts the region.
     *
     * @param ir  IR of the staticRegion.
     * @param blk The first block that identifies the begining of the region.
     * @return A string that is used as a key for the region.
     */
    public static String constructRegionIdentifier(IR ir, ISSABasicBlock blk) {
        int offset = -100;
        try {
            offset = ((IBytecodeMethod) (ir.getMethod())).getBytecodeIndex(blk.getLastInstructionIndex());
        } catch (InvalidClassFileException e) {
            e.printStackTrace();
        }
        if (offset == -100)
            try {
                throwException(new StaticRegionException("Cannot find the index of the first instruction in the region."), DONTKNOW);
            } catch (StaticRegionException e) {
                e.printStackTrace();
            }

        return constructRegionIdentifier(blk.getMethod().getSignature(), offset);
    }

    /**
     * Create the key of a Method region.
     *
     * @param methodSignature Signature of a method.
     * @return A string that is used as a key for the region.
     */
    public static String constructMethodIdentifier(String methodSignature) {
        return methodSignature;
    }

    public static String constructMethodIdentifier(ISSABasicBlock blk) {
        return constructMethodIdentifier(blk.getMethod().getSignature());
    }

    /*
    Contains a set of all the loops in the IR maintained as NatLoop objects
     */
    private final HashSet<NatLoop> loops;
    private IR ir;
    private Graph<ISSABasicBlock> domTree;

    /**
     * This is used for Phi instructions, where each edge in the graph is mapped to a list of conditions that represents the path up till that edge.
     */
    private Map<PhiEdge, List<PhiCondition>> blockConditionMap;

    Deque<PhiCondition> jitCurrentCondition = new LinkedList();
    private Set<ISSABasicBlock> jitVisitedBlocks = new HashSet<>();


    /**
     * Keeps track of the current conditions/depth while visiting nodes in the graph.
     */
    private Deque<PhiCondition> currentCondition;

    /**
     * for complex conditions, we want to record the then condition and successors.
     */
    private Map<ISSABasicBlock, Expression> thenCondition;
    private Map<ISSABasicBlock, ISSABasicBlock> thenSuccessor;
    private Map<ISSABasicBlock, ISSABasicBlock> elseSuccessor;
    private Map<ISSABasicBlock, Stmt> thenConditionSetup;

    /**
     * For memoization, so we don't visit the same blocks over and over.
     */
    private Set<ISSABasicBlock> visitedBlocks;
    // TODO: an optimization to be explored for future is to subclass the HashMap type
    // TODO: so we store *unsuccessful* regions.  This would allow us to do region
    // TODO: construction "on the fly" without revisiting unsuccessful regions multiple times.

    public CreateStaticRegions(IR ir, HashSet<NatLoop> loops) {
        blockConditionMap = new HashMap<>();
        currentCondition = new LinkedList<>();
        thenCondition = new HashMap<>();
        thenSuccessor = new HashMap<>();
        elseSuccessor = new HashMap<>();
        thenConditionSetup = new HashMap<>();
        visitedBlocks = new HashSet<>();
        this.loops = loops;
        seenLoopStartSet = new HashMap<>();

        this.ir = ir;

        /* MWW: added to determine complex conditions */
        SSACFG cfg = ir.getControlFlowGraph();
        NumberedDominators<ISSABasicBlock> dom = (NumberedDominators) Dominators.make(cfg, cfg.entry());
        this.domTree = dom.dominatorTree();
    }

    private void reset() {
        blockConditionMap = new HashMap<>();
        currentCondition = new LinkedList<>();
        jitVisitedBlocks = new HashSet<>();
    }

    public boolean isBranch(SSACFG cfg, ISSABasicBlock block) {
        return cfg.getNormalSuccessors(block).size() == 2;
    }

    /**
     * This creates a composition statement between two statements
     *
     * @param stmt1 First statement to be used in a composition.
     * @param stmt2 Second statement to be used in a composition.
     * @return A composition statement in RangerIR.
     */
    public Stmt conjoin(Stmt stmt1, Stmt stmt2) {
        if (stmt1 instanceof SkipStmt) {
            return stmt2;
        } else if (stmt2 instanceof SkipStmt) {
            return stmt1;
        } else {
            return new CompositionStmt(stmt1, stmt2);
        }
    }

    /**
     * This translate the last block in an identified region by visiting all its instructions and creating a Gamma if a Phi instruction was found.
     *
     * @param currentBlock The last block in the region.
     * @return A statement in RangerIR that represents the last block in the region.
     * @throws StaticRegionException
     */
    private Stmt translateTruncatedFinalBlock(ISSABasicBlock currentBlock) throws StaticRegionException {
        SSAToStatIVisitor visitor =
                new SSAToStatIVisitor(ir, currentBlock, blockConditionMap, currentCondition);
        Stmt stmt = SkipStmt.skip;
        for (SSAInstruction ins : currentBlock) {
            if (!(ins instanceof SSAPhiInstruction))
                return stmt;
            else {
                Stmt gamma = visitor.convert(ins);
                // This simplification causes problems in the LocalOutputInvariantVisitor in StaticRegion constructor
                // that tries to ensure that all local outputs in outputTable have a assignment using a gamma expression.
                // This part of the LocalOutputInvariantVisitor is now commented out (04/29/2019).
                /* Vaibhav: this simplification should not make a correctness difference unless we have a region that
                * writes the same value to a local variable on both sides of a branch. But, having this simplification
                * turned on causes the LocalOutputInvariantVisitor to not create a stack output for the lhs of such
                * gamma expressions. An example of this is in replace.amatch([C[CI)I#56 that ends on the instruction
                * at offset 62. Using this simplification, we now dont assume that such regions have a stack output and therefore
                * dont want such regions to end on a stack consuming instruction. These regions appear right before the
                * beginning of a loop and these gamma expressions are assigning a value that would be modified in the
                * loop. */
                if (gamma instanceof AssignmentStmt && ((AssignmentStmt) gamma).rhs instanceof GammaVarExpr) {
                    Expression exp1 = ((GammaVarExpr) ((AssignmentStmt) gamma).rhs).thenExpr;
                    Expression exp2 = ((GammaVarExpr) ((AssignmentStmt) gamma).rhs).elseExpr;
                    if (exp1.equals(exp2))
                        gamma = new AssignmentStmt(((AssignmentStmt) gamma).lhs, ((GammaVarExpr) ((AssignmentStmt) gamma).rhs).thenExpr);
                }
                stmt = conjoin(stmt, gamma);
            }
        }
        return stmt;
    }

    private Stmt jitTranslateTruncatedFinalBlock2(ISSABasicBlock currentBlock, Map<PhiEdge, List<PhiCondition>> insertedBlockConditionMap, Deque<PhiCondition> insertedCurrentCondition) throws StaticRegionException {
        SSAToStatIVisitor visitor =
                new SSAToStatIVisitor(ir, currentBlock, insertedBlockConditionMap, insertedCurrentCondition);
        Stmt stmt = SkipStmt.skip;
        for (SSAInstruction ins : currentBlock) {
            if (!(ins instanceof SSAPhiInstruction))
                return stmt;
            else {
                Stmt gamma = visitor.convert(ins);
                stmt = conjoin(stmt, gamma);
            }
        }
        return stmt;
    }


    /**
     * This translates "internal" blocks inside the region, these are blocks that are not the begining or the end of the region.
     *
     * @param currentBlock Current block that needs to be translated.
     * @return A statement in RangerIR that represents the translated statement.
     * @throws StaticRegionException An exception that indicates a problem in the translation.
     */
    private Stmt translateInternalBlock(ISSABasicBlock currentBlock) throws StaticRegionException {
        SSAToStatIVisitor visitor =
                new SSAToStatIVisitor(ir, currentBlock, blockConditionMap, currentCondition);
        Stmt stmt = SkipStmt.skip;
        for (SSAInstruction ins : currentBlock) {
            if ((ins instanceof SSAConditionalBranchInstruction) ||
                    (ins instanceof SSAGotoInstruction)) {
                // properly formed blocks will only have branches and gotos as the last instruction.
                // We will handle branches in attemptSubregion.
            } else {
                stmt = conjoin(stmt, visitor.convert(ins));
            }
        }
        return stmt;
    }

    private Stmt jitTranslateTruncatedFinalBlock(ISSABasicBlock currentBlock) throws StaticRegionException {
        SSAToStatIVisitor visitor =
                new SSAToStatIVisitor(ir, currentBlock, blockConditionMap, currentCondition);
        Stmt stmt = SkipStmt.skip;
        for (SSAInstruction ins : currentBlock) {
            if (ins instanceof SSAPhiInstruction) {
                // properly formed blocks will only have branches and gotos as the last instruction.
                // We will handle branches in attemptSubregion.
            } else {
                stmt = conjoin(stmt, visitor.convert(ins));
            }
        }
        return stmt;
    }


    /**
     * @param currentBlock
     * @return
     * @throws StaticRegionException
     */
    private Stmt jitTranslateTruncatedConditionalBlock(ISSABasicBlock currentBlock) throws StaticRegionException {
        SSAToStatIVisitor visitor =
                new SSAToStatIVisitor(ir, currentBlock, blockConditionMap, currentCondition);
        Stmt stmt = SkipStmt.skip;
        for (SSAInstruction ins : currentBlock) {
            if ((ins instanceof SSAConditionalBranchInstruction) ||
                    (ins instanceof SSAGotoInstruction) ||
                    (ins instanceof SSAPhiInstruction)) { //Phi instructions should have been translated in attemptConditionalSubregion
                // properly formed blocks will only have branches and gotos as the last instruction.
                // We will handle branches in attemptSubregion.
            } else {
                stmt = conjoin(stmt, visitor.convert(ins));
            }
        }
        return stmt;
    }


    /**
     * Gets the immediate dominator of a block.
     *
     * @param elem Block for which we want to find its immediate dominator.
     * @return Immediate dominator of a block.
     */
    private ISSABasicBlock getIDom(ISSABasicBlock elem) {
        assert (this.domTree.getPredNodeCount(elem) == 1);
        return (ISSABasicBlock) this.domTree.getPredNodes(elem).next();
    }


    /**
     * This method checks to see whether each node in a subgraph up to a terminus has a subgraph.
     *
     * @param entry    Entry block, from which a search/check starts.
     * @param terminus End block, where search/check should terminates.
     * @return True if the entry to the terminus is a self contained subregion.
     * @throws StaticRegionException Exception that indicates something went wrong during computation.
     */
    private boolean isSelfContainedSubgraph(ISSABasicBlock entry, ISSABasicBlock terminus) throws StaticRegionException {
        // trivial case.
        if (entry == terminus) {
            return false;
        }

        SSACFG cfg = ir.getControlFlowGraph();
        PriorityQueue<ISSABasicBlock> toVisit = SSAUtil.constructSortedBlockPQ();
        Set<ISSABasicBlock> visited = new HashSet<>();

        visited.add(entry);
        toVisit.addAll(SSAUtil.getNonReturnSuccessors(cfg, entry));

        while (!toVisit.isEmpty()) {
            ISSABasicBlock current = toVisit.remove();
            if (!visited.contains(current)) {
                visited.add(current);
                ISSABasicBlock immediatePreDom = getIDom(current);
                if (current == terminus) {
                    // because of priority queue, a non-empty queue means we have
                    // successor nodes beyond the terminus node, so error out.
                    if (!toVisit.isEmpty()) {
                        throwException(new StaticRegionException("isSelfContainedSubgraph: non-empty queue at return"), STATIC);
                    }
                    return true;
                } else if (!visited.contains(immediatePreDom)) {
                    // not self contained!
                    return false;
                } else {
                    SSAUtil.getNonReturnSuccessors(cfg, current).forEach(
                            succ -> SSAUtil.enqueue(toVisit, succ));
                }
            }
        }
        // This condition occurs when we have a region terminated by a 'return'
        // We treat these as self-contained.
        return true;
    }

    /**
     * This searches a self contained subgraph inside the region.
     */
    private void findSelfContainedSubgraphs(ISSABasicBlock entry,
                                            ISSABasicBlock current,
                                            ISSABasicBlock terminus,
                                            Set<ISSABasicBlock> subgraphs) throws StaticRegionException {

        if (subgraphs.contains(current) || current == terminus) {
            return;
        }

        if (isSelfContainedSubgraph(current, terminus)) {
            subgraphs.add(current);
        } else {
            // in 'else' because we want only the earliest self-contained subgraphs
            for (ISSABasicBlock succ : ir.getControlFlowGraph().getNormalSuccessors(current)) {
                findSelfContainedSubgraphs(entry, succ, terminus, subgraphs);
            }
        }
    }

    /*
        Re-constructs a complex condition for an if/then/else condition.

        MWW: I make several assumptions here about the structure of the nodes between
            currentBlock and entry; if they are violated then I have misunderstood something
            about the structure of the region, so I throwException(a 'severe' exception.

        If there are stateful operations in the if/then/else, then the internal
        conditions will have >1 statement.  For now we will abort with a SRE, but
        we could hoist them out in some cases.

        MWW TODO: Do we wish to allow stateful conditions in ITEs?
           TODO: We would have to hoist operations; a little bit
           TODO: tricky, so I am not going to bother with it now.
     */

    /**
     * Re-constructs a complex condition for an if/then/else condition.
     * <p>
     * MWW: 9/10/2018.  The assertion: (child.getNumber() > entry.getNumber()) at
     * the top of this function is too restrictive.  The issue is that we assume
     * all parents are within the path between entry and child.  This is true
     * for "top-level" Java if/then/else expressions, but if we wish to
     * construct regions from within complex conditions, it no longer holds.
     * <p>
     * There are two ways to examine this case: we can
     */
    private Pair<Expression, Stmt> createComplexIfCondition(ISSABasicBlock child,
//    private Expression createComplexIfCondition(ISSABasicBlock child,
                                                            ISSABasicBlock entry) throws StaticRegionException {
        assert (child.getNumber() > entry.getNumber());
        SSACFG cfg = ir.getControlFlowGraph();
        Expression returnExpr = null;
        Stmt setupStmt = null;

        for (ISSABasicBlock parent : cfg.getNormalPredecessors(child)) {

            // 9/10/2018 MWW: missing condition: if entry is "inside" a complex
            // if condition, then it should be possible to construct a region that
            // corresponds only to those branches within the subgraph.  However,
            // my intuition *may* be wrong here; it will be a great comfort when
            // Vaibhav finishes his equivalence checker.
            if (parent.getNumber() < entry.getNumber()) {
                continue;
                // throwException(new StaticRegionException("createComplexIfCondition: funky non-self-contained region");
            }

            if (!isConditionalBranch(parent)) {
                if (parent.getLastInstruction() instanceof SSAGetInstruction) {
                    setupStmt = compose(setupStmt, new GetInstruction((SSAGetInstruction) parent.getLastInstruction()), false);
                } else if (parent.getLastInstruction() instanceof SSAArrayLoadInstruction) {
                    setupStmt = compose(setupStmt, new ArrayLoadInstruction((SSAArrayLoadInstruction) parent.getLastInstruction()), false);
                } else
                    throwException(new StaticRegionException("createComplexIfCondition: unconditional branch (continue or break)"), STATIC);
            } else if (parent != entry && SSAUtil.statefulBlock(parent)) {
                throwException(new StaticRegionException("createComplexIfCondition: stateful condition"), STATIC);
            }

            Expression branchExpr;
            Expression condExpr = null;
            if (isConditionalBranch(parent)) {
                assert (child == Util.getTakenSuccessor(cfg, parent) ||
                        child == Util.getNotTakenSuccessor(cfg, parent));
                condExpr = SSAUtil.convertCondition(ir, SSAUtil.getLastBranchInstruction(parent));
                if (child == Util.getNotTakenSuccessor(cfg, parent)) {
                    condExpr = new Operation(Operation.Operator.NOT, condExpr);
                }
            }

            if (parent == entry) {
                branchExpr = condExpr;
            } else {
                Pair<Expression, Stmt> parentExprStmt = createComplexIfCondition(parent, entry);
                Expression parentExpr = parentExprStmt.getFirst();
                setupStmt = compose(parentExprStmt.getSecond(), setupStmt, true);
                branchExpr = condExpr != null ? new Operation(Operation.Operator.AND, parentExpr, condExpr) : parentExpr;
            }
            assert branchExpr != null;

            if (returnExpr == null) {
                returnExpr = branchExpr;
            } else {
                returnExpr = new Operation(Operation.Operator.OR, returnExpr, branchExpr);
            }
        }
// Vaibhav: This happens when we have a region like assert (x != 0 ? count == x + 3 : count == 3); which is in
// FieldTest3. All predecessors of child have a number less than parent because of which the we never run any full
// iterations through the "for (ISSABasicBlock parent : cfg.getNormalPredecessors(child))" loop. I think it is best to
// not create such a region. It is also good to not crash Java Ranger on encountering such a region.
//        assert (returnExpr != null);
        if (returnExpr == null) throwException(new StaticRegionException("createComplexIfCondition: failed to recover condition"), STATIC);
        return new Pair<>(returnExpr, setupStmt);
    }

    /*
        // MWW: debugging
        System.out.println("For entry: " + entry);
        for (ISSABasicBlock starter: subgraphs) {
            System.out.println("   Subgraph: " + starter);
        }
        // MWW: end of debugging.
     */

    /**
     * Attempts to discover conditional successors on the then or the else side of a conditional block.
     *
     * @param entry    Entry block.
     * @param terminus End blcok where search needs to stop
     * @throws StaticRegionException An Exception that indicates that something went wrong during computation.
     */
    private void findConditionalSuccessors(ISSABasicBlock entry,
                                           ISSABasicBlock terminus) throws StaticRegionException {

        Set<ISSABasicBlock> subgraphs = new HashSet<>();
        SSACFG cfg = ir.getControlFlowGraph();
        ISSABasicBlock initialThenBlock = Util.getTakenSuccessor(cfg, entry);
        ISSABasicBlock initialElseBlock = Util.getNotTakenSuccessor(cfg, entry);
        ISSABasicBlock thenBlock = null, elseBlock = null;

        findSelfContainedSubgraphs(entry, initialThenBlock, terminus, subgraphs);
        findSelfContainedSubgraphs(entry, initialElseBlock, terminus, subgraphs);

        // if (no-else) region
        if (subgraphs.size() == 1) {
            thenBlock = subgraphs.iterator().next();
            elseBlock = terminus;
        }
        // if/else region; choice of 'thenBlock' is arbitrary.
        else if (subgraphs.size() == 2) {
            Iterator<ISSABasicBlock> it = subgraphs.iterator();
            thenBlock = it.next();
            elseBlock = it.next();
        } else {
            // MWW: I don't anticipate this condition ever occurring, but it might;
            // esp. for JVM programs not compiled by Java compiler.
            String errorText = "Unexpected number (" + subgraphs.size() +
                    ") of self-contained regions in findConditionalSuccessors";
            System.out.println(errorText);
            throwException(new StaticRegionException(errorText), STATIC);
        }
        this.thenSuccessor.put(entry, thenBlock);
        this.elseSuccessor.put(entry, elseBlock);
        Pair<Expression, Stmt> condExprStmt = createComplexIfCondition(thenBlock, entry);
        this.thenCondition.put(entry, condExprStmt.getFirst());
        this.thenConditionSetup.put(entry, condExprStmt.getSecond());
    }

    /**
     * Translates from current block but does not include the ending block.
     *
     * @param cfg          Control flow graph.
     * @param currentBlock Current block
     * @param endingBlock  End block, this is not included in this translation.
     * @return a statement that represents this part of cfg in RangerIR.
     * @throws StaticRegionException
     */
    public Stmt attemptSubregionRec(SSACFG cfg, ISSABasicBlock currentBlock, ISSABasicBlock endingBlock) throws StaticRegionException {

        if (currentBlock == endingBlock) {
            return SkipStmt.skip;
        }

        Stmt stmt = translateInternalBlock(currentBlock);

        if (cfg.getNormalSuccessors(currentBlock).size() == 2) {
            FindStructuredBlockEndNode finder = new FindStructuredBlockEndNode(cfg, currentBlock, endingBlock);
            ISSABasicBlock terminus = finder.findMinConvergingNode();
            Stmt condStmt = conditionalBranch(cfg, currentBlock, terminus);

            stmt = conjoin(stmt, condStmt);
            stmt = conjoin(stmt, attemptSubregionRec(cfg, terminus, endingBlock));
        } else if (cfg.getNormalSuccessors(currentBlock).size() == 1) {
            ISSABasicBlock nextBlock = cfg.getNormalSuccessors(currentBlock).iterator().next();
            this.blockConditionMap.put(new PhiEdge(currentBlock, nextBlock), new ArrayList(currentCondition));

            if (nextBlock.getNumber() < endingBlock.getNumber()) {
                if (isLoopStart(loops, nextBlock)) {
                    // Not sure why, but if we see the beginning of a loop more than twice, we're seeing a infinite loop.
                    // This check correctly detects infinite loops in Pad.main() and
                    // java.lang.ref.Reference$ReferenceHandler.run() while not classifying any other loops as infinite loops.
                    if (seenLoopStartSet.containsKey(nextBlock) && seenLoopStartSet.get(nextBlock) > 2)
                        throwException(new StaticRegionException(currentBlock.toString() + " is the beginning of an infinite loop"), STATIC);
                    else {
                        if (seenLoopStartSet.containsKey(nextBlock))
                            seenLoopStartSet.put(nextBlock, seenLoopStartSet.get(nextBlock) + 1);
                        else seenLoopStartSet.put(nextBlock, 1);
                    }
                }
                stmt = conjoin(stmt, attemptSubregionRec(cfg, nextBlock, endingBlock));
            }
        }
        return stmt;
    }


    /**
     * Attempts to translate a conditional part of the cfg to IfThenElse statement in RangerIR.
     *
     * @param cfg          Current control flow graph.
     * @param currentBlock current block
     * @param terminus     End block.
     * @return A RangerIR IfThenElse statement.
     * @throws StaticRegionException
     */
    private Stmt conditionalBranch(SSACFG cfg, ISSABasicBlock currentBlock, ISSABasicBlock terminus)
            throws StaticRegionException {

        if (!isConditionalBranch(currentBlock)) {
            throwException(new StaticRegionException("conditionalBranch: no conditional branch!"), STATIC);
        }

        findConditionalSuccessors(currentBlock, terminus);
        Expression condExpr = thenCondition.get(currentBlock);
        ISSABasicBlock thenBlock = thenSuccessor.get(currentBlock);
        ISSABasicBlock elseBlock = elseSuccessor.get(currentBlock);

        Stmt thenStmt, elseStmt;
        currentCondition.addLast(new PhiCondition(PhiCondition.Branch.Then, condExpr));
        this.blockConditionMap.put(new PhiEdge(currentBlock, thenBlock), new ArrayList(currentCondition));
        if (thenBlock.getNumber() < terminus.getNumber()) {
            thenStmt = attemptSubregionRec(cfg, thenBlock, terminus);
        } else {
            thenStmt = SkipStmt.skip;
        }
        currentCondition.removeLast();

        currentCondition.addLast(new PhiCondition(PhiCondition.Branch.Else, condExpr));
        this.blockConditionMap.put(new PhiEdge(currentBlock, elseBlock), new ArrayList(currentCondition));
        if (elseBlock.getNumber() < terminus.getNumber()) {
            elseStmt = attemptSubregionRec(cfg, elseBlock, terminus);
        } else {
            elseStmt = SkipStmt.skip;
        }
        currentCondition.removeLast();
        Stmt returnStmt = compose(this.thenConditionSetup.get(currentBlock),
                new IfThenElseStmt(SSAUtil.getLastBranchInstruction(currentBlock), condExpr, thenStmt, elseStmt),
                false);

        return returnStmt;
    }


    // precondition: terminus is the loop join.

    /**
     * Attempts to translate a conditional part of the cfg to IfThenElse statement in RangerIR.
     *
     * @param cfg          Current control flow graph.
     * @param currentBlock current block
     * @param terminus     End block.
     * @return A RangerIR IfThenElse statement.
     * @throws StaticRegionException
     */
    private Stmt jitConditionalBranch(SSACFG cfg, ISSABasicBlock currentBlock, ISSABasicBlock terminus, Map<PhiEdge, List<PhiCondition>> insertedBlockConditionMap)
            throws StaticRegionException {

        if (!isConditionalBranch(currentBlock)) {
            throwException(new StaticRegionException("conditionalBranch: no conditional branch!"), STATIC);
        }

        jitVisitedBlocks.add(currentBlock);

        findConditionalSuccessors(currentBlock, terminus);
        Expression condExpr = thenCondition.get(currentBlock);
        ISSABasicBlock thenBlock = thenSuccessor.get(currentBlock);
        ISSABasicBlock elseBlock = elseSuccessor.get(currentBlock);

        ISSABasicBlock actualElseBlock = Util.getTakenSuccessor(cfg, currentBlock);
        ISSABasicBlock actualThenBlock = Util.getNotTakenSuccessor(cfg, currentBlock);

        Stmt thenStmt, elseStmt;
        currentCondition.addLast(new PhiCondition(PhiCondition.Branch.Then, condExpr));
        this.blockConditionMap.put(new PhiEdge(currentBlock, thenBlock), new ArrayList(currentCondition));
        insertedBlockConditionMap.put(new PhiEdge(currentBlock, thenBlock), new ArrayList(currentCondition));

        if (thenBlock.getNumber() < terminus.getNumber()) {
            Pair<Stmt, Map<PhiEdge, List<PhiCondition>>> stmtMapPair = jitAttemptSubregionRec(cfg, thenBlock, terminus);
            thenStmt = stmtMapPair.getFirst();
            insertedBlockConditionMap.putAll(stmtMapPair.getSecond());
        } else {
            thenStmt = SkipStmt.skip;
        }
        currentCondition.removeLast();

        currentCondition.addLast(new PhiCondition(PhiCondition.Branch.Else, condExpr));
        this.blockConditionMap.put(new PhiEdge(currentBlock, elseBlock), new ArrayList(currentCondition));
        insertedBlockConditionMap.put(new PhiEdge(currentBlock, elseBlock), new ArrayList(currentCondition));

        if (elseBlock.getNumber() < terminus.getNumber()) {
            Pair<Stmt, Map<PhiEdge, List<PhiCondition>>> stmtMapPair = jitAttemptSubregionRec(cfg, elseBlock, terminus);
            elseStmt = stmtMapPair.getFirst();
            insertedBlockConditionMap.putAll(stmtMapPair.getSecond());
        } else {
            elseStmt = SkipStmt.skip;
        }
        currentCondition.removeLast();

        Stmt returnStmt = compose(this.thenConditionSetup.get(currentBlock),
                new IfThenElseStmt(SSAUtil.getLastBranchInstruction(currentBlock), condExpr, thenStmt, elseStmt),
                false);

        if (!actualThenBlock.equals(thenBlock) &&(!actualThenBlock.equals(elseBlock)))
            populateMissedRegions(cfg, actualThenBlock, terminus);

        if (!actualElseBlock.equals(thenBlock) &&(!actualElseBlock.equals(elseBlock)))
            populateMissedRegions(cfg, actualElseBlock, terminus);

        return returnStmt;

    }


/*
    This method translates from currentBlock up to but not including endingBlock.
     * Doing it this way makes it much simpler to deal with nested if/then/elses that land in the same spot.
     *
             * It also makes it simpler to tailor the end of the translation: for methods, we want to grab the remaining code within the method, while for conditional blocks we only want to grab the subsequent \phi functions.
            *
            * NB: same block may be visited multiple times!*/

    /**
     * Translates from current block but does not include the ending block.
     *
     * @param cfg          Control flow graph.
     * @param currentBlock Current block
     * @param endingBlock  End block, this is not included in this translation.
     * @return a statement that represents this part of cfg in RangerIR.
     * @throws StaticRegionException
     */
    public Pair<Stmt, Map<PhiEdge, List<PhiCondition>>> jitAttemptSubregionRec(SSACFG cfg, ISSABasicBlock currentBlock, ISSABasicBlock endingBlock) throws StaticRegionException {

        jitCurrentCondition = new LinkedList<>(currentCondition);
        jitCurrentCondition.removeLast();

        Map<PhiEdge, List<PhiCondition>> jitBlockConditionMap = new HashMap<>();

        if (currentBlock == endingBlock) {
            return new Pair(SkipStmt.skip, jitBlockConditionMap);
        }

        Stmt stmt = translateInternalBlock(currentBlock);

        if (cfg.getNormalSuccessors(currentBlock).size() == 2) {

            FindStructuredBlockEndNode finder = new FindStructuredBlockEndNode(cfg, currentBlock, endingBlock);
            ISSABasicBlock terminus = finder.findMinConvergingNode();

            Stmt condStmt = jitConditionalBranch(cfg, currentBlock, terminus, jitBlockConditionMap);

            stmt = conjoin(stmt, condStmt);
            Stmt partialGammaStmt = jitTranslateTruncatedFinalBlock2(terminus, jitBlockConditionMap, jitCurrentCondition);
            int endIns;

            try {
                endIns = ((IBytecodeMethod) (ir.getMethod())).getBytecodeIndex(terminus.getFirstInstructionIndex());
                Stmt s = conjoin(stmt, partialGammaStmt);
                veritestingRegions.put(CreateStaticRegions.constructRegionIdentifier(ir, currentBlock), new StaticRegion(s, ir, false, endIns, currentBlock, terminus, null));
                System.out.println("Subregion" + System.lineSeparator() + PrettyPrintVisitor.print(s));

            } catch (InvalidClassFileException e) {
                System.out.println("Unable to create subregion.  Reason: " + e.toString());
            } catch (StaticRegionException e) {
                System.out.println("Unable to create subregion.  Reason: " + e.toString());
            }
            Pair<Stmt, Map<PhiEdge, List<PhiCondition>>> stmtMapPair = jitAttemptSubregionRec(cfg, terminus, endingBlock);
            Stmt subRegStmt = stmtMapPair.getFirst();
            stmt = conjoin(stmt, subRegStmt);
            jitBlockConditionMap.putAll(stmtMapPair.getSecond());

        } else if (cfg.getNormalSuccessors(currentBlock).size() == 1) {
            ISSABasicBlock nextBlock = cfg.getNormalSuccessors(currentBlock).iterator().next();
            this.blockConditionMap.put(new PhiEdge(currentBlock, nextBlock), new ArrayList(currentCondition));
            jitBlockConditionMap.put(new PhiEdge(currentBlock, nextBlock), new ArrayList(currentCondition));
            if (nextBlock.getNumber() < endingBlock.getNumber()) {
                if (isLoopStart(loops, nextBlock)) {
                    // Not sure why, but if we see the beginning of a loop more than twice, we're seeing a infinite loop.
                    // This check correctly detects infinite loops in Pad.main() and
                    // java.lang.ref.Reference$ReferenceHandler.run() while not classifying any other loops as infinite loops.
                    if (seenLoopStartSet.containsKey(nextBlock) && seenLoopStartSet.get(nextBlock) > 2)
                        throwException(new StaticRegionException(currentBlock.toString() + " is the beginning of an infinite loop"), STATIC);
                    else {
                        if (seenLoopStartSet.containsKey(nextBlock))
                            seenLoopStartSet.put(nextBlock, seenLoopStartSet.get(nextBlock) + 1);
                        else seenLoopStartSet.put(nextBlock, 1);
                    }
                }
                Pair<Stmt, Map<PhiEdge, List<PhiCondition>>> stmtMapPair = jitAttemptSubregionRec(cfg, nextBlock, endingBlock);
                stmt = conjoin(stmt, stmtMapPair.getFirst());
                jitBlockConditionMap.putAll(stmtMapPair.getSecond());
            }
        }
        return new Pair(stmt, jitBlockConditionMap);
    }

    // precondition: endingBlock is the terminus of the loop

    /**
     * Attempts to translate conditional region and translates it to RangerIR statement
     *
     * @param cfg           Control flow graph
     * @param startingBlock Starting block that is a branch instruction.
     * @param terminus      End of the region.
     * @return Translated statement in RangerIR that has decompiled the CFG.
     * @throws StaticRegionException
     */
    private Stmt attemptConditionalSubregion(SSACFG cfg, ISSABasicBlock startingBlock, ISSABasicBlock terminus) throws StaticRegionException {

        assert (isBranch(cfg, startingBlock));
        Stmt stmt = conditionalBranch(cfg, startingBlock, terminus);
        stmt = conjoin(stmt, translateTruncatedFinalBlock(terminus));
        return stmt;
    }

    private Stmt jitAttemptConditionalSubregion(SSACFG cfg, ISSABasicBlock startingBlock, ISSABasicBlock terminus) throws StaticRegionException {

        assert (isBranch(cfg, startingBlock));
        Stmt stmt = jitConditionalBranch(cfg, startingBlock, terminus, new HashMap<>());
        stmt = conjoin(stmt, translateTruncatedFinalBlock(terminus));
        return stmt;
    }

    /**
     * Attempts to translate a method region to a RangerIR statement.
     *
     * @param cfg
     * @param startingBlock
     * @param endingBlock
     * @return
     * @throws StaticRegionException
     */
    private Stmt attemptMethodSubregion(SSACFG cfg, ISSABasicBlock startingBlock, ISSABasicBlock endingBlock) throws StaticRegionException {
        Stmt stmt = attemptSubregionRec(cfg, startingBlock, endingBlock);
        stmt = conjoin(stmt, translateInternalBlock(endingBlock));
        return stmt;
    }

    /**
     * This class walks through method, attempting to find conditional veritesting regions
     *
     * @param currentBlock
     * @param endingBlock
     * @param veritestingRegions
     * @throws StaticRegionException
     */
    private void createStructuredConditionalRegions(ISSABasicBlock currentBlock,
                                                    ISSABasicBlock endingBlock,
                                                    HashMap<String, StaticRegion> veritestingRegions) throws StaticRegionException {

        if (visitedBlocks.contains(currentBlock)) {
            return;
        }
        visitedBlocks.add(currentBlock);

        SSACFG cfg = ir.getControlFlowGraph();
        // terminating conditions
        if (currentBlock == endingBlock) {
            return;
        }


        if (isBranch(cfg, currentBlock)) {
            try {
                reset();
                FindStructuredBlockEndNode finder = new FindStructuredBlockEndNode(cfg, currentBlock, endingBlock);
                ISSABasicBlock terminus = finder.findMinConvergingNode();
                Stmt s = attemptConditionalSubregion(cfg, currentBlock, terminus);
                int endIns;

                endIns = ((IBytecodeMethod) (ir.getMethod())).getBytecodeIndex(terminus.getFirstInstructionIndex());
                veritestingRegions.put(CreateStaticRegions.constructRegionIdentifier(ir, currentBlock), new StaticRegion(s, ir, false, endIns, currentBlock, terminus, null));
                System.out.println("Subregion: " + System.lineSeparator() + PrettyPrintVisitor.print(s));

            } catch (StaticRegionException e) {
                //SSAUtil.printBlocksUpTo(cfg, endingBlock.getNumber());
                System.out.println("Unable to create subregion.  Reason: " + e.toString());
            } catch (InvalidClassFileException e) {
                System.out.println("Unable to create subregion.  Reason: " + e.toString());
            } catch (IllegalArgumentException e) {
                System.out.println("Unable to create subregion.  Serious error. Reason: " + e.toString());
                throwException(e, STATIC);
            }
        }
        for (ISSABasicBlock nextBlock : cfg.getNormalSuccessors(currentBlock)) {
            createStructuredConditionalRegions(nextBlock, endingBlock, veritestingRegions);
        }
    }


    public void createStructuredConditionalRegions(HashMap<String, StaticRegion> veritestingRegions) throws StaticRegionException {
        SSACFG cfg = ir.getControlFlowGraph();
        // SSAUtil.printBlocksUpTo(cfg, cfg.exit().getNumber());
        createStructuredConditionalRegions(cfg.entry(), cfg.exit(), veritestingRegions);
    }

    /**
     * This class walks through method, attempting to find method regions veritesting regions
     */
    public void createStructuredMethodRegion(HashMap<String, StaticRegion> veritestingRegions) throws StaticRegionException {
        reset();
        SSACFG cfg = ir.getControlFlowGraph();

        try {
            Stmt s = attemptMethodSubregion(cfg, cfg.entry(), cfg.exit());
            System.out.println("Method" + System.lineSeparator() + PrettyPrintVisitor.print(s));
            veritestingRegions.put(CreateStaticRegions.constructMethodIdentifier(cfg.entry()), new StaticRegion(s, ir, true, 0, null, null, null));
        } catch (StaticRegionException sre) {
            System.out.println("Unable to create a method summary region for: " + cfg.getMethod().getName().toString());
        }
    }

    /**
     * This methods attempt to connect discover multi-path regions and connecting them to recover the method as well.
     *
     * @param cfg
     * @param currentBlock
     * @param endingBlock
     * @return
     * @throws StaticRegionException
     */
    public Stmt attemptMethodAndMultiPathRegions(SSACFG cfg, ISSABasicBlock currentBlock, ISSABasicBlock endingBlock) throws StaticRegionException {

        if (currentBlock == endingBlock) {
            return SkipStmt.skip;
        }

        Stmt stmt;

        if (cfg.getNormalSuccessors(currentBlock).size() == 2) {
            stmt = jitTranslateTruncatedConditionalBlock(currentBlock);


            FindStructuredBlockEndNode finder = new FindStructuredBlockEndNode(cfg, currentBlock, endingBlock);
            ISSABasicBlock terminus = finder.findMinConvergingNode();
            Stmt condStmt = jitAttemptConditionalSubregion(cfg, currentBlock, terminus);
            int endIns;
            try {
                endIns = ((IBytecodeMethod) (ir.getMethod())).getBytecodeIndex(terminus.getFirstInstructionIndex());
                veritestingRegions.put(CreateStaticRegions.constructRegionIdentifier(ir, currentBlock), new StaticRegion(condStmt, ir, false, endIns, currentBlock, terminus, null));
            } catch (InvalidClassFileException e) {
                System.out.println("unable to create static region:" + e.getMessage());
            } catch (StaticRegionException sre) {
                System.out.println("unable to create static region:" + sre.getMessage());
            }
            stmt = conjoin(stmt, condStmt);

            stmt = conjoin(stmt, attemptMethodAndMultiPathRegions(cfg, terminus, endingBlock));
        } else if (cfg.getNormalSuccessors(currentBlock).size() == 1) {
            if (phiBlock(currentBlock))
                stmt = jitTranslateTruncatedFinalBlock(currentBlock);
            else
                stmt = translateInternalBlock(currentBlock);

            ISSABasicBlock nextBlock = cfg.getNormalSuccessors(currentBlock).iterator().next();
            this.blockConditionMap.put(new PhiEdge(currentBlock, nextBlock), new ArrayList(currentCondition));

            if (nextBlock.getNumber() < endingBlock.getNumber()) {
                if (isLoopStart(loops, nextBlock)) {
                    // Not sure why, but if we see the beginning of a loop more than twice, we're seeing a infinite loop.
                    // This check correctly detects infinite loops in Pad.main() and
                    // java.lang.ref.Reference$ReferenceHandler.run() while not classifying any other loops as infinite loops.
                    if (seenLoopStartSet.containsKey(nextBlock) && seenLoopStartSet.get(nextBlock) > 2)
                        throwException(new StaticRegionException(currentBlock.toString() + " is the beginning of an infinite loop"), STATIC);
                    else {
                        if (seenLoopStartSet.containsKey(nextBlock))
                            seenLoopStartSet.put(nextBlock, seenLoopStartSet.get(nextBlock) + 1);
                        else seenLoopStartSet.put(nextBlock, 1);
                    }
                }
                stmt = conjoin(stmt, attemptMethodAndMultiPathRegions(cfg, nextBlock, endingBlock));
            }
        } else
            stmt = translateInternalBlock(currentBlock);
        return stmt;
    }

    private void populateMissedRegions(SSACFG cfg, ISSABasicBlock currentBlock, ISSABasicBlock endingBlock) throws StaticRegionException {
        if (!jitVisitedBlocks.contains(currentBlock)) {
            jitVisitedBlocks.add(currentBlock);
            if (isBranch(cfg, currentBlock)) {
                //saving state
                Map<PhiEdge, List<PhiCondition>> oldBlockConditionMap = new HashMap<>(blockConditionMap);
                Deque<PhiCondition> oldCurrentCondition = new LinkedList<>(currentCondition);
                Deque<PhiCondition> oldJitCurrentCondition = new LinkedList<>(jitCurrentCondition);

                FindStructuredBlockEndNode finder = new FindStructuredBlockEndNode(cfg, currentBlock, endingBlock);
                ISSABasicBlock terminus = finder.findMinConvergingNode();


                Map<PhiEdge, List<PhiCondition>> tanslationMap = new HashMap<>();
                Stmt stmt = jitConditionalBranch(cfg, currentBlock, terminus, tanslationMap);
                Stmt partialGammaStmt = jitTranslateTruncatedFinalBlock2(terminus, tanslationMap, new LinkedList<>(jitCurrentCondition));
                stmt = conjoin(stmt, partialGammaStmt);

                //restore state
                blockConditionMap = oldBlockConditionMap;
                currentCondition = oldCurrentCondition;
                jitCurrentCondition = oldJitCurrentCondition;

                int endIns;
                try {
                    endIns = ((IBytecodeMethod) (ir.getMethod())).getBytecodeIndex(terminus.getFirstInstructionIndex());
                    veritestingRegions.put(CreateStaticRegions.constructRegionIdentifier(ir, currentBlock), new StaticRegion(stmt, ir, false, endIns, currentBlock, terminus, null));
                } catch (InvalidClassFileException e) {
                    System.out.println("unable to create static region:" + e.getMessage());
                } catch (StaticRegionException sre) {
                    System.out.println("unable to create static region:" + sre.getMessage());

                }
            }
            else
                populateMissedRegions(cfg, cfg.getNormalSuccessors(currentBlock).iterator().next(), endingBlock);
        }
    }


    private boolean phiBlock(ISSABasicBlock currentBlock) {
        boolean hasPhi = false;
        for (SSAInstruction ins : currentBlock) {
            if (ins instanceof SSAPhiInstruction)
                return hasPhi = true;
        }
        return hasPhi;
    }


    /**
     * This class walks through method, attempting to recover a method region and also recover all multi-path regions inside of it.
     */
    public void jitCreateStructuredRegion(HashMap<String, StaticRegion> veritestingRegions) throws StaticRegionException {
        this.veritestingRegions = veritestingRegions;

        reset();
        SSACFG cfg = ir.getControlFlowGraph();

        try {
            Stmt s = attemptMethodAndMultiPathRegions(cfg, cfg.entry(), cfg.exit());
            System.out.println("Method" + System.lineSeparator() + PrettyPrintVisitor.print(s));
            SSAInstruction[] insns = ir.getInstructions();
            veritestingRegions.put(CreateStaticRegions.constructMethodIdentifier(cfg.entry()), new StaticRegion(s, ir, true, 0, null, null, null));
        } catch (StaticRegionException sre) { //TODO: check if we need that for method regions.
                throw sre;
        }
    }
}
