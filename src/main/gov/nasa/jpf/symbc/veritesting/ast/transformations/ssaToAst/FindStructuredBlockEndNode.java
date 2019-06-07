package gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst;

import com.ibm.wala.ssa.*;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;

import java.util.*;

import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.ExceptionPhase.STATIC;
import static gov.nasa.jpf.symbc.veritesting.StaticRegionException.throwException;

    /* MWW: Relatively simple traversal that aborts on non-local jumps *other than for early
       returns and exceptions*.  It attempts to find the minimal convergent node
       for all non-exceptional and non-early-return paths.

        It starts from a prescribed region with a minimal and maximal node.  If there is
        no non-early-return path and no erroneous cases (described below),
        it returns the maximal node.

        Exceptional cases:
            local loops (back edges between minLimit and maxLimit).
            early continues from outer loops: a back edge from a node earlier than the minimal
                convergent node.
            user-level breaks or gotos: jumps beyond maxLimit

        For exceptions, it throws a StaticRegionException.  Since this will be a relatively
        common case, I have pre-built the exception as a static object for performance.  It
        might be better to re-factor the code to avoid exceptions, but there are currently
        many cases, so I think it simplifies the code to use them.
     */

/**
 * Attempts to discover end node of a region, by walking successors of presumably a block that ends with a conditional instruction.
 */
public class FindStructuredBlockEndNode {

    PriorityQueue<ISSABasicBlock> remaining = null;
    ISSABasicBlock minConvergingNode = null;
    ISSABasicBlock maxLimit = null;
    ISSABasicBlock minLimit = null;
    SSACFG cfg;

    // Amortize the cost of throwing the exception; much cheaper if it is static.
    public static StaticRegionException staticRegionException = new StaticRegionException("FindStructuredBlockEndNode: mal-formed region");

    public FindStructuredBlockEndNode(SSACFG cfg, ISSABasicBlock initial, ISSABasicBlock maxLimit) {
        remaining = SSAUtil.constructSortedBlockPQ();
        // set maxLimit to the end of the function if it is not provided.
        this.maxLimit = (maxLimit != null) ? maxLimit : cfg.exit();
        this.minLimit = initial;
        this.cfg = cfg;
    }

    void checkRanges(ISSABasicBlock parent, ISSABasicBlock b) throws StaticRegionException {
        // abort on "internal loop" case
        if (b.getNumber() <= parent.getNumber()) {
            throwException(staticRegionException, STATIC);
        }

        // handle "forward out of bounds" case
        if (b.getNumber() > maxLimit.getNumber()) {
            throwException(staticRegionException, STATIC);
        }
    }

    /**
     * This attempts to walk all successors of a block to try to find the end block node.
     *
     * @param b The block which we need to find the common successor for all its successors.
     * @throws StaticRegionException An exception that indicates that something has went wrong during computation.
     */
    void findCommonSuccessor(ISSABasicBlock b) throws StaticRegionException {

        for (ISSABasicBlock succ : cfg.getNormalSuccessors(b)) {
            checkRanges(b, succ);
            SSAUtil.enqueue(remaining, succ);
        }

        // Size of the queue is the number of open paths in the model.
        while (remaining.size() > 1) {
            ISSABasicBlock current = remaining.poll();
            for (ISSABasicBlock succ : SSAUtil.getNonReturnSuccessors(cfg, current)) {
                checkRanges(current, succ);
                SSAUtil.enqueue(remaining, succ);
            }
        }

        minConvergingNode = remaining.poll();
    }

    /**
     * Finds the end block of a region.
     *
     * @return End block of a region.
     * @throws StaticRegionException An exception that indicates that something has went wrong during computation.
     */
    public ISSABasicBlock findMinConvergingNode() throws StaticRegionException {

        // we have already computed it.
        if (minConvergingNode != null) {
            return minConvergingNode;
        }

        List<ISSABasicBlock> succs = new ArrayList<>(cfg.getNormalSuccessors(minLimit));
        if (succs.size() == 0) {
            throwException(staticRegionException, STATIC);
            return null;
        } else if (succs.size() == 1) {
            return succs.get(0);
        } else {
            findCommonSuccessor(minLimit);
            return minConvergingNode;
        }
    }

    public boolean predIsReturn(ISSABasicBlock terminus) {
        List<ISSABasicBlock> preds = new ArrayList<>(cfg.getNormalPredecessors(terminus));

        Iterator<ISSABasicBlock> prdItr = preds.iterator();

        boolean isReturn = true;
        while (prdItr.hasNext() && isReturn)
            if (!(prdItr.next().getLastInstruction() instanceof SSAReturnInstruction))
                isReturn = false;
        return isReturn;
    }
}
