package gov.nasa.jpf.symbc.veritesting.ast.transformations.SPFCases;

import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ExprUtil;
import gov.nasa.jpf.symbc.veritesting.ast.def.SPFCaseStmt;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.removeEarlyReturns.RemoveEarlyReturns;

import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;

public class SPFCaseList {
    public final LinkedHashSet<SPFCaseStmt> casesList = new LinkedHashSet<>();


    public SPFCaseList(LinkedHashSet<SPFCaseStmt> spfCaseList) {
        Iterator<SPFCaseStmt> itr = spfCaseList.iterator();
        while(itr.hasNext()){
            addCase(itr.next());
        }
    }

    public SPFCaseList() {

    }

    //we can do optimization here to check if we already had added this case before.
    public void addCase(SPFCaseStmt c) { //removes duplicated spfCases conditions
        boolean found = false;
        Iterator<SPFCaseStmt> caseItr = casesList.iterator();
        while (caseItr.hasNext() && !found) {
            if (caseItr.next().spfCondition.equals(c.spfCondition))
                found = true;
        }
        if (!found)
            casesList.add(c);
    }

    public void addAll(SPFCaseList cl) {
        casesList.addAll(cl.casesList);
    }

    public void print(){
        Iterator<SPFCaseStmt> itr = casesList.iterator();
        int i =0;
        while(itr.hasNext()){
            SPFCaseStmt aCase = itr.next();
            System.out.println("Case(" + i + "): ");
            System.out.println(ExprUtil.AstToString(aCase.spfCondition) + "--------- reason:" + aCase.reason);
            ++i;
        }
    }
}