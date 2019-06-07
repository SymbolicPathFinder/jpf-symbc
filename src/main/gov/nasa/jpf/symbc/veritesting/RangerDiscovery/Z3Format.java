package gov.nasa.jpf.symbc.veritesting.RangerDiscovery;

import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;

import java.util.HashSet;

public class Z3Format {

    public static String toSMT(String query, HashSet z3FunDecSet) {
        assert (query.length() > 0);

        String newQuery = new String();
        /*removing the outer solve*/
        query = query.substring(8, query.length() - 1);

        int startingIndex = 0;
        int endingIndex = query.length();
        while (startingIndex < endingIndex) {
            Pair startEndIndecies = findAssertion(query, startingIndex);

            startingIndex = (int) startEndIndecies.getFirst();
            int assertionEndIndex = (int) startEndIndecies.getSecond();

            String assertion = query.substring(startingIndex, assertionEndIndex + 1); //+1 because substring is not inclusive for the endIndex.
            newQuery += "(assert " + assertion + ")\n";
            startingIndex = assertionEndIndex + 1;
        }

        newQuery = "  (set-logic QF_BV)\n" +
                "  (set-info :smt-lib-version 2.0)\n" +
                "  (set-option :produce-unsat-cores true)\n" +
                generateFunDec(z3FunDecSet) +
                newQuery
                + "(check-sat)\n" +
                "(get-unsat-core)\n" +
                "(exit)\n";

        return newQuery;
    }

    private static String generateFunDec(HashSet<String> z3FunDecSet) {
        String funDec = "";
        for (String varName : z3FunDecSet) {
            funDec = funDec + "(declare-fun " + varName + " () (_ BitVec 32))\n";
        }
        return funDec;
    }


    /**
     * This takes the starting index of an opening bracket for which we want to find a matching closing bracket. It returns the index of the closing bracket.
     *
     * @param query
     * @param startingIndex
     * @return
     */
    private static Pair findAssertion(String query, int startingIndex) {
        int closingIndex = 0;
        int bracket = 0;
        boolean closingBracketFound = false;
        boolean firstOpenBracketEncountered = false;
        int walkingIndex = startingIndex;

        /*This loop tries to find the index of the first opening bracket. At the end of the loop, the walkingIndex will have this index number.*/
        while (!firstOpenBracketEncountered) {
            char c = query.charAt(walkingIndex);
            if (c == '(')
                firstOpenBracketEncountered = true;
            else {
                ++walkingIndex;
            }
        }

        startingIndex = walkingIndex;
        while (!closingBracketFound) {
            char c = query.charAt(walkingIndex);
            if (c == '(')
                ++bracket;
            else if (c == ')')
                --bracket;

            if (bracket == 0) {
                closingBracketFound = true;
                closingIndex = walkingIndex;
            }
            ++walkingIndex;
        }
        return new Pair(startingIndex, closingIndex);
    }
}
