package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;


import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.symbc.veritesting.ast.def.CloneableVariable;
import gov.nasa.jpf.symbc.veritesting.ast.def.WalaVarExpr;
import za.ac.sun.cs.green.expr.Variable;

import java.util.*;

//slot -> var
public class DynamicOutputTable extends Table<Integer, CloneableVariable> {

    public DynamicOutputTable(String tableName, String label1, String label2) {
        super(tableName, label1, label2);
    }

    public DynamicOutputTable(OutputTable staticTable, int uniqueNum) throws StaticRegionException {
        super(staticTable.tableName, staticTable.label1, staticTable.label2);

        List keys = new ArrayList(staticTable.table.keySet());
        Collections.sort(keys);
        Collections.reverse(keys);
        Iterator itr = keys.iterator();
        while(itr.hasNext()){
            Integer slot = (Integer) itr.next();
            Integer oldWalaId = staticTable.lookup(slot);
            WalaVarExpr newWalaVar = new WalaVarExpr(oldWalaId);
            newWalaVar = newWalaVar.makeUnique(uniqueNum);
            table.put(slot, newWalaVar);
        }
    }

    /**
     * Returns all keys of the table.
     */

    public ArrayList<Integer> getKeys() {
        return new ArrayList<Integer>(this.table.keySet());
    }

    public Integer reverseLookup(CloneableVariable var) {
        Iterator itr = table.entrySet().iterator();
        while (itr.hasNext()) {
            Map.Entry<Integer, CloneableVariable> entry = (Map.Entry) itr.next();
            if (entry.getValue().equals(var)) return entry.getKey();
        }
        return null;
    }

}
