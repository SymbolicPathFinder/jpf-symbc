package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;

import za.ac.sun.cs.green.expr.Expression;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

/**
 * SH: This table contains the values for the region input and the constant wala variables.
  Region input is defined as the first use of every stack slot, if the first time a var is associated
  to a stack slot happens to be  a def then this is not an input to the region, nor any of its subsequent vars.
  all values stored here should be in the form of a green expression
 */


public class ValueSymbolTable extends StaticTable<Expression> {


    public ValueSymbolTable() {
        super("var-value table", "var", "value");
    }

    /**
     * Clones the VarTypeTable to a new VarTypeTable, by creating new entries for the keys.
     * @return A new VarTypeTable that has a new copy for the keys.
     */

    public ValueSymbolTable clone(){
        ValueSymbolTable valueSymbolTable = new ValueSymbolTable();
        valueSymbolTable.tableName = this.tableName;
        valueSymbolTable.label1 = this.label1;
        valueSymbolTable.label2 = this.label2;
        Set<Integer> keys = this.table.keySet();
        Iterator<Integer> iter = keys.iterator();
        while(iter.hasNext()){
            Integer key = iter.next();
            Expression value = this.lookup(key);
            valueSymbolTable.add(new Integer(key.intValue()), value);
        }
        return valueSymbolTable;
    }

}
