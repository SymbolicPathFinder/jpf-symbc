package gov.nasa.jpf.symbc.veritesting.ast.transformations.Environment;

import gov.nasa.jpf.symbc.veritesting.ast.def.AssignmentStmt;

import java.util.*;

public class Table<K, V> {

    public final LinkedHashMap<K, V> table;
    protected String tableName;
    protected String label1;
    protected String label2;


    protected Table() {
        this.table = new LinkedHashMap<>();
    }

    public Table(String tableName, String label1, String label2) {
        this.table = new LinkedHashMap<>();
        this.tableName = tableName;
        this.label1 = label1;
        this.label2 = label2;
    }


    /**
     * Basic add row inside the table.
     */

    public void add(K v1, V v2) {
        if ((v1 != null) && (v2 != null))
            table.put(v1, v2);
    }

    /**
     * Basic lookup inside the table.
     * @param v
     */
    public V lookup(K v) {
        return table.get(v);
    }

    /**
     * Basic remove element/row inside the table.
     */

    public void remove(K v1) {
        table.remove(v1);
    }


    /**
     * Merging another table to current one.
     *
     * @param t
     */
    public void mergeTable(Table t) {
        this.table.putAll(t.table);
    }

    /**
     * Basic print of the table. inside the table.
     */

    public void print() {
        System.out.println("\nprinting " + tableName + " (" + label1 + "->" + label2 + ")");
        Collection<V> values = table.values();
        if (values != null) {
            Iterator itr = values.iterator();
            if (itr.hasNext())
                if (itr.next() instanceof int[])
                    table.forEach((v1, stackSlots) -> System.out.println(v1 + " --------- " + Arrays.toString((int[]) stackSlots)));
                else
                    table.forEach((v1, v2) -> System.out.println(v1 + " --------- " + v2));
        }

    }

}
