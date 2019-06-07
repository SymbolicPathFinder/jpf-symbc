package gov.nasa.jpf.symbc.veritesting.AdapterSynth;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;

import static gov.nasa.jpf.symbc.veritesting.AdapterSynth.TestInput.rand;


public class ArgSubAdapter {
    public boolean[] i_is_const;
    public int[] i_val;

    public boolean b_is_const[];
    public int b_val[];

    public boolean c_is_const[];
    public int c_val[];

    public ArgSubAdapter(boolean[] i_is_const, int[] i_val, boolean[] b_is_const, int[] b_val, boolean[] c_is_const,
                         int[] c_val) {
        this.i_is_const = i_is_const;
        this.i_val = i_val;
        this.b_is_const = b_is_const;
        this.b_val = b_val;
        this.c_is_const = c_is_const;
        this.c_val = c_val;
    }

    public static ArgSubAdapter randomAdapter() {
        ArgSubAdapter ret = new ArgSubAdapter(new boolean[6], new int[6], new boolean[6], new int[6], new boolean[6], new int[6]);
        for (int i = 0; i < 6; i++) {
            ret.i_is_const[i] = rand.nextBoolean();
            ret.i_val[i] = rand.nextInt();
            ret.b_is_const[i] = rand.nextBoolean();
            ret.b_val[i] = rand.nextInt();
            ret.c_is_const[i] = rand.nextBoolean();
            ret.c_val[i] = rand.nextInt();
        }
        return ret;
    }

    public static ArgSubAdapter identityAdapter() {
        ArgSubAdapter a = new ArgSubAdapter(new boolean[6], new int[6], new boolean[6], new int[6], new boolean[6], new int[6]);
        a.i_is_const[0] = a.i_is_const[1] = a.i_is_const[2] = a.i_is_const[3] = a.i_is_const[4] = a.i_is_const[5] = false;
        a.b_is_const[0] = a.b_is_const[1] = a.b_is_const[2] = a.b_is_const[3] = a.b_is_const[4] = a.b_is_const[5] = false;
        a.c_is_const[0] = a.c_is_const[1] = a.c_is_const[2] = a.c_is_const[3] = a.c_is_const[4] = a.c_is_const[5] = false;
        for (int i = 0; i < 6; i++)
            a.i_val[i] = a.b_val[i] = a.c_val[i] = i;
        return a;
    }

    public static ArgSubAdapter zeroAdapter() {
        ArgSubAdapter a = new ArgSubAdapter(new boolean[6], new int[6], new boolean[6], new int[6], new boolean[6], new int[6]);
        a.i_is_const[0] = a.i_is_const[1] = a.i_is_const[2] = a.i_is_const[3] = a.i_is_const[4] = a.i_is_const[5] = false;
        a.b_is_const[0] = a.b_is_const[1] = a.b_is_const[2] = a.b_is_const[3] = a.b_is_const[4] = a.b_is_const[5] = false;
        a.c_is_const[0] = a.c_is_const[1] = a.c_is_const[2] = a.c_is_const[3] = a.c_is_const[4] = a.c_is_const[5] = false;
        for (int i = 0; i < 6; i++)
            a.i_val[i] = a.b_val[i] = a.c_val[i] = 0;
        return a;
    }

    public static void writeAdapter(ObjectOutputStream out, ArgSubAdapter argSub) throws IOException {
        for (int i = 0; i < 6; i++) { out.writeBoolean(argSub.i_is_const[i]); out.writeInt(argSub.i_val[i]); }
        for (int i = 0; i < 6; i++) { out.writeBoolean(argSub.b_is_const[i]); out.writeInt(argSub.b_val[i]); }
        for (int i = 0; i < 6; i++) { out.writeBoolean(argSub.c_is_const[i]); out.writeInt(argSub.c_val[i]); }
    }

    public static ArgSubAdapter readAdapter(ObjectInputStream in) throws IOException {
        ArgSubAdapter argSub = randomAdapter();
        for (int i = 0; i < 6; i++) { argSub.i_is_const[i] = in.readBoolean(); argSub.i_val[i] = in.readInt(); }
        for (int i = 0; i < 6; i++) { argSub.b_is_const[i] = in.readBoolean(); argSub.b_val[i] = in.readInt(); }
        for (int i = 0; i < 6; i++) { argSub.c_is_const[i] = in.readBoolean(); argSub.c_val[i] = in.readInt(); }
        return argSub;
    }

    @Override
    public String toString() {
        StringBuilder ret = new StringBuilder();
        ret.append("(");
        for (int i = 0; i < 6; i++) ret.append(i_is_const[i]).append(",").append(i_val[i]).append(",");
        ret.append("), (");
        for (int i = 0; i < 6; i++) ret.append(b_is_const[i]).append(",").append(b_val[i]).append(",");
        ret.append("), (");
        for (int i = 0; i < 5; i++) ret.append(c_is_const[i]).append(",").append(c_val[i]).append(",");
        ret.append(c_is_const[5]).append(",").append(c_val[5]);
        ret.append(")");
        return ret.toString();
    }

    @Override
    public boolean equals(Object o) {
        if (o instanceof ArgSubAdapter) {
            ArgSubAdapter other = (ArgSubAdapter) o;
            for (int i = 0; i < 6; i++) {
                if (i_is_const[i] != other.i_is_const[i]) {
                    System.out.println("i_is_const mismatch for i = " + i);
                    return false;
                }
                if (i_val[i] != other.i_val[i]) {
                    System.out.println("i_val mismatch for i = " + i);
                    return false;
                }
                if (b_is_const[i] != other.b_is_const[i] || b_val[i] != other.b_val[i]) return false;
                if (c_is_const[i] != other.c_is_const[i] || c_val[i] != other.c_val[i]) return false;
            }
            return true;
        }
        return false;
    }
}
