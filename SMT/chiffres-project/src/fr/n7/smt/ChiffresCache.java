package fr.n7.smt;

import java.util.HashMap;

import com.microsoft.z3.*;

class ChiffresCache {
    // Z3 context
    private Context context = Z3Utils.getZ3Context();

    // bit vectors size
    private int bvBits;

    // booleans constants cache. They are indexed by their names
    private HashMap<String, BoolExpr> boolCache = new HashMap<>();

    // bits vectors constants cache. They are indexed by their names
    private HashMap<String, BitVecExpr> bvCache = new HashMap<>();

    // integer constants cache. They are indexed by their names
    private HashMap<String, IntExpr> intCache = new HashMap<>();

    // arrays constants cache. They are indexed by their names
    private HashMap<String, ArrayExpr<IntSort, BitVecSort>> arrayCache = new HashMap<>();

    /**
     * Create new cache.
     *
     * @param bvBits the number of bits of bit vectors
     */
    ChiffresCache(int bvBits) {
        this.bvBits = bvBits;
    }

    /**
     * Returns boolean cache constant if present or create it.
     */
    private BoolExpr boolConst(String name) {
        BoolExpr res = boolCache.get(name);

        if (res == null) {
            res = Z3Utils.getZ3Context().mkBoolConst(name);
            boolCache.put(name, res);
        }

        return res;
    }

    /**
     * Returns bit vector cache constant if present or create it.
     */
    private BitVecExpr bvConst(String name) {
        BitVecExpr res = bvCache.get(name);

        if (res == null) {
            res = context.mkBVConst(name, this.bvBits);
            bvCache.put(name, res);
        }

        return res;
    }

    /**
     * Returns integer cache constant if present or create it.
     */
    private IntExpr intConst(String name) {
        IntExpr res = intCache.get(name);

        if (res == null) {
            res = context.mkIntConst(name);
            intCache.put(name, res);
        }

        return res;
    }

    /**
     * Returns array cache constant if present or create it.
     */
    private ArrayExpr<IntSort, BitVecSort> arrayConst(String name) {
        ArrayExpr<IntSort, BitVecSort> res = arrayCache.get(name);

        if (res == null) {
            res = context.mkArrayConst(name,
                                       context.getIntSort(),
                                       context.mkBitVecSort(this.bvBits));
            arrayCache.put(name, res);
        }

        return res;
    }

    /**
     * Decision variable corresponding to the action "push a numeral on the stack"
     * at a given step.
     */
    BoolExpr pushNumVar(int step, int num) {
        return boolConst("push_" + String.valueOf(num) + "@" +
                         String.valueOf(step));
    }

    /**
     * Decision variable corresponding to the action "add the two top elements
     * on the stack" at a given step.
     */
    BoolExpr addVar(int step) {
        return boolConst("add@" + String.valueOf(step));
    }

    /**
     * Decision variable corresponding to the action "substract the two
     * top elements on the stack" at a given step.
     */
    BoolExpr subVar(int step) {
        return boolConst("sub@" + String.valueOf(step));
    }

    /**
     * Decision variable corresponding to the action "multiply
     * the two top elements on the stack" at a given step.
     */
    BoolExpr mulVar(int step) {
        return boolConst("mul@" + String.valueOf(step));
    }

    /**
     * Decision variable corresponding to the action "divide the
     * two top elements of the stack" at a given step.
     */
    BoolExpr divVar(int step) {
        return boolConst("div@" + String.valueOf(step));
    }

    /**
     * State variable representing the stack at a given step.
     */
    ArrayExpr<IntSort, BitVecSort> stackStateVar(int step) {
        return arrayConst("stack@" + String.valueOf(step));
    }

    /**
     * State variable representing the top stack index at a given
     * step.
     */
    IntExpr idxStateVar(int step) {
        return intConst("idx@" + String.valueOf(step));
    }
}
