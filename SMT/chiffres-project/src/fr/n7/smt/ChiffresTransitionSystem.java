package fr.n7.smt;

import java.math.BigInteger;
import java.util.Arrays;

import com.microsoft.z3.*;

/**
 * Transition system for the "Countdown" game a.k.a. "des chiffres
 * et des lettres" in French.
 *
 * @author Christophe Garion <christophe.garion@isae-supaero.fr>
 * @author Rémi Delmas <remi.delmas@onera.fr>
 *
 */
public class ChiffresTransitionSystem extends TransitionSystem {

    private Context       context;
    private ChiffresCache cache;
    private int           bvBits;
    private int[]         nums;
    private int           target;
    private int           maxNofSteps;
    private boolean       noOverflows;

    // minmum and maximum values for bitvectors
    private BigInteger    maxBvRange;
    private BigInteger    minBvRange;

    private BitVecNum toBvNum(int num) {
        if (noOverflows) {
            BigInteger bigNum = new BigInteger(String.valueOf(num));

            if (bigNum.compareTo(minBvRange) >= 0 && bigNum.compareTo(maxBvRange) <= 0)
                return context.mkBV(num, bvBits);
            else
                throw new Error("the numeral " + String.valueOf(num) +
                                " exceed signed bitvectors of size " +
                                String.valueOf(bvBits));
        } else {
            return context.mkBV(num, bvBits);
        }
    }

    /**
     * Creates a new Chiffres transition system
     *
     * @param nums an array with the starting integers
     * @param target the target integer
     * @param bvBits the number of bits in bitvectors
     * @param noOverflows a boolean that is true if you do not want
     *        overflows with bitvectors
     */
    public ChiffresTransitionSystem(int[] nums, int target, int bvBits, boolean noOverflows) {
        this.context     = Z3Utils.getZ3Context();
        this.cache       = new ChiffresCache(bvBits);
        this.nums        = nums;
        this.target      = target;
        this.bvBits      = bvBits;
        this.maxBvRange  = new BigInteger("2").pow(bvBits-1).subtract(new BigInteger("1"));
        this.minBvRange  = new BigInteger("2").pow(bvBits-1).negate();

        // TODO: to complete!
        this.maxNofSteps = 0;

        this.noOverflows = noOverflows;
    }

    /**
     * Gets the maximum number of steps of the transition system.
     *
     */
    public int getMaxNofSteps() {
        return this.maxNofSteps;
    }

    @Override
    public BoolExpr initialStateFormula() {
        // TODO: to complete!

        return null;
    }

    @Override
    public BoolExpr finalStateFormula(int step) {
        // TODO: to complete!

        return null;
    }

    /**
     * A boolean formula that should be true iff states at step and
     * step + 1 are linked by a "push(num)" action.
     */
    private BoolExpr pushNumFormula(int step, int num) {
        // TODO: to complete!

        return null;
    }


    private interface ActionVar {
        /**
         * Returns the decision variable for the action at step.
         *
         */
        BoolExpr get(int step);
    }

    private interface ActionResult {
        /**
         * Returns the expression of the action result at step using
         * e1 and e2, the two top values of the stack.
         *
         */
        BitVecExpr get(int step, BitVecExpr e1, BitVecExpr e2);
    }

    private interface ActionPrecondition {
        /**
         * Returns the expression of the action precondition at step
         * using e1 and e2, the two top values of the stack.
         *
         */
        BoolExpr get(int step, BitVecExpr e1, BitVecExpr e2);
    }


    private BoolExpr actionFormula(int step, ActionVar actVar, ActionPrecondition precond, ActionResult opRes) {
        // TODO: to complete!

        return null;
    }

    /**
     * A boolean formula that should be true iff states at step and
     * step + 1 are linked by a "add" action.
     */
    private BoolExpr addFormula(int step) {
        // TODO: to complete!

        return null;
    }

    /**
     * A boolean formula that should be true iff states at step and
     * step + 1 are linked by a "sub" action.
     */
    private BoolExpr subFormula(int step) {
        // TODO: to complete!

        return null;
    }

    /**
     * A boolean formula that should be true iff states at step and
     * step + 1 are linked by a "mul" action.
     */
    private BoolExpr mulFormula(int step) {
        // TODO: to complete!

        return null;
    }

    /**
     * A boolean formula that should be true iff states at step and
     * step + 1 are linked by a "div" action.
     */
    private BoolExpr divFormula(int step) {
        // TODO: to complete!

        return null;
    }

    @Override
    public BoolExpr transitionFormula(int step) {
        // TODO: to complete!

        return null;
    }

    @Override
    public void printParams() {
        System.out.println("\nChiffres transition system parameters:");
        System.out.println("- nums       : " + Arrays.toString(nums));
        System.out.println("- target     : " + String.valueOf(target));
        System.out.println("- bvBits     : " + String.valueOf(bvBits));
        System.out.println("- noOverflows: " + String.valueOf(noOverflows));
    }

    /**
     * Prints the stack at step.
     */
    private void printStackAtStep(Model m, int step) {
        int idxState = ((IntNum) m.eval(cache.idxStateVar(step), true)).getInt();

        for (int idx = 0; idx <= maxNofSteps; idx++) {
            BitVecExpr resbv =
                (BitVecExpr) context.mkSelect(cache.stackStateVar(step),
                                              context.mkInt(idx));
            IntExpr resi = context.mkBV2Int(resbv, true);

            if (idx == 0) {
                System.out.print("|");
            }

            if (idx < idxState) {
                System.out.print("|\033[7m");
            } else {
                System.out.print("|");
            }

            System.out.printf("%4d", ((IntNum) m.eval(resi, true)).getInt());

            if (idx < idxState) {
                System.out.print("\033[m");
            }
        }
    }

    @Override
    public void printModel(Model m, int steps) {
        System.out.printf("  init %3s ~> ", " ");
        printStackAtStep(m, 0);
        System.out.println();

        for (int step = 0; step < steps; step++) {
            for (int num : nums) {
                if (m.eval(cache.pushNumVar(step, num), true).isTrue()) {
                    System.out.printf("  push %3d ~> ", num);
                }
            }

            if (m.eval(cache.mulVar(step), true).isTrue()) {
                System.out.printf("  mul %4s ~> ", " ");
            }

            if (m.eval(cache.divVar(step), true).isTrue()) {
                System.out.printf("  div %4s ~> ", " ");
            }

            if (m.eval(cache.addVar(step), true).isTrue()) {
                System.out.printf("  add %4s ~> ", " ");
            }

            if (m.eval(cache.subVar(step), true).isTrue()) {
                System.out.printf("  sub %4s ~> ", " ");
            }

            printStackAtStep(m, step + 1);

            System.out.println();
        }
    }
}
