package fr.n7.smt;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.ArrayList;

import com.microsoft.z3.*;
import com.sun.jdi.AbsentInformationException;
import javax.swing.event.MenuKeyEvent;

/**
* Transition system for the "Countdown" game a.k.a. "des chiffres
* et des lettres" in French.
*
* @author Christophe Garion <christophe.garion@isae-supaero.fr>
* @author RÃ©mi Delmas <remi.delmas@onera.fr>
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
        this.maxNofSteps = 2*nums.length-1;
        
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
        
        return context.mkEq(cache.idxStateVar(0),this.context.mkInt(0));

    }
    
    @Override
    public BoolExpr finalStateFormula(int step) {
        ArrayExpr<IntSort,BitVecSort> pile = cache.stackStateVar(step);
        IntExpr index = cache.idxStateVar(step);
        
        BitVecExpr valeur = (BitVecExpr) context.mkSelect(pile, context.mkSub(index, context.mkInt(1)));
        
        BoolExpr finalState = context.mkEq(index, context.mkInt(1));
        finalState = context.mkAnd(finalState, context.mkEq(valeur, toBvNum(this.target)));
        return finalState;
    }
    
    /**
    * A boolean formula that should be true iff states at step and
    * step + 1 are linked by a "push(num)" action.
    */
    private BoolExpr pushNumFormula(int step, int num) {


        BoolExpr pushAction = cache.pushNumVar(step, num);


        IntExpr currentIdx = cache.idxStateVar(step);
        IntExpr nextIdx = cache.idxStateVar(step + 1);
        BoolExpr idxUpdate = context.mkEq(nextIdx, context.mkAdd(currentIdx, context.mkInt(1)));


        ArrayExpr<IntSort, BitVecSort> currentStack = cache.stackStateVar(step);
        ArrayExpr<IntSort, BitVecSort> nextStack = cache.stackStateVar(step + 1);
        BitVecExpr numBV = toBvNum(num);

        ArrayExpr<IntSort, BitVecSort> updatedStack = context.mkStore(currentStack, currentIdx, numBV);
        BoolExpr stackUpdate = context.mkEq(nextStack, updatedStack);


        BoolExpr numUsedOnce = context.mkTrue();
        for (int j = 0; j < step; j++) {
            numUsedOnce = context.mkAnd(numUsedOnce, context.mkNot(cache.pushNumVar(j, num)));
        }


        BoolExpr state = context.mkAnd(pushAction, idxUpdate, stackUpdate, numUsedOnce);

        return context.mkImplies(cache.pushNumVar(step, num), state);
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

        ArrayExpr<IntSort, BitVecSort> currentStack = cache.stackStateVar(step);
        ArrayExpr<IntSort, BitVecSort> nextStack = cache.stackStateVar(step + 1);
        IntExpr currentIdx = cache.idxStateVar(step);
        IntExpr nextIdx = cache.idxStateVar(step + 1);

        BoolExpr auMoins2 = context.mkGe(currentIdx, context.mkInt(2));


        BitVecExpr e1 = (BitVecExpr) context.mkSelect(currentStack, context.mkSub(currentIdx, context.mkInt(1)));
        BitVecExpr e2 = (BitVecExpr) context.mkSelect(currentStack, context.mkSub(currentIdx, context.mkInt(2)));



        BoolExpr precondCheck = precond.get(step, e1, e2);


        BitVecExpr res = opRes.get(step + 1, e1, e2);

        ArrayExpr<IntSort, BitVecSort> updatedStack = context.mkStore(currentStack, context.mkSub(currentIdx, context.mkInt(2)), res);


        BoolExpr idxUpdate = context.mkEq(nextIdx, context.mkSub(currentIdx, context.mkInt(1)));


        BoolExpr stackUpdate = context.mkEq(nextStack, updatedStack);


        BoolExpr action = actVar.get(step);
  
        //on conjoncte toutes les formules
        BoolExpr state = context.mkAnd(auMoins2, idxUpdate, stackUpdate, precondCheck);

        return context.mkImplies(action, state);
    }
    
    /**
     * A boolean formula that should be true iff states at step and
     * step + 1 are linked by a "add" action.
     */
    private BoolExpr addFormula(int step) {
        ActionVar a = cache::addVar;

        ActionPrecondition p = (s, e1, e2) -> {
            if (noOverflows) {
                return context.mkAnd(context.mkBVAddNoOverflow(e1, e2, true), context.mkBVAddNoUnderflow(e1, e2));
            } else {
                return context.mkTrue();
            }
        };

        ActionResult r = (s, e1, e2) -> {
            return context.mkBVAdd(e1, e2);
        };

        return actionFormula(step, a, p, r);
    }

    /**
     * A boolean formula that should be true iff states at step and
     * step + 1 are linked by a "sub" action.
     */
    private BoolExpr subFormula(int step) {
        
        ActionVar a = cache::subVar;

        ActionPrecondition p = (s, e1, e2) -> {
            if (noOverflows) {
                return context.mkAnd(context.mkBVSubNoOverflow(e1, e2), context.mkBVSubNoUnderflow(e1, e2, true));
            } else {
                return context.mkTrue();
            }
        };

        ActionResult r = (s, e1, e2) -> {
            return context.mkBVSub(e1, e2);
        };

        return actionFormula(step, a, p, r);
    }

    /**
     * A boolean formula that should be true iff states at step and
     * step + 1 are linked by a "mul" action.
     */
    private BoolExpr mulFormula(int step) {
        
        ActionVar a = cache::mulVar;

        ActionPrecondition p = (s, e1, e2) -> {
            if (noOverflows) {
                return context.mkAnd(context.mkBVMulNoOverflow(e1, e2, true), context.mkBVMulNoUnderflow(e1, e2));
            } else {
                return context.mkTrue();
            }
        };

        ActionResult r = (s, e1, e2) -> {
            return context.mkBVMul(e1, e2);
        };

        return actionFormula(step, a, p, r);
    }

    /**
     * A boolean formula that should be true iff states at step and
     * step + 1 are linked by a "div" action.
     */
    private BoolExpr divFormula(int step) {
        
        ActionVar a = cache::divVar;

        ActionPrecondition p = (s, e1, e2) -> {

            BoolExpr noDiv0 = context.mkNot(context.mkEq(e2, toBvNum(0))); 

            if (noOverflows) {
                return context.mkAnd(context.mkBVMulNoOverflow(e1, e2, true), context.mkBVMulNoUnderflow(e1, e2), noDiv0);
            } else {
                return noDiv0;
            }
            
        };

        ActionResult r = (s, e1, e2) -> {
            return context.mkBVSDiv(e1, e2);
        };

        return actionFormula(step, a, p, r);
    }   


    @Override
    public BoolExpr transitionFormula(int step) {
        ArrayList<BoolExpr> actionsList = new ArrayList<BoolExpr>();
        actionsList.add(cache.addVar(step));
        actionsList.add(cache.subVar(step));
        actionsList.add(cache.mulVar(step));
        actionsList.add(cache.divVar(step));

        for (int num : nums) {
            actionsList.add(cache.pushNumVar(step,num));
        }

        BoolExpr[] actions = actionsList.toArray(new BoolExpr[0]);

        BoolExpr action = Z3Utils.exactlyOne(actions);
        BoolExpr transition = context.mkAnd(action, addFormula(step), subFormula(step), mulFormula(step), divFormula(step));

        for (int num : nums) {
            transition = context.mkAnd(transition, pushNumFormula(step, num));
        }
        
        return transition;
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

    @Override
    public BitVecExpr finalStateApproxCriterion(int step) {
        ArrayExpr<IntSort,BitVecSort> pile = cache.stackStateVar(step);
        IntExpr index = cache.idxStateVar(step);
        
        BitVecExpr valeur = (BitVecExpr) context.mkSelect(pile, context.mkSub(index, context.mkInt(1)));

        return context.mkBVSub(valeur, toBvNum(this.target));
        
        
    }
    
}