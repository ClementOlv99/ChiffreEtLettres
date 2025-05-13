package fr.n7.smt;


import com.microsoft.z3.*;

/**
 * A Bounded Model-Checking (BMC) motor on a transition system.
 *
 * All warnings about unchecked type safety problems are suppressed.
 *
 * @author Christophe Garion
 */
@SuppressWarnings("unchecked")
public class BMC {

    private TransitionSystem system;
    private Context          context;
    private int              maxNOfSteps;
    private boolean          useApprox;
    private boolean          simulation;

    private void printParams() {
        System.out.println("\nBMC parameters:");
        System.out.println("- max nb of steps: " + this.maxNOfSteps);
        this.system.printParams();
    }

    /**
     * Create a BMC instance for a particular transition system.
     *
     * @param system the transition system
     * @param maxNOfSteps the maximum number of unrolling steps
     * @param useApprox to use approximate resolution when needed
     * @param simulation if true, then BMC is used to simulate the system
     *                   In this case, no approximate solver is used.
     */
    public BMC(TransitionSystem system,
               int maxNOfSteps,
               boolean useApprox,
               boolean simulation) {
        this.context = Z3Utils.getZ3Context();

        // initialize system
        this.system      = system;
        this.maxNOfSteps = maxNOfSteps;
        this.useApprox   = simulation ? false : useApprox;
        this.simulation  = simulation;
    }

    /**
     * This method tries to exactly solve the BMC problem. It unrolls
     * at most maxNOfSteps transitions starting from initial state.
     *
     * For each iteration of BMC:
     *
     * 1. a transition formula for the next step is added to the solver
     * 2. the final state formula for the next step is pushed into the solver
     * 3. if the problem is SAT then solution is printed
     *    else if the problem is UNSAT, the final state formula is popped
     *    and the next iteration is done
     *
     *    If the problem is UNKNOWN, the UNKNOWN status is returned.
     * 4. if the problem is UNSAT for all iterations, the UNSAT status
     *    is returned
     *
     * If the BMC solver is configured for simulation (cf. {@link BMC}),
     * then the final state formula is always True and the BMC is executed
     * exactly maxNOfSteps.
     *
     * @param timeout the timeout to use. If negative, no timeout is used
     */
    private Status solveExact(int timeout) {
        

        // add initial state formula

        // config timeout if necessary

        // main loop:
        // - if not in simulation mode, add final state formula
        //   if it is not null
        // - check satisfiability
        //   - if UNKNOWN, return UNKNOWN
        //   - if UNSAT, add a new transition step
        //   - if SAT, return SATISFIABLE if not in simulation mode
        //   - print simple info (SAT/UNSAT/UNKWON at step XXX etc)

        // return UNSATISFIABLE or SATISFIABLE if in simulation mode


        Solver solver  = context.mkSolver();

        solver.add(system.initialStateFormula());

        int step = 0;
        while(step <= (maxNOfSteps-1)) {
            if (!simulation) {
                solver.push();
                solver.add(system.finalStateFormula(step));
            }

            

            Status q = solver.check();

            switch (q) {
                case UNKNOWN:
                    System.out.println("  Unknown because:\n" + solver.getReasonUnknown());
                    return Status.UNKNOWN;
                

                case SATISFIABLE:
                    
                    if (!simulation) {
                        System.out.println("SAT");
                        system.printModel(solver.getModel(), step);
                        return Status.SATISFIABLE;
                    } else {
                        system.printModel(solver.getModel(), step);
                        solver.add(system.transitionFormula(step)); 
                    }

                break;
               

                default:
                    System.out.println("UNSAT");
                    if (!simulation) {
                        solver.pop();
                        solver.add(system.transitionFormula(step));
                    }
                break;

            }
            step++;
        }
        Status qf = solver.check();
        return (qf);
    }

    /**
     * This method tries to approximatively solve the BMC problem using
     * a Max-SMT solver. The main differences with the exact solver are
     * are the following:
     *
     * 1. push and pop cannot be used, therefore the complete set of
     *    formulas has to be built at each iteration
     * 2. the negation of the expected property has to be added for
     *    the next step
     * 3. the problem should therefore be SAT at each iteration. If not,
     *    return the corresponding status (UNSAT or UNKNOWN). If the
     *    problem is SAT at each step, return SAT.
     *
     * @param timeout the timeout to use. If negative, no timeout is used
     */
    private Status solveApprox(int timeout) {
        // TODO: to complete!

        return Status.SATISFIABLE;
    }

    /**
     * Tries to solve the BMC problem using exact resolution and
     * approximate resolution if asked.
     *
     * @param timeout the timeout to use. If negative, no timeout is used
     */
    public Status solve(int timeout) {
        this.printParams();

        Status s = this.solveExact(timeout);

        if (this.useApprox && s != Status.SATISFIABLE) {
            s = this.solveApprox(timeout);
        }

        return s;
    }
}
