/**
 * Simple class with some utility methods for programs
 *
 * @author C. Garion
 */

package fr.n7.smt;

import com.microsoft.z3.Status;

public class MainUtils {
    public static void runTest(int[] nums,
                               int target,
                               int bvBits,
                               boolean noOverflows,
                               boolean approximate,
                               int timeout,
                               boolean satExpected,
                               String message) {
        System.out.println("\n\n* Starting test " + message);
        ChiffresTransitionSystem chiffresTS = new ChiffresTransitionSystem(nums, target, bvBits, noOverflows);
        BMC solver = new BMC(chiffresTS, chiffresTS.getMaxNofSteps(), approximate, false);

        Status s = null;

        try {
            s = solver.solve(timeout);
        } catch (Throwable t) {
            System.out.println("failed with error:");
            System.out.println(t);
        }

        if (satExpected) {
            assert s == Status.SATISFIABLE : "should be SAT!";
        } else {
            assert s == Status.UNSATISFIABLE : "should be UNSAT!";
        }
    }
}
