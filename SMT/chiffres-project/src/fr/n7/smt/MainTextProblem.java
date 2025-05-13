package fr.n7.smt;

/**
 * Program to solve the text problem.
 *
 * @author Christophe Garion <christophe.garion@isae-supaero.fr>
 *
 */
public class MainTextProblem {

    static int[] nums = { 8, 10, 2, 1, 5, 50 };

    static int   target = 899;

    public static void main(String[] args) {
        ChiffresTransitionSystem chiffresTS = new ChiffresTransitionSystem(nums, target, 16, true);
        BMC solver = new BMC(chiffresTS, chiffresTS.getMaxNofSteps(),
                             false, false);

        try {
            solver.solve(-1);
        } catch (Throwable t) {
            System.out.println("failed with error:");
            System.out.println(t);
        }
    }
}
