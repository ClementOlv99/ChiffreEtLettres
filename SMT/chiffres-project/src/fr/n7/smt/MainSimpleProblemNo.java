package fr.n7.smt;

/**
 * Program to solve a simple problem: [10, 20, 30, 40] as starting
 * numbers and 119 target. Do not consider overflows.
 *
 * There is no solution!
 *
 * @author Christophe Garion <christophe.garion@isae-supaero.fr>
 *
 */
public class MainSimpleProblemNo {
    private static int[] nums = {10, 20, 30, 40};

    private static int timeout = 10_000; // in milliseconds

    public static void main(String[] args) {
        System.out.println("\n\033[1mRunning simple tests with NO solution.\033[0m");
        MainUtils.runTest(nums, 119, 8, false, false, timeout,
                          false, "not solvable with target 119");
        MainUtils.runTest(nums, 119, 14, false, false, timeout,
                          false, "not solvable with target 119");
    }
}
