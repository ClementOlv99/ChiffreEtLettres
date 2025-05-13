package fr.n7.smt;

/**
 * Program to solve a simple problem: [10, 20, 30, 40] as starting
 * numbers and 120 target. Do not consider overflows.
 *
 * @author Christophe Garion <christophe.garion@isae-supaero.fr>
 *
 */
public class MainSimpleProblem {
    private static int[] nums = {10, 20, 30, 40};

    private static int timeout = 10_000; // in milliseconds

    public static void main(String[] args) {
        System.out.println("\n\033[1mRunning simple tests with a solution.\033[0m");

        MainUtils.runTest(nums, 120, 4, false, false, timeout,
                          true, "solvable with target 120");
        MainUtils.runTest(nums, 120, 8, false, false, timeout,
                          true, "solvable with target 120");
        MainUtils.runTest(nums, 120, 14, false, false, timeout,
                          true, "solvable with target 120");
    }
}
