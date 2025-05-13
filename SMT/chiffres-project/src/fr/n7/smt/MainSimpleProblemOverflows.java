package fr.n7.smt;

/**
 * Program to solve a simple problem: [10, 20, 30, 40] as starting
 * numbers and 118 target. There is a solution with bitvectors of
 * size 8 if you accept overflows, otherwise no!
 *
 * @author Christophe Garion <christophe.garion@isae-supaero.fr>
 *
 */
public class MainSimpleProblemOverflows {
    private static int[] nums = {10, 20, 30, 40};

    private static int timeout = 10_000; // in milliseconds

    public static void main(String[] args) {
        System.out.println("\n\033[1mRunning simple tests with overflows.\033[0m");
        MainUtils.runTest(nums, 118, 8, false, false, timeout,
                          true, "solvable with target 118 with overflows");

        MainUtils.runTest(nums, 118, 8, true, false, timeout,
                          false, "solvable with target 118 without overflows");

    }
}
