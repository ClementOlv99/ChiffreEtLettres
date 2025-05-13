package fr.n7.smt;

/**
 * Program to solve COMPLEX problems. Use it when you are condident in
 * your implementation!
 *
 * @author Christophe Garion <christophe.garion@isae-supaero.fr>
 *
 */
public class MainComplexProblems {

    private static int[][] nums = {
        {3, 4, 6, 10, 12, 78, 89, 560},
        {8, 10, 2, 1, 5, 50}
    };

    private static int[] target = {6176, 899};

    private static int timeout = 20_000; // in milliseconds

    public static void main(String[] args) {
        MainUtils.runTest(nums[0], target[0], 14, true,
                          false, timeout, true,
                          "on first complex problem");
        MainUtils.runTest(nums[1], target[1], 14, true,
                          false, timeout, true,
                          "on second complex problem");
    }
}
