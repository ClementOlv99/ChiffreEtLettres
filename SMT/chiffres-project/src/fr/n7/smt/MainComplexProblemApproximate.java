package fr.n7.smt;

/**
 * Program to solve a problem with approximate algorithm.
 *
 * Beware, it takes some time!
 *
 * @author Christophe Garion <christophe.garion@isae-supaero.fr>
 *
 */
public class MainComplexProblemApproximate {

    private static int[] nums = {2, 3, 5, 11};

    private static int[] nums2 = {5, 6, 7, 9 };

    private static int target = 111;

    private static int target2 = 300;

    private static int timeout = 40_000; // in milliseconds

    public static void main(String[] args) {
        /* 
        MainUtils.runTest(nums, target, 14, true,
                          true, timeout, true,
                          "on first complex problem");
        */
        

        MainUtils.runTest(nums2, target2, 14, true,
                          true, timeout, true,
                          "on second complex problem");

        
    }
}
