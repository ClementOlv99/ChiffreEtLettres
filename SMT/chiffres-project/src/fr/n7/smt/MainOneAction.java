package fr.n7.smt;

/**
 * Program to solve "atomic" problems, only one or two actions are required.
 *
 * @author Christophe Garion <christophe.garion@isae-supaero.fr>
 *
 */
public class MainOneAction {

    private static int[][] numsUnit = {
        {},
        {10, 4},
        {4, 10}
    };

    private static int[] targetsUnit = {
        10, 14, 6, 40, 2
    };

    private static int timeout = 10_000; // in milliseconds

    private static void testNoNumbers() {
        MainUtils.runTest(numsUnit[0], targetsUnit[1], 8, false, false, timeout,
                          false, "without numbers (no solution)");
    }

    private static void testOnlyPush() {
        MainUtils.runTest(numsUnit[1], targetsUnit[0], 8, false, false, timeout,
                          true, "solvable with only push");
        MainUtils.runTest(numsUnit[2], targetsUnit[0], 8, false, false, timeout,
                          true, "solvable with only push");
    }

    private static void testOnlyAdd() {
        MainUtils.runTest(numsUnit[1], targetsUnit[1], 8, false, false, timeout,
                          true, "solvable with only add");
        MainUtils.runTest(numsUnit[2], targetsUnit[1], 8, false, false, timeout,
                          true, "solvable with only add");
    }

    private static void testOnlySub() {
        MainUtils.runTest(numsUnit[1], targetsUnit[2], 8, false, false, timeout,
                          true, "solvable with only sub");
        MainUtils.runTest(numsUnit[2], targetsUnit[2], 8, false, false, timeout,
                          true, "solvable with only sub");
    }

    private static void testOnlyMul() {
        MainUtils.runTest(numsUnit[1], targetsUnit[3], 8, false, false, timeout,
                          true, "solvable with only mul");
        MainUtils.runTest(numsUnit[2], targetsUnit[3], 8, false, false, timeout,
                          true, "solvable with only mul");
    }

    private static void testOnlyDiv() {
        MainUtils.runTest(numsUnit[1], targetsUnit[4], 8, false, false, timeout,
                          true, "solvable with only div");
        MainUtils.runTest(numsUnit[2], targetsUnit[4], 8, false, false, timeout,
                          true, "solvable with only div");
    }

    private static void testSimpleUnitTests() {
        testNoNumbers();
        testOnlyPush();
        testOnlyAdd();
        testOnlySub();
        testOnlyMul();
        testOnlyDiv();
    }

    public static void main(String[] args) {
        System.out.println("\n\033[1mRunning \"unit\" tests with only few actions.\033[0m");

        testSimpleUnitTests();
    }
}
