package fr.n7.smt;

/**
 * A simple simulation using the BMC algorithm for {@link DummyTransitionSystem}.
 *
 * @author Christophe Garion
 */

public class MainDummySimulation {
    public static void main(String[] args) {
        int maxNOfSteps = 150;

        DummyTransitionSystem dummySystem =
            new DummyTransitionSystem(3, maxNOfSteps, 150);
        BMC simulation = new BMC(dummySystem, maxNOfSteps, false, true);

        simulation.solve(-1);
    }
}
