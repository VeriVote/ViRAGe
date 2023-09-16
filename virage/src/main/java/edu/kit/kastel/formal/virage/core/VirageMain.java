package edu.kit.kastel.formal.virage.core;

import edu.kit.kastel.formal.util.SystemUtils;

/**
 * The main entry point.
 *
 * @author VeriVote
 */
public final class VirageMain {
    // /**
    //  * The logger.
    //  */
    // private static final Logger LOGGER = LogManager.getLogger(VirageMain.class);

    private VirageMain() { }

    /**
     * The main entry point for ViRAGe.
     *
     * @param args the command-line arguments
     */
    public static void main(final String[] args) {
        // try {
        final VirageCore core = new VirageCore(args);
        final Thread coreThread = new Thread(core, "core");
        coreThread.start();
        while (true) {
            SystemUtils.semiBusyWaitingHelper();
        }
        // } catch (final RuntimeException e) {
        //     e.printStackTrace();
        //     LOGGER.fatal("An unrecoverable error has occurred.", e);
        //     LOGGER.fatal("The program will now terminate.");
        // }
        // Last point of failure, no idea what is thrown this far.
        // If this is ever executed, something has gone so wrong
        // that I cannot even imagine it now, so no more specialized
        // catch clause is possible.
        // SystemUtils.exit(1);
    }
}
