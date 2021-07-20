package com.fr2501.virage.core;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * The main entry point.
 *
 */
public class VirageMain {
    /**
     * The logger.
     */
    private static final Logger LOGGER = LogManager.getLogger(VirageMain.class);

    /**
     * The main entry point for ViRAGe.
     *
     * @param args the command-line arguments
     */
    public static void main(final String[] args) {
        try {
            final VirageCore core = new VirageCore(args);
            final Thread coreThread = new Thread(core, "core");
            coreThread.start();

            while (true) {
            }
            // Last point of failure, no idea what is thrown this far.
            // If this is ever executed, something has gone so wrong
            // that I cannot even imagine it now, so no more specialized
            // catch clause is possible.
        } catch (final Exception e) {
            LOGGER.fatal("An unrecoverable error has occurred.", e);
            LOGGER.fatal("The program will now terminate.");
        }
        System.exit(1);
    }
}
