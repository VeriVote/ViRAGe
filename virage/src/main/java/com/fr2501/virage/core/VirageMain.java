package com.fr2501.virage.core;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * The main entry point.
 *
 */
public class VirageMain {
    private static final Logger logger = LogManager.getLogger(VirageMain.class);

    /**
     * The main entry point for ViRAGe.
     * 
     * @param args the command-line arguments
     */
    public static void main(String[] args) {
        try {
            VirageCore core = new VirageCore(args);
            Thread coreThread = new Thread(core, "core");
            coreThread.start();

            while (true) {
            }
        } catch (Exception e) {
            logger.fatal("An unrecoverable error has occurred.", e);
            logger.fatal("The program will now terminate.");
        }
        System.exit(1);
    }
}
