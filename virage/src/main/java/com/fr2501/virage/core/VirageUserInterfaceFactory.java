package com.fr2501.virage.core;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * A factory for {@link VirageUserInterface}.
 *
 */
public class VirageUserInterfaceFactory {
    private static final Logger logger = LogManager.getLogger(VirageUserInterfaceFactory.class);

    /**
     * Creates the user interface described by string, defaults to
     * {@link VirageCommandLineInterface}.
     * 
     * @param string the string
     * @param core the core object the user interface will use for execution
     * @return a user interface
     */
    public VirageUserInterface getUi(String string, VirageCore core) {
        VirageUserInterface res;

        if (string.equals(VirageStrings.CLI_ARG)) {
            res = new VirageCommandLineInterface(core);

        } else {
            logger.info("Invalid ui value, defaulting to cli.");
            res = new VirageCommandLineInterface(core);
        }

        return res;
    }
}
