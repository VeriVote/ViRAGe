package com.fr2501.virage.core;

/**
 * A factory for {@link VirageUserInterface}.
 *
 * @author VeriVote
 */
public class VirageUserInterfaceFactory {
    /**
     * Creates the user interface described by string, defaults to
     * {@link VirageCommandLineInterface}.
     *
     * @param string the string
     * @param core the core object the user interface will use for execution
     * @return a user interface
     */
    public VirageUserInterface getUi(final String string, final VirageCore core) {
        final VirageUserInterface res;

        if (string.equals(VirageStrings.CLI_ARG)) {
            res = new VirageCommandLineInterface(core);

        } else {
            res = new VirageCommandLineInterface(core);
        }

        return res;
    }
}
