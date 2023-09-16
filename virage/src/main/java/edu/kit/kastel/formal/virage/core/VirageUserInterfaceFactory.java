package edu.kit.kastel.formal.virage.core;

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
     * @param string                    the user interface selection string
     * @param core                      the core object the user interface will use for execution
     * @return a user interface
     * @throws IllegalArgumentException in case of an illegal interface selection
     */
    public VirageUserInterface getUi(final String string, final VirageCore core) {
        switch (string) {
        case VirageStrings.CLI_ARG:
            return new VirageCommandLineInterface(core);
        case VirageStrings.NO_ARG:
            return null;
        default:
            throw new IllegalArgumentException("Illegal user interface selection.");
        }
    }
}
