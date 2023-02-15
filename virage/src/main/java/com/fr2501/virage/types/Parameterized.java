package com.fr2501.virage.types;

import java.util.List;

/**
 * Parts of the framework which have parameters.
 *
 * @author VeriVote
 */
public interface Parameterized {
    /**
     * Simple getter.
     * @return the parameters types
     */
    List<ComponentType> getParameters();
}
