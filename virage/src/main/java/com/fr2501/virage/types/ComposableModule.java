package com.fr2501.virage.types;

import java.util.List;

/**
 * A composable module (a special type of components) for the modular framework.
 *
 * @author VeriVote
 */
@Deprecated
public class ComposableModule extends Component {
    /**
     * Simple constructor.
     * @param type the type
     * @param name the name
     */
    public ComposableModule(final ComponentType type, final String name) {
        super(type, name);
    }

    /**
     * Simple constructor.
     * @param type the type
     * @param name the name
     * @param parameters the parameters
     */
    public ComposableModule(final ComponentType type, final String name,
            final List<ComponentType> parameters) {
        super(type, name, parameters);
    }
}
