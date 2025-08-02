package edu.kit.kastel.formal.virage.types;

import java.util.List;

/**
 * A module that can be composed (a special type of components) for the modular framework.
 * <b>Warning:</b> This was set to deprecated with no explicit justification,
 * maybe handle with care.
 *
 * @author VeriVote
 */
public class ComposableModule extends Component {
    /**
     * Simple constructor.
     *
     * @param type the type
     * @param name the name
     */
    public ComposableModule(final ComponentType type, final String name) {
        super(type, name);
    }

    /**
     * Simple constructor.
     *
     * @param type the type
     * @param name the name
     * @param parameters the parameters
     */
    public ComposableModule(final ComponentType type, final String name,
                            final List<ComponentType> parameters) {
        super(type, name, parameters);
    }
}
