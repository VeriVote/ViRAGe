package edu.kit.kastel.formal.virage.analyzer;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import edu.kit.kastel.formal.util.StringUtils;
import edu.kit.kastel.formal.virage.types.DecompositionTree;
import edu.kit.kastel.formal.virage.types.ExternalSoftwareUnavailableException;
import edu.kit.kastel.formal.virage.types.FrameworkRepresentation;
import edu.kit.kastel.formal.virage.types.Property;
import edu.kit.kastel.formal.virage.types.SearchResult;
import edu.kit.kastel.formal.virage.types.ValueNotPresentException;

/**
 * Simple implementation of the {@link CompositionAnalyzer}, using Prolog with iterative deepening.
 *
 * @author VeriVote
 */
public final class AdmissionCheckPrologCompositionAnalyzer extends SimplePrologCompositionAnalyzer {
    /**
     * The logger.
     */
    private static final Logger LOGGER = LogManager.getLogger();

    /**
     * Default variable name.
     */
    private static final String DEFAULT_VARIABLE = "X";

    /**
     * Initializes a SimplePrologCompositionAnalyzer and consults the specified framework.
     *
     * @param framework the framework
     * @throws IOException but should actually not
     * @throws ExternalSoftwareUnavailableException if SWI-Prolog is unavailable
     */
    public AdmissionCheckPrologCompositionAnalyzer(final FrameworkRepresentation framework)
            throws IOException, ExternalSoftwareUnavailableException {
        super(framework);
        LOGGER.info("Initialising AdmissionCheckPrologCompositionAnalyzer");
    }

    @Override
    protected void consultKnowledgeBase() {
        super.consultKnowledgeBase();
        final AdmissionGuardGenerator generator = new AdmissionGuardGenerator(this.getFramework());
        final File admissionGuards;
        try {
            admissionGuards = generator.createAdmissionGuardFile();
            this.getFacade().consultFile(admissionGuards.getAbsolutePath());
            if (!metaInterpreterLoaded()) {
                this.getFacade().consultFile(
                        this.getClass().getClassLoader().getResource(META_INTERPRETER));
                setMetaInterpreterLoaded(true);
            }
        } catch (final IOException e) {
            LOGGER.error("An error occured.", e);
        }
    }

    @Override
    public SearchResult<DecompositionTree> generateComposition(final List<Property> properties) {
        for (final Property property: properties) {
            if (property.getArity() != 1) {
                throw new IllegalArgumentException(
                        "For now, only unary " + "properties can be used in queries.");
            }
        }
        // Safety measure to ensure all properties talking about the same element.
        final List<String> admitStrings = new LinkedList<String>();
        final List<String> propertyStrings = new LinkedList<String>();
        for (final Property property: properties) {
            admitStrings.add(AdmissionGuardStrings.ADMITS
                    + property.getInstantiatedString(DEFAULT_VARIABLE));
            propertyStrings.add(property.getName() + AdmissionGuardStrings.SUFFIX
                    + property.getInstantiatedStringWithoutName(DEFAULT_VARIABLE));
        }
        admitStrings.addAll(propertyStrings);
        final String query = StringUtils.printCollection(admitStrings);
        final SearchResult<Map<String, String>> result =
                this.getFacade().iterativeDeepeningQuery(query);
        Map<String, String> resultMap = Map.of();
        final DecompositionTree solutionTree;
        if (result.hasValue()) {
            try {
                resultMap = result.getValue();
            } catch (final ValueNotPresentException e) {
                // This should never happen.
                LOGGER.warn("This should not have happened.");
                LOGGER.warn(e);
            }
            solutionTree = DecompositionTree.parseString(resultMap.get(DEFAULT_VARIABLE));
        } else {
            solutionTree = null;
        }
        return new SearchResult<DecompositionTree>(result.getState(), solutionTree);
    }
}
