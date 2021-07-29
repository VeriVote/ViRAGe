package com.fr2501.virage.analyzer;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import com.fr2501.util.StringUtils;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.ExternalSoftwareUnavailableException;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.Property;
import com.fr2501.virage.types.SearchResult;
import com.fr2501.virage.types.ValueNotPresentException;

/**
 * Simple implementation of the {@link CompositionAnalyzer}, using Prolog with iterative deepening.
 *
 * @author VeriVote
 */
public final class AdmissionCheckPrologCompositionAnalyzer extends SimplePrologCompositionAnalyzer {
    /** The logger. */
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

        final AdmissionGuardGenerator generator = new AdmissionGuardGenerator(this.framework);

        final File admissionGuards;
        try {
            admissionGuards = generator.createAdmissionGuardFile();

            this.facade.consultFile(admissionGuards.getAbsolutePath());

            if (!loadedMetaInterpreter) {
                this.facade.consultFile(
                        this.getClass().getClassLoader().getResource("meta_interpreter.pl"));
                loadedMetaInterpreter = true;
            }
        } catch (final IOException e) {
            LOGGER.error("An error occured.", e);
        }
    }

    @Override
    public SearchResult<DecompositionTree> generateComposition(final List<Property> properties) {
        for (final Property property : properties) {
            if (property.getArity() != 1) {
                throw new IllegalArgumentException(
                        "For now, only unary " + "properties can be used in queries.");
            }
        }

        // Safety measure to ensure all properties talking about the same element.
        final List<String> admitStrings = new LinkedList<String>();
        final List<String> propertyStrings = new LinkedList<String>();
        for (final Property property : properties) {
            admitStrings.add(AdmissionGuardStrings.ADMITS
                    + property.getInstantiatedString(DEFAULT_VARIABLE));
            propertyStrings.add(property.getName() + AdmissionGuardStrings.SUFFIX
                    + property.getInstantiatedStringWithoutName(DEFAULT_VARIABLE));
        }
        admitStrings.addAll(propertyStrings);

        final String query = StringUtils.printCollection(admitStrings);

        final SearchResult<Map<String, String>> result = this.facade.iterativeDeepeningQuery(query);

        Map<String, String> resultMap = null;
        if (result.hasValue()) {
            try {
                resultMap = result.getValue();
            } catch (final ValueNotPresentException e) {
                // This should never happen.
                LOGGER.warn("This should not have happened.");
                LOGGER.warn(e);
            }

            final String solution = resultMap.get(DEFAULT_VARIABLE);
            final DecompositionTree solutionTree = DecompositionTree.parseString(solution);

            return new SearchResult<DecompositionTree>(result.getState(), solutionTree);
        } else {
            return new SearchResult<DecompositionTree>(result.getState(), null);
        }
    }

}
