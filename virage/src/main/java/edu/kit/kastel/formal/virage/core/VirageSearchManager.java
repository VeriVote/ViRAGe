package edu.kit.kastel.formal.virage.core;

import java.util.LinkedList;
import java.util.List;

import edu.kit.kastel.formal.virage.analyzer.CompositionAnalyzer;
import edu.kit.kastel.formal.virage.types.BooleanWithUncertainty;
import edu.kit.kastel.formal.virage.types.CompositionProof;
import edu.kit.kastel.formal.virage.types.DecompositionTree;
import edu.kit.kastel.formal.virage.types.Property;
import edu.kit.kastel.formal.virage.types.SearchResult;

/**
 * A class used to enable the use of different solvers without having to change application code.
 *
 * @author VeriVote
 */
public class VirageSearchManager {
    /**
     * Error message for missing analyzers.
     */
    private static final String NO_ANALYZERS = "No analyzers available!";

    /**
     * The list of analyzers to be used by this manager.
     */
    private final List<CompositionAnalyzer> analyzers;

    /**
     * Simple constructor.
     */
    public VirageSearchManager() {
        this.analyzers = new LinkedList<CompositionAnalyzer>();
    }

    /**
     * Adds an analyzer to the manager.
     *
     * @param analyzer the analyzer
     */
    public void addAnalyzer(final CompositionAnalyzer analyzer) {
        this.analyzers.add(analyzer);
    }

    /**
     * Calls {@link CompositionAnalyzer#analyzeComposition} on all its analyzers.
     *
     * @param composition the decomposition tree
     * @param properties the desired property set
     * @return a list of results, ordered in the same way as the analyzers
     * @throws IllegalStateException if no analyzers are available
     */
    public List<List<SearchResult<BooleanWithUncertainty>>> analyzeComposition(
            final DecompositionTree composition, final List<Property> properties)
                    throws IllegalStateException {
        if (this.analyzers.isEmpty()) {
            throw new IllegalStateException(NO_ANALYZERS);
        }
        // TODO Parallelize.
        final List<List<SearchResult<BooleanWithUncertainty>>> results =
                new LinkedList<List<SearchResult<BooleanWithUncertainty>>>();
        for (final CompositionAnalyzer analyzer: this.analyzers) {
            results.add(analyzer.analyzeComposition(composition, properties));
        }
        return results;
    }

    /**
     * Calls {@link CompositionAnalyzer#generateComposition} on all its analyzers.
     *
     * @param properties the desired property set
     * @return a list of results, ordered in the same way as the analyzers
     * @throws IllegalStateException if no analyzers are available
     */
    public List<SearchResult<DecompositionTree>> generateComposition(
            final List<Property> properties) throws IllegalStateException {
        if (this.analyzers.isEmpty()) {
            throw new IllegalStateException(NO_ANALYZERS);
        }
        // TODO Parallelize.
        final List<SearchResult<DecompositionTree>> results =
                new LinkedList<SearchResult<DecompositionTree>>();
        for (final CompositionAnalyzer analyzer: this.analyzers) {
            results.add(analyzer.generateComposition(properties));
        }
        return results;
    }

    /**
     * Calls {@link CompositionAnalyzer#proveClaims} on all its analyzers.
     *
     * @param composition the decomposition tree
     * @param properties the proposed property set
     * @return a list of results, ordered in the same way as the analyzers
     * @throws IllegalStateException if no analyzers are available
     */
    public List<List<CompositionProof>> proveClaims(final DecompositionTree composition,
                                                    final List<Property> properties)
                                                            throws IllegalStateException {
        if (this.analyzers.isEmpty()) {
            throw new IllegalStateException(NO_ANALYZERS);
        }
        // TODO Parallelize.
        final List<List<CompositionProof>> results = new LinkedList<List<CompositionProof>>();
        for (final CompositionAnalyzer analyzer: this.analyzers) {
            results.add(analyzer.proveClaims(composition, properties));
        }
        return results;
    }
}
