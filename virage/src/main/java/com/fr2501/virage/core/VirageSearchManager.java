package com.fr2501.virage.core;

import java.util.LinkedList;
import java.util.List;

import com.fr2501.virage.analyzer.CompositionAnalyzer;
import com.fr2501.virage.types.BooleanWithUncertainty;
import com.fr2501.virage.types.CompositionProof;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.Property;
import com.fr2501.virage.types.SearchResult;

/**
 * A class used to enable the use of different solvers without having to change application code.
 *
 */
public class VirageSearchManager {
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
     */
    public List<List<SearchResult<BooleanWithUncertainty>>> analyzeComposition(
            final DecompositionTree composition, final List<Property> properties)
                    throws IllegalStateException {
        if (this.analyzers.isEmpty()) {
            throw new IllegalStateException("No analyzers available.");
        }

        // TODO Parallelize.
        final List<List<SearchResult<BooleanWithUncertainty>>> results =
                new LinkedList<List<SearchResult<BooleanWithUncertainty>>>();

        for (int i = 0; i < this.analyzers.size(); i++) {
            final List<SearchResult<BooleanWithUncertainty>> result = this.analyzers.get(i)
                    .analyzeComposition(composition, properties);
            results.add(result);
        }

        return results;
    }

    /**
     * Calls {@link CompositionAnalyzer#generateComposition} on all its analyzers.
     *
     * @param properties the desired property set
     * @return a list of results, ordered in the same way as the analyzers
     */
    public List<SearchResult<DecompositionTree>> generateComposition(
            final List<Property> properties) throws IllegalStateException {
        if (this.analyzers.isEmpty()) {
            throw new IllegalStateException("No analyzers available.");
        }

        // TODO Parallelize.
        final List<SearchResult<DecompositionTree>> results =
                new LinkedList<SearchResult<DecompositionTree>>();

        for (int i = 0; i < this.analyzers.size(); i++) {
            final SearchResult<DecompositionTree> result = this.analyzers.get(i)
                    .generateComposition(properties);
            results.add(result);
        }

        return results;
    }

    /**
     * Calls {@link CompositionAnalyzer#proveClaims} on all its analyzers.
     *
     * @param composition the decomposition tree
     * @param properties the proposed property set
     * @return a list of results, ordered in the same way as the analyzers
     */
    public List<List<CompositionProof>> proveClaims(final DecompositionTree composition,
            final List<Property> properties) throws IllegalStateException {
        if (this.analyzers.isEmpty()) {
            throw new IllegalStateException("No analyzers available.");
        }

        // TODO Parallelize.
        final List<List<CompositionProof>> results = new LinkedList<List<CompositionProof>>();

        for (int i = 0; i < this.analyzers.size(); i++) {
            final List<CompositionProof> result = this.analyzers.get(i).proveClaims(composition,
                    properties);
            results.add(result);
        }

        return results;
    }
}
