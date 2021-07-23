package com.fr2501.virage.analyzer;

import java.io.IOException;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import com.fr2501.util.StringUtils;
import com.fr2501.virage.prolog.JplFacade;
import com.fr2501.virage.prolog.PrologProof;
import com.fr2501.virage.prolog.QueryState;
import com.fr2501.virage.types.BooleanWithUncertainty;
import com.fr2501.virage.types.CompositionProof;
import com.fr2501.virage.types.CompositionRule;
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
public class SimplePrologCompositionAnalyzer implements CompositionAnalyzer {
    /**
     * True if resources/meta_interpreter.pl is loaded, false otherwise.
     */
    protected static boolean loadedMetaInterpreter;

    /**
     * The default timeout.
     */
    protected static final long DEFAULT_TIMEOUT = 10000;

    /**
     * The logger.
     */
    private static final Logger LOGGER = LogManager.getLogger();

    /**
     * The JPL facade.
     */
    protected JplFacade facade;
    /**
     * The current Compositional Framework.
     */
    protected FrameworkRepresentation framework;

    /**
     * Initializes a SimplePrologCompositionAnalyzer and consults the specified framework.
     *
     * @param framework the framework
     * @throws IOException but should actually not
     * @throws ExternalSoftwareUnavailableException if swipl is unavailable
     */
    public SimplePrologCompositionAnalyzer(final FrameworkRepresentation framework)
            throws IOException, ExternalSoftwareUnavailableException {
        LOGGER.info("Initialising SimplePrologCompositionAnalyzer.");
        this.framework = framework;

        this.facade = new JplFacade(DEFAULT_TIMEOUT);
        this.consultKnowledgeBase();
    }

    /**
     * Safe to override.
     */
    @Override
    public List<SearchResult<BooleanWithUncertainty>> analyzeComposition(
            final DecompositionTree composition, final List<Property> properties) {
        final List<SearchResult<BooleanWithUncertainty>> result =
                new LinkedList<SearchResult<BooleanWithUncertainty>>();

        for (final Property property : properties) {
            if (property.getArity() != 1) {
                throw new IllegalArgumentException(
                        "For now, only unary " + "properties can be used in queries.");
            }
        }

        final String votingRule = composition.toString();

        for (final Property property : properties) {
            final String query = property.getInstantiatedString(votingRule);
            final SearchResult<Boolean> queryResult = this.facade.factQuery(query);

            final SearchResult<BooleanWithUncertainty> searchResult;
            if (queryResult.hasValue()) {
                final boolean original = queryResult.getValue();

                if (original) {
                    searchResult = new SearchResult<BooleanWithUncertainty>(QueryState.SUCCESS,
                            BooleanWithUncertainty.TRUE);
                } else {
                    searchResult = new SearchResult<BooleanWithUncertainty>(QueryState.SUCCESS,
                            BooleanWithUncertainty.MAYBE);
                }
            } else {
                searchResult = new SearchResult<BooleanWithUncertainty>(QueryState.FAILED, null);
            }

            result.add(searchResult);
        }

        return result;
    }

    /**
     * Safe to override.
     */
    @Override
    public SearchResult<DecompositionTree> generateComposition(final List<Property> properties) {
        for (final Property property : properties) {
            if (property.getArity() != 1) {
                throw new IllegalArgumentException(
                        "For now, only unary " + "properties can be used in queries.");
            }
        }

        // Safety measure to ensure all properties talking about the same element.
        final List<String> propertyStrings = new LinkedList<String>();
        for (final Property property : properties) {
            propertyStrings.add(property.getInstantiatedString("X"));
        }

        final String query = StringUtils.printCollection(propertyStrings);

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

            final String solution = resultMap.get("X");
            final DecompositionTree solutionTree = DecompositionTree.parseString(solution);

            return new SearchResult<DecompositionTree>(result.getState(), solutionTree);
        } else {
            return new SearchResult<DecompositionTree>(result.getState(), null);
        }
    }

    /**
     * Safe to override.
     */
    @Override
    public List<CompositionProof> proveClaims(final DecompositionTree composition,
            final List<Property> properties) {
        final List<PrologProof> proofs = new LinkedList<PrologProof>();

        for (final Property property : properties) {
            if (property.getArity() != 1) {
                throw new IllegalArgumentException();
            }
        }

        final String votingRule = composition.toString();

        for (final Property property : properties) {
            // This is fine as it's the only variable.
            final String proofVariable = "P";
            final String query = "prove((" + property.getInstantiatedString(votingRule) + "),"
                    + proofVariable + ")";

            LOGGER.debug(query);

            // Disabling timeout as these queries are typically fast
            final long oldTimeout = this.facade.getTimeout();
            this.facade.setTimeout(Integer.MAX_VALUE / 2);
            final SearchResult<Map<String, String>> result = this.facade
                    .iterativeDeepeningQuery(query);
            this.facade.setTimeout(oldTimeout);

            if (result.hasValue()) {
                try {
                    final Map<String, String> map = result.getValue();

                    if (map.containsKey(proofVariable)) {
                        LOGGER.debug(map.get(proofVariable));

                        proofs.add(PrologProof.createProofFromString(map.get(proofVariable)));
                    } else {
                        throw new IllegalArgumentException();
                    }
                } catch (final ValueNotPresentException e) {
                    throw new IllegalArgumentException();
                }
            } else {
                throw new IllegalArgumentException();
            }
        }

        final List<CompositionProof> res = new LinkedList<CompositionProof>();
        for (final PrologProof proof : proofs) {
            res.add(this.findCompositionRules(proof));
        }

        return res;
    }

    /**
     * Safe to override.
     */
    @Override
    public void setTimeout(final long millis) {
        this.facade.setTimeout(millis);
    }

    /**
     * Consults both the current (E)PL file and the resources/meta_interpreter.pl.
     */
    protected void consultKnowledgeBase() {
        this.facade.consultFile(this.framework.getAbsolutePath());

        if (!loadedMetaInterpreter) {
            this.facade.consultFile(
                    this.getClass().getClassLoader().getResource("meta_interpreter.pl"));
            loadedMetaInterpreter = true;
        }
    }

    private CompositionProof findCompositionRules(final PrologProof prologProof) {
        final List<CompositionProof> subgoals = new LinkedList<CompositionProof>();

        for (final PrologProof prologSubgoal : prologProof.getSubgoals()) {
            subgoals.add(this.findCompositionRules(prologSubgoal));
        }

        final CompositionRule rule = this.findMatchingCompositionRule(prologProof);

        return new CompositionProof(prologProof.getGoal(), subgoals, rule);
    }

    private CompositionRule findMatchingCompositionRule(final PrologProof proof) {
        for (final CompositionRule rule : this.framework.getCompositionRules()) {
            String generic = rule.getSuccedent().toString();
            String specific = proof.getGoal();

            if (!this.facade.subsumesTerm(generic, specific)) {
                // "Heads" don't match, no need to look at subgoals.
                continue;
            }

            final Map<String, String> replacements = this.facade.unifiable(generic, specific);

            // Check subgoals.
            if (proof.getSubgoals().size() != rule.getAntecedents().size()) {
                // Number of arguments does not match.
                continue;
            }

            boolean rightRule = true;
            for (int i = 0; i < proof.getSubgoals().size(); i++) {
                generic = rule.getAntecedents().get(i).toString();
                specific = proof.getSubgoals().get(i).getGoal();

                // Manual "unification"
                for (final String key : replacements.keySet()) {
                    // Some regex magic has to be done here. A variable consists of [A-Za-z0-9_] =
                    // [\\w]
                    // characters. Boundaries should not be replaced and finding out whether they
                    // are
                    // commas, spaces, brackets or anything else seemed even more tedious than this.
                    // Careful: Naively replacing all occurrences of a variable name is not a
                    // valid solution, as they are not prefix free, e.g. replacing X by c in
                    // "a(X,X1)"
                    // would yield "a(c,c1").
                    final Pattern pattern = Pattern.compile("[^\\w_]" + key + "[^\\w_]");
                    Matcher matcher = pattern.matcher(generic);

                    while (matcher.find()) {
                        final String start = generic.substring(0, matcher.start() + 1);
                        final String middle = replacements.get(key);
                        final String end = generic.substring(matcher.end() - 1, generic.length());

                        generic = start + middle + end;

                        matcher = pattern.matcher(generic);
                    }
                }

                if (!this.facade.subsumesTerm(generic, specific)) {
                    // A subgoal does not match, wrong rule.
                    rightRule = false;
                    break;
                }
            }

            if (rightRule) {
                return rule;
            }
        }

        throw new IllegalArgumentException();
    }
}
