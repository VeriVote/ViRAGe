package edu.kit.kastel.formal.virage.analyzer;

import java.io.IOException;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import edu.kit.kastel.formal.util.StringUtils;
import edu.kit.kastel.formal.virage.prolog.JplFacade;
import edu.kit.kastel.formal.virage.prolog.PrologParser;
import edu.kit.kastel.formal.virage.prolog.PrologProof;
import edu.kit.kastel.formal.virage.prolog.QueryState;
import edu.kit.kastel.formal.virage.types.BooleanWithUncertainty;
import edu.kit.kastel.formal.virage.types.CompositionProof;
import edu.kit.kastel.formal.virage.types.CompositionRule;
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
public class SimplePrologCompositionAnalyzer implements CompositionAnalyzer {
    /**
     * The default timeout.
     */
    protected static final long DEFAULT_TIMEOUT = 10000;

    /**
     * The file name of the Prolog meta interpreter file.
     */
    protected static final String META_INTERPRETER = "meta_interpreter" + PrologParser.DOT_PL;

    /**
     * True if resources/meta_interpreter.pl is loaded, false otherwise.
     */
    private static boolean loadedMetaInterpreter;

    /**
     * The logger.
     */
    private static final Logger LOGGER = LogManager.getLogger();

    /**
     * Default variable name.
     */
    private static final String DEFAULT_VARIABLE = "X";

    /**
     * The JPL facade.
     */
    private final JplFacade facade;

    /**
     * The current Compositional Framework.
     */
    private final FrameworkRepresentation framework;

    /**
     * Initializes a SimplePrologCompositionAnalyzer and consults the specified framework.
     *
     * @param frameworkValue the framework
     * @throws IOException but should actually not
     * @throws ExternalSoftwareUnavailableException if SWI Prolog is unavailable
     */
    public SimplePrologCompositionAnalyzer(final FrameworkRepresentation frameworkValue)
            throws IOException, ExternalSoftwareUnavailableException {
        LOGGER.info("Initialising SimplePrologCompositionAnalyzer.");
        this.framework = frameworkValue;
        this.facade = new JplFacade(DEFAULT_TIMEOUT);
        this.consultKnowledgeBase();
    }

    /**
     * Simple getter.
     * @return the loadedMetaInterpreter
     */
    protected static boolean metaInterpreterLoaded() {
        return loadedMetaInterpreter;
    }

    /**
     * Simple setter.
     * @param newLoadedMetaInterpreter the loadedMetaInterpreter to set
     */
    protected static void setMetaInterpreterLoaded(final boolean newLoadedMetaInterpreter) {
        SimplePrologCompositionAnalyzer.loadedMetaInterpreter = newLoadedMetaInterpreter;
    }

    /**
     * Safe to override.
     */
    @Override
    public List<SearchResult<BooleanWithUncertainty>> analyzeComposition(
            final DecompositionTree composition, final List<Property> properties) {
        final List<SearchResult<BooleanWithUncertainty>> result =
                new LinkedList<SearchResult<BooleanWithUncertainty>>();
        for (final Property property: properties) {
            if (property.getArity() != 1) {
                this.throwArityException();
            }
        }
        final String votingRule = composition.toString();
        for (final Property property: properties) {
            final SearchResult<Boolean> queryResult =
                    this.facade.factQuery(property.getInstantiatedString(votingRule));
            final QueryState state;
            final BooleanWithUncertainty booleanValue;
            if (queryResult.hasValue()) {
                booleanValue = queryResult.getValue()
                        ? BooleanWithUncertainty.TRUE : BooleanWithUncertainty.MAYBE;
                state = QueryState.SUCCESS;
            } else {
                booleanValue = null;
                state = QueryState.FAILED;
            }
            result.add(new SearchResult<BooleanWithUncertainty>(state, booleanValue));
        }
        return result;
    }

    /**
     * Safe to override.
     */
    @Override
    public SearchResult<DecompositionTree> generateComposition(final List<Property> properties) {
        for (final Property property: properties) {
            if (property.getArity() != 1) {
                this.throwArityException();
            }
        }
        // Safety measure to ensure all properties talking about the same element.
        final List<String> propertyStrings = new LinkedList<String>();
        for (final Property property: properties) {
            propertyStrings.add(property.getInstantiatedString(DEFAULT_VARIABLE));
        }
        final String query = StringUtils.printCollection(propertyStrings);
        final SearchResult<Map<String, String>> result = this.facade.iterativeDeepeningQuery(query);
        final DecompositionTree solutionTree;
        if (result.hasValue()) {
            Map<String, String> resultMap;
            try {
                resultMap = result.getValue();
            } catch (final ValueNotPresentException e) {
                // This should never happen.
                LOGGER.warn("This should not have happened.");
                LOGGER.warn(e);
                resultMap = Map.of();
            }
            solutionTree = DecompositionTree.parseString(resultMap.get(DEFAULT_VARIABLE));
        } else {
            solutionTree = null;
        }
        return new SearchResult<DecompositionTree>(result.getState(), solutionTree);
    }

    /**
     * Safe to override.
     */
    @Override
    public List<CompositionProof> proveClaims(final DecompositionTree composition,
                                              final List<Property> properties) {
        final List<PrologProof> proofs = new LinkedList<PrologProof>();
        for (final Property property: properties) {
            if (property.getArity() != 1) {
                throw new IllegalArgumentException();
            }
        }
        final String votingRule = composition.toString();
        for (final Property property: properties) {
            // This is fine as it is the only variable.
            final String proofVariable = "P";
            final String query =
                    StringUtils.func(
                            "prove",
                            StringUtils.parenthesize(property.getInstantiatedString(votingRule)),
                            proofVariable);
            LOGGER.debug(query);
            // Disabling timeout as these queries are typically fast
            final long oldTimeout = this.facade.getTimeout();
            this.facade.setTimeout(Integer.MAX_VALUE / 2);
            final SearchResult<Map<String, String>> result = this.facade
                    .iterativeDeepeningQuery(query);
            this.facade.setTimeout(oldTimeout);
            if (result.hasValue()) {
                try {
                    final String val = result.getValue().get(proofVariable);
                    if (val != null) {
                        LOGGER.debug(val);
                        proofs.add(PrologProof.createProofFromString(val));
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
        for (final PrologProof proof: proofs) {
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
                    this.getClass().getClassLoader().getResource(META_INTERPRETER));
            loadedMetaInterpreter = true;
        }
    }

    /**
     * Simple getter.
     * @return the facade
     */
    protected JplFacade getFacade() {
        return this.facade;
    }

    /**
     * Simple getter.
     * @return the framework
     */
    protected FrameworkRepresentation getFramework() {
        return this.framework;
    }

    private CompositionProof findCompositionRules(final PrologProof prologProof) {
        final List<CompositionProof> subgoals = new LinkedList<CompositionProof>();
        for (final PrologProof prologSubgoal: prologProof.getSubgoals()) {
            subgoals.add(this.findCompositionRules(prologSubgoal));
        }
        final CompositionRule rule = this.findMatchingCompositionRule(prologProof);
        return new CompositionProof(prologProof.getGoal(), subgoals, rule);
    }

    private CompositionRule findMatchingCompositionRule(final PrologProof proof) {
        for (final CompositionRule rule: this.framework.getCompositionRules()) {
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
                for (final Map.Entry<String, String> entry: replacements.entrySet()) {
                    // Some regular expression magic has to be done here. A variable consists of
                    // [A-Za-z0-9_] = [\\w]
                    // characters. Boundaries should not be replaced and finding out whether they
                    // are
                    // commas, spaces, brackets or anything else seemed even more tedious than this.
                    // Careful: Naively replacing all occurrences of a variable name is not a
                    // valid solution, as they are not prefix free, e.g. replacing X by c in
                    // "a(X,X1)"
                    // would yield "a(c,c1").
                    final String nonWord = "[^\\w_]";
                    final Pattern pattern = Pattern.compile(nonWord + entry.getKey() + nonWord);
                    Matcher matcher = pattern.matcher(generic);

                    while (matcher.find()) {
                        final String start = generic.substring(0, matcher.start() + 1);
                        final String middle = entry.getValue();
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

    /**
     * Called when arities mismatch, only throws an exception.
     * @throws IllegalArgumentException as that is its purpose
     */
    private void throwArityException() {
        throw new IllegalArgumentException(
                "For now, only unary properties can be used in queries.");
    }
}
