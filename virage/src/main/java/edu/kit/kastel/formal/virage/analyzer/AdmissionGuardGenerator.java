package edu.kit.kastel.formal.virage.analyzer;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import edu.kit.kastel.formal.util.SimpleFileWriter;
import edu.kit.kastel.formal.util.StringUtils;
import edu.kit.kastel.formal.util.SystemUtils;
import edu.kit.kastel.formal.virage.prolog.ExtendedPrologStrings;
import edu.kit.kastel.formal.virage.prolog.PrologClause;
import edu.kit.kastel.formal.virage.prolog.PrologParser;
import edu.kit.kastel.formal.virage.prolog.PrologPredicate;
import edu.kit.kastel.formal.virage.types.CompositionRule;
import edu.kit.kastel.formal.virage.types.FrameworkRepresentation;

/**
 * Generates a new Prolog file containing admission guards from a given
 * {@link FrameworkRepresentation}.
 *
 * @author VeriVote
 */
public class AdmissionGuardGenerator {
    /** The framework representation used throughout. */
    private final FrameworkRepresentation frameworkField;

    /**
     * Simple constructor.
     *
     * @param framework the framework representation to be used
     */
    public AdmissionGuardGenerator(final FrameworkRepresentation framework) {
        this.frameworkField = framework;
    }

    private static PrologPredicate copyAndAnonymizeVariables(final PrologPredicate predicate) {
        String newName = StringUtils.EMPTY;
        if (Character.isUpperCase(predicate.getName().charAt(0))) {
            newName = PrologPredicate.ANONYMOUS;
        } else {
            newName = predicate.getName();
        }
        final List<PrologPredicate> newParameters = new LinkedList<PrologPredicate>();
        for (final PrologPredicate parameter: predicate.getParameters()) {
            newParameters.add(copyAndAnonymizeVariables(parameter));
        }
        return new PrologPredicate(newName, newParameters);
    }

    /**
     * Generates the file containing the admission guards.
     *
     * @return the file
     * @throws IOException but should actually not
     */
    public File createAdmissionGuardFile() throws IOException {
        final List<CompositionRule> newRules = this.generateAdmissionGuards();
        // Looks weird, but otherwise CompositionRule.toString() would have to output
        // Prolog source.
        final List<PrologClause> newClauses = new LinkedList<PrologClause>();
        for (final CompositionRule rule: newRules) {
            newClauses.add(rule.getClause());
        }
        final File file = SystemUtils.tempFile("admission_guards", PrologParser.DOT_PL);
        file.deleteOnExit();
        final SimpleFileWriter writer = new SimpleFileWriter();
        writer.writeToFile(file.getAbsolutePath(), newClauses);
        return file;
    }

    private List<CompositionRule> generateAdmissionGuards() {
        final List<CompositionRule> originalRules = this.frameworkField.getCompositionRules();
        final List<CompositionRule> newRules = new LinkedList<CompositionRule>();

        // First, generate the rules that introduce the admission guards.
        for (final CompositionRule oldRule: originalRules) {
            final PrologPredicate succedent = oldRule.getSuccedent();
            final String newSuccedentName = AdmissionGuardStrings.ADMITS + succedent.getName();
            final PrologPredicate newSuccedent;
            final List<PrologPredicate> newAntecedents = new LinkedList<PrologPredicate>();

            // Simple implications should keep their antecedents and variables.
            // (Some facts are hit as well, but that does not matter.)
            if (succedent.getDepth() == 1) {
                newSuccedent = new PrologPredicate(newSuccedentName, succedent.getParameters());
                for (final PrologPredicate antecedent: oldRule.getAntecedents()) {
                    final String newAntecedentName =
                            AdmissionGuardStrings.ADMITS + antecedent.getName();
                    newAntecedents
                    .add(new PrologPredicate(newAntecedentName, antecedent.getParameters()));
                }
            } else {
                final PrologPredicate anonymizedSuccedent =
                        copyAndAnonymizeVariables(succedent);
                newSuccedent =
                        new PrologPredicate(newSuccedentName, anonymizedSuccedent.getParameters());
                // newAntecedents stays empty.
            }
            final PrologClause newClause = new PrologClause(newSuccedent, newAntecedents);
            newRules.add(
                    new CompositionRule(StringUtils.EMPTY, ExtendedPrologStrings.ASSUMPTION,
                                        newClause));
        }

        // Now, update the old rules to include them.
        for (final CompositionRule oldRule: originalRules) {
            final String newSuccedentName = oldRule.getSuccedent().getName()
                    + AdmissionGuardStrings.SUFFIX;
            final PrologPredicate newSuccedent =
                    new PrologPredicate(newSuccedentName, oldRule.getSuccedent().getParameters());
            final List<PrologPredicate> newAntecedents = new LinkedList<PrologPredicate>();

            for (final PrologPredicate antecedent: oldRule.getAntecedents()) {
                final PrologPredicate newAntecedent =
                        new PrologPredicate(AdmissionGuardStrings.ADMITS + antecedent.getName(),
                                            antecedent.getParameters());
                newAntecedents.add(newAntecedent);
            }

            for (final PrologPredicate antecedent: oldRule.getAntecedents()) {
                final PrologPredicate newAntecedent =
                        new PrologPredicate(antecedent.getName() + AdmissionGuardStrings.SUFFIX,
                                            antecedent.getParameters());
                newAntecedents.add(newAntecedent);
            }
            final PrologClause newClause = new PrologClause(newSuccedent, newAntecedents);
            newRules.add(
                    new CompositionRule(StringUtils.EMPTY, ExtendedPrologStrings.ASSUMPTION,
                                        newClause));
        }
        return newRules;
    }
}
