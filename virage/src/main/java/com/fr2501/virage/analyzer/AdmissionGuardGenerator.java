package com.fr2501.virage.analyzer;

import com.fr2501.util.SimpleFileWriter;
import com.fr2501.virage.prolog.PrologClause;
import com.fr2501.virage.prolog.PrologPredicate;
import com.fr2501.virage.types.CompositionRule;
import com.fr2501.virage.types.FrameworkRepresentation;
import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

/**
 * Generates a new Prolog file containing admission guards from a given
 * {@link FrameworkRepresentation}.
 *
 */
public class AdmissionGuardGenerator {
    private FrameworkRepresentation framework;

    public AdmissionGuardGenerator(FrameworkRepresentation framework) {
        this.framework = framework;
    }

    /**
     * Generates the file containing the admission guards.
     * 
     * @return the file
     * @throws IOException but should actually not
     */
    public File createAdmissionGuardFile() throws IOException {
        List<CompositionRule> newRules = this.generateAdmissionGuards();

        // Looks weird, but otherwise CompositionRule.toString() would have to output
        // Prolog source.
        List<PrologClause> newClauses = new LinkedList<PrologClause>();

        for (CompositionRule rule : newRules) {
            newClauses.add(rule.getClause());
        }

        File file = File.createTempFile("admission_guards", ".pl");
        file.deleteOnExit();

        SimpleFileWriter writer = new SimpleFileWriter();
        writer.writeToFile(file.getAbsolutePath(), newClauses);

        return file;
    }

    private List<CompositionRule> generateAdmissionGuards() {
        List<CompositionRule> originalRules = this.framework.getCompositionRules();
        List<CompositionRule> newRules = new LinkedList<CompositionRule>();

        // First, generate the rules that introduce the admission guards.
        for (CompositionRule oldRule : originalRules) {
            PrologPredicate succedent = oldRule.getSuccedent();

            String newSuccedentName = AdmissionGuardStrings.ADMITS + succedent.getName();

            PrologPredicate newSuccedent;

            List<PrologPredicate> newAntecedents = new LinkedList<PrologPredicate>();

            // Simple implications should keep their antecedents and variables.
            // (Some facts are hit as well, but that does not matter.)
            if (succedent.getDepth() == 1) {
                newSuccedent = new PrologPredicate(newSuccedentName, succedent.getParameters());

                for (PrologPredicate antecedent : oldRule.getAntecedents()) {
                    String newAntecedentName = AdmissionGuardStrings.ADMITS + antecedent.getName();

                    newAntecedents.add(
                            new PrologPredicate(newAntecedentName, antecedent.getParameters()));
                }
            } else {
                PrologPredicate anonymizedSuccedent = this.copyAndAnonymizeVariables(succedent);
                newSuccedent = new PrologPredicate(newSuccedentName,
                        anonymizedSuccedent.getParameters());

                // newAntecedents stays empty.
            }

            PrologClause newClause = new PrologClause(newSuccedent, newAntecedents);
            newRules.add(new CompositionRule("", AdmissionGuardStrings.ORIGIN, newClause));
        }

        // Now, alter the old rules to include them.
        for (CompositionRule oldRule : originalRules) {
            String newSuccedentName = oldRule.getSuccedent().getName()
                    + AdmissionGuardStrings.SUFFIX;
            PrologPredicate newSuccedent = new PrologPredicate(newSuccedentName,
                    oldRule.getSuccedent().getParameters());

            List<PrologPredicate> newAntecedents = new LinkedList<PrologPredicate>();

            for (PrologPredicate antecedent : oldRule.getAntecedents()) {
                PrologPredicate newAntecedent = new PrologPredicate(
                        AdmissionGuardStrings.ADMITS + antecedent.getName(),
                        antecedent.getParameters());

                newAntecedents.add(newAntecedent);
            }

            for (PrologPredicate antecedent : oldRule.getAntecedents()) {
                PrologPredicate newAntecedent = new PrologPredicate(
                        antecedent.getName() + AdmissionGuardStrings.SUFFIX,
                        antecedent.getParameters());

                newAntecedents.add(newAntecedent);
            }

            PrologClause newClause = new PrologClause(newSuccedent, newAntecedents);

            newRules.add(new CompositionRule("", AdmissionGuardStrings.ORIGIN, newClause));
        }

        return newRules;
    }

    private PrologPredicate copyAndAnonymizeVariables(PrologPredicate predicate) {
        String newName = "";

        if (Character.isUpperCase(predicate.getName().charAt(0))) {
            newName = "_";
        } else {
            newName = predicate.getName();
        }

        List<PrologPredicate> newParameters = new LinkedList<PrologPredicate>();
        for (PrologPredicate parameter : predicate.getParameters()) {
            newParameters.add(this.copyAndAnonymizeVariables(parameter));
        }

        return new PrologPredicate(newName, newParameters);
    }
}
