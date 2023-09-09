package edu.kit.kastel.formal.virage.jobs;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import edu.kit.kastel.formal.util.StringUtils;
import edu.kit.kastel.formal.virage.core.ConfigReader;
import edu.kit.kastel.formal.virage.core.VirageCore;
import edu.kit.kastel.formal.virage.core.VirageSearchManager;
import edu.kit.kastel.formal.virage.core.VirageUserInterface;
import edu.kit.kastel.formal.virage.types.BooleanWithUncertainty;
import edu.kit.kastel.formal.virage.types.DecompositionTree;
import edu.kit.kastel.formal.virage.types.Property;
import edu.kit.kastel.formal.virage.types.SearchResult;

/**
 * VirageJob used to analyze all properties of a composition.
 * @author VeriVote
 */
public class VirageAnalyzeAllPropertiesJob extends
    VirageJobWithExplicitResult<List<List<SearchResult<BooleanWithUncertainty>>>> {
    /**
     * The passed composition.
     */
    private final String compositionField;

    /**
     * All unary properties of the current framework.
     */
    private List<Property> unaryProperties;

    /**
     * Simple constructor.
     * @param issuer the issuing UI.
     * @param composition the composition to be analyzed
     */
    public VirageAnalyzeAllPropertiesJob(final VirageUserInterface issuer,
                                         final String composition) {
        super(issuer);
        this.compositionField = composition;
    }

    @Override
    public final boolean externalSoftwareAvailable() {
        return ConfigReader.getInstance().hasJpl();
    }

    @Override
    public final String getDescription() {
        return "Checking all available unary properties ...";
    }

    @Override
    public final String presentConcreteResult() {
        final List<Boolean> hasProperties = new LinkedList<Boolean>();
        for (int i = 0; i < this.unaryProperties.size(); i++) {
            hasProperties.add(false);
        }
        for (final List<SearchResult<BooleanWithUncertainty>> resultList: this.getResult()) {
            for (int i = 0; i < resultList.size(); i++) {
                final SearchResult<BooleanWithUncertainty> result = resultList.get(i);
                hasProperties.set(i, hasProperties.get(i) || result.hasValue()
                        && result.getValue() == BooleanWithUncertainty.TRUE);
            }
        }
        String res = StringUtils.EMPTY;
        for (int i = 0; i < this.unaryProperties.size(); i++) {
            final String propertySatisfaction =
                    hasProperties.get(i) ? "has" : "cannot be shown to have";
            res += StringUtils.appendPeriod(this.compositionField
                    + StringUtils.SPACE + propertySatisfaction + " the property "
                    + this.unaryProperties.get(i).toString()) + System.lineSeparator();
        }
        return res;
    }

    @Override
    protected final void concreteExecute() throws Exception {
        this.unaryProperties = new LinkedList<Property>();
        final VirageCore execCore = this.getExecutingCore();
        for (final Property candidate: execCore.getFrameworkRepresentation().getProperties()) {
            if (!candidate.isAtomic() && candidate.getArity() == 1) {
                this.unaryProperties.add(candidate);
            }
        }
        Collections.sort(this.unaryProperties,
                (final Property a, final Property b) -> a.getName().compareTo(b.getName()));
        final VirageSearchManager manager = execCore.getSearchManager();
        this.setResult(manager.analyzeComposition(DecompositionTree.parseString(
                    this.compositionField), this.unaryProperties));
    }
}
