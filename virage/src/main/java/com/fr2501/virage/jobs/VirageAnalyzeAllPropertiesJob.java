package com.fr2501.virage.jobs;

import java.util.LinkedList;
import java.util.List;

import com.fr2501.util.StringUtils;
import com.fr2501.virage.core.ConfigReader;
import com.fr2501.virage.core.VirageSearchManager;
import com.fr2501.virage.core.VirageUserInterface;
import com.fr2501.virage.types.BooleanWithUncertainty;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.Property;
import com.fr2501.virage.types.SearchResult;

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
        for(int i = 0; i < this.unaryProperties.size(); i++) {
            hasProperties.add(false);
        }

        for (final List<SearchResult<BooleanWithUncertainty>> resultList : this.getResult()) {
            for (int i = 0; i < resultList.size(); i++) {
                final SearchResult<BooleanWithUncertainty> result = resultList.get(i);

                hasProperties.set(i, hasProperties.get(i) || result.hasValue()
                        && result.getValue() == BooleanWithUncertainty.TRUE);
            }
        }

        String res = "";
        for(int i = 0; i < this.unaryProperties.size(); i++) {
            if (hasProperties.get(i)) {
                res += StringUtils.appendPeriod(this.compositionField + " has the property "
                        + this.unaryProperties.get(i).toString()) + System.lineSeparator();
            } else {
                res += StringUtils.appendPeriod(this.compositionField
                        + " cannot be shown to have the property "
                        + this.unaryProperties.get(i).toString()) + System.lineSeparator();
            }
        }

        return res;
    }

    @Override
    protected final void concreteExecute() throws Exception {
        this.unaryProperties = new LinkedList<Property>();
        for(final Property candidate : this.getExecutingCore()
                .getFrameworkRepresentation().getProperties()) {
            if(!candidate.isAtomic() && candidate.getArity() == 1) {
                this.unaryProperties.add(candidate);
            }
        }

        final VirageSearchManager manager = this.getExecutingCore().getSearchManager();
        this.setResult(manager.analyzeComposition(DecompositionTree.parseString(
                    this.compositionField), this.unaryProperties));

    }
}
