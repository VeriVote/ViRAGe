package com.fr2501.virage.analyzer;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import com.fr2501.virage.prolog.ExtendedPrologStrings;
import com.fr2501.virage.prolog.JPLFacade;
import com.fr2501.virage.prolog.PrologPredicate;
import com.fr2501.virage.prolog.QueryState;
import com.fr2501.virage.types.Component;
import com.fr2501.virage.types.ComponentType;
import com.fr2501.virage.types.CompositionRule;
import com.fr2501.virage.types.CompositionalStructure;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.Property;
import com.fr2501.virage.types.SearchResult;

public class SetBasedCompositionAnalyzer implements CompositionAnalyzer {
	private static final Logger logger = LogManager.getLogger(SetBasedCompositionAnalyzer.class);
	private JPLFacade facade;
	
	private long timeout;
	private long remainingTime;
	
	private FrameworkRepresentation framework;
	private List<CompositionRule> compositionRules;
	private Set<Property> simpleProperties;
	private Set<Property> relationalProperties;
	
	private Map<CompositionalStructure, Set<String>> structureSets;
	private Map<Component, Set<String>> componentSets;
	
	public SetBasedCompositionAnalyzer(FrameworkRepresentation framework) {
		this.framework = framework;
		this.compositionRules = framework.getCompositionRules();
		
		this.facade = new JPLFacade(this.timeout);
		
		this.splitProperties();
		this.initializeMaps();
		// TODO: "Implicational closure"
	}
	
	private void splitProperties() {
		Set<Property> allProperties = this.framework.getProperties();
		Set<Property> simpleProperties = new HashSet<Property>();
		Set<Property> relationalProperties = new HashSet<Property>();
		
		for(Property property: allProperties) {
			List<ComponentType> parameters = property.getParameters();
			int numCompcomponents = 0;
			
			for(ComponentType type: parameters) {
				if(type.equals(new ComponentType(ExtendedPrologStrings.COMPONENT)) ||
						type.equals(new ComponentType(this.framework.getAlias()))) {
					numCompcomponents++;
				}
			}
			
			if(numCompcomponents > 1) {
				relationalProperties.add(property);
			} else {
				simpleProperties.add(property);
			}
		}
		
		this.simpleProperties = simpleProperties;
		this.relationalProperties = relationalProperties;
 	}
	
	private void initializeMaps() {
		this.structureSets = new HashMap<CompositionalStructure, Set<String>>();
		this.componentSets = new HashMap<Component, Set<String>>();
		
		for(CompositionalStructure structure: this.framework.getCompositionalStructures()) {
			this.structureSets.put(structure, new HashSet<String>());
		}
		
		for(Component component: this.framework.getComponents()) {
			this.componentSets.put(component, new HashSet<String>());
		}
		
		for(Component component: this.framework.getComposableModules()) {
			this.componentSets.put(component, new HashSet<String>());
		}
		
		for(CompositionRule rule: this.compositionRules) {
			PrologPredicate succedent = rule.getSuccedent();
			Property property = rule.getSuccedentAsProperty(this.framework);
			
			if(this.simpleProperties.contains(property)) {
				for(PrologPredicate predicate: succedent.getParameters()) {
					String paramName = predicate.getName();
					
					// One of these two will always be null, distinction will be made later.
					Component component = this.framework.getComponent(paramName);
					CompositionalStructure structure = this.framework.getCompositionalStructure(paramName);
					
					if(component == null && structure == null) {
						continue;
					}
					// A parameter was found which is either a component or a compositional structure
					
					List<String> paramStrings = new LinkedList<String>();
					for(PrologPredicate param: succedent.getParameters()) {
						if(param == predicate) {
							paramStrings.add(ExtendedPrologStrings.COMPONENT.toUpperCase());
							continue;
						}
						paramStrings.add(param.toString());
					}
					
					String instantiatedProperty = property.getInstantiatedString(paramStrings);
					
					if(component != null) {
						this.componentSets.get(component).add(instantiatedProperty);
					} else if(structure != null) {
						this.structureSets.get(structure).add(instantiatedProperty);
					}
					
					// Simple property, so this was the only one.
					break;
				}
			} else if(this.relationalProperties.contains(property)) {
				// TODO Implement
			}
		}
	}

	@Override
	public void setTimeout(long millis) {
		this.timeout = timeout;
	}

	@Override
	public SearchResult<Boolean> analyzeComposition(DecompositionTree composition, Set<Property> properties) {
		String compositionType = composition.getLabel();
		
		// TODO: Implement
		return null;
	}

	@Override
	public SearchResult<DecompositionTree> generateComposition(Set<Property> properties) {
		Set<String> propertyStrings = new HashSet<String>();
		
		for(Property property: properties) {
			propertyStrings.add(property.toString());		
		}
		
		// Check components first as they are the base case
		for(Component component: this.componentSets.keySet()) {
			Set<String> componentSet = this.componentSets.get(component);
			
			if(this.checkSubsumptionalSubset(componentSet, propertyStrings)) {
				// Found an electing component which might yield all the required properties
				logger.info(component.getName());
				
				return new SearchResult<DecompositionTree>(QueryState.SUCCESS, new DecompositionTree(component.getName()));
			}
		}
		
		for(CompositionalStructure structure: this.structureSets.keySet()) {
			Set<String> structureSet = this.structureSets.get(structure);
			
			if(this.checkSubsumptionalSubset(structureSet, propertyStrings)) {
				// Found an applicable compositional structure
				
				// TODO: Find new required sets
				
				// TODO: Find solutions for those
				
				// TODO: Put things together
			}
		}
		
		return new SearchResult<DecompositionTree>(QueryState.ERROR, null);
	}
	
	private boolean checkSubsumptionalSubset(Set<String> set, Set<String> subset) {
		for(String subsetString: subset) {
			boolean found = false;
			
			for(String setString: set) {
				if(subsetString.equals(setString) || this.checkSubsumption(setString, subsetString)) {
					found = true;
					break;
				}
			}
			
			if(!found) return false;
		}
		
		return true;
	}
	
	private boolean checkSubsumption(String generic, String specific) {
		String query = "subsumes_term(" + generic + "," + specific + ")";
		
		// This query should happen very quickly, no timeout needed.
		SearchResult<Boolean> res = this.facade.factQuery(query, 100000);
		
		if(res.hasValue()) {
			try {
				return res.getValue();
			} catch(Exception e) {
				return false;
			}
		} else {
			return false;
		}
	}
}
