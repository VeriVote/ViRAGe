package com.fr2501.virage.types;

import java.util.LinkedList;
import java.util.List;

import com.fr2501.util.StringUtils;

public class DecompositionTree {
	private String label;
	private int arity;
	private List<DecompositionTree> children;
	
	public DecompositionTree(String label, List<DecompositionTree> children) {
		this.label = label;
		this.arity = children.size();
		this.children = children;
	}
	
	public DecompositionTree(String label) {
		this(label, new LinkedList<DecompositionTree>());
	}
	
	public DecompositionTree(String label, DecompositionTree child) {
		List<DecompositionTree> children = new LinkedList<DecompositionTree>();
		children.add(child);
		
		this.label = label;
		this.arity = 1;
		this.children = children;
	}
	
	public String getLabel() {
		return label;
	}

	public int getArity() {
		return arity;
	}

	public List<DecompositionTree> getChildren() {
		return children;
	}

	public static DecompositionTree parseString(String s) {
		s = StringUtils.removeWhitespace(s);
		
		String label = "";
		List<DecompositionTree> children = new LinkedList<DecompositionTree>();
		String currentChild = "";
		int level = 0;
		
		
		for(int i=0; i<s.length(); i++) {
			char current = s.charAt(i);
			
			if(current == '(') {
				level++;
				if(level == 1) continue;
			} else if(current == ')') {
				level--;
				if(level<0) {
					throw new IllegalArgumentException();
				}
				if(level == 0) continue;
			} else {		
				if(level == 0) {
					label += current;
				} else if(level == 1) {
					if(current == ',') {
						children.add(DecompositionTree.parseString(currentChild));
						currentChild = "";
						continue;
					}
				}
			}
				
			if(level>0) {
				currentChild += current;
			}
		}
		
		if(!currentChild.equals("")) {
			children.add(DecompositionTree.parseString(currentChild));
		}
		
		if(level != 0) {
			throw new IllegalArgumentException();
		}
		
		return new DecompositionTree(label, children);
	}
	
	@Override
	public String toString() {
		if(this.arity == 0) {
			return this.label;
		} else {
			return this.label += "(" + StringUtils.printCollection(children) + ")";
		}
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + arity;
		result = prime * result + ((children == null) ? 0 : children.hashCode());
		result = prime * result + ((label == null) ? 0 : label.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		DecompositionTree other = (DecompositionTree) obj;
		if (arity != other.arity)
			return false;
		if (children == null) {
			if (other.children != null)
				return false;
		} else {
			for(int i=0; i<this.arity; i++) {
				if(!this.children.get(i).equals(other.children.get(i))) {
					return false;
				}
			}
		}
		
		if (label == null) {
			if (other.label != null)
				return false;
		} else if (!label.equals(other.label))
			return false;
		return true;
	}
}
