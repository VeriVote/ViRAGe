package edu.pse.beast.highlevel.javafx;

import edu.pse.beast.datatypes.propertydescription.PreAndPostConditionsDescription;
import javafx.scene.control.TreeItem;

public class PublicParentTreeItem extends ParentTreeItem {
	public PublicParentTreeItem(final PreAndPostConditionsDescription propertyDesc) {
		
		super(propertyDesc, true, new TreeItem<CustomTreeItem>(), true);
	}
}
