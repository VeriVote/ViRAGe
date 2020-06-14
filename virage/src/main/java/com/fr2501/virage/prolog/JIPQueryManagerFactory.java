package com.fr2501.virage.prolog;

import com.fr2501.virage.types.FrameworkRepresentation;

// TODO: Documentation
public class JIPQueryManagerFactory {
	public static JIPQueryManager getJIPQueryManager(FrameworkRepresentation framework) {
		JIPQueryManager manager = new JIPQueryManager(framework);
		
		Thread thread = new Thread(manager, "JIPQueryManager");
		thread.start();
		
		return manager;
	}
}
