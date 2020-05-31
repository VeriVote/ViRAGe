package com.fr2501.util;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;

public class SimpleFileReader {
	private BufferedReader reader;
	
	public String readFileByLine(File file) {
		String res = "";
		
		try {
			this.reader = new BufferedReader(new FileReader(file));
		
		
			String line = reader.readLine();
			while(line != null) {
				res += line;
				line = reader.readLine();
			}
		} catch(FileNotFoundException e) {
			// TODO
			e.printStackTrace();
			System.out.println("Invalid file.");
		} catch(IOException e) {
			// TODO
			e.printStackTrace();
			System.out.println("Something went wrong while reading the file.");
		} finally {
			try {
				this.reader.close();
			} catch(IOException e) {
				// TODO
				e.printStackTrace();
				System.out.println("Reader could not be closed.");
			}
		}
		
		return res;
	}
}
