JIProlog is not part of any official Maven repository.
Get the jar file from jiprolog.com and install as follows:

mvn install:install-file
  -Dfile=<path-to-file>
  -DgroupId=com.ugos
  -DartifactId=jiprolog
  -Dversion=4.1.6.1
  -Dpackaging=jar
  -DgeneratePom=true
 
Where: <path-to-file>  the path to the file to load

If any of the info changes, it has to be changed in pom.xml as well.
