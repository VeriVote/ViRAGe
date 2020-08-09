export SWI_HOME_DIR=/lib/swipl

export CLASSPATH=$SWI_HOME_DIR/lib/jpl.jar:$CLASSPATH
export LD_LIBRARY_PATH=$SWI_HOME_DIR/lib/x86_64-linux/
export LD_PRELOAD=$LD_LIBRARY_PATH/libswipl.so

java -jar target/ViRAGe-0.0.1-SNAPSHOT.jar

