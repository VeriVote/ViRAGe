# VotingRuleGenerator

## Installation

For ViRAGe to work properly, some dependencies have to be supplied manually.

### Isabelle/HOL

Download and install Isabelle/HOL, for example from the package sources of your Linux distribution or from its [official page](http://isabelle.in.tum.de/). After installation, you have to make sure that Isabelle is accessible via the command line, i.e. the console call "isabelle" must be possible on your system. How to achieve this is heavily dependent on your system.

### SWI-Prolog

ViRAGe uses [JPL7](https://jpl7.org/) for its Prolog interaction. On some operating systems, it is shipped with the default swi-prolog/swipl install, on some others (e.g. Ubuntu), swi-prolog-java has to be installed explicitly. Sometimes it is necessary to also set some environment variables, as described [here](https://jpl7.org/TutorialResources). Bash scripts for building and running ViRAGe can be found in the repository, but the SWI_HOME_DIR variable has to be changed to fit your installation of SWI-Prolog. These scripts only change the bare minimum of variables, on some systems this might not be enough, follow the tutorial above in case of further problems.
