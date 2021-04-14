# ViRAGe

ViRAGe is a tool for analysis and generation of voting rules. It is also capable of generating executable implementations of those rules in Scala. Furthermore, claims it makes about whether or not some rule satisfies given social choice properties can oftentimes be fully automatically proven within Isabelle.

In case of urgent questions or problems, contacting me at fabian.richter@student.kit.edu might help to find a solution.

## Installation

For ViRAGe to work properly, some dependencies have to be supplied manually.

### Isabelle

Download and install Isabelle, for example from the package sources of your Linux distribution or from its [official page](http://isabelle.in.tum.de/). After installation, you have to make sure that Isabelle is accessible via the command line, i.e. the console command ```isabelle``` must point to the executable of the same name located in ```../isabelle/bin```. How to achieve this is heavily dependent on your system, and at this point is not possible on Windows machines, as this executable does not run there.

For Manjaro: Install isabelle from the AUR, that's it.
For Ubuntu: Download Isabelle from its [website](https://isabelle.in.tum.de/), extract the tar and add the ```./Isabelle2020/bin``` to your path. There might be other solutions as well.

### SWI-Prolog

ViRAGe uses [JPL7](https://jpl7.org/) for its Prolog interaction. On some operating systems, it is shipped with the default swi-prolog/swipl install, for Ubuntu and other Debian-bases systems see [here](https://swi-prolog.org/build/PPA.txt) and ```swi-prolog-java``` has to be installed explicitly. Sometimes it is necessary to also set some environment variables, as described [here](https://jpl7.org/TutorialResources). Bash scripts for building and running ViRAGe can be found in the repository, but the SWI_HOME_DIR variable has to be changed to fit your installation of SWI-Prolog. These scripts only change the bare minimum of variables, on some systems this might not be enough, follow the tutorial above in case of further problems. When the required environment variables are set correctly and permanently, the scripts can be omitted and ViRAGe can be built and run using Maven alone.

### Scala

Make sure to install Scala on your system if ViRAGe shall compile generated source files automatically. At least ```scala 2.13.0``` is required, as Isabelle uses ```scala.util.chaining.*```.

### pdflatex

The Isabelle document tool requires ```pdflatex``` to be installed. As this tool is invoked on every proof process started by ViRAGe, make sure ```pdflatex``` is available. ```texlive-full``` is recommended, ```texlive-core``` does not contain all packages required by Isabelle.

### BEAST

The experimental SBMC integration requires the BEAST framework to be available. Clone the repository, check out the ```experimental``` branch and run ```mvn clean install```. If this procedure changes at some point, this README should be updated, in doubt, refer to the BEAST repository.

## Usage

When launching ViRAGe, one must supply an (Extended)-Prolog file. An example of such a file can be found is ```../src/test/resources/framework.pl```. This file describes the Voting Rule Framework at its current state and is therefore the default right now (Just press 'enter' on the prompt.). Still, looking at it might give useful hints at the syntax ViRAGe expects for compositions and properties, which is structurally similar to Prolog.

After a while, one of the following modes can then be chosen by typing the corresponding letter on the next prompt:

### Composition Generation

Here, the user can supply a set of properties (e.g. "monotone,electing"), ViRAGe will then attempt to generate a composition satisfying these properties. ViRAGe will attempt to do so in different ways, and each result will be displayed, so there might be more than one.

### Composition Analysis

The user can again supply a set of properties, together with a composition (e.g. "seq_comp(pass_module(1,_),elect_module)") and ViRAGe will check whether or not the composition satisfies these properties. (Caution: Prolog has a "closed world assumption", e.g. ViRAGe might yield false negatives.) Again, more than one result will be displayed, but considering how Prolog answers queries it will usually be clear which one to trust.

### Proving Claims

This mode is not very useful on its own, but it tells ViRAGe to derive a proof. Usage is similar to Composition Analysis, but a rudimentary proof tree will be displayed.

### Generating Isabelle Code

Again, usage is similar to Composition Analysis, using this mode ViRAGe will generate an Isabelle theory file containing proofs for its results, these can then be checked fully automatically.

### Generating Scala Code

Here, the user only has to supply a composition, ViRAGe will then make use of Isabelle's code generation capabilities to create an executable implementation of that composition which will be compiled automatically, the result is an executable Scala jar file. 

Test instances for these can be found in ```../src/test/instances```, each line representing one ballot, ordered from least to most preferred candidate (Yes, that is slightly unintuitive and might be changed later).

### Exiting ViRAGe

Typing "exit" will terminate ViRAGe :-)

## Known Problems

Error messages are often just logged Exceptions at this point. For somebody not familiar with ViRAGe's internals, this might be more confusing than helpful and will be changed in the future. (If any of the classes in the stack-trace is one of JPL's, that probably means that JPL is not set up correctly yet.)

When invoking the Isabelle process on the "Voting" session (required for Code Generation and Automatic Verification) for the first time, this session has to be built. This might take a considerable amount of time and, on some machines, not work on the first try. In this case, navigating to ```../src/test/resources/theories/``` and calling ```isabelle build -o quick_and_dirty -o browser_info -b -D .``` might help. While the build process might not finish on first try due to SMT-timeouts, rerunning it a few times will usually work at some point, ViRAGe can then be restarted in the usual way. A better solution is very desirable, but not available yet.

Using the elimination module currently breaks both the Automatic Verification as well as Code Generation. There is no theoretical reason for this, but the Theory Generation is currently unable to process the elimination module correctly.
