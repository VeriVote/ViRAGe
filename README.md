# ViRAGe

ViRAGe is a tool for analysis and generation of voting rules. It is also capable of generating executable implementations of those rules in Scala. Furthermore, claims it makes about whether or not some rule satisfies given social choice properties can oftentimes be fully automatically proven within Isabelle.

In case of urgent questions or problems, contacting me at fabian.richter@student.kit.edu might help to find a solution.

## Installation

For ViRAGe to work properly, some dependencies have to be supplied manually.

### Isabelle

Download and install Isabelle, for example from the package sources of your Linux distribution or from its [official page](http://isabelle.in.tum.de/). After installation, you have to verify that the settings within ```src/main/resources/config.properties``` are correct and rebuild ViRAGe if necessary.

For Manjaro: Install isabelle from the AUR, that's it.
For Ubuntu: Download Isabelle from its [website](https://isabelle.in.tum.de/), extract the tar and add the ```./Isabelle2020/bin``` to your path. There might be other solutions as well.

### SWI-Prolog

ViRAGe uses [JPL7](https://jpl7.org/) for its Prolog interaction, so at least SWI-Prolog 8.0.0 is required. On some operating systems, it is shipped with the default swi-prolog/swipl install, for Ubuntu and other Debian-bases systems see [here](https://swi-prolog.org/build/PPA.txt) and ```swi-prolog-java``` has to be installed explicitly. Sometimes it is necessary to also set some environment variables, as described [here](https://jpl7.org/TutorialResources). ViRAGe will assist you with doing this, but as for Isabelle, some settings might have to be changed manually.

Be careful when installing via snap. The ```swi-prolog``` package is available there, but ```swi-prolog-java``` is not and compatibility cannot be ensured.

### pdflatex

The Isabelle document tool requires ```pdflatex``` to be installed. As this tool is invoked on every proof process started by ViRAGe, make sure ```pdflatex``` is available. ```texlive-full``` is recommended, ```texlive-core``` does not contain all packages required by Isabelle. If ```pdflatex``` is missing, all session builds will fail!

## Usage

When launching ViRAGe, one can either run it directly on an Isabelle session directory, or must supply an (Extended)-Prolog file. An example of such a file is the ```format_guide.pl``` within this repository. After a while, a Compositional Framework is loaded from either the session or an (E)PL file, then one of the following modes can then be chosen by typing the corresponding letter on the next prompt:

### Composition Generation

Here, the user can supply a set of properties (e.g. "monotone,electing"), ViRAGe will then attempt to generate a composition satisfying these properties.

### Composition Analysis

The user can again supply a set of properties, together with a composition (e.g. "seq_comp(pass_module(1,_),elect_module)") and ViRAGe will check whether or not the composition satisfies these properties. (Caution: Prolog has a "closed world assumption", e.g. ViRAGe might yield false negatives.)

### Proving Claims

This mode is not very useful on its own, but it tells ViRAGe to derive a proof. Usage is similar to Composition Analysis.

### Generating Isabelle Code

Again, usage is similar to Composition Analysis, using this mode ViRAGe will generate an Isabelle theory file containing proofs for its results, these can then be checked fully automatically.

### Generating Scala Code

Here, the user only has to supply a composition, ViRAGe will then make use of Isabelle's code generation capabilities to create an executable implementation of that composition which will be compiled automatically, the result is an executable Scala jar file. 

Test instances for these can be found in ```../src/test/instances```, each line representing one ballot, ordered from least to most preferred candidate (Yes, that is slightly unintuitive and might be changed later).

### Generating C Code

ViRAGe is capable of generating executable C implementations of voting rules from user-defined C snippets. This feature is required for automatic verification via BEAST/CBMC, but it is still in an experimental state.

### Exiting ViRAGe

Typing "exit" will terminate ViRAGe :-)
