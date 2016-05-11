# Hipster - theory exploration in Isabelle/HOL

Hipster is still under development, but feel free to play around with it! To
install Hipster, you first need Isabelle, QuickSpec and HipSpec.

Isabelle is available from: http://isabelle.in.tum.de/index.html. Hipster works
with [Isabelle 2015][Isa15], preferably in jEdit if you want nice syntactic
sugar (use the branch `Isabelle2014` if you want the [Isabelle 2014][Isa14]
compatible version).

For a version compatible with the newest [Isabelle 2016][Isa16] (although
unstable due to further development), checkout the branch `Isabelle2016`.

First install the following Haskell package, called `Happy`:
	
	cabal install happy

To download the appropriate [QuickSpec][QS]:

	git clone https://github.com/nick8325/quickspec.git
	cd quickspec
	git checkout hipster
	cd ..

To dowload [HipSpec][HS], you will need to run the following commands:

    git clone https://github.com/danr/hipspec
    cd hipspec
    git checkout hipster
    cd ..
	
Then install QuickSpec and HipSpec together (avoids version conflicts) by issuing the command:

    cabal install hipspec/ quickspec/	

You can now clone the Hipster repository itself, and compile the `HipSpecifyer`:

    git clone https://github.com/moajohansson/IsaHipster.git
    cd IsaHipster
    cabal install hipspecifyer/

Finally, you need to tell Isabelle where to find Hipster, HipSpec, QuickSpec and the HipSpecifyer which you just installed. 
Do this by setting the environment variables `$HIPSTER_HOME` and `$HASKELL_HOME` in the file `$ISABELLE_HOME_USER/etc/settings`
(create this file if it does not exist yet), where Isabelle normally has set
`$ISABELLE_HOME_USER` to `$USER_HOME/.isabelle`. `$HIPSTER_HOME` should then
point to the path for the IsaHipster directory you just cloned. `$HASKELL_HOME`
should point to where cabal installs your Haskell executables (usually something like `$HOME/Library/Haskell/bin/`).

See the Isabelle System's Manual for more info on how to set up Isabelle's system
enviroment. 

Alternatively, you may set the environment variables in your bash environment
file, but then Isabelle will only find Hipster if you start it from the
terminal, so I would recommend the former approach.

If you want to use Hipster from an Isabelle theory file, it needs to import the
`IsaHipster.thy` file (which essentially sets up Hipster) by including the
line:

```isabelle
imports "$HIPSTER_HOME/IsaHipster"
```
    
Now, you should be able to try Hipster.  
Start up Isabelle on for example `Examples/TreeDemo.thy` and have a go.

_Common Issues_: As Hipster currently depends on specific versions of QuickSpec and HipSpec, some
users have experienced problems with accidentally having conflicting cabal installation of several versions of the tools,
which usually manifest itself in that Hipster gives you some strange error messages.
If you've ended up with several versions of QuickSpec and/or HipSpec, you can remove unwanted 
ones using the command line tool `ghc-pkg unregister <Name-Of-Unwanted-Version>`. 

_Disclaimer_: Hipster is always under development. Let us know if you run into anything too odd,
and we'll try to fix it.


[QS]: https://github.com/nick8325/quickspec
[HS]: https://github.com/danr/hipspec
[Isa14]: http://isabelle.in.tum.de/download_past.html
[Isa15]: http://isabelle.in.tum.de/download_past.html
[Isa16]: http://isabelle.in.tum.de/installation.html

