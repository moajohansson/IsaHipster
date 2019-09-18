# Hipster - theory exploration in Isabelle/HOL

Hipster is always under development, but feel free to play around with it! To
install Hipster, you first need Isabelle and TIP-tools.

Isabelle is available from: http://isabelle.in.tum.de/index.html. Hipster works
with [Isabelle 2019][Isa19].


Start by installing [TIP-tools][TIP]. You need to have Haskell installed, as well as [Stack][ST]: 

    git clone https://github.com/tip-org/tools.git
    cd tools
    stack setup
    stack install

You can now clone the Hipster repository itself:

    git clone https://github.com/moajohansson/IsaHipster.git

Finally, you need to tell Isabelle where to find Hipster and TIP-tools, which you just installed. 
Do this by setting the environment variables `$HIPSTER_HOME` and `$HASKELL_HOME` in the file `$ISABELLE_HOME_USER/etc/settings`
(create this file if it does not exist yet), where Isabelle normally has set
`$ISABELLE_HOME_USER` to `$USER_HOME/.isabelle`. `$HIPSTER_HOME` should then
point to the path for the IsaHipster directory you just cloned. `$HASKELL_HOME`
should point to where Stack installs your Haskell executables (usually something like `$HOME/.local/bin/`).

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

To try coinductive theory exploration, check out `Examples/StreamExample.thy`.


_Disclaimer_: Hipster is always under development. Let us know if you run into anything too odd,
and we'll try to fix it.


[TIP]: https://github.com/tip-org/tools
[Isa19]: http://isabelle.in.tum.de/installation.html
[ST]: https://www.haskell.org/downloads
