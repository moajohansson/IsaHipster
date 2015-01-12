Hipster is still under development, but feel free to play around with it!
To install Hipster, you first need Isabelle, Z3 and HipSpec.

Isabelle is available from: http://isabelle.in.tum.de/index.html.
Hipster works with Isabelle 2013-2, preferably in jEdit if you want
nice syntactic sugar.

Z3 is available from: http://z3.codeplex.com/releases.

To install HipSpec, you will need to run the following commands (you
will need to have Git installed):

    git clone https://github.com/danr/hipspec
    cd hipspec
    git checkout hipster
    cabal update
    cabal install 

When you have installed the above, return to the IsaHipster directory and open the file called `IsaHipster.thy`. Edit the ML value `basepath` to point to your IsaHipster directory (yes, we know, this is not so nice, we'll fix it...). 

You will also have to compile the "HipSpecifyer":

    cabal install hipspecifyer/
    
Now, you should be able to try Hipster. Start up Isabelle on for example Examples/TreeDemo.thy and have a go.

_Disclaimer_: There are quite a few hacks around, and Hipster is not a polished and finished product by any means. Let us know if you run into anything too odd, and we'll try to fix it.
