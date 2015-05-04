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

You will also have to compile the "HipSpecifyer":

    cabal install hipspecifyer/
    
Finally, you should set the environment variable $HIPSTER_HOME (e.g. in your .profile file) to the path for the IsaHipster directory you just cloned. If you want to use Hipster from an Isabelle file, it need to import the IsaHipster.thy file, which sets up Hipster, by including the line: 
    
    imports "$HIPSTER_HOME/IsaHipster"
    
Now, you should be able to try Hipster. Start up Isabelle on for example Examples/TreeDemo.thy and have a go.

_Disclaimer_: There are quite a few hacks around, and Hipster is not a polished and finished product by any means. Let us know if you run into anything too odd, and we'll try to fix it.
