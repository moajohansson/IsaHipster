Hipster is still under development, but feel free to play around with it!
To install Hipster, you first need HipSpec and Isabelle. 

Isabelle is availble from: http://isabelle.in.tum.de/index.html.
Hipster works with Isabelle 2013-2.

Installation instructions for HipSpec and the systems it relies on (QuickSpec and QuickCheck) are availble from: https://github.com/danr/hipspec.
Note that you will need to switch to the branch called `isabelle' after you have cloned the repo. Issue this command in the created repository directory for HipSpec:

     git checkout isabelle

When you have installed the above, return to the IsaHipster directory and open the file called `IsaHipster.thy`. Edit the ML value `basepath` to point to your IsaHipster directory (yes, we know, this is not so nice, we'll fix it...). 

You will also have to compile the "HipSpecifyer":

    cabal install hipspecifyer/
    
Finally, create an (empty) directory called `GenCode` in the top-level directory:

    mkdir -p GenCode
    
This is where Hipster will store generated Haskell-files (this requirement will shortly dissapear, when we tidy things up...).

Now, you should be able to try Hipster. Start up Isabelle on for example Examples/TreeDemo.thy and have a go.

_Disclaimer_: There are quite a few hacks around, and Hipster is not a polished and finished product by any means. Let us know if you run into anything too odd, and we'll try to fix it.
