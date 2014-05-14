Hipster is still under development, but feel free to play around with it!
To install Hipster, you first need HipSpec and Isabelle. 

Isabelle is availble from: http://isabelle.in.tum.de/index.html.
Hipster works with Isabelle 2013-2.

Installation instructions for HipSpec and the system it relies on are availble from: https://github.com/danr/hipspec.
Note that you will need to clone the branch called "isabelle" to get the right version of HipSpec. 

When you have installed the above, you should open the file called IsaHipster.thy and edit the ML value 'basepath' to point to your IsaHipster directory (yes, we know, this is not so nice, we'll fix it...). 

You will also have to compile some Haskell files: HipSpecifyer.hs and Examples/GenericArbitrary.hs. 

Now, you should be able to try Hipster. Start up Isabelle on for example Examples/TreeDemo.thy and have a go.

DISCLIMER: There are quite a few hacks around, and Hipster is not a polished and finished product by any means. Let us know if you run into anything too odd, and we'll try to fix it.
