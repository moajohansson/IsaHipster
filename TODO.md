Implementation TODOs for coinduction paper
=====================================================

Enhancements
--------------
* Automate observer functions (automatically create observer functions where needed to perform exploration)
  * Sólrún working on this (21/11), I think this can be done via the tip tools when the quickspec  
* Implement tactic that combines coinduction and induction, using whichever is appropriate in each case

Bugs
-----------
* If desired `t.coinduct` rule doesn't exist the proof-loop crashes, we should catch this!
* Reconstructed Sledgehammer proof script may contain faulty fastforce calls like `by (fastforce Llist.collapse(1) lemma_a)` which gives rise to error message "Bad arguments for method 'fastforce'"
* (Fixed, [see commit](https://github.com/moajohansson/IsaHipster/commit/9f85dca46f73e078710b83ba2c8a516927f617f6)
 Sometimes "Unification bound exceeded" is printed about 1000 times in the middle of the proof-loop (For example when `hipster lappend` is called in `/benchmark/she/Coinductive_List/Lappend_assoc.thy`)
