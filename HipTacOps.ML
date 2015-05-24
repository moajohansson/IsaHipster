
structure Hip_Tac_Ops =
struct

datatype T = Data of
    { with_full_types : bool,
      simp_filter : (thm -> bool) list,
      metis_filter : (thm -> bool) list,
      metis_to : int,
      whole_to : int
    }

fun get_with_full_types (Data d) = (#with_full_types d);
fun get_simp_filter (Data d) = (#simp_filter d);
fun get_metis_filter (Data d) = (#metis_filter d);
fun get_metis_to (Data d) = (#metis_to d);
fun get_whole_to (Data d) = (#whole_to d);

fun update_with_full_types f (Data d) =
    Data { with_full_types = f (#with_full_types d),
           simp_filter = #simp_filter d, metis_filter = #metis_filter d,
           metis_to = #metis_to d, whole_to = #whole_to d }
fun update_simp_filter f (Data d) =
    Data { with_full_types = #with_full_types d,
           simp_filter = f (#simp_filter d), metis_filter = #metis_filter d,
           metis_to = #metis_to d, whole_to = #whole_to d }
fun update_metis_filter f (Data d) =
    Data { with_full_types = #with_full_types d,
           simp_filter = #simp_filter d, metis_filter = f (#metis_filter d),
           metis_to = #metis_to d, whole_to = #whole_to d }
fun update_metis_to f (Data d) =
    Data { with_full_types = #with_full_types d,
           simp_filter = #simp_filter d, metis_filter = #metis_filter d,
           metis_to = f (#metis_to d), whole_to = #whole_to d }
fun update_whole_to f (Data d) =
    Data { with_full_types = #with_full_types d,
           simp_filter = #simp_filter d, metis_filter = #metis_filter d,
           metis_to = #metis_to d, whole_to = f (#whole_to d) }

val middle_tac_ops = Data { with_full_types = false,
                            simp_filter = [K false],
                            metis_filter = [K true],
                            metis_to = 400,
                            whole_to = 1500 }

structure Data = Theory_Data
                    ( type T = T
                      val empty = middle_tac_ops
                      val extend = I
                      val merge = fst )

fun metis_cond ctxt = (get_metis_filter (Data.get (Proof_Context.theory_of ctxt)));
fun simp_cond ctxt = (get_simp_filter (Data.get (Proof_Context.theory_of ctxt)));
fun use_full_types ctxt = (get_with_full_types (Data.get (Proof_Context.theory_of ctxt)));
fun metis_to ctxt = (get_metis_to (Data.get (Proof_Context.theory_of ctxt)));

fun add_metis_filter ctxt f = Data.put (update_metis_filter (fn lfs => lfs @ [f]) (Data.get (Proof_Context.theory_of ctxt)));
fun prio_metis_filter ctxt f = Data.put (update_metis_filter (fn lfs => f :: lfs) (Data.get (Proof_Context.theory_of ctxt)));
fun set_metis_filter ctxt f = Data.put (update_metis_filter (K [f]) (Data.get (Proof_Context.theory_of ctxt)));

fun add_simp_filter ctxt f = Data.put (update_simp_filter (fn lfs => lfs @ [f]) (Data.get (Proof_Context.theory_of ctxt)));
fun prio_simp_filter ctxt f = Data.put (update_simp_filter (fn lfs => f :: lfs) (Data.get (Proof_Context.theory_of ctxt)));
fun set_simp_filter ctxt f = Data.put (update_simp_filter (K [f]) (Data.get (Proof_Context.theory_of ctxt)));

fun set_full_types ctxt b = Data.put (update_with_full_types (K b) (Data.get (Proof_Context.theory_of ctxt)));
fun toggle_full_types ctxt = Data.put (update_with_full_types not (Data.get (Proof_Context.theory_of ctxt)));

fun set_metis_to ctxt t = Data.put (update_metis_to (K t) (Data.get (Proof_Context.theory_of ctxt)));
fun bump_metis_to ctxt diff = Data.put (update_metis_to (fn t => t + diff) (Data.get (Proof_Context.theory_of ctxt)));
fun set_whole_to ctxt t = Data.put (update_whole_to (K t) (Data.get (Proof_Context.theory_of ctxt)));
fun bump_whole_to ctxt diff = Data.put (update_whole_to (fn t => t + diff) (Data.get (Proof_Context.theory_of ctxt)));

end;


