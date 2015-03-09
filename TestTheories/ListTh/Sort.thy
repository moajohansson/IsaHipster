theory Sort
imports ../Sorting

begin

lemma setCountSort: "count t ts = count t (isort ts)"
oops

lemma elemIns: "\<not> eqN r t \<Longrightarrow> elem r (insert t ts) = elem r ts"
oops

lemma insLen: "len (insert t ts) = S (len ts)"
oops

lemma lenIort: "len (isort ts) = len ts"
oops

end

