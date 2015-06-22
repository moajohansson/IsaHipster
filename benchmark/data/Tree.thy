theory Tree
imports Main
begin
datatype 'a Tree = Leaf | Node "'a Tree" 'a "'a Tree"
end

