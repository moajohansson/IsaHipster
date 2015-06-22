theory prop_29
imports Main
        "../../TestTheories/Listi"
        "../../TestTheories/Naturals"
        "../../IsaHipster"

begin


theorem revZip: "len rs = len ts \<Longrightarrow> rev (zip rs ts) = zip (rev rs) (rev ts)"
oops

end



