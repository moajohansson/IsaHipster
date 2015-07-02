theory prop_29
imports Main
        "../../TestTheories/Listi"
        "../../TestTheories/Naturals"
        "$HIPSTER_HOME/IsaHipster"

begin


theorem revZip: "len rs = len ts \<Longrightarrow> rev (zip rs ts) = zip (rev rs) (rev ts)"
oops

end



