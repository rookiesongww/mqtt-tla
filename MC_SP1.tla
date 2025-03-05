---- MODULE MC_SP1 ----
EXTENDS MCSpec

SP1 == 
	[] /\ \A a \in clients : a \in active ~> (pc[a] = "connected")
====