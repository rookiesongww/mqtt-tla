---- MODULE MCSpec ----
EXTENDS Spec, Attacker

MCInit ==
    /\ Init
    /\ AttackerInit

MCNext ==
    \/ /\ Next 
       /\ UNCHANGED attacker_vars
    \/ /\ AttackerAction
       /\ UNCHANGED agent_vars

MCSpec == MCInit /\ [][MCNext]_(vars \o attacker_vars) 

TypeCheckSeq(seq, set) == \A i \in 1..Len(seq) : seq[i] \in set

TypeCheckSet(set, type) ==
    /\ IsFiniteSet(set)
    /\ \A e \in set : e \in type

TypeOK ==
    /\ used_num \subseteq 1..maxPubNum
    /\ \A s \in subscribers \ {attacker} : Len(store[s]) <= maxPubNum
    /\ \A t \in topics, q \in {QoS0,QoS1,QoS2} :
        /\ TypeCheckSeq(store[broker][t][q], 1..maxPubNum*2)
        /\ TypeCheckSet(topic_subscribers[t][q], subscribers)

AllSubscribedBeforePublish ==
    \A p \in publishers :
        (pc[p] = "publishingwithqos1" \/ pc[p] = "publishingwithqos2") =>
        (\A s \in subscribers : pc[s] = "connected" /\ \E t \in topics, q \in {QoS0, QoS1, QoS2} : s \in topic_subscribers[t][q])

AllMessagesSentAndPushedBeforeUnsubscribe ==
    \A s \in subscribers :
        pc[s] = "unsubscribing" =>
        (\A p \in publishers : store[p] = {}) /\
        (\A t \in topics, q \in {QoS0, QoS1, QoS2} : store[broker][t][q] = <<>>)

LenConstraint == \A a1,a2 \in agents : Len(network[a1]) + Len(network[a2]) <= 2

SpecConstraints == 
	/\ AllSubscribedBeforePublish 
	/\ AllMessagesSentAndPushedBeforeUnsubscribe
	/\ LenConstraint 
====