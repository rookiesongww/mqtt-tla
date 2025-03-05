---- MODULE Attacker ----
EXTENDS MQTTBase

CONSTANT attacker
CONSTANT isEncrypted \*是否加密

VARIABLE 
    kmsgs,  \* 攻击者消息库,保存从网络中拦截的消息
    knows    \* 攻击者知识库,保存从密文中获取的知识

attacker_vars == <<kmsgs,knows>>    

\* Attacker 
Eavesdrop == 
    /\ \E a \in agents : Len(network[a]) > 0 
    /\ LET x == CHOOSE a \in agents : Len(network[a]) > 0  IN
        /\ kmsgs' = kmsgs \cup {Head(network[x])}  
        /\ UNCHANGED network
    /\ UNCHANGED knows

Intercept ==
    /\ \E a \in agents : Len(network[a]) > 0   
    /\ LET x == CHOOSE a \in agents : Len(network[a]) > 0  IN
        /\ kmsgs' = kmsgs \cup {Head(network[x])}  
        /\ network' = [network EXCEPT ![x] = Tail(network[x])]
    /\ UNCHANGED knows 

Replay ==
    /\ kmsgs /= {}  
    /\ LET  des == CHOOSE a \in agents : TRUE   
            msg == CHOOSE one \in kmsgs : TRUE 
       IN 
         /\ LET source == CHOOSE s \in agents : s # des IN 
            /\ LET fmsg == [msg EXCEPT !.from = source, !.to = des] IN 
                    /\ network' = send(fmsg,fmsg.to) 
                    /\ UNCHANGED kmsgs
    /\ UNCHANGED knows

Forward ==
    /\ kmsgs /= {}  
    /\ LET msg == CHOOSE one \in kmsgs : TRUE IN 
        /\ LET amsg == [msg EXCEPT !.from = attacker] IN 
            /\ network' = send(amsg, amsg.to)
            /\ UNCHANGED kmsgs
    /\ UNCHANGED knows

Forge == 
    /\ ~isEncrypted
    /\ kmsgs /= {}
    /\ knows.clientId /= {} 
    /\ \E m \in kmsgs : m.type = CONNECT
    /\ LET 
        msg == CHOOSE one \in kmsgs : one.type = CONNECT 
        x == CHOOSE one \in knows.clientId : TRUE
       IN
        /\ LET fmsg == [msg EXCEPT !.payload.clientId = x] IN 
            /\ kmsgs' = kmsgs \cup {fmsg}
            /\ UNCHANGED knows
            /\ UNCHANGED network

Resolve == 
    /\ ~isEncrypted 
    /\ kmsgs /= {}
    /\ LET msg == CHOOSE one \in kmsgs : TRUE IN
        /\ knows' = CASE msg.type = CONNECT -> [knows EXCEPT !.clientId = @ \cup {msg.payload.clientId} ] 
                    [] msg.type = PUBLISH -> [knows EXCEPT !.msgID = @ \cup {msg.packetID}, !.topic = @ \cup {msg.topic}] 
                    [] msg.type = SUBSCRIBE -> [knows EXCEPT !.topic = @ \cup {msg.topic}]
                    [] OTHER -> knows 
    /\ UNCHANGED network
    /\ UNCHANGED kmsgs

IoTDeviceAttack ==
    /\ knows' = [knows EXCEPT !.clientId = @ \cup clients]
    /\ UNCHANGED network
    /\ UNCHANGED kmsgs

AttackerInit == 
    /\ kmsgs = {} \* 初始时，消息库为空集
    /\ knows = [ \*初始时，知识库为空
        clientId |-> {}, 
        topic |-> {}, 
        msgID |-> {}
        ] 

AttackerAction ==
    \/ Eavesdrop 
    \/ Intercept 
    \/ Forward 
    \/ Replay
    \/ Resolve
    \/ Forge
    \/ IoTDeviceAttack
====