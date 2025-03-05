---- MODULE Broker ----
EXTENDS MQTTBase

HandleConnectReq ==
	/\ Len(network[broker]) > 0
	/\ LET msg == Head(network[broker]) IN
		/\ msg.to = broker 
		/\ msg.type = CONNECT
		/\ \E m \in msgs:
			/\ m.type = CONACK
			/\ m.from = msg.to 
			/\ m.to = msg.from
			/\ network' = response(m,m.from,m.to)
			/\ active' = active \cup {msg.from} 
	/\ UNCHANGED pc 
	/\ UNCHANGED topic_subscribers
  	/\ UNCHANGED store 
	/\ UNCHANGED used_num

HandleSubscribeReq ==
	/\ Len(network[broker]) > 0
	/\ LET msg == Head(network[broker]) IN
		/\ msg.from \in active
		/\ msg.to = broker 
		/\ msg.type = SUBSCRIBE
		/\ \E m \in msgs:
			/\ m.type = SUBACK
			/\ m.from = msg.to 
			/\ m.to = msg.from
			/\ m.topic = msg.topic
			/\ m.qos = msg.qos 
			/\ LET q == CASE m.qos = 0 -> QoS0 [] m.qos = 1 -> QoS1 [] m.qos = 2 -> QoS2 IN
				/\ topic_subscribers' = [topic_subscribers EXCEPT ![m.topic][q] = @ \cup {msg.from}]
				/\ network' =  response(m,m.from,m.to)
	/\ UNCHANGED <<pc,active>>
  	/\ UNCHANGED store  	  
	/\ UNCHANGED used_num

HandleUnsubscribeReq ==
	/\ Len(network[broker]) > 0
	/\ LET msg == Head(network[broker]) IN
		/\ msg.from \in active
		/\ msg.to = broker 
		/\ msg.type = UNSUBSCRIBE
			/\ \E m \in msgs :
				/\ m.type = UNSUBACK
				/\ m.from = msg.to 
				/\ m.to = msg.from
				/\ m.topic = msg.topic
				/\ canSendTo(m.to)
				/\ \E q \in {QoS0,QoS1,QoS2} :
					/\ topic_subscribers[msg.topic][q] /= {} 
					/\ topic_subscribers' = [topic_subscribers EXCEPT ![m.topic][q] = @ \ {msg.from}]
					/\ network' = response(m,m.from,m.to) 
	/\ UNCHANGED <<pc,active>>
  	/\ UNCHANGED store 
	/\ UNCHANGED used_num

HandlePingReq ==
	/\ Len(network[broker]) > 0
	/\ LET msg == Head(network[broker]) IN
		/\ msg.from \in active
		/\ msg.to = broker 
		/\ msg.type = PINGREQ
		/\ \E m \in msgs:
			/\ m.type = PINGRESP
			/\ m.from = msg.to 
			/\ m.to = msg.from
			/\ network' = response(m,m.from,m.to)
	/\ UNCHANGED pc
    /\ UNCHANGED active 
	/\ UNCHANGED topic_subscribers
    /\ UNCHANGED store  
	/\ UNCHANGED used_num

HandlePublishWithQoS0Req ==
	/\ Len(network[broker]) > 0
	/\ LET msg == Head(network[broker]) IN
		/\ msg.to = broker 
		/\ msg.type = PUBLISH 
		/\ msg.qos = 0 
		/\ network' = rcv(msg,broker)
		/\ store' = [store EXCEPT ![broker][msg.topic][QoS0] = Append(@, msg.packetID)]
	/\ UNCHANGED pc
    /\ UNCHANGED active 
    /\ UNCHANGED topic_subscribers
	/\ UNCHANGED used_num

HandlePublishWithQoS1Req ==
	/\ Len(network[broker]) > 0
	/\ LET msg == Head(network[broker]) IN
		/\ msg.to = broker 
		/\ msg.type = PUBLISH
		/\ msg.qos = 1
		/\ \E m \in msgs :
			/\ m.type = PUBACK
			/\ m.from = msg.to 
			/\ m.to = msg.from
			/\ m.packetID = msg.packetID
			/\ network' = response(m,m.from,m.to)
            /\ store' = [store EXCEPT ![broker][msg.topic][QoS1] = Append(@, msg.packetID)]
	/\ UNCHANGED pc
    /\ UNCHANGED active 
    /\ UNCHANGED topic_subscribers
	/\ UNCHANGED used_num

HandlePushQoS1Res == 
	/\ Len(network[broker]) > 0
	/\ LET m == Head(network[broker]) IN
		/\ \E t \in topics :
			/\ \E qos \in {QoS0,QoS1,QoS2}:
				/\ Len(store[broker][t][qos]) > 0
				/\ m.to = broker 
				/\ m.type = PUBACK
				/\ m.packetID = Head(store[broker][t][qos]) + maxPubNum
				/\ network' = rcv(m,broker)
				/\ store' = CASE  \A q \in {QoS0,QoS1,QoS2} : topic_subscribers[t][q] \ {m.from} = {} -> [store EXCEPT ![broker][t][qos] = Tail(@)] [] OTHER -> store 
	/\ UNCHANGED pc
	/\ UNCHANGED active
	/\ UNCHANGED topic_subscribers
	/\ UNCHANGED used_num

HandlePublishWithQoS2Req ==
    /\ Len(network[broker]) > 0
    /\ LET msg == Head(network[broker]) IN
        /\ msg.to = broker 
        /\ msg.type = PUBLISH
        /\ msg.qos = 2
        /\ \E m \in msgs :
            /\ m.type = PUBREC
            /\ m.from = msg.to 
            /\ m.to = msg.from
            /\ m.packetID = msg.packetID
            /\ network' = response(m,m.from,m.to)
            /\ store' = [store EXCEPT ![broker][msg.topic][QoS2] = Append(@, msg.packetID)]
    /\ UNCHANGED pc
    /\ UNCHANGED active 
    /\ UNCHANGED topic_subscribers
    /\ UNCHANGED used_num

HandlePubrelReq ==
    /\ Len(network[broker]) > 0
    /\ LET msg == Head(network[broker]) IN
        /\ msg.to = broker 
        /\ msg.type = PUBREL
        /\ \E m \in msgs :
            /\ m.type = PUBCOMP
            /\ m.from = msg.to 
            /\ m.to = msg.from
            /\ m.packetID = msg.packetID
            /\ network' = response(m,m.from,m.to)
	/\ UNCHANGED store
    /\ UNCHANGED pc
    /\ UNCHANGED active 
    /\ UNCHANGED topic_subscribers
    /\ UNCHANGED used_num

HandlePushQoS2Res == 
	/\ Len(network[broker]) > 0
	/\ LET m == Head(network[broker]) IN
		/\ \E t \in topics :
			/\ \E qos \in {QoS2} :
				/\ Len(store[broker][t][qos]) > 0
				/\ m.from \in subscribers
				/\ m.to = broker 
				/\ m.type = PUBREC
				/\ m.packetID = Head(store[broker][t][qos]) + maxPubNum
				/\ \E rmsg \in msgs : 
					/\ rmsg.from = m.to
					/\ rmsg.to = m.from
					/\ rmsg.type = PUBREL
					/\ rmsg.packetID = m.packetID
					/\ network' = response(rmsg,rmsg.from,rmsg.to)
	/\ UNCHANGED store
	/\ UNCHANGED pc
	/\ UNCHANGED active
	/\ UNCHANGED topic_subscribers
	/\ UNCHANGED used_num

HandlePubCompRes == 
	/\ Len(network[broker]) > 0
	/\ LET m == Head(network[broker]) IN
		/\ \E t \in topics :
			/\ \E qos \in {QoS2}:
				/\ Len(store[broker][t][qos]) > 0
				/\ m.to = broker 
				/\ m.type = PUBCOMP
				/\ m.packetID = Head(store[broker][t][qos]) + maxPubNum
				/\ network' = rcv(m,broker)
				/\ store' = CASE \A q \in {QoS0,QoS1,QoS2} : topic_subscribers[t][q] \ {m.from} = {} -> [store EXCEPT ![broker][t][QoS2] = Tail(@)] [] OTHER -> store 
	/\ UNCHANGED pc
	/\ UNCHANGED active
	/\ UNCHANGED topic_subscribers
	/\ UNCHANGED used_num

HandleDisConReq ==
    /\ Len(network[broker]) > 0
    /\ LET msg == Head(network[broker]) IN
        /\ msg.to = broker 
        /\ msg.type = DISCONNECT
        /\ network' = rcv(msg, broker)
        /\ active' = active \ {msg.from}  
	/\ UNCHANGED store
    /\ UNCHANGED pc
    /\ UNCHANGED topic_subscribers
    /\ UNCHANGED used_num

MinQoS(a,b) == IF (a = QoS0 /\ b \in  {QoS1,QoS2}) \/ (a = QoS1 /\ b = QoS2) THEN  a ELSE b 

PushMsgsWithQoS0 ==
	/\ Len(network[broker]) = 0 
  	/\ \E t \in topics :
		\E q1,q2 \in {QoS0,QoS1,QoS2}:
			/\ Len(store[broker][t][q1]) > 0
			/\ topic_subscribers[t][q2] /= {}
			/\ MinQoS(q1,q2) = QoS0
			/\ LET  
				pId == Head(store[broker][t][q1]) 
				subscriber == CHOOSE one \in topic_subscribers[t][q2] : TRUE
			   IN
					/\ subscriber \in active
					/\ pc[subscriber] = "connected"
					/\ \E m \in msgs :
						/\ m.from = broker 
						/\ m.type = PUBLISH
						/\ m.to = subscriber
						/\ m.qos = 0
						/\ m.topic = t
						/\ m.packetID = pId + maxPubNum
						/\ canSendTo(subscriber)
						/\ pc[subscriber] = "connected"
						/\ \/ /\ Len(store[subscriber]) > 0  \* 尚未把该消息推送给订阅者
						      /\ \A i \in 1..Len(store[subscriber]) : store[subscriber][i] /= m.packetID
						   \/ /\ Len(store[subscriber]) = 0 
						/\ network' = send(m,subscriber)
						/\ store' = CASE \A q \in {QoS0,QoS1,QoS2} : topic_subscribers[t][q] \ {m.to} = {} -> [store EXCEPT ![broker][t][q1] = Tail(@)] [] OTHER -> store 
	/\ UNCHANGED used_num					
	/\ UNCHANGED pc
	/\ UNCHANGED active
	/\ UNCHANGED topic_subscribers

PushMsgsWithQoS1 ==
	/\ Len(network[broker]) = 0 
  	/\ \E t \in topics :
		\E q1,q2 \in {QoS0,QoS1,QoS2}:
			/\ Len(store[broker][t][q1]) > 0
			/\ topic_subscribers[t][q2] /= {}
			/\ MinQoS(q1,q2) = QoS1
			/\ LET  
				pId == Head(store[broker][t][q1]) 
				subscriber == CHOOSE one \in topic_subscribers[t][q2] : TRUE
			   IN
					/\ subscriber \in active
					/\ pc[subscriber] = "connected"
					/\ \E m \in msgs :
						/\ m.from = broker 
						/\ m.type = PUBLISH
						/\ m.to = subscriber
						/\ m.qos = 1 
						/\ m.topic = t
						/\ m.packetID = pId + maxPubNum
						/\ canSendTo(subscriber)
						/\ \/ /\ Len(store[subscriber]) > 0  \* 尚未把该消息推送给订阅者
						      /\ \A i \in 1..Len(store[subscriber]) : store[subscriber][i] /= m.packetID
						   \/ /\ Len(store[subscriber]) = 0 
						/\ network' = send(m,m.to)
	/\ UNCHANGED store
	/\ UNCHANGED used_num					
	/\ UNCHANGED pc
	/\ UNCHANGED active
	/\ UNCHANGED topic_subscribers

PushMsgsWithQoS2 ==
	/\ Len(network[broker]) = 0 
  	/\ \E t \in topics :
		\E q1,q2 \in {QoS0,QoS1,QoS2}:
			/\ Len(store[broker][t][q1]) > 0
			/\ topic_subscribers[t][q2] /= {}
			/\ MinQoS(q1,q2) = QoS2
			/\ LET  
				pId == Head(store[broker][t][q1]) 
				subscriber == CHOOSE one \in topic_subscribers[t][q2] : TRUE
			   IN
					/\ subscriber \in active
					/\ pc[subscriber] = "connected"
					/\ \E m \in msgs :
						/\ m.from = broker 
						/\ m.type = PUBLISH
						/\ m.to = subscriber
						/\ m.qos = 2 
						/\ m.topic = t
						/\ m.packetID = pId + maxPubNum
						/\ canSendTo(subscriber)
						/\ \/ /\ Len(store[subscriber]) > 0  \* 尚未把该消息推送给订阅者
						      /\ \A i \in 1..Len(store[subscriber]) : store[subscriber][i] /= m.packetID
						   \/ /\ Len(store[subscriber]) = 0 
						/\ network' = send(m,m.to)
	/\ UNCHANGED store
	/\ UNCHANGED used_num					
	/\ UNCHANGED pc
	/\ UNCHANGED active
	/\ UNCHANGED topic_subscribers

HandleRes ==
	\/ HandlePushQoS1Res
	\/ HandlePushQoS2Res
	\/ HandlePubCompRes

HandleReq ==
	\/ HandleConnectReq
	\/ HandleSubscribeReq
	\/ HandleUnsubscribeReq
    \/ HandlePingReq
	\/ HandlePublishWithQoS0Req
	\/ HandlePublishWithQoS1Req
	\/ HandlePublishWithQoS2Req
	\/ HandlePubrelReq
	\/ HandleDisConReq

PushMsgtoSubscribers == 
	\/ PushMsgsWithQoS0
	\/ PushMsgsWithQoS1
	\/ PushMsgsWithQoS2

BrokerAction ==
	\/ HandleReq
	\/ HandleRes
	\/ PushMsgtoSubscribers
====