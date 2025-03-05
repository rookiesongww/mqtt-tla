---- MODULE Client ----
EXTENDS MQTTBase


ReqConnect(self) ==
	/\ pc[self] = "start"
	/\ \E m \in msgs : 
	    /\ m.from = self 
	    /\ m.to = broker 
		/\ m.type = CONNECT 
		/\ m.payload.clientId = self
		/\ canSendTo(broker)
  	    /\ network' = send(m,broker) 
	    /\ pc' = [pc EXCEPT ![self] = "connecting"]
	/\ UNCHANGED active
	/\ UNCHANGED topic_subscribers
    /\ UNCHANGED store
	/\ UNCHANGED used_num

RcvConnectRes(self) ==
	/\ pc[self] = "connecting"
	/\ Len(network[self]) > 0
	/\ LET m == Head(network[self]) IN  
		/\ m.from = broker 
		/\ m.to = self 
		/\ m.type = CONACK
		/\ network' = rcv(m,self) 
		/\ pc' = [pc EXCEPT ![self] = "connected"]
	/\ UNCHANGED active
	/\ UNCHANGED topic_subscribers
    /\ UNCHANGED store
	/\ UNCHANGED used_num

ReqPing(self) ==
	/\ pc[self] = "connected"
	/\ \E m \in msgs : 
		/\ m.from = self 
		/\ m.to = broker 
		/\ m.type = PINGREQ
		/\ canSendTo(broker)
  	 	/\ network' = send(m,broker) 
		/\ pc' = [pc EXCEPT ![self] = "ping"]
	/\ UNCHANGED active
	/\ UNCHANGED topic_subscribers
  	/\ UNCHANGED store
	/\ UNCHANGED used_num

RcvPingRes(self) ==
	/\ pc[self] = "ping"
	/\ Len(network[self]) > 0
	/\ LET m == Head(network[self]) IN  
		/\ m.from = broker 
		/\ m.to = self 
		/\ m.type = PINGRESP
  	 	/\ network' = rcv(m,self) 
		/\ pc' = [pc EXCEPT ![self] = "connected"]
	/\ UNCHANGED active
	/\ UNCHANGED topic_subscribers
    /\ UNCHANGED store
	/\ UNCHANGED used_num


ReqPublishWithQoS0(self) ==
  	/\ pc[self] = "connected"
	/\ store[self] /= {}
	/\ \E m \in msgs :
		/\ m.from = self 
		/\ m.to = broker 
	    /\ m.type = PUBLISH
		/\ m.qos = 0
		/\ m.packetID \notin used_num
		/\ canSendTo(broker)
  	    /\ network' = send(m,broker)
		/\ store' = [store EXCEPT ![self] = @ \ {m.packetID}]
		/\ used_num' = used_num \cup {m.packetID}  
	/\ UNCHANGED pc
	/\ UNCHANGED active
	/\ UNCHANGED topic_subscribers

ReqPublishWithQoS1(self) ==
  	/\ pc[self] = "connected"
	/\ store[self] /= {}
	/\ \E m \in msgs :
		/\ m.from = self 
		/\ m.to = broker 
	    /\ m.type = PUBLISH
		/\ m.qos = 1
		/\ m.packetID \notin used_num
		/\ canSendTo(broker)
  	    /\ network' = send(m,broker)
		/\ used_num' = used_num \cup {m.packetID}
    /\ pc' =  [pc EXCEPT ![self] = "publishingwithqos1"]
	/\ UNCHANGED active
    /\ UNCHANGED store
	/\ UNCHANGED topic_subscribers

RcvPublishWithQoS1Res(self) ==
	/\ pc[self] = "publishingwithqos1"
	/\ Len(network[self]) > 0
	/\ LET m == Head(network[self]) IN  
		/\ m.from = broker 
		/\ m.to = self 
		/\ m.type = PUBACK
  	 	/\ network' = rcv(m,self)
		/\ store' = [store EXCEPT ![self] = @ \ {m.packetID}] 
	/\ pc' = [pc EXCEPT ![self] = "connected"]
	/\ UNCHANGED active
	/\ UNCHANGED topic_subscribers
	/\ UNCHANGED used_num

ReqPublishWithQoS2(self) ==
    /\ pc[self] = "connected"
    /\ store[self] /= {}
    /\ \E m \in msgs :
        /\ m.from = self 
        /\ m.to = broker 
        /\ m.type = PUBLISH
        /\ m.qos = 2
        /\ m.packetID \notin used_num
        /\ canSendTo(broker)
        /\ network' = send(m,broker)
        /\ used_num' = used_num \cup {m.packetID}
    /\ pc' =  [pc EXCEPT ![self] = "publishingwithqos2"]
    /\ UNCHANGED active
    /\ UNCHANGED store
    /\ UNCHANGED topic_subscribers

RcvPubrecAndResPubrel(self) ==
    /\ pc[self] = "publishingwithqos2"
    /\ Len(network[self]) > 0
    /\ LET m == Head(network[self]) IN  
        /\ m.from = broker 
        /\ m.to = self 
        /\ m.type = PUBREC
        /\ \E rmsg \in msgs :
            /\ rmsg.type = PUBREL
            /\ rmsg.from = self
            /\ rmsg.to = broker
            /\ rmsg.packetID = m.packetID
            /\ canSendTo(broker)
            /\ network' = response(rmsg,rmsg.from,rmsg.to)
    /\ pc' = [pc EXCEPT ![self] = "waitingpubcomp"]
    /\ UNCHANGED active
    /\ UNCHANGED store
    /\ UNCHANGED topic_subscribers
    /\ UNCHANGED used_num

RcvPubComp(self) ==
    /\ pc[self] = "waitingpubcomp"
    /\ Len(network[self]) > 0
    /\ LET m == Head(network[self]) IN  
        /\ m.from = broker 
        /\ m.to = self 
        /\ m.type = PUBCOMP
        /\ network' = rcv(m,self)
        /\ store' = [store EXCEPT ![self] = @ \ {m.packetID}] 
    /\ pc' = [pc EXCEPT ![self] = "connected"]
    /\ UNCHANGED active
    /\ UNCHANGED topic_subscribers
    /\ UNCHANGED used_num



ReqSubscribe(self) ==
	/\ pc[self] = "connected"
	/\ \E m \in msgs :
		 /\ \E t \in topics : 
		 	/\ \A q \in {QoS0,QoS1,QoS2} : 
				/\ topic_subscribers[t][q] \cap {self} = {}		 
				/\ m.from = self 
				/\ m.to = broker
				/\ m.type = SUBSCRIBE
				/\ m.topic = t 
				/\ canSendTo(broker) 
				/\ network' = send(m,broker) 
	/\ pc' = [pc EXCEPT ![self] = "subscribing"]
	/\ UNCHANGED active
	/\ UNCHANGED topic_subscribers
  	/\ UNCHANGED store
	/\ UNCHANGED used_num

RcvSubscribeRes(self) ==
	/\ pc[self] = "subscribing"
	/\ Len(network[self]) > 0
	/\ LET m == Head(network[self]) IN  
		/\ m.from = broker 
		/\ m.to = self 
		/\ m.type = SUBACK
  	 	/\ network' = rcv(m,self) 
		/\ pc' = [pc EXCEPT ![self] = "connected"]
	/\ UNCHANGED active
	/\ UNCHANGED topic_subscribers
  	/\ UNCHANGED store
	/\ UNCHANGED used_num

ReqUnsubscribe(self) ==
	/\ pc[self] = "connected"
	/\ Len(network[self]) = 0 
	/\ \E m \in msgs : 
		 /\ \E t \in topics : 
		 	\E q \in {QoS0,QoS1,QoS2} :
				/\ topic_subscribers[t][q] \cap {self} /= {}		 		 
				/\ m.from = self 
				/\ m.to = broker 
				/\ m.type = UNSUBSCRIBE
				/\ m.topic = t
				/\ canSendTo(broker)
				/\ network' = send(m,broker) 
	/\ pc' = [pc EXCEPT ![self] = "unsubscribing"]
	/\ UNCHANGED active
	/\ UNCHANGED topic_subscribers
  	/\ UNCHANGED store 
	/\ UNCHANGED used_num

RcvUnsubscribeRes(self) ==
	/\ pc[self] = "unsubscribing"
	/\ Len(network[self]) > 0
	/\ LET m == Head(network[self]) IN  
		/\ m.from = broker 
		/\ m.to = self 
		/\ m.type = UNSUBACK
  		/\ network' = rcv(m,self) 
		/\ pc' = [pc EXCEPT ![self] = "connected"]
	/\ UNCHANGED active
	/\ UNCHANGED topic_subscribers
  	/\ UNCHANGED store
	/\ UNCHANGED used_num

GetMsgWithQoS0(self) == 
	/\ pc[self] = "connected"
	/\ Len(network[self]) > 0
	/\ LET msg == Head(network[self]) IN
		/\ msg.type = PUBLISH 
		/\ msg.qos = 0 
		/\ network' = rcv(msg,self)
		/\ 	\/ Len(store[self]) = 0
			\/	/\ Len(store[self]) > 0
				/\ \E i \in 1..Len(store[self]) : store[self][i] /= msg.packetID 
		/\ store' = [store EXCEPT ![self] = Append(@,msg.packetID)]
	/\ UNCHANGED pc
    /\ UNCHANGED active 
    /\ UNCHANGED topic_subscribers
	/\ UNCHANGED used_num

GetMsgWithQoS1AndRes(self) ==
	/\ pc[self] = "connected" 
	/\ Len(network[self]) > 0
	/\ LET msg == Head(network[self]) IN
		/\ msg.to = self 
		/\ msg.type = PUBLISH
		/\ msg.qos = 1
		/\ \E m \in msgs :
			/\ m.type = PUBACK
			/\ m.from = msg.to 
			/\ m.to = msg.from
			/\ m.packetID = msg.packetID
			/\ 	\/ Len(store[self]) = 0
				\/	/\ Len(store[self]) > 0
					/\ \E i \in 1..Len(store[self]) : store[self][i] /= msg.packetID 
			/\ network' = response(m,m.from,m.to)
            /\ store' = [store EXCEPT ![self] = Append(@, msg.packetID)]
	/\ UNCHANGED pc
    /\ UNCHANGED active 
    /\ UNCHANGED topic_subscribers
	/\ UNCHANGED used_num

GetMsgWithQoS2AndRes(self) ==
	/\ pc[self] = "connected" 
	/\ Len(network[self]) > 0
	/\ LET msg == Head(network[self]) IN
		/\ msg.to = self 
		/\ msg.type = PUBLISH
		/\ msg.qos = 2
		/\ \E m \in msgs :
			/\ m.type = PUBREC
			/\ m.from = msg.to 
			/\ m.to = msg.from
			/\ m.packetID = msg.packetID
			/\ 	\/ Len(store[self]) = 0
				\/	/\ Len(store[self]) > 0
					/\ \E i \in 1..Len(store[self]) : store[self][i] /= msg.packetID 
			/\ network' = response(m,m.from,m.to)
            /\ store' = [store EXCEPT ![self] = Append(@, msg.packetID)]
			/\ pc' = [pc EXCEPT ![self] = "waittingpubrel"]
    /\ UNCHANGED active 
    /\ UNCHANGED topic_subscribers
	/\ UNCHANGED used_num

GetMsgWithQoS2PubRelAndRes(self) ==
	/\ pc[self] = "waittingpubrel" 
	/\ Len(network[self]) > 0
	/\ LET msg == Head(network[self]) IN
		/\ msg.to = self 
		/\ msg.type = PUBREL
		/\ \E m \in msgs :
			/\ m.type = PUBCOMP
			/\ m.from = msg.to 
			/\ m.to = msg.from
			/\ m.packetID = msg.packetID
			/\ network' = response(m,m.from,m.to)
			/\ pc' = [pc EXCEPT ![self] = "connected"]
	/\ UNCHANGED store
    /\ UNCHANGED active 
    /\ UNCHANGED topic_subscribers
	/\ UNCHANGED used_num

PublisherDone(self) ==
    /\ pc[self] = "connected"
    /\ Len(network[self]) = 0
    /\ Cardinality(used_num) = maxPubNum
	/\ \E m \in msgs :
		/\ m.from = self
		/\ m.type = DISCONNECT  
		/\ m.to = broker
		/\ canSendTo(broker)
		/\ network' = send(m,m.to)
    /\ pc' = [pc EXCEPT ![self] = "closed"]
	/\ UNCHANGED store
    /\ UNCHANGED active 
    /\ UNCHANGED topic_subscribers
	/\ UNCHANGED used_num

SubscriberDone(self) ==
    /\ pc[self] = "connected"
    /\ Len(network[self]) = 0
	/\ \E m \in msgs :
		/\ m.from = self
		/\ m.type = DISCONNECT  
		/\ m.to = broker
		/\ canSendTo(broker)
		/\ network' = send(m,m.to)
    /\ pc' = [pc EXCEPT ![self] = "closed"]
	/\ UNCHANGED store
    /\ UNCHANGED active 
    /\ UNCHANGED topic_subscribers
	/\ UNCHANGED used_num

SubscriberAction ==
	\E self \in subscribers :
		\/ ReqConnect(self)
		\/ RcvConnectRes(self)
		\/ ReqSubscribe(self)
		\/ RcvSubscribeRes(self)
		\/ ReqUnsubscribe(self)
		\/ RcvUnsubscribeRes(self)
		\/ GetMsgWithQoS0(self)
		\/ GetMsgWithQoS1AndRes(self)
		\/ GetMsgWithQoS2AndRes(self)
		\/ GetMsgWithQoS2PubRelAndRes(self)
        \/ SubscriberDone(self) 

PublisherAction ==
	\E self \in publishers :
		\/ ReqConnect(self)
		\/ RcvConnectRes(self)
		\/ ReqPublishWithQoS0(self)
		\/ ReqPublishWithQoS1(self)
		\/ RcvPublishWithQoS1Res(self)
		\/ ReqPublishWithQoS2(self)
		\/ RcvPubrecAndResPubrel(self)
		\/ RcvPubComp(self)
        \/ PublisherDone(self)

ClientsDone == \* whenall clients disconnneted
    /\ \A c \in clients : 
        /\ pc[c] = "closed" 
        /\ Len(network[c]) = 0 
    /\ UNCHANGED vars
====