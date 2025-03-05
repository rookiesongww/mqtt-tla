---- MODULE Spec ----
EXTENDS TLC, Broker, Client

Init ==
    /\ pc = [c \in clients |-> "start"]
	/\ active = {}
    /\ network = [a \in agents |-> <<>>]
	/\ topic_subscribers = [t \in topics |-> [qos \in {QoS0,QoS1,QoS2} |-> {}]]
	/\ used_num = {}
    /\ store = 
		[
			a \in agents |-> CASE a \in publishers -> 1..maxPubNum 
			[] a = broker -> [t \in topics |-> [qos \in {QoS0,QoS1,QoS2} |-> <<>>]]
			[] a \in subscribers -> <<>>
		]

Next ==
	\/ PublisherAction
	\/ SubscriberAction
	\/ BrokerAction
    \/ ClientsDone

Liveness == 
    /\ \A p \in publishers : 
        /\ SF_vars(ReqConnect(p))
        /\ SF_vars(ReqPublishWithQoS0(p)\/ ReqPublishWithQoS1(p)\/ ReqPublishWithQoS2(p))
        /\ WF_vars(PublisherDone(p))
    /\ \A s \in subscribers :    
        /\ SF_vars(ReqConnect(s))
        /\ SF_vars(ReqSubscribe(s)) 
        /\ SF_vars(GetMsgWithQoS0(s)\/ GetMsgWithQoS1AndRes(s)\/ GetMsgWithQoS2AndRes(s))
        /\ SF_vars(ReqUnsubscribe(s))
        /\ WF_vars(SubscriberDone(s)) 
    /\ SF_vars(HandleConnectReq)
    /\ SF_vars(HandleSubscribeReq)
    /\ SF_vars(HandleUnsubscribeReq)
    /\ SF_vars(HandlePublishWithQoS0Req)
    /\ SF_vars(HandlePublishWithQoS1Req)
    /\ SF_vars(HandlePublishWithQoS2Req)
    /\ SF_vars(HandlePubrelReq)
    /\ SF_vars(HandlePushQoS1Res)
    /\ SF_vars(HandlePushQoS2Res)
    /\ SF_vars(HandlePubCompRes)
    /\ SF_vars(PushMsgsWithQoS0)
    /\ SF_vars(PushMsgsWithQoS1)
    /\ SF_vars(PushMsgsWithQoS2)
    
Spec == Init /\ [][Next]_vars /\ Liveness      
====