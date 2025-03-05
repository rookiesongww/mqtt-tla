---- MODULE MC_SP2 ----
EXTENDS MCSpec

SP2 == \* 订阅阶段消息的认证性
    []\A s \in subscribers : 
    	/\ \E t \in topics : 
		 	/\ \A q \in {QoS0,QoS1,QoS2} : 
				/\ topic_subscribers[t][q] \cap {s} /= {} => pc[s] /= "start"
====