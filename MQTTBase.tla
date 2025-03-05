---- MODULE MQTTBase ----
EXTENDS TLC, FiniteSets, Sequences, Naturals

CONSTANTS \*控制报文的类型
  	CONNECT,CONACK,PUBLISH,PUBACK,PUBREL,PUBREC,PUBCOMP,SUBSCRIBE,SUBACK,UNSUBSCRIBE,UNSUBACK,PINGREQ,PINGRESP,DISCONNECT,NULL,QoS0,QoS1,QoS2

CONSTANTS 
	publishers,
	subscribers,
	broker,
	topics,
	maxQueueLen,
	maxPubNum

VARIABLES 
  	pc, \* 客户端的状态指针 
  	\* pub2q \* qos2待发布队列
  	store, \* 存储发布消息
  	active, \* 已连接的客户端集合
  	network, \* 消息接收信道
	topic_subscribers, \* 主题订阅者集合
	used_num \*使用过的随机数 一是用来标识发布/订阅消息中的报文ID
	
vars == <<pc, active, network, store, used_num, topic_subscribers>>
agent_vars == <<pc, active, store, used_num, topic_subscribers>>
clients == publishers \cup subscribers  
agents == clients \cup {broker}
maxSubNum == Cardinality(topics)

PUBLISHERS == Permutations(publishers)
SUBSCRIBERS == Permutations(subscribers)
CLIENTS == PUBLISHERS \cup SUBSCRIBERS

msgs ==         
	[from : clients, to : {broker}, type : {CONNECT},  payload : [clientId : clients] ]
	\cup [from : clients, to : {broker}, type : {PINGREQ} ]
	\cup [from : {broker}, to : clients, type : {CONACK,PINGRESP}, qos : {NULL}, topics : {NULL}, packedID : {NULL},  payload : {NULL} ] 
    \cup [from : publishers, to : {broker}, type : {PUBLISH}, qos : {0,1,2}, topic : topics, packetID : 1..maxPubNum, payload : {NULL}]
	\cup [from : publishers, to : {broker}, type : {PUBREL}, packetID : 1..maxPubNum] 
	\cup [from : subscribers, to : {broker}, type : {UNSUBSCRIBE}, topic : topics] 
	\cup [from : subscribers, to : {broker}, type : {SUBSCRIBE}, qos : {0,1,2}, topic : topics, packetID : 1..maxSubNum]  
	\cup [from : {broker}, to : publishers,  type : {PUBACK,PUBREC,PUBCOMP}, packetID : 1..maxPubNum] 
    \cup [from : {broker}, to : subscribers, type : {SUBACK}, qos : {0,1,2}, topic : topics, packetID : 1..maxSubNum] 
    \cup [from : {broker}, to : subscribers, type : {UNSUBACK}, topic : topics]
    \cup [from : {broker}, to : subscribers, type : {PUBLISH}, qos : {0,1,2}, topic : topics, packetID : maxPubNum+1..maxPubNum*2]
	\cup [from : {broker}, to : subscribers, type : {PUBREL}, packetID : maxPubNum+1..maxPubNum*2] 
	\cup [from : subscribers, to : {broker}, type : {PUBACK,PUBREC,PUBCOMP}, packetID : maxPubNum+1..maxPubNum*2] 
	\cup [from : clients, to : {broker}, type : {DISCONNECT}] 

canSendTo(chan) == Len(network[chan]) < maxQueueLen

send(msg,chan) == [network EXCEPT ![chan] = Append(@, msg)]
	
rcv(msg,chan) == [network EXCEPT ![chan] = Tail(@)]

response(msg,from,to) == [network EXCEPT ![to] = Append(@, msg),![from] = Tail(@)]

====