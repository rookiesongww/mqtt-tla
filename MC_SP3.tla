---- MODULE MC_SP3 ----
EXTENDS MCSpec

SP3 == \* 发布阶段消息的秘密性
    [] (\A num \in used_num : knows.msgID \cap {num} = {}) 
====