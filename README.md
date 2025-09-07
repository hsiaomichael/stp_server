ack as SCTP server able support M3UA , SCCP , TCAP  , MAP as STP simulator
1. Send MO-FSM to SMSC
2. SRI-SM request received from SMSC , send SRI-SM response with configuration NNN and GT
3. Recv MT-FSM request from SMSC
4. Response MT-FSM response back to SMSC
5. Submit MO-FSM to SMSC
6. Support both Short and Long message (send TCAP begin before segments message)
7. Support both GSM7 and UCS2
8. Submit MT-FSM to SMSC (Ack as FSG , Send SRI-SM to SMSC , once SRI-SM response send MT-FSM to SMSC)
