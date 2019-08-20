---------------------- MODULE UnidrectionalPayment ----------------------
(***************************************************************************)
(* This module specifies a unidrectional payment channel, where a user     *)
(* can deposit money, and then send this money in increments to a receiver.*)
(* The value sent to the receiver can _only_ increase!  *)
(***************************************************************************)

EXTENDS Integers, FiniteSets

(***************************************************************************)
(* The deposit is the size that has been locked up on-chain                *)
(***************************************************************************)
CONSTANTS Deposit


(* --algorithm channel
variables curr_value_to_receiver = 0, curr_nonce_to_receiver = 0, curr_value_to_chain = 0, curr_nonce_to_chain = 0;

begin
    Exec:
        while curr_value_to_receiver < Deposit /\ curr_nonce_to_chain = 0 do
          either
            Transfer:
              with value \in 1..Deposit, nonce \in 1..Deposit do
                (* receiver only accepts if nonce and value are incremented *)
                if curr_nonce_to_receiver < nonce /\ curr_value_to_receiver < value then
                    curr_value_to_receiver := value;
                    curr_nonce_to_receiver := nonce;
                end if;
              end with;
          or
            Settle:
                (* The sender only tries to steal (they don't give money away)
                 and so they only show messages with a value not greater than what
                 they've actually sent *)
              if curr_value_to_receiver > 0 then
                  with value \in 1..curr_value_to_receiver, nonce \in 1..Deposit do
                    if curr_nonce_to_chain < nonce then
                        curr_value_to_chain := value;
                        curr_nonce_to_chain := nonce;
                    end if;
                  end with;
              end if;
          end either;
        end while;
    (* If the channel ever settles, or all money has been transfered, we have 
    the receiver try and settle with the highest nonce (and thus value) that
    they have, unless the value transfered to them onchain is higher *) 
    FinalSettle:
        if curr_nonce_to_chain < curr_nonce_to_receiver /\ curr_value_to_chain < curr_value_to_receiver then
            curr_value_to_chain := curr_value_to_receiver;
            curr_nonce_to_chain := curr_nonce_to_receiver;
        end if;
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES curr_value_to_receiver, curr_nonce_to_receiver, curr_value_to_chain, 
          curr_nonce_to_chain, pc

vars == << curr_value_to_receiver, curr_nonce_to_receiver, 
           curr_value_to_chain, curr_nonce_to_chain, pc >>

Init == (* Global variables *)
        /\ curr_value_to_receiver = 0
        /\ curr_nonce_to_receiver = 0
        /\ curr_value_to_chain = 0
        /\ curr_nonce_to_chain = 0
        /\ pc = "Exec"

Exec == /\ pc = "Exec"
        /\ IF curr_value_to_receiver < Deposit /\ curr_nonce_to_chain = 0
              THEN /\ \/ /\ pc' = "Transfer"
                      \/ /\ pc' = "Settle"
              ELSE /\ pc' = "FinalSettle"
        /\ UNCHANGED << curr_value_to_receiver, curr_nonce_to_receiver, 
                        curr_value_to_chain, curr_nonce_to_chain >>

Transfer == /\ pc = "Transfer"
            /\ \E value \in 1..Deposit:
                 \E nonce \in 1..Deposit:
                   IF curr_nonce_to_receiver < nonce /\ curr_value_to_receiver < value
                      THEN /\ curr_value_to_receiver' = value
                           /\ curr_nonce_to_receiver' = nonce
                      ELSE /\ TRUE
                           /\ UNCHANGED << curr_value_to_receiver, 
                                           curr_nonce_to_receiver >>
            /\ pc' = "Exec"
            /\ UNCHANGED << curr_value_to_chain, curr_nonce_to_chain >>

Settle == /\ pc = "Settle"
          /\ IF curr_value_to_receiver > 0
                THEN /\ \E value \in 1..curr_value_to_receiver:
                          \E nonce \in 1..Deposit:
                            IF curr_nonce_to_chain < nonce
                               THEN /\ curr_value_to_chain' = value
                                    /\ curr_nonce_to_chain' = nonce
                               ELSE /\ TRUE
                                    /\ UNCHANGED << curr_value_to_chain, 
                                                    curr_nonce_to_chain >>
                ELSE /\ TRUE
                     /\ UNCHANGED << curr_value_to_chain, curr_nonce_to_chain >>
          /\ pc' = "Exec"
          /\ UNCHANGED << curr_value_to_receiver, curr_nonce_to_receiver >>

FinalSettle == /\ pc = "FinalSettle"
               /\ IF curr_nonce_to_chain < curr_nonce_to_receiver /\ curr_value_to_chain < curr_value_to_receiver
                     THEN /\ curr_value_to_chain' = curr_value_to_receiver
                          /\ curr_nonce_to_chain' = curr_nonce_to_receiver
                     ELSE /\ TRUE
                          /\ UNCHANGED << curr_value_to_chain, 
                                          curr_nonce_to_chain >>
               /\ pc' = "Done"
               /\ UNCHANGED << curr_value_to_receiver, curr_nonce_to_receiver >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Exec \/ Transfer \/ Settle \/ FinalSettle
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

(* note as the receiver can only get as much money as is sent by the sender
this also says that the receiver loses the money they have sent, which is fair *)
ReceiverGetsMoney == <>(curr_value_to_chain = curr_value_to_receiver)

                 
=============================================================================
\* Modification History
\* Last modified Mon Aug 19 20:39:44 EDT 2019 by nate
\* Last modified Sat Dec 22 14:17:18 PST 2018 by lamport
\* Created Thu Dec 20 11:44:08 PST 2018 by lamport
