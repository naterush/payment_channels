---------------------- MODULE UnidrectionalPayment ----------------------
(***************************************************************************)
(* This module specifies a unidrectional payment channel, where a user     *)
(* can deposit money, and then send this money in increments to a receiver.*)
(* The value sent to the receiver can _only_ increase, and as such this    *)
(* this channel only requires signatures from the sender!                  *)
(***************************************************************************)

EXTENDS Integers

(***************************************************************************)
(* The deposit is the size that has been locked up on-chain                *)
(***************************************************************************)
CONSTANTS Deposit, Timeout


(* --algorithm channel
variables curr_value_to_receiver = 0, curr_nonce_to_receiver = 0, curr_value_to_chain = 0, curr_nonce_to_chain = 0, 
    time_to_close = FALSE, sender_steal = FALSE;

define
    UpdatesSmartContract(nonce) == nonce > curr_nonce_to_chain
end define;

begin
    (* This is the off-chain execution of the channel, where the sender signs messages *)
    (* and sends them to the receiver, or stops sending them. *)
    Offchain:
        while curr_value_to_receiver < Deposit /\ ~time_to_close do
            either
                Transfer:
                    (* The sender in the channel continues to send messages*)
                    with value \in 1..Deposit, nonce \in 1..Deposit do
                        (* Only accept payments if the nonce and value are incremented *)
                        if curr_nonce_to_receiver < nonce /\ curr_value_to_receiver < value then
                            curr_value_to_receiver := value;
                            curr_nonce_to_receiver := nonce;
                        end if;
                    end with;
            or
                DecideToClose:
                    (* The sender in the channel stops sending messages, or the receiver wants to settle *)
                    time_to_close := TRUE
            end either;
        end while;
    (* This is the on-chain execution, which we model as happening after all off-chain interaction*)
    (* In practice, parties can stop interacting after they see action on chain. *)
    Onchain:
        either
            SenderFirst:
                (* Sender lies to the smart contract first, and enters lockup period*)
                if curr_value_to_receiver > 0 then
                    (* They try and say they paid less than they actually did *)
                    (* so they won't sign a message with a value greater than what they sent *)
                    with value \in 1..curr_value_to_receiver, nonce \in 1..Deposit do
                        if UpdatesSmartContract(nonce) then
                            curr_value_to_chain := value;
                            curr_nonce_to_chain := nonce;
                        end if;
                    end with;
                end if;
                
                (* And now during the timeout the receiver comes along and challenges *)
                if UpdatesSmartContract(curr_nonce_to_receiver) then
                    Close:
                        curr_value_to_chain := curr_value_to_receiver;
                        curr_nonce_to_chain := curr_nonce_to_receiver;
                end if;
           
        or
            ReceiverFirst:
                (* The receiver comes along and closes the channel first, entering timeout *)
                if UpdatesSmartContract(curr_nonce_to_receiver) then
                    curr_value_to_chain := curr_value_to_receiver;
                    curr_nonce_to_chain := curr_nonce_to_receiver;
                end if;
                
                (* The sender now has a chance to try and steal money *)
                if curr_value_to_receiver > 0 then
                    Challenge:
                        (* Again, they don't send more than they actually paid *)
                        with value \in 1..curr_value_to_receiver, nonce \in 1..Deposit do
                            if UpdatesSmartContract(nonce) then
                                curr_value_to_chain := value;
                                curr_nonce_to_chain := nonce;
                            end if;
                        end with;
                end if;
        end either;
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES curr_value_to_receiver, curr_nonce_to_receiver, curr_value_to_chain, 
          curr_nonce_to_chain, time_to_close, sender_steal, pc

(* define statement *)
UpdatesSmartContract(nonce) == nonce > curr_nonce_to_chain


vars == << curr_value_to_receiver, curr_nonce_to_receiver, 
           curr_value_to_chain, curr_nonce_to_chain, time_to_close, 
           sender_steal, pc >>

Init == (* Global variables *)
        /\ curr_value_to_receiver = 0
        /\ curr_nonce_to_receiver = 0
        /\ curr_value_to_chain = 0
        /\ curr_nonce_to_chain = 0
        /\ time_to_close = FALSE
        /\ sender_steal = FALSE
        /\ pc = "Offchain"

Offchain == /\ pc = "Offchain"
            /\ IF curr_value_to_receiver < Deposit /\ ~time_to_close
                  THEN /\ \/ /\ pc' = "Transfer"
                          \/ /\ pc' = "DecideToClose"
                  ELSE /\ pc' = "Onchain"
            /\ UNCHANGED << curr_value_to_receiver, curr_nonce_to_receiver, 
                            curr_value_to_chain, curr_nonce_to_chain, 
                            time_to_close, sender_steal >>

Transfer == /\ pc = "Transfer"
            /\ \E value \in 1..Deposit:
                 \E nonce \in 1..Deposit:
                   IF curr_nonce_to_receiver < nonce /\ curr_value_to_receiver < value
                      THEN /\ curr_value_to_receiver' = value
                           /\ curr_nonce_to_receiver' = nonce
                      ELSE /\ TRUE
                           /\ UNCHANGED << curr_value_to_receiver, 
                                           curr_nonce_to_receiver >>
            /\ pc' = "Offchain"
            /\ UNCHANGED << curr_value_to_chain, curr_nonce_to_chain, 
                            time_to_close, sender_steal >>

DecideToClose == /\ pc = "DecideToClose"
                 /\ time_to_close' = TRUE
                 /\ pc' = "Offchain"
                 /\ UNCHANGED << curr_value_to_receiver, 
                                 curr_nonce_to_receiver, curr_value_to_chain, 
                                 curr_nonce_to_chain, sender_steal >>

Onchain == /\ pc = "Onchain"
           /\ \/ /\ pc' = "SenderFirst"
              \/ /\ pc' = "ReceiverFirst"
           /\ UNCHANGED << curr_value_to_receiver, curr_nonce_to_receiver, 
                           curr_value_to_chain, curr_nonce_to_chain, 
                           time_to_close, sender_steal >>

SenderFirst == /\ pc = "SenderFirst"
               /\ IF curr_value_to_receiver > 0
                     THEN /\ \E value \in 1..curr_value_to_receiver:
                               \E nonce \in 1..Deposit:
                                 IF UpdatesSmartContract(nonce)
                                    THEN /\ curr_value_to_chain' = value
                                         /\ curr_nonce_to_chain' = nonce
                                    ELSE /\ TRUE
                                         /\ UNCHANGED << curr_value_to_chain, 
                                                         curr_nonce_to_chain >>
                     ELSE /\ TRUE
                          /\ UNCHANGED << curr_value_to_chain, 
                                          curr_nonce_to_chain >>
               /\ IF UpdatesSmartContract(curr_nonce_to_receiver)
                     THEN /\ pc' = "Close"
                     ELSE /\ pc' = "Done"
               /\ UNCHANGED << curr_value_to_receiver, curr_nonce_to_receiver, 
                               time_to_close, sender_steal >>

Close == /\ pc = "Close"
         /\ curr_value_to_chain' = curr_value_to_receiver
         /\ curr_nonce_to_chain' = curr_nonce_to_receiver
         /\ pc' = "Done"
         /\ UNCHANGED << curr_value_to_receiver, curr_nonce_to_receiver, 
                         time_to_close, sender_steal >>

ReceiverFirst == /\ pc = "ReceiverFirst"
                 /\ IF UpdatesSmartContract(curr_nonce_to_receiver)
                       THEN /\ curr_value_to_chain' = curr_value_to_receiver
                            /\ curr_nonce_to_chain' = curr_nonce_to_receiver
                       ELSE /\ TRUE
                            /\ UNCHANGED << curr_value_to_chain, 
                                            curr_nonce_to_chain >>
                 /\ IF curr_value_to_receiver > 0
                       THEN /\ pc' = "Challenge"
                       ELSE /\ pc' = "Done"
                 /\ UNCHANGED << curr_value_to_receiver, 
                                 curr_nonce_to_receiver, time_to_close, 
                                 sender_steal >>

Challenge == /\ pc = "Challenge"
             /\ \E value \in 1..curr_value_to_receiver:
                  \E nonce \in 1..Deposit:
                    IF UpdatesSmartContract(nonce)
                       THEN /\ curr_value_to_chain' = value
                            /\ curr_nonce_to_chain' = nonce
                       ELSE /\ TRUE
                            /\ UNCHANGED << curr_value_to_chain, 
                                            curr_nonce_to_chain >>
             /\ pc' = "Done"
             /\ UNCHANGED << curr_value_to_receiver, curr_nonce_to_receiver, 
                             time_to_close, sender_steal >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Offchain \/ Transfer \/ DecideToClose \/ Onchain \/ SenderFirst
           \/ Close \/ ReceiverFirst \/ Challenge
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

(* note as the receiver can only get as much money as is sent by the sender
this also says that the receiver loses the money they have sent, which is fair *)
ReceiverGetsMoney == <>(curr_value_to_chain = curr_value_to_receiver)

                 
=============================================================================
\* Modification History
\* Last modified Tue Aug 20 09:23:34 EDT 2019 by nate
\* Last modified Sat Dec 22 14:17:18 PST 2018 by lamport
\* Created Thu Dec 20 11:44:08 PST 2018 by lamport
