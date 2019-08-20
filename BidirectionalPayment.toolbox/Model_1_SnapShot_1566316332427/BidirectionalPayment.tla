---------------------- MODULE BidirectionalPayment ----------------------
(***************************************************************************)
(* This module specifies a non-dual funded, bidirectional payment channel. *)
(***************************************************************************)

EXTENDS Integers

(***************************************************************************)
(* The deposit is the size that has been locked up on-chain                *)
(* The timeout is the number of blocks the channel waits for a challenge.  *)
(* The MaxSendsAndReceives is the number of message passing events offchain*)
(***************************************************************************)
CONSTANTS Deposit, Timeout, MaxSendsAndReceives


(* --algorithm bidirectional_channel
variables message = [i \in 1..MaxSendsAndReceives |-> <<0, 0>>], 
    max_signed_by_sender = 1, max_signed_by_receiver = 1,
    max_seen_signed_by_sender = 1, max_seen_signed_by_receiver = 1, (* seen as having been signed by both*)
    num_sends_and_receives = 0, exit_cancelled = FALSE, curr_time = 0,
    curr_value_to_chain = 0, curr_nonce_to_chain = 0;

define
    UpdatesSmartContract(nonce) == nonce > curr_nonce_to_chain
end define;

begin
    (*
        Offchain execution is message passing between the sender and the receiver, where in each round
        the sender may sign + send a message, or the receiver may receive + sign a message, or the sender
        may get back a message they have already signed with the other signature on it. 
    *)
    Offchain:
        while num_sends_and_receives < MaxSendsAndReceives do
            either
                (* The sender signs a new message with and floats it towards the receiver *)
                SenderSignSend:
                    (* Since the receiver will only accept in-order nonces, only signs in-order nonces *)
                    with value \in 0..Deposit do
                        message[max_signed_by_sender + 1] := <<value, max_signed_by_sender>>;
                    end with;
                    max_signed_by_sender := max_signed_by_sender + 1;
                    
            or
                (* The receiver gets one new message from sender, signs it also, and floats back towards the sender *)
                ReceiverReceiveSignSend:
                    max_signed_by_receiver :=  max_signed_by_receiver + 1;
                    max_seen_signed_by_receiver := max_seen_signed_by_receiver + 1;
            or
                (* The sender receives the message from the receiver that is now signed by both *)
                SenderReceive:
                    max_seen_signed_by_sender := max_seen_signed_by_sender + 1;
            
            end either;
            Update:
                num_sends_and_receives := num_sends_and_receives + 1;
        end while;
    
    (*
        Now, we enter the on-chain portion. We attack the smart contract in all possible ways:
        each user settles the chain with any message that gives them more money. The sender wants
        to minimize the value posted to the chain, and the receiver wants to maximize the value
        posted to the chain. After the users try and settle with a message, the other user has
        a chance to respond with a later message signed by both validators to cancel their exit;
        they cannot cancel the highest signed message, and thus it should not be canceled only in this case
    *)
    Onchain:   
        either
            (* No one tries to steal, and the receiver posts the most recent state *)
            if UpdatesSmartContract(message[max_seen_signed_by_receiver][2]) then
                curr_value_to_chain := message[max_seen_signed_by_receiver][1];
                curr_nonce_to_chain := message[max_seen_signed_by_receiver][2];
            end if;
        or
            (* We have the sender try and steal in this case *)
            with msg_idx \in 1..max_seen_signed_by_sender do
                if message[msg_idx][1] =< message[max_seen_signed_by_sender][1] then
                    if UpdatesSmartContract(message[msg_idx][2]) then
                        curr_value_to_chain := message[msg_idx][1];
                        curr_nonce_to_chain := message[msg_idx][2];
                    end if;
                end if;
            end with;            
        or
            (* Here, the receiver tries to steal *)
            with msg_idx \in 1..max_seen_signed_by_receiver do
                if message[msg_idx][1] >= message[max_seen_signed_by_receiver][1] then
                    if UpdatesSmartContract(message[msg_idx][2]) then
                        curr_value_to_chain := message[msg_idx][1];
                        curr_nonce_to_chain := message[msg_idx][2];
                    end if;
                end if;
            end with;
        end either;
        
        (*
            Now, both parties have the ability to challenge, if they so desire. We
            model a challenge as canceling the above exit (if it is invalid)
        *)
        
        (* Challenge from receiver *)
        ChallengeFromReceiver:
            if curr_value_to_chain <= message[max_seen_signed_by_receiver][1] then
                if UpdatesSmartContract(message[max_seen_signed_by_receiver][2]) then
                    exit_cancelled := TRUE;
                end if;
            end if;
        
        (* Challenge from sender *)
        ChallengeFromSender:
            if curr_value_to_chain >= message[max_seen_signed_by_sender][1] then
                if UpdatesSmartContract(message[max_seen_signed_by_sender][2]) then
                    exit_cancelled := TRUE;
                end if;
            end if;
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES message, max_signed_by_sender, max_signed_by_receiver, 
          max_seen_signed_by_sender, max_seen_signed_by_receiver, 
          num_sends_and_receives, exit_cancelled, curr_time, 
          curr_value_to_chain, curr_nonce_to_chain, pc

(* define statement *)
UpdatesSmartContract(nonce) == nonce > curr_nonce_to_chain


vars == << message, max_signed_by_sender, max_signed_by_receiver, 
           max_seen_signed_by_sender, max_seen_signed_by_receiver, 
           num_sends_and_receives, exit_cancelled, curr_time, 
           curr_value_to_chain, curr_nonce_to_chain, pc >>

Init == (* Global variables *)
        /\ message = [i \in 1..MaxSendsAndReceives |-> <<0, 0>>]
        /\ max_signed_by_sender = 1
        /\ max_signed_by_receiver = 1
        /\ max_seen_signed_by_sender = 1
        /\ max_seen_signed_by_receiver = 1
        /\ num_sends_and_receives = 0
        /\ exit_cancelled = FALSE
        /\ curr_time = 0
        /\ curr_value_to_chain = 0
        /\ curr_nonce_to_chain = 0
        /\ pc = "Offchain"

Offchain == /\ pc = "Offchain"
            /\ IF num_sends_and_receives < MaxSendsAndReceives
                  THEN /\ \/ /\ pc' = "SenderSignSend"
                          \/ /\ pc' = "ReceiverReceiveSignSend"
                          \/ /\ pc' = "SenderReceive"
                  ELSE /\ pc' = "Onchain"
            /\ UNCHANGED << message, max_signed_by_sender, 
                            max_signed_by_receiver, max_seen_signed_by_sender, 
                            max_seen_signed_by_receiver, 
                            num_sends_and_receives, exit_cancelled, curr_time, 
                            curr_value_to_chain, curr_nonce_to_chain >>

Update == /\ pc = "Update"
          /\ num_sends_and_receives' = num_sends_and_receives + 1
          /\ pc' = "Offchain"
          /\ UNCHANGED << message, max_signed_by_sender, 
                          max_signed_by_receiver, max_seen_signed_by_sender, 
                          max_seen_signed_by_receiver, exit_cancelled, 
                          curr_time, curr_value_to_chain, curr_nonce_to_chain >>

SenderSignSend == /\ pc = "SenderSignSend"
                  /\ \E value \in 0..Deposit:
                       message' = [message EXCEPT ![max_signed_by_sender + 1] = <<value, max_signed_by_sender>>]
                  /\ max_signed_by_sender' = max_signed_by_sender + 1
                  /\ pc' = "Update"
                  /\ UNCHANGED << max_signed_by_receiver, 
                                  max_seen_signed_by_sender, 
                                  max_seen_signed_by_receiver, 
                                  num_sends_and_receives, exit_cancelled, 
                                  curr_time, curr_value_to_chain, 
                                  curr_nonce_to_chain >>

ReceiverReceiveSignSend == /\ pc = "ReceiverReceiveSignSend"
                           /\ max_signed_by_receiver' = max_signed_by_receiver + 1
                           /\ max_seen_signed_by_receiver' = max_seen_signed_by_receiver + 1
                           /\ pc' = "Update"
                           /\ UNCHANGED << message, max_signed_by_sender, 
                                           max_seen_signed_by_sender, 
                                           num_sends_and_receives, 
                                           exit_cancelled, curr_time, 
                                           curr_value_to_chain, 
                                           curr_nonce_to_chain >>

SenderReceive == /\ pc = "SenderReceive"
                 /\ max_seen_signed_by_sender' = max_seen_signed_by_sender + 1
                 /\ pc' = "Update"
                 /\ UNCHANGED << message, max_signed_by_sender, 
                                 max_signed_by_receiver, 
                                 max_seen_signed_by_receiver, 
                                 num_sends_and_receives, exit_cancelled, 
                                 curr_time, curr_value_to_chain, 
                                 curr_nonce_to_chain >>

Onchain == /\ pc = "Onchain"
           /\ \/ /\ IF UpdatesSmartContract(message[max_seen_signed_by_receiver][2])
                       THEN /\ curr_value_to_chain' = message[max_seen_signed_by_receiver][1]
                            /\ curr_nonce_to_chain' = message[max_seen_signed_by_receiver][2]
                       ELSE /\ TRUE
                            /\ UNCHANGED << curr_value_to_chain, 
                                            curr_nonce_to_chain >>
              \/ /\ \E msg_idx \in 1..max_seen_signed_by_sender:
                      IF message[msg_idx][1] =< message[max_seen_signed_by_sender][1]
                         THEN /\ IF UpdatesSmartContract(message[msg_idx][2])
                                    THEN /\ curr_value_to_chain' = message[msg_idx][1]
                                         /\ curr_nonce_to_chain' = message[msg_idx][2]
                                    ELSE /\ TRUE
                                         /\ UNCHANGED << curr_value_to_chain, 
                                                         curr_nonce_to_chain >>
                         ELSE /\ TRUE
                              /\ UNCHANGED << curr_value_to_chain, 
                                              curr_nonce_to_chain >>
              \/ /\ \E msg_idx \in 1..max_seen_signed_by_receiver:
                      IF message[msg_idx][1] >= message[max_seen_signed_by_receiver][1]
                         THEN /\ IF UpdatesSmartContract(message[msg_idx][2])
                                    THEN /\ curr_value_to_chain' = message[msg_idx][1]
                                         /\ curr_nonce_to_chain' = message[msg_idx][2]
                                    ELSE /\ TRUE
                                         /\ UNCHANGED << curr_value_to_chain, 
                                                         curr_nonce_to_chain >>
                         ELSE /\ TRUE
                              /\ UNCHANGED << curr_value_to_chain, 
                                              curr_nonce_to_chain >>
           /\ pc' = "CancelFromReceiver"
           /\ UNCHANGED << message, max_signed_by_sender, 
                           max_signed_by_receiver, max_seen_signed_by_sender, 
                           max_seen_signed_by_receiver, num_sends_and_receives, 
                           exit_cancelled, curr_time >>

CancelFromReceiver == /\ pc = "CancelFromReceiver"
                      /\ IF curr_value_to_chain <= message[max_seen_signed_by_receiver][1]
                            THEN /\ IF UpdatesSmartContract(message[max_seen_signed_by_receiver][2])
                                       THEN /\ exit_cancelled' = TRUE
                                       ELSE /\ TRUE
                                            /\ UNCHANGED exit_cancelled
                            ELSE /\ TRUE
                                 /\ UNCHANGED exit_cancelled
                      /\ pc' = "CancelFromSender"
                      /\ UNCHANGED << message, max_signed_by_sender, 
                                      max_signed_by_receiver, 
                                      max_seen_signed_by_sender, 
                                      max_seen_signed_by_receiver, 
                                      num_sends_and_receives, curr_time, 
                                      curr_value_to_chain, curr_nonce_to_chain >>

CancelFromSender == /\ pc = "CancelFromSender"
                    /\ IF curr_value_to_chain >= message[max_seen_signed_by_sender][1]
                          THEN /\ IF UpdatesSmartContract(message[max_seen_signed_by_sender][2])
                                     THEN /\ exit_cancelled' = TRUE
                                     ELSE /\ TRUE
                                          /\ UNCHANGED exit_cancelled
                          ELSE /\ TRUE
                               /\ UNCHANGED exit_cancelled
                    /\ pc' = "Done"
                    /\ UNCHANGED << message, max_signed_by_sender, 
                                    max_signed_by_receiver, 
                                    max_seen_signed_by_sender, 
                                    max_seen_signed_by_receiver, 
                                    num_sends_and_receives, curr_time, 
                                    curr_value_to_chain, curr_nonce_to_chain >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Offchain \/ Update \/ SenderSignSend \/ ReceiverReceiveSignSend
           \/ SenderReceive \/ Onchain \/ CancelFromReceiver \/ CancelFromSender
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

(* note as the receiver can only get as much money as is sent by the sender
this also says that the receiver loses the money they have sent, which is fair *)
CancelledOrFair == <>(exit_cancelled \/ curr_value_to_chain = message[max_seen_signed_by_receiver][1])

                 
=============================================================================
\* Modification History
\* Last modified Tue Aug 20 11:51:26 EDT 2019 by nate
\* Last modified Sat Dec 22 14:17:18 PST 2018 by lamport
\* Created Thu Dec 20 11:44:08 PST 2018 by lamport
