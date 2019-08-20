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
              with value \in 1..Deposit1, nonce \in 1..Deposit do
                if curr_nonce_to_chain < nonce then
                    curr_value_to_chain := value;
                    curr_nonce_to_chain := nonce;
                end if;
              end with;
          end either;
        end while;
    (* If the channel ever settles, or all money has been transfered, we have 
    the receiver try and settle with the highest nonce (and thus value) that
    they have*) 
    FinalSettle:
        if curr_nonce_to_chain < curr_nonce_to_receiver then
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
          /\ \E value \in 1..Deposit:
               \E nonce \in 1..Deposit:
                 IF curr_nonce_to_chain < nonce
                    THEN /\ curr_value_to_chain' = value
                         /\ curr_nonce_to_chain' = nonce
                    ELSE /\ TRUE
                         /\ UNCHANGED << curr_value_to_chain, 
                                         curr_nonce_to_chain >>
          /\ pc' = "Exec"
          /\ UNCHANGED << curr_value_to_receiver, curr_nonce_to_receiver >>

FinalSettle == /\ pc = "FinalSettle"
               /\ IF curr_nonce_to_chain < curr_nonce_to_receiver
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



(***************************************************************************)
(* The usual reason for writing a spec is to check the system you're       *)
(* specifying for errors.  This means checking that all possible           *)
(* executions satisfy some property.  The most commonly checked property   *)
(* is invariance, asserting that some condition is satisfied by every      *)
(* state in in every possible execution.                                   *)
(*                                                                         *)
(* The purpose of this spec is to solve the cannibals and missionaries     *)
(* problem, which means finding some possible execution in which everyone  *)
(* reaches bank "W".  We can find that solution by having the TLC model    *)
(* checker check the invariance property that, in every reachable state,   *)
(* there is someone left on bank "E".  When TLC find that an invariant     *)
(* it's checking isn't an invariant, it outputs an execution that reaches  *)
(* a state in which the invariant isn't true--which in this case means an  *)
(* execution that solves the problem (one ending in a state with no one on *)
(* bank "E").  So to find the solution, you just have to run TLC on a      *)
(* model of this specification in which three-element sets are substituted *)
(* for the constants Missionaries and Cannibals, instructing TLC to check  *)
(* that the formula                                                        *)
(*                                                                         *)
(*    who_is_on_bank["E"] /= {}                                            *)
(*                                                                         *)
(* is an invariant.  The error trace TLC produces is a solution to the     *)
(* problem.  You can run TLC from the TLA+ Toolbox.  Go to the TLA+ web    *)
(* page to find out how to learn to do that.                               *)
(*                                                                         *)
(* This problem was proposed to me by Jay Misra, who then suggested        *)
(* improvements to my first version of the spec.                           *)
(***************************************************************************)                  
=============================================================================
\* Modification History
\* Last modified Mon Aug 19 20:16:03 EDT 2019 by nate
\* Last modified Sat Dec 22 14:17:18 PST 2018 by lamport
\* Created Thu Dec 20 11:44:08 PST 2018 by lamport
