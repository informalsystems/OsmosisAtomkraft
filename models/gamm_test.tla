---- MODULE gamm_test ----

EXTENDS 
    gamm

Init ==
    /\ pool_assets = [d \in {} |-> [amount |-> 0, weight |-> 0]]
    /\ total_shares = [share_denom |-> "", amount |-> 0]
    /\ total_weight = 0
    /\ users = {}
    /\ action_taken = EmptyAction
    /\ outcome_status = ""

Next == 
    \E sender \in Identifiers:
        \/ \E amount \in Amounts:
            \/ JoinPool(sender, amount)
            \/ ExitPool(sender, amount)
        \/ \E initialAssets \in InitialAssets:
            CreatePool(sender, initialAssets)

(* ======== Invariants ======= *)

CreateSuccess ==
    /\ outcome_status = CREATE_SUCCESS
    /\ total_weight /= 0
    /\ Cardinality(users) = 1
CreateSuccessCEX == ~ CreateSuccess

\* apalache check --config=gamm_test.cfg --inv=CreateTwoPoolsJoinAndExitFromFirstCEX --max-error=3 gamm_test.tla
(* ---> *)
\* @type: Seq(STATE) => Bool;
CreateTwoPoolsJoinAndExitFromFirst(trace) ==
    \E i, j \in 1..7:
        /\  LET stateI1 == trace[i] IN
            LET stateI2 == trace[i+1] IN
            LET stateJ1 == trace[j] IN
            LET stateJ2 == trace[j+1] IN
            /\ i < j
            /\ stateI1.outcome_status = CREATE_SUCCESS
            /\ stateI2.outcome_status = CREATE_SUCCESS
            /\ stateJ1.outcome_status = JOIN_SUCCESS
            /\ stateJ2.outcome_status = EXIT_SUCCESS
            /\ stateI1.action_taken.poolId = stateJ1.action_taken.poolId
            /\ stateI1.action_taken.poolId = stateJ2.action_taken.poolId
            /\ Len(trace) > j

CreateTwoPoolsJoinAndExitFromFirstCEX(trace) == ~ CreateTwoPoolsJoinAndExitFromFirst(trace)
(* <--- *)

====