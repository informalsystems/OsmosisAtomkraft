# Atomkraft - Osmosis findings

## Execute all scenarios

```
atomkraft test trace --path=traces/scenarios  --reactor=reactors/mp_gamm.py --keypath=action.tag
```

## Execute specific scenario

Replace $SCENARIO-ID$ with the name of desired scenario itf.json file. 
```
atomkraft test trace --path=traces/scenarios/$SCENARIO-ID$.itf.json  --reactor=reactors/mp_gamm.py --keypath=action.tag
```

# List of test scenarios

---
### Scenario: User creates a pool and exits with the same number of shares

Outcome:

```
Error:(Code 8) failed to execute message; message index: 0: share ratio is zero or negative: invalid calculated result
```

Traces: `traces/scenarios/scenario4.itf.json`

---


### Scenario: Try to initialize a wallet with asset amount `(2^(256-60) - 1)`

Outcome: Passed

Traces: `traces/scenarios/scenario4.itf.json`

---

### Scenario: Try to join a pool with a low share

Outcome:

```
(Code 8) failed to execute message; message index: 0: share ratio is zero or negative: invalid calculated result
```

Traces: `traces/scenarios/scenario5.itf.json`, `traces/scenarios/scenario10.itf.json`, `traces/scenarios/scenario10.itf.json`

---

### Scenario: Create, Join, Exit

Outcome: Pass

Traces: `traces/scenarios/scenario6.itf.json`

---

### Scenario: Create, Exit, Join

Outcome: Pass

Traces: `traces/scenarios/scenario7.itf.json`

---

### Scenario: ExitPool min amount check is calculated incorrectly

Outcome:

```
(Code 7) failed to execute message; message index: 0: Exit pool returned 4uatom,1ujuno , minimum tokens out specified as 4uatom,2ujuno: calculated amount is lesser than min amount
```

Explanation:

```
Pool status:
Share: 92307692307692307745
Assets: 27uatom, 13ujuno

Exit pool:
Out share: 14201183431952662730
Atomkraft calculated out assets: 4uatom,2ujuno
Osmosisd calculated out assets: 4uatom,1ujuno

Osmosisd calculated wrong because 2 = 13 (juno amount in pool) * 14201183431952662730 (out share) / 92307692307692307745 (current share)
```

Traces: `traces/scenarios/scenario8.itf.json`

---

### Scenario: ExitPool can leave with zero assets with a low share

Outcome: Pass

Explanation:

```
Pool create:
uosmo: 1
uatom: 1
share: 10^20

Pool exit:
out_share: 1
out_uosmo: 0
out_uatom: 0

Pool status:
uosmo: 1
uatom: 1
share: 10^20 - 1
```

Traces: `traces/scenarios/scenario9.itf.json`

---

### Scenario: Swap using a pool via `swap-exact-amount-in`

Outcome: Pass

Traces: `traces/scenarios/scenario12.itf.json`, `traces/scenarios/scenario13.itf.json`

---

### Scenario: Swap using a pool via `swap-exact-amount-out`

Outcome: Pass

Traces: `traces/scenarios/scenario14.itf.json`

---

### Scenario: Swap using a pool via `swap-exact-amount-out`

Outcome: Recovered panic

```
(Code 111222) recovered: base must be lesser than two
stack:
goroutine 246 [running]:
runtime/debug.Stack()
	runtime/debug/stack.go:24 +0x65
github.com/cosmos/cosmos-sdk/baseapp.newDefaultRecoveryMiddleware.func1({0x1d4ab80, 0xc005abf0e0})
	github.com/cosmos/cosmos-sdk@v0.45.11/baseapp/recovery.go:71 +0x27
github.com/cosmos/cosmos-sdk/baseapp.newRecoveryMiddleware.func1({0x1d4ab80?, 0xc005abf0e0?})
	github.com/cosmos/cosmos-sdk@v0.45.11/baseapp/recovery.go:39 +0x30
github.com/cosmos/cosmos-sdk/baseapp.processRecovery({0x1d4ab80, 0xc005abf0e0}, 0xc005abd680?)
	github.com/cosmos/cosmos-sdk@v0.45.11/baseapp/recovery.go:28 +0x37
github.com/cosmos/cosmos-sdk/baseapp.processRecovery({0x1d4ab80, 0xc005abf0e0}, 0x26f5400?)
	github.com/cosmos/cosmos-sdk@v0.45.11/baseapp/recovery.go:33 +0x5e
github.com/cosmos/cosmos-sdk/baseapp.(*BaseApp).runTx.func1()
	github.com/cosmos/cosmos-sdk@v0.45.11/baseapp/baseapp.go:657 +0xf0
panic({0x1d4ab80, 0xc005abf0e0})
	runtime/panic.go:884 +0x212
github.com/osmosis-labs/osmosis/v13/osmomath.Pow({0xc005aecf20?}, {0x2444450?})
	github.com/osmosis-labs/osmosis/v13/osmomath/math.go:64 +0x13e
github.com/osmosis-labs/osmosis/v13/x/gamm/pool-models/balancer.solveConstantFunctionInvariant({0xc005ab4e00?}, {0x0?}, {0x1?}, {0xc005aecdc0?}, {0xc005aecde0?})
	github.com/osmosis-labs/osmosis/v13/x/gamm/pool-models/balancer/amm.go:108 +0x6f
github.com/osmosis-labs/osmosis/v13/x/gamm/pool-models/balancer.Pool.CalcInAmtGivenOut({{0xc005ab4e00, 0x3f}, 0x1, {{0xc005aecdc0}, {0xc005aecde0}, 0x0}, {0x0, 0x0}, {{0xc005ad4360, 0xb}, ...}, ...}, ...)
	github.com/osmosis-labs/osmosis/v13/x/gamm/pool-models/balancer/pool.go:555 +0x16d
github.com/osmosis-labs/osmosis/v13/x/gamm/keeper.Keeper.createMultihopExpectedSwapOuts({{0x26c9838, 0xc0013e57a0}, {0x26f3240, 0xc001175510}, {{0x26f3240, 0xc001175510}, 0xc00011fd68, {0x26c9838, 0xc0013e5730}, {0x26c9888, ...}, ...}, ...}, ...)
	github.com/osmosis-labs/osmosis/v13/x/gamm/keeper/multihop.go:326 +0x2a8
github.com/osmosis-labs/osmosis/v13/x/gamm/keeper.Keeper.MultihopSwapExactAmountOut({{0x26c9838, 0xc0013e57a0}, {0x26f3240, 0xc001175510}, {{0x26f3240, 0xc001175510}, 0xc00011fd68, {0x26c9838, 0xc0013e5730}, {0x26c9888, ...}, ...}, ...}, ...)
	github.com/osmosis-labs/osmosis/v13/x/gamm/keeper/multihop.go:178 +0x32b
github.com/osmosis-labs/osmosis/v13/x/gamm/keeper.msgServer.SwapExactAmountOut({0x4133a5?}, {0x26e24f8?, 0xc005af0720?}, 0xc005571900)
	github.com/osmosis-labs/osmosis/v13/x/gamm/keeper/msg_server.go:194 +0x219
github.com/osmosis-labs/osmosis/v13/x/gamm/types._Msg_SwapExactAmountOut_Handler.func1({0x26e24f8, 0xc005af0720}, {0x1fce7c0?, 0xc005571900})
	github.com/osmosis-labs/osmosis/v13/x/gamm/types/tx.pb.go:1260 +0x78
github.com/cosmos/cosmos-sdk/baseapp.(*MsgServiceRouter).RegisterService.func2.1({0x26e24f8, 0xc005af06f0}, {0x4c3666?, 0x412deb?}, 0x2010e20?, 0xc005ab7278)
	github.com/cosmos/cosmos-sdk@v0.45.11/baseapp/msg_service_router.go:113 +0xd2
github.com/osmosis-labs/osmosis/v13/x/gamm/types._Msg_SwapExactAmountOut_Handler({0x1f13560?, 0xc000014530}, {0x26e24f8, 0xc005af06f0}, 0x2444240, 0xc005aecd20)
	github.com/osmosis-labs/osmosis/v13/x/gamm/types/tx.pb.go:1262 +0x138
github.com/cosmos/cosmos-sdk/baseapp.(*MsgServiceRouter).RegisterService.func2({{0x26e24f8, 0xc005adce70}, {0x26f5400, 0xc005adeb80}, {{0xb, 0x0}, {0xc00528dcf9, 0x7}, 0xb, {0x20a97a02, ...}, ...}, ...}, ...)
	github.com/cosmos/cosmos-sdk@v0.45.11/baseapp/msg_service_router.go:134 +0x45e
github.com/cosmos/cosmos-sdk/baseapp.(*BaseApp).runMsgs(_, {{0x26e24f8, 0xc005adce70}, {0x26f5400, 0xc005adeb80}, {{0xb, 0x0}, {0xc00528dcf9, 0x7}, 0xb, ...}, ...}, ...)
	github.com/cosmos/cosmos-sdk@v0.45.11/baseapp/baseapp.go:799 +0x5a5
github.com/cosmos/cosmos-sdk/baseapp.(*BaseApp).runTx(0xc00137fba0, 0x3, {0xc000657200, 0x114, 0x114})
	github.com/cosmos/cosmos-sdk@v0.45.11/baseapp/baseapp.go:742 +0xbc5
github.com/cosmos/cosmos-sdk/baseapp.(*BaseApp).DeliverTx(0xc00137fba0, {{0xc000657200?, 0x20?, 0xc00541e6e0?}})
	github.com/cosmos/cosmos-sdk@v0.45.11/baseapp/abci.go:288 +0x193
github.com/tendermint/tendermint/abci/client.(*localClient).DeliverTxAsync(0xc001346780, {{0xc000657200?, 0x0?, 0xc001346780?}})
	github.com/tendermint/tendermint@v0.34.22/abci/client/local_client.go:93 +0x105
github.com/tendermint/tendermint/proxy.(*appConnConsensus).DeliverTxAsync(0xc005a97a60?, {{0xc000657200?, 0x20?, 0xb?}})
	github.com/tendermint/tendermint@v0.34.22/proxy/app_conn.go:85 +0x26
github.com/tendermint/tendermint/state.execBlockOnProxyApp({0x26e3918?, 0xc0015a8000}, {0x26ebcf0, 0xc00144d1a0}, 0xc004b483c0, {0x26f4808, 0xc0002a81e0}, 0xa?)
	github.com/tendermint/tendermint@v0.34.22/state/execution.go:320 +0x847
github.com/tendermint/tendermint/state.(*BlockExecutor).ApplyBlock(_, {{{0xb, 0x0}, {0xc00148c030, 0x7}}, {0xc00148c037, 0x7}, 0x1, 0xa, {{0xc005850b20, ...}, ...}, ...}, ...)
	github.com/tendermint/tendermint@v0.34.22/state/execution.go:140 +0x171
github.com/tendermint/tendermint/consensus.(*State).finalizeCommit(0xc0011a2000, 0xb)
	github.com/tendermint/tendermint@v0.34.22/consensus/state.go:1659 +0xafd
github.com/tendermint/tendermint/consensus.(*State).tryFinalizeCommit(0xc0011a2000, 0xb)
	github.com/tendermint/tendermint@v0.34.22/consensus/state.go:1568 +0x2ff
github.com/tendermint/tendermint/consensus.(*State).enterCommit.func1()
	github.com/tendermint/tendermint@v0.34.22/consensus/state.go:1503 +0x94
github.com/tendermint/tendermint/consensus.(*State).enterCommit(0xc0011a2000, 0xb, 0x0)
	github.com/tendermint/tendermint@v0.34.22/consensus/state.go:1541 +0xccf
github.com/tendermint/tendermint/consensus.(*State).addVote(0xc0011a2000, 0xc005a84640, {0xc00063c0c0, 0x28})
	github.com/tendermint/tendermint@v0.34.22/consensus/state.go:2155 +0x18dc
github.com/tendermint/tendermint/consensus.(*State).tryAddVote(0xc0011a2000, 0xc005a84640, {0xc00063c0c0?, 0xc005a8c200?})
	github.com/tendermint/tendermint@v0.34.22/consensus/state.go:1953 +0x2c
github.com/tendermint/tendermint/consensus.(*State).handleMsg(0xc0011a2000, {{0x26c4360?, 0xc005a88148?}, {0xc00063c0c0?, 0x0?}})
	github.com/tendermint/tendermint@v0.34.22/consensus/state.go:856 +0x170
github.com/tendermint/tendermint/consensus.(*State).receiveRoutine(0xc0011a2000, 0x0)
	github.com/tendermint/tendermint@v0.34.22/consensus/state.go:763 +0x3f9
created by github.com/tendermint/tendermint/consensus.(*State).OnStart
	github.com/tendermint/tendermint@v0.34.22/consensus/state.go:379 +0x12d
: panic
```

Explanation:

```
Pool create:
uatom: 2
ujuno: 8

Pool swap out exact:
denom_in: uatom
denom_out: ujuno
amount_out: 4


Osmosisd panics in cases when trying to swap exact or more that 50% of the denom balance from the pool.
```



Traces: `traces/scenarios/scenario15.itf.json`

---

### Scenario: Swap using a pool via `swap-exact-amount-out`

Outcome: Two panics

```
Failure: (Code 111222) recovered: base must be lesser than two
...
: panic
```

```
Failure: (Code 111222) recovered: base must be greater than 0
...
: panic
```
Explanation:

```
Pool create:
uosmo: 3
uatom: 100000000000000000003
ujuno: 2

1. Pool swap out exact:
denom_in: uatom
denom_out: ujuno
amount_out: 1

2. Pool swap out exact:
denom_in: ujuno
denom_out: uatom
amount_out: 150000000000000000004


Osmosisd panics in cases when trying to swap exact or more that 50% of the denom balance from the pool
and for the second panic, when trying to swap out more than containing in the pool.
```

Traces: `traces/scenarios/scenario16.itf.json`

---
s
### Scenario: Swap using a pool via `swap-exact-amount-out`

Outcome: panic

```
Failure: (Code 111222) recovered: division by zero
...
: panic
```

Explanation: scenario contains multiple steps impacting to the final step producing this error.

As the result of prior executions the balance in the pool with Id = 3 is as follows:

```
[Pool status]:  {... 
'pool_params': {'swap_fee': '0.000000000000000000',   
'exit_fee': '0.000000000000000000',   
'smooth_weight_change_params': None},  
'future_pool_governor': '',  
'total_shares': {'denom': 'gamm/pool/3', 'amount': '99999999999999999999'},   
'pool_assets': [{'token': {'denom': 'uatom', 'amount': '1'}, 'weight': '1073741824'}, {'token': {'denom': 'uosmo', 'amount': '1'}, 'weight': '1073741824'}],  
'total_weight': '2147483648'}  

```
then with next step:
```
swap-exact-amount-out:
amount_out: 1  
denom_in: uatom  
denom_out: uosmo  


Osmosisd panics in cases when doing swap-exit-amount-out for amount_out being equal to the balance of the token in the pool.
```

Traces: `traces/scenarios/scenario17.itf.json`

---

### Scenario: Join pool 

Outcome:

```
Failure: (Code 1) failed to execute message; message index: 0: unexpected error in MaximalExactRatioJoin
```
Explanation: scenario contains multiple steps impacting to the final step producing this error.

As the result of prior executions the balance in the pool with Id = 2 is as follows:

```
[Pool status]: 
{...
'pool_params': {'swap_fee': '0.000000000000000000',  
'exit_fee': '0.000000000000000000',  
'smooth_weight_change_params': None},  
'future_pool_governor': '',   
'total_shares': {'denom': 'gamm/pool/2', 'amount': '200000000000000000000'},   
'pool_assets': [{'token': {'denom': 'ujuno', 'amount': '2'}, 'weight': '1073741824'}, {'token': {'denom': 'uosmo', 'amount': '2'},  
'weight': '1073741824'}],   
'total_weight': '2147483648'}
```
then with next step:
```
join pool:	
max-amounts-in: 49999999999999999998uosmo  49999999999999999998ujuno
share-amount-out 3333333333333333333216666666666666666666



Osmosisd returns error in calculation of `MaximalExactRatioJoin` because `minShareRatio` is equal to `maxSortableDec` - `shareRatio` was not less or equal to `minShareRatio`.
```


Traces: `traces/scenarios/scenario18.itf.json`

---

### Scenario: Swap in amount

Outcome:

```
Failure: (Code 1) failed to execute message; message index: 0: function swapExactAmountIn failed due to internal reason: base must be greater than 0
```

Explanation: scenario contains multiple steps impacting to the final step producing this error.

As the result of prior executions the balance in the pool with Id = 1 is as follows:

```
[Pool status]: 
{'@type': '/osmosis.gamm.v1beta1.Pool', 'address': 'osmo1mw0ac6rwlp5r8wapwk3zs6g29h8fcscxqakdzw9emkne6c8wjp9q0t3v8t', 'id': '1', 'pool_params': {'swap_fee': '0.000000000000000000',   
'exit_fee': '0.000000000000000000',    
'smooth_weight_change_params': None},   
'future_pool_governor': '',   
'total_shares': {'denom': 'gamm/pool/1', 'amount': '100000000000000000000'},  
'pool_assets': [{'token': {'denom': 'uatom', 'amount': '2'}, 'weight': '1073741824'}, {'token': {'denom': 'ujuno', 'amount': '50000000000000000000'}, 'weight': '1073741824'}],  
'total_weight': '2147483648'}
```
then with next step:
```
swap-exact-amount-in:
tokenIn: 11111111111111111111uatom
token-out-min-amount 11111111111111111110
swap-route-pool-ids: 1
swap-route-denoms: ujuno

Osmosisd is probably panicking due to taking out  >50% amount from the pool.
```


Traces: `traces/scenarios/scenario19.itf.json`, `traces/scenarios/scenario20.itf.json`

---

