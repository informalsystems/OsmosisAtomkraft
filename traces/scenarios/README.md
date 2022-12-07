# Atomkraft - Osmosis findings

## Execute all scenarios

```
atomkraft test trace --path traces/scenarios --reactor=reactors/mp_gamm.py --keypath=action.tag
```

## List of test scenarios

Scenario: User C creates one pool, then user B joins this pool with x shares and exits the pool with x shares.
Outcome: Pass
Traces: traces/trace1.itf.json

---

Scenario: Outcome: Error-XX
Traces: violation1.itf.json

---

Scenario: Joining pools without TokenInMax arg - try joining for large number of ShareOutAmount, to try and spend users balance for denom (it seems it is possible to Join the pool without specifying this amount, but the behaviour is diff for JoinSwapShareAmountOut - not modeled with our TLA spec)

Outcome:

Traces:

---

Scenario: User creates a pool and exits with the same number of shares

Outcome:

```
Error:(Code 8) failed to execute message; message index: 0: share ratio is zero or negative: invalid calculated result
```

Traces: `traces/scenarios/scenario4.itf.json`

---

Scenario: Try to initialize a wallet with asset amount `(2^(256+60) - 1)`

Outcome:

```
failed to parse coins: failed to parse decimal coin amount: 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433535: decimal out of range; bitLen: got 376, max 256
```

Traces: `traces/scenarios/scenario2.itf.json`

---

Scenario: Try to initialize a wallet with asset amount `(2^256 - 1)`

Outcome:

```
failed to parse coins: failed to parse decimal coin amount: 115792089237316195423570985008687907853269984665640564039457584007913129639935: decimal out of range; bitLen: got 316, max 256
```

Traces: `traces/scenarios/scenario3.itf.json`

---

Scenario: Try to initialize a wallet with asset amount `(2^(256-60) - 1)`

Outcome: Passed

Traces: `traces/scenarios/scenario4.itf.json`

---

Scenario: Try to join a pool with a low share

Outcome:

```
(Code 8) failed to execute message; message index: 0: share ratio is zero or negative: invalid calculated result
```

Traces: `traces/scenarios/scenario5.itf.json`, `traces/scenarios/scenario10.itf.json`

---

Scenario: Create, Join, Exit

Outcome: Pass

Traces: `traces/scenarios/scenario6.itf.json`

---

Scenario: Create, Exit, Join

Outcome: Pass

Traces: `traces/scenarios/scenario7.itf.json`

---

Scenario: ExitPool min amount check is calculated incorrectly

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

Scenario: ExitPool can leave with zero assets with a low share

Outcome: Pass

Traces: `traces/scenarios/scenario9.itf.json`

---

Scenario: Swap using a pool

Outcome: Pass

Traces: `traces/scenarios/scenario12.itf.json`

---

Scenario: Create, join and exit pools with more than two denominations. (Info: ValidateBasic will reject creation of pools with more than 8 denominations)

Outcome:

Traces:
