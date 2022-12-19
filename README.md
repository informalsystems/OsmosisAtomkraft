# OsmosisAtomkraft

Informal Systems Atomkraft adaptations and TLA specs for Osmosis audit project

# git clone

```
git clone PROJECT_URL --branch BRANCH_NAME
```

# Setup

```
git submodule update --init
(cd osmosis; make build)
```

# Generate traces

```
atomkraft model simulate --model-path=models/test_mp_gamm.tla --max-trace=3 --length=4 --traces-dir=traces/mp_gamm
```

# Execute tests

```
atomkraft test trace --path=traces/mp_gamm --reactor=reactors/mp_gamm.py --keypath=action.tag
```

# Execute scenarios created during the GAMM audit

The list of all the scenarios created and executed during the GAMM audit and the results can be found in [scenarios/readme.md](traces/scenarios/README.md).

One example of executing scenatio trace is presented here:

```
atomkraft test trace --path=traces/mp_gamm/scenarios/scenario8.itf.json --reactor=reactors/mp_gamm.py --keypath=action.tag
```