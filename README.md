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
