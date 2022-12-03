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
atomkraft model simulate --model-path=models/multi_pool_gamm.tla --max-trace=3 --length=5 --traces-dir=traces/multi_pool_gamm
```

# Executing tests

```
atomkraft test trace --path=traces/multi_pool_gamm --reactor=reactors/multi_pool_gamm.py --keypath=action.tag
```
