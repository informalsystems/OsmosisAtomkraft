# OsmosisAtomkraft

Informal Systems Atomkraft adaptations and TLA specs for Osmosis audit project

# Setup

```
git submodule update --init
(cd osmosis; make build)
```

# Running a test

```
atomkraft test trace --path traces/trace1.itf.json --reactor reactors/reactor.py --keypath action_taken.action_type
```
