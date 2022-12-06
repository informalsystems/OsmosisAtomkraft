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

# Running a test

```
atomkraft test trace --path traces --reactor reactors/reactor.py --keypath action_taken.action_type
```
