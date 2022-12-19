# OsmosisAtomkraft

This repository is a workspace for Informal Systems' Atomkraft adaptations and TLA specs
created specially for Osmosis audit project. 
All the important informations regarding the audit can be found in Informal Sysytems & Osmosis partnership repository, where 
Osmosis Atomkraft can is placed as a submodule under the 2022/Q4

### To clone just the Atomkraft artifacts Informal created during the audit

``` sh
git clone git@github.com:Ethernal-Tech/OsmosisAtomkraft.git
```
### To clone all the Atomkraft artifacts, including Osmosis source code at the relevant commit that has been audited
### and the traces were executed against:

``` sh
git clone --recurse-submodules git@github.com:Ethernal-Tech/OsmosisAtomkraft.git
```

### To update the submodules (Osmosis source code) if you've already cloned the repository

``` sh
git submodule update --init --recursive
```

# Setup

## building osmosis
Current version of the Atomkraft tool is using Osmosis v13.1.0 to execute traces against.
To setup the environment, you must build the osmosis locally with:

```
git submodule update --init
cd osmosis
make build
```
## Building different version of Atomkraft:
To run traces against a different Osmosis version, run commands:
```
git submodule update --init
cd osmosis
make build
```

## Install Atomkraft
Installing Atomkraft is as easy as: 
```
pip install atomkraft
```
However since Atomkraft is depending on:
- python 3.8 or newer
- python package manager - pip

it could be neccessary to follow the installation instructions from: [Installing Atomkraft](https://github.com/informalsystems/atomkraft/blob/343c6ec914b7cfcf6bbcd8fef50a29f24da5d67f/INSTALLATION.md?plain=1#L10-L22).

For basic usage of Osmosis Atomkraft tool - to run already generated test cases and scenarios, this is all you need.

If there is a need for "advance usage" - generating more traces and test cases that will be executed against the chaina, due to 
further TLA spec changes and/or newly defined scenario invariants, 
you should also check the [Java dependency](https://github.com/informalsystems/atomkraft/blob/343c6ec914b7cfcf6bbcd8fef50a29f24da5d67f/INSTALLATION.md?plain=1#L46-L50) chapter from Informal's Atomkraft Installation.md

# Working with Atomkraft and traces generated by Apalache
## Generate traces

```
atomkraft model simulate --model-path=models/test_mp_gamm.tla --max-trace=3 --length=4 --traces-dir=traces/mp_gamm
```

## Execute tests

```
atomkraft test trace --path=traces/mp_gamm --reactor=reactors/mp_gamm.py --keypath=action.tag
```

## Execute scenarios created during the GAMM audit

The list of all the scenarios created and executed during the GAMM audit and the results can be found in [scenarios/readme.md](traces/scenarios/README.md).

One example of executing scenatio trace is presented here:

```
atomkraft test trace --path=traces/scenarios/scenario8.itf.json --reactor=reactors/mp_gamm.py --keypath=action.tag
```