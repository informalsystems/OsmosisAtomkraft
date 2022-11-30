"""
The reactor file connects a test scenario described by a trace
(obtained from a model or written by hand) with the actual execution
of the test scenario on the testnet.

It contains one @step decorated function per each action appearing in the trace:
those function implement changes to the blockchain corresponding to the
abstract action from the trace.

All step functions receive the following arguments:
    testnet: a `Testnet` object on which blockchain transactions can be
             executed.
    action: object from the trace which corresponds to the parameters
            of the taken step.
    home_dir: directory of binary file
"""

import json
import logging
import os
import random
import string
import subprocess
from pathlib import Path
from typing import Dict

import munch
import pytest
from atomkraft.chain import Testnet
from atomkraft.chain.utils import TmEventSubscribe
from modelator.pytest.decorators import step

keypath = "action"


pool_file_ID = 0


@pytest.fixture
def home_dir(tmp_path):
    return tmp_path / "osmosisd"


def map_string(i, size: int):
    r = random.Random(i)
    return "".join(r.choices(string.ascii_lowercase + string.digits, k=size))


@pytest.fixture
def state():
    """
    Defines any additional logical state (beyond the state of the chain)
    that needs to be maintained throughout the execution. This state
    will be passed as an argument to @step functions.
    """

    # TODO: replace the empty stub object with a different state object
    # if necessary
    return {}


@step("empty")
def init(testnet: Testnet, state: Dict, home_dir: Path):
    """
    Implements the effects of the step `init`
    on blockchain `testnet` and state `state`.
    It additionally has access to the model (trace) state variable `action_taken`.
    """
    logging.info("Step: init")
    state["pool_id"] = 0

    # TODO Mirel: we need to be assigning wallets, as in transfer example in init state -> TLA spec change is needed
    # identifiers -> wallets
    balances = {}
    for e in ["A", "B", "C"]:
        balances[e] = {}
        for d in ["uosmo", "uatom"]:
            balances[e][d] = int(1e10)
    testnet.set_accounts(balances.keys())
    testnet.set_account_balances(balances)
    testnet.verbose = True
    testnet.oneshot()
    # Tendermint event sybscriber
    with TmEventSubscribe({"tm.event": "NewBlock"}):
        logging.info("\tStatus: Testnet launched...\n")

    # recover accounts for a testnet
    for (user, account) in testnet.accounts.items():
        args = (
            f"{testnet.binary} "
            f"keys add {user} "
            "--recover "
            "--keyring-backend test "
            f"--home {home_dir} "
        ).split()
        subprocess.run(
            args,
            check=True,
            input=f"{account.wallet.mnemonic()}\n".encode(),
        )


@step("create pool")
def create_pool(
    testnet: Testnet, state: Dict, pool_assets, action_taken, home_dir: Path
):
    """
    Implements the effects of the step `create pool`
    on blockchain `testnet` and state `state`.
    It additionally has access to the model (trace) state variable `action_taken`.
    """

    # TX Msg: osmosisd tx gamm create-pool --pool-file [config-file] --from WALLET_NAME --chain-id osmosis-1
    # file should be saved in pool-files directory by the name of pool_INV_NUM
    pool_file_location = home_dir / "pool-files"
    pool_file_location.mkdir(exist_ok=True, parents=True)
    state["pool_id"] += 1
    pool_file_name = f"pool-file-{pool_file_ID}.json"
    logging.info("Step: create pool")

    """
    pool file should look like:
    {
        "weights": [list weighted denoms],
        "initial-deposit": [list of denoms with initial deposit amount],
        "swap-fee": [swap fee in percentage],
        "exit-fee": [exit fee in percentage],
        "future-governor": [see options in pool parameters section above]
    } 
    """
    # pool_config: swap-fee, exit-fee,
    # future-governor are now predefined, but maybe values should also be parsed form TLA spec
    init_deposit_uosmo = pool_assets["OSMO"]["amount"]
    init_weight_uosmo = pool_assets["OSMO"]["weight"]
    init_deposit_uatom = pool_assets["ATOM"]["amount"]
    init_weight_uatom = pool_assets["ATOM"]["weight"]

    pool_config = {
        "weights": f"{init_weight_uosmo}uosmo, {init_weight_uatom}uatom",
        "initial-deposit": f"{init_deposit_uosmo}uosmo, {init_deposit_uatom}uatom",
        "swap-fee": "0.00",
        "exit-fee": "0.00",
        "future-governor": "",
    }

    # Writing to .json
    pool_conf_json_file = os.path.join(pool_file_location, pool_file_name)
    with open(pool_conf_json_file, "w") as outfile:
        json.dump(pool_config, outfile, indent=4)

    # action = action_taken.action_type
    # we need to remember poolId -> created pool Id on chain, due to test asertions
    # read this from the result -> add mapping TLA_poolID -> chain_poolID (add this map as part of the def state)
    poolId = action_taken.poolId

    senderId = action_taken.sender
    sender = testnet.acc_addr(senderId)

    # create transaction and send it to nodes rpc port
    rpc_addr = testnet.get_validator_port(0, "rpc")

    args = (
        f"{testnet.binary} "
        "tx gamm "
        "create-pool "
        f"--pool-file {pool_conf_json_file} "
        f"--from {senderId} "
        "--broadcast-mode block "
        "-y "
        "--keyring-backend test "
        f"--home {home_dir} "
        f"--chain-id {testnet.chain_id} "
        f"--node {rpc_addr} "
        "--output json "
    ).split()
    proc = subprocess.run(args, capture_output=True)

    # subscribe to event or check the result of broadcasting the tx
    # event = TmEventSubscribe({"tm.event":"Tx"})._subscribe("AND pool-create.pool-id"):

    if proc.returncode:
        logging.info(f"\tCLI Error: {proc.stderr}")
    else:
        result = None
        if proc.stdout:
            result = munch.munchify(json.loads(proc.stdout.decode()))

        if result is None:
            logging.info("\tNo response!!")
        elif result.code == 0:
            logging.info(f"\tPosted: {munch.unmunchify(action_taken.action_type)}")

            for event in result.logs[0].events:
                if event.type == "pool_created":
                    assert event.attributes[0].key == "pool_id"
                    state["chain_pool_id"] = event.attributes[0].value
                    break
            else:
                raise RuntimeError("Did not find pool_id of the created pool")
        else:
            code = result.code
            msg = result.raw_log
            logging.info(f"\tFailure: (Code {code}) {msg}")

    args = (
        f"{testnet.binary} "
        "q gamm "
        f"pool {state['pool_id']} "
        f"--home {home_dir} "
        f"--chain-id {testnet.chain_id} "
        f"--node {rpc_addr} "
        "--output json "
    ).split()
    logging.info("\tCurrent LP: %s", subprocess.check_output(args).decode())


@step("join pool")
def join_pool(testnet: Testnet, state: Dict, action_taken, home_dir: Path):
    """
    Implements the effects of the step `join pool`
    on blockchain `testnet` and state `state`.
    It additionally has access to the model (trace) state variable `action_taken`.
    """

    # TODO: replace the logging stub with the effects of the action `join pool`
    logging.info("Step: join pool")
    # Tx Msg: osmosisd tx gamm join-pool --pool-id --max-amounts-in --share-amount-out --from --chain-id
    # osmosisd tx gamm join-swap-extern-amount-in [token-in] [share-out-min-amount]
    logging.info(action_taken)

    # create transaction and send it to nodes rpc port
    rpc_addr = testnet.get_validator_port(0, "rpc")

    args = (
        f"{testnet.binary} "
        "q gamm "
        f"pool {state['pool_id']} "
        f"--home {home_dir} "
        f"--chain-id {testnet.chain_id} "
        f"--node {rpc_addr} "
        "--output json "
    ).split()

    lp_data = json.loads(subprocess.check_output(args).decode())

    action_share = action_taken.shares

    current_share = int(lp_data["pool"]["total_shares"]["amount"])
    current_pool_assets = {
        e["token"]["denom"]: int(e["token"]["amount"])
        for e in lp_data["pool"]["pool_assets"]
    }

    max_amounts_in = ""
    for k, v in current_pool_assets.items():
        max_amounts_in += f"--max-amounts-in {v * action_share / current_share}{k} "

    args = (
        f"{testnet.binary} "
        "tx gamm "
        "join-pool "
        f"{max_amounts_in} "
        f"--share-amount-out {action_share} "
        f"--pool-id {state['pool_id']} "
        f"--from {action_taken.sender} "
        "--broadcast-mode block "
        "-y "
        "--keyring-backend test "
        f"--home {home_dir} "
        f"--chain-id {testnet.chain_id} "
        f"--node {rpc_addr} "
        "--output json "
    ).split()
    proc = subprocess.run(args, capture_output=True)

    if proc.returncode:
        logging.info(f"\tCLI Error: {proc.stderr}")
    else:
        result = None
        if proc.stdout:
            result = munch.munchify(json.loads(proc.stdout.decode()))

        if result is None:
            logging.info("\tNo response!!")
        elif result.code == 0:
            logging.info("\tSuccess")
        else:
            code = result.code
            msg = result.raw_log
            logging.info(f"\tFailure: (Code {code}) {msg}")

    args = (
        f"{testnet.binary} "
        "q gamm "
        f"pool {state['pool_id']} "
        f"--home {home_dir} "
        f"--chain-id {testnet.chain_id} "
        f"--node {rpc_addr} "
        "--output json "
    ).split()
    logging.info("\tCurrent LP: %s", subprocess.check_output(args).decode())


@step("exit pool")
def exit_pool(testnet: Testnet, state: Dict, action_taken, home_dir: Path):
    """
    Implements the effects of the step `exit pool`
    on blockchain `testnet` and state `state`.
    It additionally has access to the model (trace) state variable `action_taken`.
    """

    # TODO: replace the logging stub with the effects of the action `exit pool`
    logging.info("Step: exit pool")
    # Tx Msg:
    # osmosisd tx gamm exit-swap-extern-amount-out [token-out] [share-in-max-amount] [flags]
    logging.info(action_taken)

    # create transaction and send it to nodes rpc port
    rpc_addr = testnet.get_validator_port(0, "rpc")

    args = (
        f"{testnet.binary} "
        "q gamm "
        f"pool {state['pool_id']} "
        f"--home {home_dir} "
        f"--chain-id {testnet.chain_id} "
        f"--node {rpc_addr} "
        "--output json "
    ).split()

    lp_data = json.loads(subprocess.check_output(args).decode())

    action_share = action_taken.shares

    current_share = int(lp_data["pool"]["total_shares"]["amount"])
    current_pool_assets = {
        e["token"]["denom"]: int(e["token"]["amount"])
        for e in lp_data["pool"]["pool_assets"]
    }

    min_amounts_out = ""
    for k, v in current_pool_assets.items():
        min_amounts_out += f"--min-amounts-out {v * action_share / current_share}{k} "

    args = (
        f"{testnet.binary} "
        "tx gamm "
        "exit-pool "
        f"{min_amounts_out} "
        f"--share-amount-in {action_share} "
        f"--pool-id {state['pool_id']} "
        f"--from {action_taken.sender} "
        "--broadcast-mode block "
        "-y "
        "--keyring-backend test "
        f"--home {home_dir} "
        f"--chain-id {testnet.chain_id} "
        f"--node {rpc_addr} "
        "--output json "
    ).split()
    proc = subprocess.run(args, capture_output=True)

    if proc.returncode:
        logging.info(f"\tCLI Error: {proc.stderr}")
    else:
        result = None
        if proc.stdout:
            result = munch.munchify(json.loads(proc.stdout.decode()))

        if result is None:
            logging.info("\tNo response!!")
        elif result.code == 0:
            logging.info("\tSuccess")
        else:
            code = result.code
            msg = result.raw_log
            logging.info(f"\tFailure: (Code {code}) {msg}")

    args = (
        f"{testnet.binary} "
        "q gamm "
        f"pool {state['pool_id']} "
        f"--home {home_dir} "
        f"--chain-id {testnet.chain_id} "
        f"--node {rpc_addr} "
        "--output json "
    ).split()
    logging.info("\tCurrent LP: %s", subprocess.check_output(args).decode())
