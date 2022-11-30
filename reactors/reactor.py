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


@step("init")
def init(testnet: Testnet, state: Dict, action_taken):
    """
    Implements the effects of the step `init`
    on blockchain `testnet` and state `state`.
    It additionally has access to the model (trace) state variable `action_taken`.
    """
    logging.info("Step: init")
    POOL_ID = 0

    # TODO Mirel: we need to be assigning wallets, as in transfer example in init state -> TLA spec change is needed
    # identifiers -> wallets
    # testnet.set_accounts(wallets)
    # testnet.set_account_balances(balances)
    testnet.verbose = True
    testnet.oneshot()
    testnet.sleep(10)
    logging.info("Status: Testnet launched...\n")

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
def create_pool(testnet: Testnet, state: Dict, action_taken):
    """
    Implements the effects of the step `create pool`
    on blockchain `testnet` and state `state`.
    It additionally has access to the model (trace) state variable `action_taken`.
    """

    # TX Msg: osmosisd tx gamm create-pool --pool-file [config-file] --from WALLET_NAME --chain-id osmosis-1
    # file should be saved in pool-files directory by the name of pool_INV_NUM
    pool_file_location = "../pool-files/"
    POOL_ID += 1
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
    init_deposit_uosmo = action_taken.pool_assets["OSMO"]["amount"]
    init_weight_uosmo = action_taken.pool_assets["OSMO"]["weight"]
    init_deposit_uatom = action_taken.pool_assets["ATOM"]["amount"]
    init_weight_uatom = action_taken.pool_assets["ATOM"]["weight"]

    pool_config = {
        "weights": "{init_weight_uosmo}uosmo, {init_weight_uatom}uatom",
        "initial-deposit": "{init_deposit_uosmo}uosmo, {init_deposit_uatom}uatom",
        "swap-fee": "0.01",
        "exit-fee": "0.01",
        "future-governor": " ",
    }

    # Serializing json
    json_object = json.dumps(pool_config, indent=4)

    # Writing to .json
    filepath = os.path.join(pool_file_location, pool_file_name)
    with open(filepath, "w") as outfile:
        outfile.write(json_object)

    # action = action_taken.action_type
    # we need to remember poolId -> created pool Id on chain, due to test asertions
    # read this from the result -> add mapping TLA_poolID -> chain_poolID (add this map as part of the def state)
    poolId = action_taken.poolId

    senderId = action_taken.sender
    sender = testnet.acc_addr(senderId)

    # create transaction and send it to nodes rpc port
    rpc_addr = testnet.get_validator_port(0, "rpc")

    args = (
        f"{testnet.binary}"
        "tx gamm"
        f"create-pool {pool_file_location}.json"
        f"--from {senderId}"
        f"--broadcast-mode block"
        f"--chain-id {testnet.chain_id}"
        f"--node {rpc_addr}"
    ).split()
    proc = subprocess.run(args, check=True, capture_output=True)

    # subscribe to event or check the result of broadcasting the tx
    # event = TmEventSubscribe({"tm.event":"Tx"})._subscribe("AND pool-create.pool-id"):

    chain_pool_Id = 0
    result = None
    if proc.stdout:
        result = json.loads(proc.stdout.decode())

    if result is None:
        logging.info("\tNo response!!")
    elif result["code"] == 0:
        logging.info(f"\tPosted: {munch.unmunchify(action_taken.action_type)}")

        for event in result.logs[0].events:
            if event.type == "create_pool":
                assert event.attributes[0].key == "pool_id"
                chain_pool_Id = event.attributes[0].value
                break

            else:
                raise RuntimeError("Did not find pool_id of the created pool")
    else:
        code = result["code"]
        msg = result["raw_log"]
        logging.info(f"\tFailure: (Code {code}) {msg}")

    if proc.stderr:
        logging.info(f"\tstderr: {proc.stderr.decode()}")


@step("join pool")
def join_pool(testnet: Testnet, state: Dict, action_taken):
    """
    Implements the effects of the step `join pool`
    on blockchain `testnet` and state `state`.
    It additionally has access to the model (trace) state variable `action_taken`.
    """

    # TODO: replace the logging stub with the effects of the action `join pool`
    logging.info("Step: join pool")
    # Tx Msg: osmosisd tx gamm join-pool --pool-id --max-amounts-in --share-amount-out --from --chain-id


@step("exit pool")
def exit_pool(testnet: Testnet, state: Dict, action_taken):
    """
    Implements the effects of the step `exit pool`
    on blockchain `testnet` and state `state`.
    It additionally has access to the model (trace) state variable `action_taken`.
    """

    # TODO: replace the logging stub with the effects of the action `exit pool`
    logging.info("Step: exit pool")
    # Tx Msg:
