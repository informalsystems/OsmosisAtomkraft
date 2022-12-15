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
    outcome: object from the trace which corresponds to the outcomes
            of the taken step
    home_dir: home directory of client binary
"""

import json
import logging
import os
import random
import string
import subprocess
from pathlib import Path
from subprocess import CompletedProcess
from typing import Dict, Optional

import munch
import pytest
from atomkraft.chain import Testnet
from atomkraft.chain.utils import TmEventSubscribe
from modelator.pytest.decorators import step

keypath = "action"


@pytest.fixture
def home_dir(tmp_path):
    return tmp_path / "osmosisd"


def map_string(i, size: int):
    r = random.Random(i)
    return "".join(r.choices(string.ascii_lowercase + string.digits, k=size))


def get_current_lp(testnet: Testnet, pool_id: int, home_dir: Path) -> Optional[Dict]:
    rpc_addr = testnet.get_validator_port(0, "rpc")
    args = (
        f"{testnet.binary} "
        "q gamm "
        f"pool {pool_id} "
        f"--home {home_dir} "
        f"--chain-id {testnet.chain_id} "
        f"--node {rpc_addr} "
        "--output json "
    ).split()
    proc = subprocess.run(args, capture_output=True, check=False)

    if proc.returncode:
        logging.warning("\t[Pool query error]: %s", proc.stderr.decode())
        return None

    return json.loads(proc.stdout.decode())


def get_user_balance(testnet: Testnet, user: str, home_dir: Path) -> Optional[Dict]:
    rpc_addr = testnet.get_validator_port(0, "rpc")

    args = (
        f"{testnet.binary} "
        f"keys show {user} -a "
        "--keyring-backend test "
        f"--home {home_dir} "
    ).split()

    addr = subprocess.check_output(args).decode().strip()

    args = (
        f"{testnet.binary} "
        f"q bank balances {addr} "
        f"--home {home_dir} "
        f"--chain-id {testnet.chain_id} "
        f"--node {rpc_addr} "
        "--output json "
    ).split()

    proc = subprocess.run(args, capture_output=True, check=False)

    if proc.returncode:
        logging.warning("\t[Bank query error]: %s", proc.stderr.decode())
        return None

    return json.loads(proc.stdout.decode())["balances"]


def log_current_lp(testnet: Testnet, pool_id: int, home_dir: Path) -> None:
    lp_data = get_current_lp(testnet, pool_id, home_dir)
    logging.info("\t[Pool status]: %s", lp_data["pool"])


def run_capture_output(cmd_string) -> CompletedProcess:
    logging.info("\t[Tx CMD]: %s", cmd_string)
    args = cmd_string.split()
    proc = subprocess.run(args, capture_output=True)
    return proc


@step("Genesis")
def init(testnet: Testnet, home_dir: Path, action):
    """
    Implements the effects of the step `Genesis`
    on blockchain `testnet` and state `state`.
    It additionally has access to the model (trace) state variable `action`.
    """
    logging.info("[Step]: init")

    testnet.set_accounts(action.value.keys())
    testnet.set_account_balances(action.value)
    testnet.verbose = True
    testnet.oneshot()
    # Tendermint event sybscriber
    with TmEventSubscribe({"tm.event": "NewBlock"}):
        logging.info("\t[Status]: Testnet launched...\n")

    # initialize accounts for client binary
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


@step("CreatePool")
def create_pool(testnet: Testnet, home_dir: Path, action, outcome, pools):
    """
    Implements the effects of the step `CreatePool`
    on blockchain `testnet` and state `state`.
    It additionally has access to the model (trace) state variable `action`, `outcome`, `pools`.
    """

    # TX Msg: osmosisd tx gamm create-pool --pool-file [config-file] --from WALLET_NAME --chain-id osmosis-1
    # file should be saved in pool-files directory by the name of pool_INV_NUM
    pool_file_location = home_dir / "pool-files"
    pool_file_location.mkdir(exist_ok=True, parents=True)
    pool_file_name = "pool-file-config.json"
    logging.info("[Step]: create pool")

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
    # future-governor are now predefined, but maybe values should also be parsed form TLA spec

    pool_config = {
        "weights": ",".join(f"{a}{d}" for (d, a) in action.value.weights.items()),
        "initial-deposit": ",".join(
            f"{a}{d}" for (d, a) in action.value.amounts.items()
        ),
        "swap-fee": "0.00",
        "exit-fee": "0.00",
        "future-governor": "",
    }

    # Writing to .json
    pool_conf_json_file = os.path.join(pool_file_location, pool_file_name)
    with open(pool_conf_json_file, "w") as outfile:
        json.dump(pool_config, outfile, indent=4)

    logging.info(munch.unmunchify(action))
    logging.info(munch.unmunchify(outcome))

    sender_id = action.value.sender

    rpc_addr = testnet.get_validator_port(0, "rpc")

    proc = run_capture_output(
        f"{testnet.binary} "
        "tx gamm "
        "create-pool "
        f"--pool-file {pool_conf_json_file} "
        f"--from {sender_id} "
        "--broadcast-mode block "
        "--gas 500000 "
        "-y "
        "--keyring-backend test "
        f"--home {home_dir} "
        f"--chain-id {testnet.chain_id} "
        f"--node {rpc_addr} "
        "--output json "
    )

    if proc.returncode:
        logging.error(f"\t[CLI Error]: {proc.stderr.decode()}")
    else:
        result = None
        if proc.stdout:
            result = munch.munchify(json.loads(proc.stdout.decode()))

        if result is None:
            logging.warning("\t[CLI Error]: No response!!")
        elif result.code == 0:
            # logging.info("\t[Tx status]: Success")
            for event in result.logs[0].events:
                if event.type == "pool_created":
                    assert event.attributes[0].key == "pool_id"
                    assert int(event.attributes[0].value) == outcome.value.id
                    break
            else:
                raise RuntimeError("Did not find pool_id of the created pool")
            log_current_lp(testnet, outcome.value.id, home_dir)
            logging.info(munch.unmunchify(pools[outcome.value.id - 1]))
        else:
            code = result.code
            msg = result.raw_log
            logging.error("\t(Code %s) %s", code, msg)


@step("JoinPool")
def join_pool(testnet: Testnet, home_dir: Path, action, outcome, pools):
    """
    Implements the effects of the step `JoinPool`
    on blockchain `testnet` and state `state`.
    It additionally has access to the model (trace) state variable `action`, `outcome`, `pools`.
    """

    logging.info("[Step]: join pool")
    # Tx Msg: osmosisd tx gamm join-pool --pool-id --max-amounts-in --share-amount-out --from --chain-id
    # osmosisd tx gamm join-swap-extern-amount-in [token-in] [share-out-min-amount]
    logging.info(munch.unmunchify(action))
    logging.info(munch.unmunchify(outcome))

    # create transaction and send it to nodes rpc port
    rpc_addr = testnet.get_validator_port(0, "rpc")

    lp_data = get_current_lp(testnet, action.value.id, home_dir)

    if lp_data:
        amounts = " ".join(
            f"--max-amounts-in {a}{d}" for (d, a) in outcome.value.deltas.items()
        )

        proc = run_capture_output(
            f"{testnet.binary} "
            "tx gamm "
            "join-pool "
            f"{amounts} "
            f"--share-amount-out {action.value.share} "
            f"--pool-id {action.value.id} "
            f"--from {action.value.sender} "
            "--broadcast-mode block "
            "--gas 500000 "
            "-y "
            "--keyring-backend test "
            f"--home {home_dir} "
            f"--chain-id {testnet.chain_id} "
            f"--node {rpc_addr} "
            "--output json "
        )

        if proc.returncode:
            logging.error(f"\t[CLI Error]: {proc.stderr.decode()}")
        else:
            result = None
            if proc.stdout:
                result = munch.munchify(json.loads(proc.stdout.decode()))

            if result is None:
                logging.warning("\t[CLI]: No response!!")
            elif result.code == 0:
                # logging.info("\t[CLI status]: Success")
                log_current_lp(testnet, action.value.id, home_dir)
                logging.info(munch.unmunchify(pools[action.value.id - 1]))
            else:
                code = result.code
                msg = result.raw_log
                logging.error(f"\t(Code %s) %s", code, msg)


@step("ExitPool")
def exit_pool(testnet: Testnet, home_dir: Path, action, outcome, pools):
    """
    Implements the effects of the step `ExitPool`
    on blockchain `testnet` and state `state`.
    It additionally has access to the model (trace) state variable `action`, `outcome`, `pools`.
    """

    logging.info("[Step]: exit pool")
    # Tx Msg:
    # osmosisd tx gamm exit-swap-extern-amount-out [token-out] [share-in-max-amount] [flags]
    logging.info(munch.unmunchify(action))
    logging.info(munch.unmunchify(outcome))

    rpc_addr = testnet.get_validator_port(0, "rpc")

    lp_data = get_current_lp(testnet, action.value.id, home_dir)

    if lp_data:
        # deltas are negative for exit pool
        amounts = " ".join(
            f"--min-amounts-out {abs(a)}{d}" for (d, a) in outcome.value.deltas.items()
        )

        proc = run_capture_output(
            f"{testnet.binary} "
            "tx gamm "
            "exit-pool "
            f"{amounts} "
            f"--share-amount-in {action.value.share} "
            f"--pool-id {action.value.id} "
            f"--from {action.value.sender} "
            "--broadcast-mode block "
            "--gas 500000 "
            "-y "
            "--keyring-backend test "
            f"--home {home_dir} "
            f"--chain-id {testnet.chain_id} "
            f"--node {rpc_addr} "
            "--output json "
        )

        if proc.returncode:
            logging.error(f"\t[CLI error]: {proc.stderr.decode()}")
        else:
            result = None
            if proc.stdout:
                result = munch.munchify(json.loads(proc.stdout.decode()))

            if result is None:
                logging.warning("\t[CLI]: No response!!")
            elif result.code == 0:
                # logging.info("\t[CLI Status]: Success")
                log_current_lp(testnet, action.value.id, home_dir)
                logging.info(munch.unmunchify(pools[action.value.id - 1]))
            else:
                code = result.code
                msg = result.raw_log
                logging.error("\t(Code %s) %s", code, msg)


@step("SwapInAmount")
def swap_in_amount(testnet: Testnet, home_dir: Path, action, outcome, pools):
    """
    Implements the effects of the step `SwapInAmount`
    on blockchain `testnet` and state `state`.
    It additionally has access to the model (trace) state variable `action`, `outcome`, `pools`.
    """

    logging.info("[Step]: swap in amount")
    # Tx Msg:
    # osmosisd tx gamm swap-exact-amount-in [token-in] [token-out-min-amount] [flags]
    logging.info(
        "Old balance of %s: %s",
        action.value.sender,
        get_user_balance(testnet, action.value.sender, home_dir),
    )
    logging.info(munch.unmunchify(action))
    logging.info(munch.unmunchify(outcome))

    rpc_addr = testnet.get_validator_port(0, "rpc")

    lp_data = get_current_lp(testnet, action.value.id, home_dir)

    # denom out delta is negative
    amount_out = -outcome.value.deltas[action.value.denom_out]

    assert amount_out >= 0

    if lp_data:
        proc = run_capture_output(
            f"{testnet.binary} "
            "tx gamm "
            "swap-exact-amount-in "
            f"{action.value.amount_in}{action.value.denom_in} "
            f"{amount_out} "
            f"--swap-route-pool-ids {action.value.id} "
            f"--swap-route-denoms {action.value.denom_out} "
            f"--from {action.value.sender} "
            "--broadcast-mode block "
            "--gas 500000 "
            "-y "
            "--keyring-backend test "
            f"--home {home_dir} "
            f"--chain-id {testnet.chain_id} "
            f"--node {rpc_addr} "
            "--output json "
        )

        if proc.returncode:
            logging.error(f"\t[CLI Error]: {proc.stderr.decode()}")
        else:
            result = None
            if proc.stdout:
                result = munch.munchify(json.loads(proc.stdout.decode()))

            if result is None:
                logging.warning("\t[CLI]: No response!!")
            elif result.code == 0:
                # logging.info("\t[CLI Status]: Success")
                log_current_lp(testnet, action.value.id, home_dir)
                logging.info(munch.unmunchify(pools[action.value.id - 1]))
                logging.info(
                    "New balance of %s: %s",
                    action.value.sender,
                    get_user_balance(testnet, action.value.sender, home_dir),
                )
            else:
                code = result.code
                msg = result.raw_log
                logging.error("\t(Code %s) %s", code, msg)


@step("SwapOutAmount")
def swap_out_amount(testnet: Testnet, home_dir: Path, action, outcome, pools):
    """
    Implements the effects of the step `SwapOutAmount`
    on blockchain `testnet` and state `state`.
    It additionally has access to the model (trace) state variable `action`, `outcome`, `pools`.
    """

    logging.info("[Step]: swap out amount")
    # Tx Msg:
    # osmosisd tx gamm swap-exact-amount-out [token-out] [token-in-max-amount] [flags]
    logging.info(
        "Old balance of %s: %s",
        action.value.sender,
        get_user_balance(testnet, action.value.sender, home_dir),
    )
    logging.info(munch.unmunchify(action))
    logging.info(munch.unmunchify(outcome))

    rpc_addr = testnet.get_validator_port(0, "rpc")

    lp_data = get_current_lp(testnet, action.value.id, home_dir)

    amount_in = outcome.value.deltas[action.value.denom_in]

    assert amount_in >= 0

    if lp_data:
        proc = run_capture_output(
            f"{testnet.binary} "
            "tx gamm "
            "swap-exact-amount-out "
            f"{action.value.amount_out}{action.value.denom_out} "
            f"{amount_in} "
            f"--swap-route-pool-ids {action.value.id} "
            f"--swap-route-denoms {action.value.denom_in} "
            f"--from {action.value.sender} "
            "--broadcast-mode block "
            "--gas 500000 "
            "-y "
            "--keyring-backend test "
            f"--home {home_dir} "
            f"--chain-id {testnet.chain_id} "
            f"--node {rpc_addr} "
            "--output json "
        )

        if proc.returncode:
            logging.error(f"\t[CLI Error]: {proc.stderr.decode()}")
        else:
            result = None
            if proc.stdout:
                result = munch.munchify(json.loads(proc.stdout.decode()))

            if result is None:
                logging.warning("\t[CLI]: No response!!")
            elif result.code == 0:
                # logging.info("\t[CLI status]: Success")
                log_current_lp(testnet, action.value.id, home_dir)
                logging.info(munch.unmunchify(pools[action.value.id - 1]))
                logging.info(
                    "New balance of %s: %s",
                    action.value.sender,
                    get_user_balance(testnet, action.value.sender, home_dir),
                )
            else:
                code = result.code
                msg = result.raw_log
                logging.error("\t(Code %s) %s", code, msg)


@step("ExitAndSwapAmount")
def exit_and_swap_pool(testnet: Testnet, home_dir: Path, action, outcome, pools):
    """
    Implements the effects of the step `ExitAndSwapAmount`
    on blockchain `testnet` and state `state`.
    It additionally has access to the model (trace) state variable `action`, `outcome`, `pools`.
    """

    logging.info("Step: exit and swap")
    # Tx Msg:
    # osmosisd tx gamm exit-swap-share-amount-in [token-out-denom] [share-in-amount] [token-out-min-amount] [flags]
    logging.info(
        "Old balance of %s: %s",
        action.value.sender,
        get_user_balance(testnet, action.value.sender, home_dir),
    )
    logging.info(munch.unmunchify(action))
    logging.info(munch.unmunchify(outcome))

    rpc_addr = testnet.get_validator_port(0, "rpc")

    lp_data = get_current_lp(testnet, action.value.id, home_dir)

    amount_out = -outcome.value.deltas[action.value.denom_out]

    assert amount_out >= 0

    if lp_data:
        proc = run_capture_output(
            f"{testnet.binary} "
            "tx gamm "
            "exit-swap-share-amount-in "
            f"{action.value.denom_out} "
            f"{action.value.share} "
            f"{amount_out} "
            f"--pool-id {action.value.id} "
            f"--from {action.value.sender} "
            "--broadcast-mode block "
            "--gas 500000 "
            "-y "
            "--keyring-backend test "
            f"--home {home_dir} "
            f"--chain-id {testnet.chain_id} "
            f"--node {rpc_addr} "
            "--output json "
        )

        if proc.returncode:
            logging.error(f"\t[CLI Error]: {proc.stderr.decode()}")
        else:
            result = None
            if proc.stdout:
                result = munch.munchify(json.loads(proc.stdout.decode()))

            if result is None:
                logging.warning("\t[CLI]: No response!!")
            elif result.code == 0:
                # logging.info("\t[CLI Status]: Success")
                log_current_lp(testnet, action.value.id, home_dir)
                logging.info(munch.unmunchify(pools[action.value.id - 1]))
                logging.info(
                    "New balance of %s: %s",
                    action.value.sender,
                    get_user_balance(testnet, action.value.sender, home_dir),
                )
            else:
                code = result.code
                msg = result.raw_log
                logging.error("\t(Code %s) %s", code, msg)
