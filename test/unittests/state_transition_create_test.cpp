// evmone: Fast Ethereum Virtual Machine implementation
// Copyright 2023 The evmone Authors.
// SPDX-License-Identifier: Apache-2.0

#include "../utils/bytecode.hpp"
#include "state_transition.hpp"

using namespace evmc::literals;
using namespace evmone::test;

TEST_F(state_transition, create2_factory)
{
    static constexpr auto create_address = 0xfd8e7707356349027a32d71eabc7cb0cf9d7cbb4_address;

    const auto factory_code =
        calldatacopy(0, 0, calldatasize()) + create2().input(0, calldatasize());
    const auto initcode = mstore8(0, push(0xFE)) + ret(0, 1);

    tx.to = To;
    tx.data = initcode;
    pre.insert(*tx.to, {.nonce = 1, .code = factory_code});

    expect.post[*tx.to].nonce = pre.get(*tx.to).nonce + 1;  // CREATE caller's nonce must be bumped
    expect.post[create_address].code = bytes{0xFE};
}

TEST_F(state_transition, create_tx)
{
    static constexpr auto create_address = 0x3442a1dec1e72f337007125aa67221498cdd759d_address;

    tx.data = mstore8(0, push(0xFE)) + ret(0, 1);

    expect.post[create_address].code = bytes{0xFE};
}

TEST_F(state_transition, create2_max_nonce)
{
    // The address to be created by CREATE2 of the "To" sender and empty initcode.
    static constexpr auto create_address = 0x36fd63ce1cb5ee2993f19d1fae4e84d52f6f1595_address;

    tx.to = To;
    pre.insert(*tx.to, {.nonce = ~uint64_t{0}, .code = create2()});

    expect.post[*tx.to].nonce = pre.get(*tx.to).nonce;  // Nonce is unchanged.
    expect.post[create_address].exists = false;
}

TEST_F(state_transition, create_tx_collision)
{
    static constexpr auto CREATED = 0x3442a1dec1e72f337007125aa67221498cdd759d_address;

    pre.insert(CREATED, {.nonce = 2});

    expect.status = EVMC_FAILURE;
    expect.post[CREATED].nonce = 2;
}

TEST_F(state_transition, create_collision)
{
    static constexpr auto CREATED = 0x8bbc3514477d75ec797bbe4e19d7961660bb849c_address;

    tx.to = To;
    pre.insert(*tx.to, {.code = create()});
    pre.insert(CREATED, {.nonce = 2});

    expect.post[*tx.to].nonce = pre.get(*tx.to).nonce + 1;
    expect.post[CREATED].nonce = pre.get(CREATED).nonce;
}

TEST_F(state_transition, create_collision_revert)
{
    static constexpr auto CREATED = 0x8bbc3514477d75ec797bbe4e19d7961660bb849c_address;

    tx.to = To;
    pre.insert(*tx.to, {.code = create() + OP_INVALID});
    pre.insert(CREATED, {.nonce = 2});

    expect.status = EVMC_INVALID_INSTRUCTION;
    expect.post[*tx.to].nonce = pre.get(*tx.to).nonce;
    expect.post[CREATED].nonce = pre.get(CREATED).nonce;
}
