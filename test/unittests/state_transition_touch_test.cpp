// evmone: Fast Ethereum Virtual Machine implementation
// Copyright 2023 The evmone Authors.
// SPDX-License-Identifier: Apache-2.0

#include "../utils/bytecode.hpp"
#include "state_transition.hpp"

using namespace evmc::literals;
using namespace evmone::test;

TEST_F(state_transition, touch_empty_sd)
{
    rev = EVMC_SPURIOUS_DRAGON;  // touching enabled
    static constexpr auto EMPTY = 0xee_address;

    tx.to = To;
    pre.insert(*tx.to, {.code = call(EMPTY)});
    pre.insert(EMPTY, {});

    expect.post[*tx.to].exists = true;
    expect.post[EMPTY].exists = false;
}
TEST_F(state_transition, touch_empty_tw)
{
    rev = EVMC_TANGERINE_WHISTLE;  // no touching
    static constexpr auto EMPTY = 0xee_address;

    tx.to = To;
    pre.insert(*tx.to, {.code = call(EMPTY)});
    pre.insert(EMPTY, {});

    expect.post[*tx.to].exists = true;
    expect.post[EMPTY].exists = true;
}

TEST_F(state_transition, touch_revert_empty)
{
    rev = EVMC_ISTANBUL;  // avoid handling account access (Berlin)
    static constexpr auto EMPTY = 0xee_address;

    tx.to = To;
    pre.insert(*tx.to, {.code = call(EMPTY) + revert(0, 0)});
    pre.insert(EMPTY, {});

    expect.status = EVMC_REVERT;
    expect.post[*tx.to].exists = true;
    expect.post[EMPTY].exists = true;
}

TEST_F(state_transition, touch_revert_nonexistent_istanbul)
{
    rev = EVMC_ISTANBUL;  // avoid handling account access (Berlin)
    static constexpr auto EMPTY = 0xee_address;

    tx.to = To;
    pre.insert(*tx.to, {.code = call(EMPTY) + revert(0, 0)});

    expect.status = EVMC_REVERT;
    expect.post[*tx.to].exists = true;
    expect.post[EMPTY].exists = false;
}

TEST_F(state_transition, touch_revert_nonexistent_tw)
{
    rev = EVMC_TANGERINE_WHISTLE;  // no touching
    static constexpr auto EMPTY = 0xee_address;

    tx.to = To;
    pre.insert(*tx.to, {.code = call(EMPTY) + OP_INVALID});

    expect.status = EVMC_INVALID_INSTRUCTION;
    expect.post[*tx.to].exists = true;
    expect.post[EMPTY].exists = false;
}
