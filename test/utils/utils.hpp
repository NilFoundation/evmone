// evmone: Fast Ethereum Virtual Machine implementation
// Copyright 2018 The evmone Authors.
// SPDX-License-Identifier: Apache-2.0
#pragma once

#include <evmc/evmc.hpp>
#include <evmc/hex.hpp>

using evmc::bytes;
using evmc::bytes_view;
using evmc::from_hex;
using evmc::from_spaced_hex;
using evmc::hex;

namespace evmone::test
{
/// The EVM revision schedule based on timestamps.
struct RevisionSchedule
{
    /// The revision of the first block.
    evmc_revision genesis_rev = EVMC_FRONTIER;

    /// The final revision to transition to.
    evmc_revision final_rev = genesis_rev;

    /// The timestamp of the transition to the final revision.
    int64_t transition_time = 0;

    /// Returns the specific revision for the given timestamp.
    [[nodiscard]] evmc_revision get_revision(int64_t timestamp) const noexcept
    {
        return timestamp >= transition_time ? final_rev : genesis_rev;
    }
};

/// Translates tests fork name to EVM revision
evmc_revision to_rev(std::string_view s);

/// Translates tests fork name to the EVM revision schedule.
RevisionSchedule to_rev_schedule(std::string_view s);

}  // namespace evmone::test

/// Converts a string to bytes by casting individual characters.
inline bytes to_bytes(std::string_view s)
{
    return {s.begin(), s.end()};
}

/// Produces bytes out of string literal.
inline bytes operator""_b(const char* data, size_t size)
{
    return to_bytes({data, size});
}

inline bytes operator""_hex(const char* s, size_t size)
{
    return from_spaced_hex({s, size}).value();
}
