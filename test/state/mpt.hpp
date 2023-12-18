// evmone: Fast Ethereum Virtual Machine implementation
// Copyright 2022 The evmone Authors.
// SPDX-License-Identifier: Apache-2.0
#pragma once

#include "hash_utils.hpp"
#include <memory>

namespace evmone::state
{
constexpr auto emptyMPTHash =
    0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421_bytes32;

/// Insert-only Merkle Patricia Trie implementation for getting the root hash
/// out of (key, value) pairs.
///
/// Limitations:
/// 1. The keys must not be longer than 32 bytes.
/// 2. A key must not be a prefix of another key.
///    This comes from the spec (Yellow Paper Appendix D) - a branch node cannot store a value.
/// 3. Inserted values cannot be updated (by inserting the same key again).
/// 4. Inserted values cannot be erased.
class MPT
{
    std::unique_ptr<class MPTNode> m_root;

public:
    MPT() noexcept;
    ~MPT() noexcept;

    void insert(bytes_view key, bytes&& value);

    [[nodiscard]] hash256 hash() const;
};

}  // namespace evmone::state
