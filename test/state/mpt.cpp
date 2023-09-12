// evmone: Fast Ethereum Virtual Machine implementation
// Copyright 2022 The evmone Authors.
// SPDX-License-Identifier: Apache-2.0

#include "mpt.hpp"
#include "rlp.hpp"
#include <algorithm>
#include <cassert>

namespace evmone::state
{
namespace
{
/// The MPT node kind.
enum class Kind : bool
{
    leaf,
    branch
};

/// The collection of nibbles (4-bit values) representing a path in a MPT.
struct Path
{
    size_t length = 0;  // TODO: Can be converted to uint8_t.
    uint8_t nibbles[64]{};

    Path() = default;

    /// Constructs a sub-path by copying nibbles from existing path.
    Path(size_t len, const uint8_t* nibs) noexcept : length{len}
    {
        std::copy_n(nibs, length, nibbles);
    }

    /// Constructs a path from bytes - each byte will produce 2 nibbles in the path.
    explicit Path(bytes_view key) noexcept : length{2 * key.size()}
    {
        assert(length <= std::size(nibbles));
        size_t i = 0;
        for (const auto b : key)
        {
            nibbles[i++] = b >> 4;
            nibbles[i++] = b & 0x0f;
        }
    }

    [[nodiscard]] Path tail(size_t pos) const noexcept
    {
        assert(pos > 0 && pos <= length);  // MPT never requests whole path copy (pos == 0).
        return {length - pos, &nibbles[pos]};
    }

    [[nodiscard]] bytes encode(Kind kind) const
    {
        if (kind == Kind::branch && length == 0)
            return {};

        const auto is_even = length % 2 == 0;
        bytes bs{static_cast<uint8_t>(
            (is_even ? 0x00 : (0x10 | nibbles[0])) | (kind == Kind::leaf ? 0x20 : 0x00))};
        for (size_t i = is_even ? 0 : 1; i < length; i += 2)
            bs.push_back(static_cast<uint8_t>((nibbles[i] << 4) | nibbles[i + 1]));
        return rlp::encode(bs);
    }
};
}  // namespace

/// The MPT Node.
///
/// The implementation is based on StackTrie from go-ethereum.
// TODO(clang-tidy-17): bug https://github.com/llvm/llvm-project/issues/50006
// NOLINTNEXTLINE(bugprone-reserved-identifier)
class MPTNode
{
    static constexpr size_t num_children = 16;

    Kind m_kind = Kind::leaf;
    Path m_path;
    bytes m_value;
    std::unique_ptr<MPTNode> m_children[num_children];

    explicit MPTNode(Kind kind, const Path& path = {}, bytes&& value = {}) noexcept
      : m_kind{kind}, m_path{path}, m_value{std::move(value)}
    {}

    /// Creates a branch node out of two children and optionally extends it with an extended
    /// node in case the path is not empty.
    static MPTNode branch(const Path& path, size_t idx1, std::unique_ptr<MPTNode> child1,
        size_t idx2, std::unique_ptr<MPTNode> child2) noexcept
    {
        assert(idx1 != idx2);
        assert(idx1 < num_children);
        assert(idx2 < num_children);

        MPTNode br{Kind::branch, path};
        br.m_children[idx1] = std::move(child1);
        br.m_children[idx2] = std::move(child2);
        return br;
    }

    /// The information how two paths are different.
    struct MismatchResult
    {
        static constexpr uint8_t invalid = 0xff;

        Path common;                ///< Common prefix.
        uint8_t nibble1 = invalid;  ///< Mismatched nibble in path 1. Invalid if paths match.
        uint8_t nibble2 = invalid;  ///< Mismatched nibble in second path.
        Path tail1;                 ///< Remaining tail after the nibble in path 1.
        Path tail2;                 ///< Remaining tail after the nibble in path 2.
    };

    /// Finds the difference between two paths.
    static MismatchResult mismatch(const Path& p1, const Path& p2) noexcept
    {
        assert(p1.length <= p2.length);  // no support for inserting keys of different lengths
        const auto [it1, it2] = std::mismatch(p1.nibbles, p1.nibbles + p1.length, p2.nibbles);

        const Path common{static_cast<size_t>(it1 - p1.nibbles), p1.nibbles};
        const auto matched = common.length == p1.length;
        const auto tail_start = common.length + 1;
        assert(!matched || p1.length != p2.length);  // matched => paths have different lengths
        assert(matched || tail_start <= p1.length);  // !matched => tail_start is valid

        return {
            .common = common,
            .nibble1 = static_cast<uint8_t>(matched ? MismatchResult::invalid : *it1),
            .nibble2 = *it2,
            .tail1 = matched ? Path{} : p1.tail(tail_start),
            .tail2 = p2.tail(tail_start),
        };
    }

public:
    MPTNode() = default;

    /// Creates new leaf node.
    static std::unique_ptr<MPTNode> leaf(const Path& path, bytes&& value) noexcept
    {
        return std::make_unique<MPTNode>(MPTNode{Kind::leaf, path, std::move(value)});
    }

    void insert(const Path& path, bytes&& value);

    [[nodiscard]] bytes encode() const;
};

void MPTNode::insert(const Path& path, bytes&& value)  // NOLINT(misc-no-recursion)
{
    // The insertion is all about branch nodes. In happy case we will find an empty slot
    // in an existing branch node. Otherwise, we need to create new branch node
    // (possibly with an extended path) and transform existing nodes around it.

    // Let's consider the following branch node with extended path "ab".
    //
    //     |
    //     |a ↙③
    //     |b
    //     |
    // [a|b|c|d]
    //  |     ②
    //  ①
    //
    // If the insert path prefix matches the "ab" we insert to one of the children:
    // - e.g. for "aba" insert into existing child ①,
    // - e.g. for "abd" create new leaf node ②.
    // If the insert path prefix doesn't match "ab" we split the extended path by
    // a new branch node of the "this" branch node and a new leaf node.
    // E.g. for "acd" insert new branch node "a" at ③ with:
    // - at "b" : the "this" branch node with empty extended path "",
    // - at "c" : the new leaf node with path "d".

    const auto [common, this_idx, insert_idx, this_tail, insert_tail] = mismatch(m_path, path);

    if (m_kind == Kind::branch && common.length == m_path.length)  // Go into the child.
    {
        if (auto& child = m_children[insert_idx]; child)
            child->insert(insert_tail, std::move(value));  // ①
        else
            child = leaf(insert_tail, std::move(value));  // ②
    }
    else  // ③: Shorten path of this node and insert it to the new branch node.
    {
        m_path = this_tail;
        *this = branch(common, this_idx, std::make_unique<MPTNode>(std::move(*this)), insert_idx,
            leaf(insert_tail, std::move(value)));
    }
}


bytes MPTNode::encode() const  // NOLINT(misc-no-recursion)
{
    static constexpr auto shorten = [](bytes&& b) {
        return (b.size() < 32) ? std::move(b) : rlp::encode(keccak256(b));
    };

    bytes payload;  // the encoded content of the node without its path
    switch (m_kind)
    {
    case Kind::leaf:
    {
        payload = rlp::encode(m_value);
        break;
    }
    case Kind::branch:
    {
        static constexpr uint8_t empty = 0x80;  // encoded empty child

        for (const auto& child : m_children)
            payload += child ? shorten(child->encode()) : bytes{empty};
        payload += empty;  // end indicator

        if (m_path.length != 0)  // extended node
            payload = shorten(rlp::internal::wrap_list(payload));
        break;
    }
    }
    return rlp::internal::wrap_list(m_path.encode(m_kind) + payload);
}


MPT::MPT() noexcept = default;
MPT::~MPT() noexcept = default;

void MPT::insert(bytes_view key, bytes&& value)
{
    if (m_root == nullptr)
        m_root = MPTNode::leaf(Path{key}, std::move(value));
    else
        m_root->insert(Path{key}, std::move(value));
}

[[nodiscard]] hash256 MPT::hash() const
{
    if (m_root == nullptr)
        return emptyMPTHash;
    return keccak256(m_root->encode());
}

}  // namespace evmone::state
