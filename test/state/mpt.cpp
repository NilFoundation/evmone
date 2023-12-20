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
enum class Kind : uint8_t
{
    leaf,
    ext,
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
        const auto is_even = length % 2 == 0;
        bytes bs{static_cast<uint8_t>(
            (is_even ? 0x00 : (0x10 | nibbles[0])) | (kind == Kind::leaf ? 0x20 : 0x00))};
        for (size_t i = is_even ? 0 : 1; i < length; i += 2)
            bs.push_back(static_cast<uint8_t>((nibbles[i] << 4) | nibbles[i + 1]));
        return bs;
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

    /// Creates an extended node.
    static MPTNode ext(const Path& path, std::unique_ptr<MPTNode> child) noexcept
    {
        assert(child->m_kind == Kind::branch);
        MPTNode node{Kind::ext, path};
        node.m_children[0] = std::move(child);
        return node;
    }

    /// Optionally wraps the child node with newly created extended node in case
    /// the provided path is not empty.
    static std::unique_ptr<MPTNode> optional_ext(
        const Path& path, std::unique_ptr<MPTNode> child) noexcept
    {
        return (path.length != 0) ? std::make_unique<MPTNode>(ext(path, std::move(child))) :
                                    std::move(child);
    }

    /// Creates a branch node out of two children and optionally extends it with an extended
    /// node in case the path is not empty.
    static MPTNode ext_branch(const Path& path, size_t idx1, std::unique_ptr<MPTNode> child1,
        size_t idx2, std::unique_ptr<MPTNode> child2) noexcept
    {
        assert(idx1 != idx2);
        assert(idx1 < num_children);
        assert(idx2 < num_children);

        MPTNode br{Kind::branch};
        br.m_children[idx1] = std::move(child1);
        br.m_children[idx2] = std::move(child2);

        return (path.length != 0) ? ext(path, std::make_unique<MPTNode>(std::move(br))) :
                                    std::move(br);
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
    // (possibly with an adjusted extended node) and transform existing nodes around it.

    const auto [common, this_idx, insert_idx, this_tail, insert_tail] = mismatch(m_path, path);

    switch (m_kind)
    {
    case Kind::branch:
    {
        assert(m_path.length == 0);  // Branch has no path.
        if (auto& child = m_children[insert_idx]; child)
            child->insert(insert_tail, std::move(value));
        else
            child = leaf(insert_tail, std::move(value));
        break;
    }

    case Kind::ext:
    {
        assert(m_path.length != 0);          // Ext must have non-empty path.
        if (common.length == m_path.length)  // Paths match: go into the child.
            return m_children[0]->insert(path.tail(common.length), std::move(value));

        // The original branch node must be pushed down, possible extended with
        // the adjusted extended node if the path split point is not directly at the branch node.
        // Clang Analyzer bug: https://github.com/llvm/llvm-project/issues/47814
        // NOLINTNEXTLINE(clang-analyzer-cplusplus.NewDeleteLeaks)
        auto this_branch = optional_ext(this_tail, std::move(m_children[0]));
        auto new_leaf = leaf(insert_tail, std::move(value));
        *this =
            ext_branch(common, this_idx, std::move(this_branch), insert_idx, std::move(new_leaf));
        break;
    }

    case Kind::leaf:
    {
        assert(m_path.length != 0);              // Leaf must have non-empty path.
        assert(common.length != m_path.length);  // Paths must be different.
        auto this_leaf = leaf(this_tail, std::move(m_value));
        auto new_leaf = leaf(insert_tail, std::move(value));
        *this = ext_branch(common, this_idx, std::move(this_leaf), insert_idx, std::move(new_leaf));
        break;
    }

    default:
        assert(false);
    }
}

/// Encodes a node and optionally hashes the encoded bytes
/// if their length exceeds the specified threshold.
static bytes encode_child(const MPTNode& child) noexcept  // NOLINT(misc-no-recursion)
{
    if (auto e = child.encode(); e.size() < 32)
        return e;  // "short" node
    else
        return rlp::encode(keccak256(e));
}

bytes MPTNode::encode() const  // NOLINT(misc-no-recursion)
{
    bytes encoded;
    switch (m_kind)
    {
    case Kind::leaf:
    {
        encoded = rlp::encode(m_path.encode(m_kind)) + rlp::encode(m_value);
        break;
    }
    case Kind::branch:
    {
        assert(m_path.length == 0);
        static constexpr uint8_t empty = 0x80;  // encoded empty child

        for (const auto& child : m_children)
        {
            if (child)
                encoded += encode_child(*child);
            else
                encoded += empty;
        }
        encoded += empty;  // end indicator
        break;
    }
    case Kind::ext:
    {
        encoded = rlp::encode(m_path.encode(m_kind)) + encode_child(*m_children[0]);
        break;
    }
    }

    return rlp::internal::wrap_list(encoded);
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
