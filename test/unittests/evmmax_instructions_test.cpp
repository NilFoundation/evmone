// evmone: Fast Ethereum Virtual Machine implementation
// Copyright 2023 The evmone Authors.
// SPDX-License-Identifier: Apache-2.0

#include "evm_fixture.hpp"
#include <evmmax/evmmax.hpp>
#include <gtest/gtest.h>
#include <array>

using namespace intx;
using namespace evmmax;
using evmone::test::evm;

TEST_P(evm, evmmax_32bytes_modulus_test)
{
    if (is_advanced())
        return;

    rev = EVMC_PRAGUE;  /// TODO: Use EVMC_EVMMAX
    // Modulus == 7
    auto code = mstore(0, 0x07);
    // 3 values slots
    // Modulus size in bytes
    // Modulus offset in EVM memory
    // Modulus ID
    code += setupx(3, 32, 0, 1);
    // value 3
    code += mstore(32, 0x03);
    // value 6
    code += mstore(64, 0x06);
    // num values
    // values offset
    // store values
    code += storex(2, 32, 0);
    // ADDMODX for values in slots 0 and 1 save result in slot 2
    code += addmodx(2, 1, 0);
    // MULMODX for values in slots 1 and 2 save result in slot 2
    code += mulmodx(2, 2, 1);
    // SUBMODX for values in slots 1 and 2 save result in slot 2
    code += submodx(2, 2, 1);
    // load values from slot 2 into EVM memory
    code += loadx(1, 2, 96);
    // return loaded result
    code += ret(96, 32);

    execute(1000, code);
    EXPECT_EQ(result.status_code, EVMC_SUCCESS);
    EXPECT_OUTPUT_INT(6);
}

TEST_P(evm, evmmax_1byte_modulus_test)
{
    if (is_advanced())
        return;

    rev = EVMC_PRAGUE;  /// TODO: Use EVMC_EVMMAX
    // Modulus == 7
    auto code = mstore8(0, 0x07);
    // 3 values slots
    // Modulus size in bytes
    // Modulus offset in EVM memory
    // Modulus ID
    code += setupx(3, 1, 0, 1);
    // value 3
    code += mstore8(8, 0x03);
    // value 6
    code += mstore8(16, 0x06);
    // num values
    // values offset
    // store values
    code += storex(2, 1, 0);
    // ADDMODX for values in slots 0 and 1 save result in slot 2
    code += addmodx(2, 1, 0);
    // MULMODX for values in slots 1 and 2 save result in slot 2
    code += mulmodx(2, 2, 1);
    // SUBMODX for values in slots 1 and 2 save result in slot 2
    code += submodx(2, 2, 1);
    // load values from slot 2 into EVM memory
    code += loadx(1, 2, 17);
    // return loaded result
    code += ret(17, 8);

    execute(1000, code);
    EXPECT_EQ(result.status_code, EVMC_SUCCESS);

    ASSERT_EQ(result.output_size, 8);
    EXPECT_EQ(hex({result.output_data, result.output_size}), "0000000000000006");
}

TEST_P(evm, evmmax_2byte_modulus_test)
{
    if (is_advanced())
        return;

    rev = EVMC_PRAGUE;  /// TODO: Use EVMC_EVMMAX
    // Modulus == 263 (0x0107)
    auto code = mstore8(0, 0x01);
    code += mstore8(1, 0x07);
    // 3 values slots
    // Modulus size in bytes
    // Modulus offset in EVM memory
    // Modulus ID
    code += setupx(3, 2, 0, 1);
    // value 258
    code += mstore8(8, 0x01);
    code += mstore8(9, 0x02);
    // value 254
    code += mstore8(16, 0x00);
    code += mstore8(17, 0xfe);
    // num values
    // values offset
    // store values
    code += storex(2, 2, 0);
    // ADDMODX for values in slots 0 and 1 save result in slot 2
    code += addmodx(2, 1, 0);  // 258 + 254 = 249 mod 263
    // MULMODX for values in slots 1 and 2 save result in slot 2
    code += mulmodx(2, 2, 1);  // 249 * 254 = 126 mod 263
    // SUBMODX for values in slots 1 and 2 save result in slot 2
    code += submodx(2, 2, 1);  // 126 - 254 = 135 mod 263
    // load values from slot 2 into EVM memory
    code += loadx(1, 2, 18);
    // return loaded result
    code += ret(18, 8);

    execute(1000, code);
    EXPECT_EQ(result.status_code, EVMC_SUCCESS);

    ASSERT_EQ(result.output_size, 8);
    EXPECT_EQ(hex({result.output_data, result.output_size}), "0000000000000087");
}

namespace
{
struct SlotsScope;

struct ValueSlotsRegister
{
private:
    friend struct SlotsScope;

    std::vector<bool> vals;

    [[nodiscard]] uint8_t register_slot() noexcept
    {
        if (const auto it = std::find(vals.begin(), vals.end(), false); it != vals.end())
        {
            *it = true;
            return static_cast<uint8_t>(std::distance(vals.begin(), it));
        }
        else
        {
            assert(vals.size() < 256);
            vals.push_back(true);
            return static_cast<uint8_t>(vals.size() - 1);
        }
    }

    void unregister_slot(uint8_t slot_idx) noexcept
    {
        if (slot_idx < vals.size())
            vals[slot_idx] = false;
        else
            assert(false);  // Invalid slot idx
    }

public:
    // Convention. O slot keeps 0; Never write to it.
    explicit ValueSlotsRegister() noexcept { (void)register_slot(); }
    [[nodiscard]] uint8_t max_slots_used() const { return static_cast<uint8_t>(vals.size()); }
};

struct SlotsScope
{
private:
    std::set<uint8_t> slots;
    ValueSlotsRegister& value_slots_register;

public:
    explicit SlotsScope(ValueSlotsRegister& vs_reg) noexcept : value_slots_register(vs_reg) {}
    explicit SlotsScope(SlotsScope& outer_scope) noexcept
      : value_slots_register(outer_scope.value_slots_register)
    {}

    [[nodiscard]] uint8_t register_slot() noexcept
    {
        const auto new_slot = value_slots_register.register_slot();
        slots.insert(new_slot);
        return new_slot;
    }

    virtual ~SlotsScope() noexcept
    {
        for (const auto& slot : slots)
            value_slots_register.unregister_slot(slot);
    }
};

template <size_t NUM_VALUES>
[[nodiscard]] bytecode copy_values(
    const std::array<uint8_t, NUM_VALUES>& inputs, const std::array<uint8_t, NUM_VALUES>& outputs)
{
    // Slot 0 stores 0 value by convention.
    auto code = bytecode{};

    for (size_t i = 0; i < NUM_VALUES; ++i)
    {
        if (inputs[i] != outputs[i])
            code += addmodx(outputs[i], inputs[i], 0);
    }

    return code;
}

template <size_t NUM_INPUTS, size_t NUM_OUTPUTS>
struct EVMMAXFunction
{
    std::array<uint8_t, NUM_INPUTS> input_ids;
    std::array<uint8_t, NUM_OUTPUTS> output_ids;
    std::vector<size_t> func_offset_placeholders_start;

    using bytecode_gen_fn = void (*)(bytecode& code, SlotsScope& scope,
        const std::array<uint8_t, NUM_INPUTS>& inputs_ids,
        const std::array<uint8_t, NUM_OUTPUTS>& outputs_ids);

    bytecode_gen_fn gen_code_func;

    explicit EVMMAXFunction(SlotsScope& scope, bytecode_gen_fn bytecode_gen_func) noexcept
      : gen_code_func(bytecode_gen_func)
    {
        std::generate(
            input_ids.begin(), input_ids.end(), [&scope] { return scope.register_slot(); });

        std::generate(
            output_ids.begin(), output_ids.end(), [&scope] { return scope.register_slot(); });
    }

    bytecode gen_call(size_t call_offset_in_code) noexcept
    {
        auto code = bytecode{};

        // push return destination to the stack. `0xFFFF` is a placeholder to be filled later
        code += push(0xFFFF);
        const auto ret_offset_placeholder_start = code.size() - 2;
        // jump to beg of the function code. `0xFFFF` is a placeholder for function body offset in
        // the code
        code += push(0xFFFF) + OP_JUMP;
        const auto func_loc_placeholder_start_offset = code.size() - 3;
        // return destination
        const auto ret_destination_offset = code.size();
        code += bytecode(OP_JUMPDEST);

        // fill return destination placeholder
        intx::be::unsafe::store(&code[ret_offset_placeholder_start],
            static_cast<uint16_t>(call_offset_in_code + ret_destination_offset));

        func_offset_placeholders_start.push_back(
            call_offset_in_code + func_loc_placeholder_start_offset);
        return code;
    }

    void finalize(SlotsScope& scope, bytecode& code) const
    {
        const auto func_offset_in_code = code.size();
        assert(func_offset_in_code <= std::numeric_limits<uint16_t>::max());
        for (const auto& p_start : func_offset_placeholders_start)
        {
            if (p_start + 1 < code.size())
                intx::be::unsafe::store(&code[p_start], static_cast<uint16_t>(func_offset_in_code));
            else
                throw std::runtime_error("invalid code size");
        }

        code += bytecode(OP_JUMPDEST);
        // sanitizer error: "error: variable 's' of type 'SlotsScope' can be declared 'const'"
        SlotsScope s(scope);  // NOLINT(misc-const-correctness)
        gen_code_func(code, s, input_ids, output_ids);
        code += bytecode(OP_JUMP);
    }
};

constexpr auto BN254Mod = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47_u256;

void bn254_ecadd(bytecode& code, SlotsScope& scope, const std::array<uint8_t, 7>& inputs,
    const std::array<uint8_t, 3>& outputs);

void bn254_dbl(bytecode& code, SlotsScope& scope, const std::array<uint8_t, 4>& inputs,
    const std::array<uint8_t, 3>& outputs);

void bn254_ecmul(bytecode& code, SlotsScope& scope, const std::array<uint8_t, 4>& inputs,
    const std::array<uint8_t, 3>& outputs);

void field_inv_bn254(bytecode& code, SlotsScope& scope, const std::array<uint8_t, 1>& x_idx_arr,
    const std::array<uint8_t, 1>& dst_idx_arr);

}  // namespace

TEST_P(evm, exec_bn254_ecadd_test)
{
    using namespace evmone::test;

    if (evm::is_advanced())
        return;

    evm::rev = EVMC_PRAGUE;  /// TODO: Use EVMC_EVMMAX

    // vm.set_option("trace", "0");

    constexpr auto size = sizeof(uint256);

    const auto x1 = 0x0f25929bcb43d5a57391564615c9e70a992b10eafa4db109709649cf48c50dd2_u256;
    const auto y1 = 0x16da2f5cb6be7a0aa72c440c53c9bbdfec6c36c7d515536431b3a865468acbba_u256;
    const auto x2 = 0x1de49a4b0233273bba8146af82042d004f2085ec982397db0d97da17204cc286_u256;
    const auto y2 = 0x0217327ffc463919bef80cc166d09c6172639d8589799928761bcd9f22c903d4_u256;

    uint8_t calldata[6 * size];  // mod, x1, y1, x2, y2, b3
    intx::be::unsafe::store(&calldata[0], BN254Mod);
    intx::be::unsafe::store(&calldata[size], x1);
    intx::be::unsafe::store(&calldata[2 * size], y1);
    intx::be::unsafe::store(&calldata[3 * size], x2);
    intx::be::unsafe::store(&calldata[4 * size], y2);
    intx::be::unsafe::store(&calldata[5 * size], 9_u256);

    ValueSlotsRegister vs_reg;
    SlotsScope scope(vs_reg);
    (void)scope.register_slot();  // Convention. O slot keeps 0; Never write to it.

    const auto x3_idx = scope.register_slot();
    const auto y3_idx = scope.register_slot();
    const auto z3_idx = scope.register_slot();

    // Stores inputs in evm memory and `1` to load it as `z` coordinates of the inputs in projective
    // space
    auto code_init = calldatacopy(push(0), push(0), push(size * 6)) + mstore(size * 6, push(1));

    auto code = bytecode{};
    {
        SlotsScope scope1(vs_reg);
        const auto x1_idx = scope1.register_slot();
        const auto y1_idx = scope1.register_slot();
        const auto z1_idx = scope1.register_slot();
        const auto x2_idx = scope1.register_slot();
        const auto y2_idx = scope1.register_slot();
        const auto z2_idx = scope1.register_slot();
        const auto b3_idx = scope1.register_slot();

        code += storex(2, size, x1_idx) + storex(1, size * 6, z1_idx);  // [x1, y1, 1]
        code +=
            storex(2, size * 3, x2_idx) + storex(1, size * 6, z2_idx);  // [x1, y1, 1, x2, y2, 1]
        code += storex(1, size * 5, b3_idx);

        {
            SlotsScope s(vs_reg);
            bn254_ecadd(code, s, {x1_idx, y1_idx, z1_idx, x2_idx, y2_idx, z2_idx, b3_idx},
                {x3_idx, y3_idx, z3_idx});
        }
    }
    {
        SlotsScope scope2(vs_reg);
        const auto z_inv_idx = scope2.register_slot();

        {
            SlotsScope s(vs_reg);
            field_inv_bn254(code, s, {z3_idx}, {z_inv_idx});
        }

        code += mulmodx(x3_idx, x3_idx, z_inv_idx);
        code += mulmodx(y3_idx, y3_idx, z_inv_idx);
    }
    ////////////////////////////////////////////////////////

    code += loadx(2, x3_idx, size * 6);
    // return loaded result
    code += ret(size * 6, size * 2);

    execute(
        1000, code_init + setupx(vs_reg.max_slots_used(), size, 0, 1) + code, {calldata, size * 6});
    EXPECT_EQ(result.status_code, EVMC_SUCCESS);

    ASSERT_EQ(result.output_size, size * 2);
    EXPECT_EQ(hex({result.output_data, result.output_size}),
        "1f4d1d80177b1377743d1901f70d7389be7f7a35a35bfd234a8aaee615b88c49018683193ae021a2f8920fed18"
        "6cde5d9b1365116865281ccf884c1f28b1df8f");
}

TEST_P(evm, exec_bn254_ecadd_function_test)
{
    using namespace evmone::test;

    if (evm::is_advanced())
        return;

    evm::rev = EVMC_PRAGUE;  /// TODO: Use EVMC_EVMMAX

    // vm.set_option("trace", "0");

    constexpr auto size = sizeof(uint256);

    const auto x1 = 0x0f25929bcb43d5a57391564615c9e70a992b10eafa4db109709649cf48c50dd2_u256;
    const auto y1 = 0x16da2f5cb6be7a0aa72c440c53c9bbdfec6c36c7d515536431b3a865468acbba_u256;
    const auto x2 = 0x1de49a4b0233273bba8146af82042d004f2085ec982397db0d97da17204cc286_u256;
    const auto y2 = 0x0217327ffc463919bef80cc166d09c6172639d8589799928761bcd9f22c903d4_u256;

    uint8_t calldata[6 * size];  // mod, x1, y1, x2, y2, b3
    intx::be::unsafe::store(&calldata[0], BN254Mod);
    intx::be::unsafe::store(&calldata[size], x1);
    intx::be::unsafe::store(&calldata[2 * size], y1);
    intx::be::unsafe::store(&calldata[3 * size], x2);
    intx::be::unsafe::store(&calldata[4 * size], y2);
    intx::be::unsafe::store(&calldata[5 * size], 9_u256);

    ValueSlotsRegister vs_reg;
    SlotsScope scope(vs_reg);
    // Reserve slots to store calculated results in them.

    EVMMAXFunction<7, 3> bn254_ecadd_f(scope, bn254_ecadd);
    EVMMAXFunction<1, 1> field_inv_f(scope, field_inv_bn254);

    auto code = calldatacopy(push(0), push(0), push(size * 6)) + mstore(size * 6, push(1)) +
                setupx(0xFF, size, 0, 1);
    const auto num_slots_placeholder_start = code.size() - 8;

    code += storex(2, size, bn254_ecadd_f.input_ids[0]) +
            storex(1, size * 6, bn254_ecadd_f.input_ids[2]);  // [x1, y1, 1]
    code += storex(2, size * 3, bn254_ecadd_f.input_ids[3]) +
            storex(1, size * 6, bn254_ecadd_f.input_ids[5]);  // [x1, y1, 1, x2, y2, 1]
    code += storex(1, size * 5, bn254_ecadd_f.input_ids[6]);

    code += bn254_ecadd_f.gen_call(code.size());

    code += copy_values({bn254_ecadd_f.output_ids[2]}, field_inv_f.input_ids);

    code += field_inv_f.gen_call(code.size());

    code += mulmodx(
        bn254_ecadd_f.output_ids[0], bn254_ecadd_f.output_ids[0], field_inv_f.output_ids[0]);
    code += mulmodx(
        bn254_ecadd_f.output_ids[1], bn254_ecadd_f.output_ids[1], field_inv_f.output_ids[0]);
    ////////////////////////////////////////////////////////

    code += loadx(2, bn254_ecadd_f.output_ids[0], size * 6);
    // return loaded result
    code += ret(size * 6, size * 2);

    bn254_ecadd_f.finalize(scope, code);
    field_inv_f.finalize(scope, code);

    code[num_slots_placeholder_start] = vs_reg.max_slots_used();

    execute(1000, code, {calldata, size * 6});
    EXPECT_EQ(result.status_code, EVMC_SUCCESS);

    ASSERT_EQ(result.output_size, size * 2);
    EXPECT_EQ(hex({result.output_data, result.output_size}),
        "1f4d1d80177b1377743d1901f70d7389be7f7a35a35bfd234a8aaee615b88c49018683193ae021a2f8920fed18"
        "6cde5d9b1365116865281ccf884c1f28b1df8f");
}

TEST_P(evm, exec_bn254_ecmul_test)
{
    using namespace evmone::test;

    if (evm::is_advanced())
        return;

    evm::rev = EVMC_PRAGUE;  /// TODO: Use EVMC_EVMMAX

    // vm.set_option("trace", "0");

    constexpr auto size = sizeof(uint256);

    const auto x = 0x025a6f4181d2b4ea8b724290ffb40156eb0adb514c688556eb79cdea0752c2bb_u256;
    const auto y = 0x2eff3f31dea215f1eb86023a133a996eb6300b44da664d64251d05381bb8a02e_u256;
    const auto c = 0x183227397098d014dc2822db40c0ac2ecbc0b548b438e5469e10460b6c3e7ea3_u256;

    //    const auto x = 0x0f25929bcb43d5a57391564615c9e70a992b10eafa4db109709649cf48c50dd2_u256;
    //    const auto y = 0x16da2f5cb6be7a0aa72c440c53c9bbdfec6c36c7d515536431b3a865468acbba_u256;
    //    const auto c = 0x0000000000000000000000000000000000000000000000000000000000000003_u256;


    uint8_t calldata[5 * size];  // mod, x, y, c, b3
    intx::be::unsafe::store(&calldata[0], BN254Mod);
    intx::be::unsafe::store(&calldata[size], x);
    intx::be::unsafe::store(&calldata[2 * size], y);
    intx::be::unsafe::store(&calldata[3 * size], c);
    intx::be::unsafe::store(&calldata[4 * size], 9_u256);

    auto code = calldatacopy(push(0), push(0), push(size * 5)) + mstore(size * 5, push(1)) +
                setupx(0xFF, size, 0, 1);
    const auto num_slots_placeholder_start = code.size() - 8;

    ValueSlotsRegister vs_reg;
    SlotsScope scope(vs_reg);
    const auto px_idx = scope.register_slot();
    const auto py_idx = scope.register_slot();
    const auto pz_idx = scope.register_slot();

    {
        SlotsScope scope0(scope);
        const auto qx_idx = scope0.register_slot();
        const auto qy_idx = scope0.register_slot();
        const auto qz_idx = scope0.register_slot();
        const auto b3_idx = scope0.register_slot();

        code += storex(2, size, qx_idx) + storex(1, size * 5, qz_idx);  // [x1, y1, 1]
        code += storex(1, size * 5, py_idx);                            // [0, 1, 0]
        code += storex(1, size * 4, b3_idx);

        code += mload(push(3 * size));  // c

        bn254_ecmul(code, scope0, {qx_idx, qy_idx, qz_idx, b3_idx}, {px_idx, py_idx, pz_idx});
    }
    const auto pz_inv_idx = scope.register_slot();

    field_inv_bn254(code, scope, {pz_idx}, {pz_inv_idx});

    code += mulmodx(px_idx, px_idx, pz_inv_idx);
    code += mulmodx(py_idx, py_idx, pz_inv_idx);

    code += loadx(2, px_idx, size * 7);
    // return loaded result
    code += ret(size * 7, size * 2);

    code[num_slots_placeholder_start] = vs_reg.max_slots_used();

    std::cout << decode(code) << std::endl;

    execute(100000, code, {calldata, size * 5});
    EXPECT_EQ(result.status_code, EVMC_SUCCESS);

    ASSERT_EQ(result.output_size, size * 2);
    //    EXPECT_EQ(hex({result.output_data, result.output_size}),
    //        "1f4d1d80177b1377743d1901f70d7389be7f7a35a35bfd234a8aaee615b88c49018683193ae021a2f8920fed18"
    //        "6cde5d9b1365116865281ccf884c1f28b1df8f");

    EXPECT_EQ(hex({result.output_data, result.output_size}),
        "14789d0d4a730b354403b5fac948113739e276c23e0258d8596ee72f9cd9d3230af18a63153e0ec25ff9f2951d"
        "d3fa90ed0197bfef6e2a1a62b5095b9d2b4a27");
}

namespace
{
void bn254_ecadd(bytecode& code, SlotsScope& scope, const std::array<uint8_t, 7>& inputs,
    const std::array<uint8_t, 3>& outputs)
{
    auto const x3_idx = outputs[0];
    auto const y3_idx = outputs[1];
    auto const z3_idx = outputs[2];

    const auto x1_idx = inputs[0];
    const auto y1_idx = inputs[1];
    const auto z1_idx = inputs[2];
    const auto x2_idx = inputs[3];
    const auto y2_idx = inputs[4];
    const auto z2_idx = inputs[5];
    const auto b3_idx = inputs[6];

    // Point addition in projective space.
    const auto t0_idx = scope.register_slot();
    const auto t1_idx = scope.register_slot();
    const auto t2_idx = scope.register_slot();
    const auto t3_idx = scope.register_slot();
    const auto t4_idx = scope.register_slot();

    code += mulmodx(t0_idx, x1_idx, x2_idx);  // 1
    code += mulmodx(t1_idx, y1_idx, y2_idx);  // 2
    code += mulmodx(t2_idx, z1_idx, z2_idx);  // 3
    code += addmodx(t3_idx, x1_idx, y1_idx);  // 4
    code += addmodx(t4_idx, x2_idx, y2_idx);  // 5
    code += mulmodx(t3_idx, t3_idx, t4_idx);  // 6
    code += addmodx(t4_idx, t0_idx, t1_idx);  // 7
    code += submodx(t3_idx, t3_idx, t4_idx);  // 8
    code += addmodx(t4_idx, y1_idx, z1_idx);  // 9
    code += addmodx(x3_idx, y2_idx, z2_idx);  // 10
    code += mulmodx(t4_idx, t4_idx, x3_idx);  // 11
    code += addmodx(x3_idx, t1_idx, t2_idx);  // 12
    code += submodx(t4_idx, t4_idx, x3_idx);  // 13
    code += addmodx(x3_idx, x1_idx, z1_idx);  // 14
    code += addmodx(y3_idx, x2_idx, z2_idx);  // 15
    code += mulmodx(x3_idx, x3_idx, y3_idx);  // 16
    code += addmodx(y3_idx, t0_idx, t2_idx);  // 17
    code += submodx(y3_idx, x3_idx, y3_idx);  // 18
    code += addmodx(x3_idx, t0_idx, t0_idx);  // 19
    code += addmodx(t0_idx, x3_idx, t0_idx);  // 20
    code += mulmodx(t2_idx, b3_idx, t2_idx);  // 21
    code += addmodx(z3_idx, t1_idx, t2_idx);  // 22
    code += submodx(t1_idx, t1_idx, t2_idx);  // 23
    code += mulmodx(y3_idx, b3_idx, y3_idx);  // 24
    code += mulmodx(x3_idx, t4_idx, y3_idx);  // 25
    code += mulmodx(t2_idx, t3_idx, t1_idx);  // 26
    code += submodx(x3_idx, t2_idx, x3_idx);  // 27
    code += mulmodx(y3_idx, y3_idx, t0_idx);  // 28
    code += mulmodx(t1_idx, t1_idx, z3_idx);  // 29
    code += addmodx(y3_idx, t1_idx, y3_idx);  // 30
    code += mulmodx(t0_idx, t0_idx, t3_idx);  // 31
    code += mulmodx(z3_idx, z3_idx, t4_idx);  // 32
    code += addmodx(z3_idx, z3_idx, t0_idx);  // 33
}

void bn254_dbl(bytecode& code, SlotsScope& scope, const std::array<uint8_t, 4>& inputs,
    const std::array<uint8_t, 3>& outputs)
{
    const auto rx_idx = outputs[0];
    const auto ry_idx = outputs[1];
    const auto rz_idx = outputs[2];

    const auto x_idx = inputs[0];
    const auto y_idx = inputs[1];
    const auto z_idx = inputs[2];
    const auto b3_idx = inputs[3];

    const auto x3_idx = rx_idx;
    const auto y3_idx = ry_idx;
    const auto z3_idx = rz_idx;
    const auto t0_idx = scope.register_slot();
    const auto t1_idx = scope.register_slot();
    const auto t2_idx = scope.register_slot();

    code += mulmodx(t0_idx, y_idx, y_idx);    // 1
    code += addmodx(z3_idx, t0_idx, t0_idx);  // 2
    code += addmodx(z3_idx, z3_idx, z3_idx);  // 3
    code += addmodx(z3_idx, z3_idx, z3_idx);  // 4
    code += mulmodx(t1_idx, y_idx, z_idx);    // 5
    code += mulmodx(t2_idx, z_idx, z_idx);    // 6
    code += mulmodx(t2_idx, b3_idx, t2_idx);  // 7
    code += mulmodx(x3_idx, t2_idx, z3_idx);  // 8
    code += addmodx(y3_idx, t0_idx, t2_idx);  // 9
    code += mulmodx(z3_idx, t1_idx, z3_idx);  // 10
    code += addmodx(t1_idx, t2_idx, t2_idx);  // 11
    code += addmodx(t2_idx, t1_idx, t2_idx);  // 12
    code += submodx(t0_idx, t0_idx, t2_idx);  // 13
    code += mulmodx(y3_idx, t0_idx, y3_idx);  // 14
    code += addmodx(y3_idx, x3_idx, y3_idx);  // 15
    code += mulmodx(t1_idx, x_idx, y_idx);    // 16
    code += mulmodx(x3_idx, t0_idx, t1_idx);  // 17
    code += addmodx(x3_idx, x3_idx, x3_idx);  // 18
}

void bn254_ecmul(bytecode& code, SlotsScope& scope, const std::array<uint8_t, 4>& inputs,
    const std::array<uint8_t, 3>& outputs)
{
    const auto px_idx = outputs[0];
    const auto py_idx = outputs[1];
    const auto pz_idx = outputs[2];

    {
        SlotsScope scope0(scope);

        const auto qx_idx = inputs[0];
        const auto qy_idx = inputs[1];
        const auto qz_idx = inputs[2];
        const auto b3_idx = inputs[3];

        code +=
            push(0x8000000000000000000000000000000000000000000000000000000000000000_u256);  // mask

        // Loop 0. Find first significant bit
        code += bytecode(OP_JUMPDEST);
        const auto loop0_begin_label = code.size() - 1;

        code += iszero(bytecode(OP_DUP1));  // dup c and check if != 0
        code += push(0xFFFF);
        const auto loop1_end_placeholder_start_0 = code.size() - 2;
        code += bytecode(OP_JUMPI);

        code += bytecode(OP_DUP2) + bytecode(OP_DUP2);  // dup c and mask
        code += bytecode(OP_AND) + OP_DUP1;  // check if c && mask != 0. if so jump to loop1
        code += push(0xFFFF);
        const auto loop1_begin_placeholder_start = code.size() - 2;
        code += bytecode(OP_JUMPI);
        code += bytecode(OP_POP);
        code += bytecode(OP_DUP1) + push(1) + bytecode(OP_SHR);  // shift right c by 1 bit
        code += bytecode(OP_SWAP1) + OP_POP;  // swap shifted c with original and pop the original c
        code += push(loop0_begin_label) + bytecode(OP_JUMP);  // jump to loop 0 start

        // Loop 1 start computation.
        code += bytecode(OP_JUMPDEST);
        const auto loop1_begin_label = code.size() - 1;
        intx::be::unsafe::store(
            &code[loop1_begin_placeholder_start], static_cast<uint16_t>(loop1_begin_label));

        code += push(0xffff);
        const auto else0_placeholder_start = code.size() - 2;
        code += bytecode(OP_JUMPI);

        const auto rx_idx = scope0.register_slot();
        const auto ry_idx = scope0.register_slot();
        const auto rz_idx = scope0.register_slot();

        {
            SlotsScope scope1(scope0);
            bn254_ecadd(code, scope1, {qx_idx, qy_idx, qz_idx, px_idx, py_idx, pz_idx, b3_idx},
                {rx_idx, ry_idx, rz_idx});
        }
        code += copy_values<3>({rx_idx, ry_idx, rz_idx}, {qx_idx, qy_idx, qz_idx});

        {
            SlotsScope scope2(scope0);
            bn254_dbl(code, scope2, {px_idx, py_idx, pz_idx, b3_idx}, {rx_idx, ry_idx, rz_idx});
        }
        code += copy_values<3>({rx_idx, ry_idx, rz_idx}, {px_idx, py_idx, pz_idx});

        code += push(0xffff);
        const auto else0_end_placeholder_start = code.size() - 2;
        code += bytecode(OP_JUMP);

        code += bytecode(OP_JUMPDEST);
        intx::be::unsafe::store(
            &code[else0_placeholder_start], static_cast<uint16_t>(code.size() - 1));

        {
            SlotsScope scope3(scope0);
            bn254_ecadd(code, scope3, {qx_idx, qy_idx, qz_idx, px_idx, py_idx, pz_idx, b3_idx},
                {rx_idx, ry_idx, rz_idx});
        }
        code += copy_values<3>({rx_idx, ry_idx, rz_idx}, {px_idx, py_idx, pz_idx});

        {
            SlotsScope scope4(scope0);
            bn254_dbl(code, scope4, {qx_idx, qy_idx, qz_idx, b3_idx}, {rx_idx, ry_idx, rz_idx});
        }
        code += copy_values<3>({rx_idx, ry_idx, rz_idx}, {qx_idx, qy_idx, qz_idx});

        code += bytecode(OP_JUMPDEST);
        intx::be::unsafe::store(
            &code[else0_end_placeholder_start], static_cast<uint16_t>(code.size() - 1));

        code += bytecode(OP_DUP1) + push(1) + bytecode(OP_SHR);  // shift right mask by 1 bit
        code += bytecode(OP_SWAP1) +
                OP_POP;  // swap shifted mask with original and pop the original mask
        code += iszero(bytecode(OP_DUP1));  // dup mask and check if != 0
        code += push(0xFFFF);
        const auto loop1_end_placeholder_start_1 = code.size() - 2;
        code += bytecode(OP_JUMPI);

        code += bytecode(OP_DUP2) + bytecode(OP_DUP2);  // dup c and mask
        code += bytecode(OP_AND);

        code += jump(push(loop1_begin_label));

        code += bytecode(OP_JUMPDEST);
        intx::be::unsafe::store(
            &code[loop1_end_placeholder_start_0], static_cast<uint16_t>(code.size() - 1));
        intx::be::unsafe::store(
            &code[loop1_end_placeholder_start_1], static_cast<uint16_t>(code.size() - 1));
    }
}

void field_inv_bn254(bytecode& code, SlotsScope& scope, const std::array<uint8_t, 1>& x_idx_arr,
    const std::array<uint8_t, 1>& dst_idx_arr)
{
    const auto x_idx = x_idx_arr[0];
    const auto dst_idx = dst_idx_arr[0];

    // Inversion computation
    // Allocate Temporaries.
    const auto t0_idx = scope.register_slot();
    const auto t1_idx = scope.register_slot();
    const auto t2_idx = scope.register_slot();
    const auto t3_idx = scope.register_slot();
    const auto t4_idx = scope.register_slot();
    const auto t5_idx = scope.register_slot();
    const auto t6_idx = scope.register_slot();
    const auto t7_idx = scope.register_slot();
    const auto t8_idx = scope.register_slot();
    const auto t9_idx = scope.register_slot();
    const auto t10_idx = scope.register_slot();
    const auto t11_idx = scope.register_slot();
    const auto t12_idx = scope.register_slot();
    const auto t13_idx = scope.register_slot();
    const auto t14_idx = scope.register_slot();
    const auto t15_idx = scope.register_slot();
    const auto t16_idx = scope.register_slot();
    const auto t17_idx = scope.register_slot();
    const auto t18_idx = scope.register_slot();
    const auto t19_idx = scope.register_slot();
    const auto t20_idx = scope.register_slot();
    const auto t21_idx = scope.register_slot();
    const auto z_idx = dst_idx;

    // Step 1: t8 = x^0x2
    code += mulmodx(t8_idx, x_idx, x_idx);

    // Step 2: t15 = x^0x3
    code += mulmodx(t15_idx, x_idx, t8_idx);

    // Step 3: z = x^0x5
    code += mulmodx(z_idx, t8_idx, t15_idx);

    // Step 4: t1 = x^0x6
    code += mulmodx(t1_idx, x_idx, z_idx);

    // Step 5: t3 = x^0x8
    code += mulmodx(t3_idx, t8_idx, t1_idx);

    // Step 6: t9 = x^0xd
    code += mulmodx(t9_idx, z_idx, t3_idx);

    // Step 7: t6 = x^0x12
    code += mulmodx(t6_idx, z_idx, t9_idx);

    // Step 8: t19 = x^0x13
    code += mulmodx(t19_idx, x_idx, t6_idx);

    // Step 9: t0 = x^0x14
    code += mulmodx(t0_idx, x_idx, t19_idx);

    // Step 10: t20 = x^0x17
    code += mulmodx(t20_idx, t15_idx, t0_idx);

    // Step 11: t2 = x^0x1c
    code += mulmodx(t2_idx, z_idx, t20_idx);

    // Step 12: t17 = x^0x20
    code += mulmodx(t17_idx, t9_idx, t19_idx);

    // Step 13: t4 = x^0x23
    code += mulmodx(t4_idx, t15_idx, t17_idx);

    // Step 14: t14 = x^0x2b
    code += mulmodx(t14_idx, t3_idx, t4_idx);

    // Step 15: t12 = x^0x2f
    code += mulmodx(t12_idx, t19_idx, t2_idx);

    // Step 16: t16 = x^0x41
    code += mulmodx(t16_idx, t6_idx, t12_idx);

    // Step 17: t18 = x^0x53
    code += mulmodx(t18_idx, t6_idx, t16_idx);

    // Step 18: t3 = x^0x5b
    code += mulmodx(t3_idx, t3_idx, t18_idx);

    // Step 19: t5 = x^0x61
    code += mulmodx(t5_idx, t1_idx, t3_idx);

    // Step 20: t0 = x^0x75
    code += mulmodx(t0_idx, t0_idx, t5_idx);

    // Step 21: t10 = x^0x91
    code += mulmodx(t10_idx, t2_idx, t0_idx);

    // Step 22: t7 = x^0x95
    code += mulmodx(t7_idx, t17_idx, t0_idx);

    // Step 23: t11 = x^0xb5
    code += mulmodx(t11_idx, t17_idx, t7_idx);

    // Step 24: t13 = x^0xbb
    code += mulmodx(t13_idx, t1_idx, t11_idx);

    // Step 25: t21 = x^0xc1
    code += mulmodx(t21_idx, t1_idx, t13_idx);

    // Step 26: t2 = x^0xc3
    code += mulmodx(t2_idx, t8_idx, t21_idx);

    // Step 27: t6 = x^0xd3
    code += mulmodx(t6_idx, t6_idx, t21_idx);

    // Step 28: t17 = x^0xe1
    code += mulmodx(t17_idx, t17_idx, t21_idx);

    // Step 29: t8 = x^0xe3
    code += mulmodx(t8_idx, t8_idx, t17_idx);

    // Step 30: t1 = x^0xe7
    code += mulmodx(t1_idx, t1_idx, t17_idx);

    // Step 38: t21 = x^0xc100
    // for (int i = 0; i < 8; ++i)
    code += mulmodx(t21_idx, t21_idx, t21_idx);
    code += mulmodx(t21_idx, t21_idx, t21_idx);
    code += mulmodx(t21_idx, t21_idx, t21_idx);
    code += mulmodx(t21_idx, t21_idx, t21_idx);
    code += mulmodx(t21_idx, t21_idx, t21_idx);
    code += mulmodx(t21_idx, t21_idx, t21_idx);
    code += mulmodx(t21_idx, t21_idx, t21_idx);
    code += mulmodx(t21_idx, t21_idx, t21_idx);

    // Step 39: t21 = x^0xc191
    code += mulmodx(t21_idx, t10_idx, t21_idx);

    // Step 49: t21 = x^0x3064400
    // for (int i = 0; i < 10; ++i)
    code += mulmodx(t21_idx, t21_idx, t21_idx);
    code += mulmodx(t21_idx, t21_idx, t21_idx);
    code += mulmodx(t21_idx, t21_idx, t21_idx);
    code += mulmodx(t21_idx, t21_idx, t21_idx);
    code += mulmodx(t21_idx, t21_idx, t21_idx);
    code += mulmodx(t21_idx, t21_idx, t21_idx);
    code += mulmodx(t21_idx, t21_idx, t21_idx);
    code += mulmodx(t21_idx, t21_idx, t21_idx);
    code += mulmodx(t21_idx, t21_idx, t21_idx);
    code += mulmodx(t21_idx, t21_idx, t21_idx);

    // Step 50: t21 = x^0x30644e7
    code += mulmodx(t21_idx, t1_idx, t21_idx);

    // Step 57: t21 = x^0x183227380
    // for (int i = 0; i < 7; ++i)
    code += mulmodx(t21_idx, t21_idx, t21_idx);
    code += mulmodx(t21_idx, t21_idx, t21_idx);
    code += mulmodx(t21_idx, t21_idx, t21_idx);
    code += mulmodx(t21_idx, t21_idx, t21_idx);
    code += mulmodx(t21_idx, t21_idx, t21_idx);
    code += mulmodx(t21_idx, t21_idx, t21_idx);
    code += mulmodx(t21_idx, t21_idx, t21_idx);

    // Step 58: t20 = x^0x183227397
    code += mulmodx(t20_idx, t20_idx, t21_idx);

    // Step 67: t20 = x^0x30644e72e00
    // for (int i = 0; i < 9; ++i)
    code += mulmodx(t20_idx, t20_idx, t20_idx);
    code += mulmodx(t20_idx, t20_idx, t20_idx);
    code += mulmodx(t20_idx, t20_idx, t20_idx);
    code += mulmodx(t20_idx, t20_idx, t20_idx);
    code += mulmodx(t20_idx, t20_idx, t20_idx);
    code += mulmodx(t20_idx, t20_idx, t20_idx);
    code += mulmodx(t20_idx, t20_idx, t20_idx);
    code += mulmodx(t20_idx, t20_idx, t20_idx);
    code += mulmodx(t20_idx, t20_idx, t20_idx);

    // Step 68: t19 = x^0x30644e72e13
    code += mulmodx(t19_idx, t19_idx, t20_idx);

    // Step 75: t19 = x^0x1832273970980
    // for (int i = 0; i < 7; ++i)
    code += mulmodx(t19_idx, t19_idx, t19_idx);
    code += mulmodx(t19_idx, t19_idx, t19_idx);
    code += mulmodx(t19_idx, t19_idx, t19_idx);
    code += mulmodx(t19_idx, t19_idx, t19_idx);
    code += mulmodx(t19_idx, t19_idx, t19_idx);
    code += mulmodx(t19_idx, t19_idx, t19_idx);
    code += mulmodx(t19_idx, t19_idx, t19_idx);

    // Step 76: t19 = x^0x183227397098d
    code += mulmodx(t19_idx, t9_idx, t19_idx);

    // Step 90: t19 = x^0x60c89ce5c2634000
    // for (int i = 0; i < 14; ++i)
    code += mulmodx(t19_idx, t19_idx, t19_idx);
    code += mulmodx(t19_idx, t19_idx, t19_idx);
    code += mulmodx(t19_idx, t19_idx, t19_idx);
    code += mulmodx(t19_idx, t19_idx, t19_idx);
    code += mulmodx(t19_idx, t19_idx, t19_idx);
    code += mulmodx(t19_idx, t19_idx, t19_idx);
    code += mulmodx(t19_idx, t19_idx, t19_idx);
    code += mulmodx(t19_idx, t19_idx, t19_idx);
    code += mulmodx(t19_idx, t19_idx, t19_idx);
    code += mulmodx(t19_idx, t19_idx, t19_idx);
    code += mulmodx(t19_idx, t19_idx, t19_idx);
    code += mulmodx(t19_idx, t19_idx, t19_idx);
    code += mulmodx(t19_idx, t19_idx, t19_idx);
    code += mulmodx(t19_idx, t19_idx, t19_idx);

    // Step 91: t18 = x^0x60c89ce5c2634053
    code += mulmodx(t18_idx, t18_idx, t19_idx);

    // Step 100: t18 = x^0xc19139cb84c680a600
    // for (int i = 0; i < 9; ++i)
    code += mulmodx(t18_idx, t18_idx, t18_idx);
    code += mulmodx(t18_idx, t18_idx, t18_idx);
    code += mulmodx(t18_idx, t18_idx, t18_idx);
    code += mulmodx(t18_idx, t18_idx, t18_idx);
    code += mulmodx(t18_idx, t18_idx, t18_idx);
    code += mulmodx(t18_idx, t18_idx, t18_idx);
    code += mulmodx(t18_idx, t18_idx, t18_idx);
    code += mulmodx(t18_idx, t18_idx, t18_idx);
    code += mulmodx(t18_idx, t18_idx, t18_idx);

    // Step 101: t17 = x^0xc19139cb84c680a6e1
    code += mulmodx(t17_idx, t17_idx, t18_idx);

    // Step 109: t17 = x^0xc19139cb84c680a6e100
    // for (int i = 0; i < 8; ++i)
    code += mulmodx(t17_idx, t17_idx, t17_idx);
    code += mulmodx(t17_idx, t17_idx, t17_idx);
    code += mulmodx(t17_idx, t17_idx, t17_idx);
    code += mulmodx(t17_idx, t17_idx, t17_idx);
    code += mulmodx(t17_idx, t17_idx, t17_idx);
    code += mulmodx(t17_idx, t17_idx, t17_idx);
    code += mulmodx(t17_idx, t17_idx, t17_idx);
    code += mulmodx(t17_idx, t17_idx, t17_idx);

    // Step 110: t16 = x^0xc19139cb84c680a6e141
    code += mulmodx(t16_idx, t16_idx, t17_idx);

    // Step 120: t16 = x^0x30644e72e131a029b850400
    // for (int i = 0; i < 10; ++i)
    code += mulmodx(t16_idx, t16_idx, t16_idx);
    code += mulmodx(t16_idx, t16_idx, t16_idx);
    code += mulmodx(t16_idx, t16_idx, t16_idx);
    code += mulmodx(t16_idx, t16_idx, t16_idx);
    code += mulmodx(t16_idx, t16_idx, t16_idx);
    code += mulmodx(t16_idx, t16_idx, t16_idx);
    code += mulmodx(t16_idx, t16_idx, t16_idx);
    code += mulmodx(t16_idx, t16_idx, t16_idx);
    code += mulmodx(t16_idx, t16_idx, t16_idx);
    code += mulmodx(t16_idx, t16_idx, t16_idx);

    // Step 121: t16 = x^0x30644e72e131a029b85045b
    code += mulmodx(t16_idx, t3_idx, t16_idx);

    // Step 126: t16 = x^0x60c89ce5c263405370a08b60
    // for (int i = 0; i < 5; ++i)
    code += mulmodx(t16_idx, t16_idx, t16_idx);
    code += mulmodx(t16_idx, t16_idx, t16_idx);
    code += mulmodx(t16_idx, t16_idx, t16_idx);
    code += mulmodx(t16_idx, t16_idx, t16_idx);
    code += mulmodx(t16_idx, t16_idx, t16_idx);

    // Step 127: t16 = x^0x60c89ce5c263405370a08b6d
    code += mulmodx(t16_idx, t9_idx, t16_idx);

    // Step 135: t16 = x^0x60c89ce5c263405370a08b6d00
    // for (int i = 0; i < 8; ++i)
    code += mulmodx(t16_idx, t16_idx, t16_idx);
    code += mulmodx(t16_idx, t16_idx, t16_idx);
    code += mulmodx(t16_idx, t16_idx, t16_idx);
    code += mulmodx(t16_idx, t16_idx, t16_idx);
    code += mulmodx(t16_idx, t16_idx, t16_idx);
    code += mulmodx(t16_idx, t16_idx, t16_idx);
    code += mulmodx(t16_idx, t16_idx, t16_idx);
    code += mulmodx(t16_idx, t16_idx, t16_idx);

    // Step 136: t15 = x^0x60c89ce5c263405370a08b6d03
    code += mulmodx(t15_idx, t15_idx, t16_idx);

    // Step 148: t15 = x^0x60c89ce5c263405370a08b6d03000
    // for (int i = 0; i < 12; ++i)
    code += mulmodx(t15_idx, t15_idx, t15_idx);
    code += mulmodx(t15_idx, t15_idx, t15_idx);
    code += mulmodx(t15_idx, t15_idx, t15_idx);
    code += mulmodx(t15_idx, t15_idx, t15_idx);
    code += mulmodx(t15_idx, t15_idx, t15_idx);
    code += mulmodx(t15_idx, t15_idx, t15_idx);
    code += mulmodx(t15_idx, t15_idx, t15_idx);
    code += mulmodx(t15_idx, t15_idx, t15_idx);
    code += mulmodx(t15_idx, t15_idx, t15_idx);
    code += mulmodx(t15_idx, t15_idx, t15_idx);
    code += mulmodx(t15_idx, t15_idx, t15_idx);
    code += mulmodx(t15_idx, t15_idx, t15_idx);

    // Step 149: t14 = x^0x60c89ce5c263405370a08b6d0302b
    code += mulmodx(t14_idx, t14_idx, t15_idx);

    // Step 161: t14 = x^0x60c89ce5c263405370a08b6d0302b000
    // for (int i = 0; i < 12; ++i)
    code += mulmodx(t14_idx, t14_idx, t14_idx);
    code += mulmodx(t14_idx, t14_idx, t14_idx);
    code += mulmodx(t14_idx, t14_idx, t14_idx);
    code += mulmodx(t14_idx, t14_idx, t14_idx);
    code += mulmodx(t14_idx, t14_idx, t14_idx);
    code += mulmodx(t14_idx, t14_idx, t14_idx);
    code += mulmodx(t14_idx, t14_idx, t14_idx);
    code += mulmodx(t14_idx, t14_idx, t14_idx);
    code += mulmodx(t14_idx, t14_idx, t14_idx);
    code += mulmodx(t14_idx, t14_idx, t14_idx);
    code += mulmodx(t14_idx, t14_idx, t14_idx);
    code += mulmodx(t14_idx, t14_idx, t14_idx);

    // Step 162: t13 = x^0x60c89ce5c263405370a08b6d0302b0bb
    code += mulmodx(t13_idx, t13_idx, t14_idx);

    // Step 170: t13 = x^0x60c89ce5c263405370a08b6d0302b0bb00
    // for (int i = 0; i < 8; ++i)
    code += mulmodx(t13_idx, t13_idx, t13_idx);
    code += mulmodx(t13_idx, t13_idx, t13_idx);
    code += mulmodx(t13_idx, t13_idx, t13_idx);
    code += mulmodx(t13_idx, t13_idx, t13_idx);
    code += mulmodx(t13_idx, t13_idx, t13_idx);
    code += mulmodx(t13_idx, t13_idx, t13_idx);
    code += mulmodx(t13_idx, t13_idx, t13_idx);
    code += mulmodx(t13_idx, t13_idx, t13_idx);

    // Step 171: t12 = x^0x60c89ce5c263405370a08b6d0302b0bb2f
    code += mulmodx(t12_idx, t12_idx, t13_idx);

    // Step 185: t12 = x^0x183227397098d014dc2822db40c0ac2ecbc000
    // for (int i = 0; i < 14; ++i)
    code += mulmodx(t12_idx, t12_idx, t12_idx);
    code += mulmodx(t12_idx, t12_idx, t12_idx);
    code += mulmodx(t12_idx, t12_idx, t12_idx);
    code += mulmodx(t12_idx, t12_idx, t12_idx);
    code += mulmodx(t12_idx, t12_idx, t12_idx);
    code += mulmodx(t12_idx, t12_idx, t12_idx);
    code += mulmodx(t12_idx, t12_idx, t12_idx);
    code += mulmodx(t12_idx, t12_idx, t12_idx);
    code += mulmodx(t12_idx, t12_idx, t12_idx);
    code += mulmodx(t12_idx, t12_idx, t12_idx);
    code += mulmodx(t12_idx, t12_idx, t12_idx);
    code += mulmodx(t12_idx, t12_idx, t12_idx);
    code += mulmodx(t12_idx, t12_idx, t12_idx);
    code += mulmodx(t12_idx, t12_idx, t12_idx);


    // Step 186: t11 = x^0x183227397098d014dc2822db40c0ac2ecbc0b5
    code += mulmodx(t11_idx, t11_idx, t12_idx);

    // Step 195: t11 = x^0x30644e72e131a029b85045b68181585d97816a00
    // for (int i = 0; i < 9; ++i)
    code += mulmodx(t11_idx, t11_idx, t11_idx);
    code += mulmodx(t11_idx, t11_idx, t11_idx);
    code += mulmodx(t11_idx, t11_idx, t11_idx);
    code += mulmodx(t11_idx, t11_idx, t11_idx);
    code += mulmodx(t11_idx, t11_idx, t11_idx);
    code += mulmodx(t11_idx, t11_idx, t11_idx);
    code += mulmodx(t11_idx, t11_idx, t11_idx);
    code += mulmodx(t11_idx, t11_idx, t11_idx);
    code += mulmodx(t11_idx, t11_idx, t11_idx);

    // Step 196: t10 = x^0x30644e72e131a029b85045b68181585d97816a91
    code += mulmodx(t10_idx, t10_idx, t11_idx);

    // Step 201: t10 = x^0x60c89ce5c263405370a08b6d0302b0bb2f02d5220
    // for (int i = 0; i < 5; ++i)
    code += mulmodx(t10_idx, t10_idx, t10_idx);
    code += mulmodx(t10_idx, t10_idx, t10_idx);
    code += mulmodx(t10_idx, t10_idx, t10_idx);
    code += mulmodx(t10_idx, t10_idx, t10_idx);
    code += mulmodx(t10_idx, t10_idx, t10_idx);

    // Step 202: t9 = x^0x60c89ce5c263405370a08b6d0302b0bb2f02d522d
    code += mulmodx(t9_idx, t9_idx, t10_idx);

    // Step 214: t9 = x^0x60c89ce5c263405370a08b6d0302b0bb2f02d522d000
    // for (int i = 0; i < 12; ++i)
    code += mulmodx(t9_idx, t9_idx, t9_idx);
    code += mulmodx(t9_idx, t9_idx, t9_idx);
    code += mulmodx(t9_idx, t9_idx, t9_idx);
    code += mulmodx(t9_idx, t9_idx, t9_idx);
    code += mulmodx(t9_idx, t9_idx, t9_idx);
    code += mulmodx(t9_idx, t9_idx, t9_idx);
    code += mulmodx(t9_idx, t9_idx, t9_idx);
    code += mulmodx(t9_idx, t9_idx, t9_idx);
    code += mulmodx(t9_idx, t9_idx, t9_idx);
    code += mulmodx(t9_idx, t9_idx, t9_idx);
    code += mulmodx(t9_idx, t9_idx, t9_idx);
    code += mulmodx(t9_idx, t9_idx, t9_idx);

    // Step 215: t8 = x^0x60c89ce5c263405370a08b6d0302b0bb2f02d522d0e3
    code += mulmodx(t8_idx, t8_idx, t9_idx);

    // Step 223: t8 = x^0x60c89ce5c263405370a08b6d0302b0bb2f02d522d0e300
    // for (int i = 0; i < 8; ++i)
    code += mulmodx(t8_idx, t8_idx, t8_idx);
    code += mulmodx(t8_idx, t8_idx, t8_idx);
    code += mulmodx(t8_idx, t8_idx, t8_idx);
    code += mulmodx(t8_idx, t8_idx, t8_idx);
    code += mulmodx(t8_idx, t8_idx, t8_idx);
    code += mulmodx(t8_idx, t8_idx, t8_idx);
    code += mulmodx(t8_idx, t8_idx, t8_idx);
    code += mulmodx(t8_idx, t8_idx, t8_idx);

    // Step 224: t7 = x^0x60c89ce5c263405370a08b6d0302b0bb2f02d522d0e395
    code += mulmodx(t7_idx, t7_idx, t8_idx);

    // Step 235: t7 = x^0x30644e72e131a029b85045b68181585d97816a916871ca800
    // for (int i = 0; i < 11; ++i)
    code += mulmodx(t7_idx, t7_idx, t7_idx);
    code += mulmodx(t7_idx, t7_idx, t7_idx);
    code += mulmodx(t7_idx, t7_idx, t7_idx);
    code += mulmodx(t7_idx, t7_idx, t7_idx);
    code += mulmodx(t7_idx, t7_idx, t7_idx);
    code += mulmodx(t7_idx, t7_idx, t7_idx);
    code += mulmodx(t7_idx, t7_idx, t7_idx);
    code += mulmodx(t7_idx, t7_idx, t7_idx);
    code += mulmodx(t7_idx, t7_idx, t7_idx);
    code += mulmodx(t7_idx, t7_idx, t7_idx);
    code += mulmodx(t7_idx, t7_idx, t7_idx);

    // Step 236: t6 = x^0x30644e72e131a029b85045b68181585d97816a916871ca8d3
    code += mulmodx(t6_idx, t6_idx, t7_idx);

    // Step 243: t6 = x^0x183227397098d014dc2822db40c0ac2ecbc0b548b438e546980
    // for (int i = 0; i < 7; ++i)
    code += mulmodx(t6_idx, t6_idx, t6_idx);
    code += mulmodx(t6_idx, t6_idx, t6_idx);
    code += mulmodx(t6_idx, t6_idx, t6_idx);
    code += mulmodx(t6_idx, t6_idx, t6_idx);
    code += mulmodx(t6_idx, t6_idx, t6_idx);
    code += mulmodx(t6_idx, t6_idx, t6_idx);
    code += mulmodx(t6_idx, t6_idx, t6_idx);

    // Step 244: t5 = x^0x183227397098d014dc2822db40c0ac2ecbc0b548b438e5469e1
    code += mulmodx(t5_idx, t5_idx, t6_idx);

    // Step 255: t5 = x^0xc19139cb84c680a6e14116da060561765e05aa45a1c72a34f0800
    // for (int i = 0; i < 11; ++i)
    code += mulmodx(t5_idx, t5_idx, t5_idx);
    code += mulmodx(t5_idx, t5_idx, t5_idx);
    code += mulmodx(t5_idx, t5_idx, t5_idx);
    code += mulmodx(t5_idx, t5_idx, t5_idx);
    code += mulmodx(t5_idx, t5_idx, t5_idx);
    code += mulmodx(t5_idx, t5_idx, t5_idx);
    code += mulmodx(t5_idx, t5_idx, t5_idx);
    code += mulmodx(t5_idx, t5_idx, t5_idx);
    code += mulmodx(t5_idx, t5_idx, t5_idx);
    code += mulmodx(t5_idx, t5_idx, t5_idx);
    code += mulmodx(t5_idx, t5_idx, t5_idx);

    // Step 256: t4 = x^0xc19139cb84c680a6e14116da060561765e05aa45a1c72a34f0823
    code += mulmodx(t4_idx, t4_idx, t5_idx);

    // Step 268: t4 = x^0xc19139cb84c680a6e14116da060561765e05aa45a1c72a34f0823000
    // for (int i = 0; i < 12; ++i)
    code += mulmodx(t4_idx, t4_idx, t4_idx);
    code += mulmodx(t4_idx, t4_idx, t4_idx);
    code += mulmodx(t4_idx, t4_idx, t4_idx);
    code += mulmodx(t4_idx, t4_idx, t4_idx);
    code += mulmodx(t4_idx, t4_idx, t4_idx);
    code += mulmodx(t4_idx, t4_idx, t4_idx);
    code += mulmodx(t4_idx, t4_idx, t4_idx);
    code += mulmodx(t4_idx, t4_idx, t4_idx);
    code += mulmodx(t4_idx, t4_idx, t4_idx);
    code += mulmodx(t4_idx, t4_idx, t4_idx);
    code += mulmodx(t4_idx, t4_idx, t4_idx);
    code += mulmodx(t4_idx, t4_idx, t4_idx);

    // Step 269: t3 = x^0xc19139cb84c680a6e14116da060561765e05aa45a1c72a34f082305b
    code += mulmodx(t3_idx, t3_idx, t4_idx);

    // Step 278: t3 = x^0x183227397098d014dc2822db40c0ac2ecbc0b548b438e5469e10460b600
    // for (int i = 0; i < 9; ++i)
    code += mulmodx(t3_idx, t3_idx, t3_idx);
    code += mulmodx(t3_idx, t3_idx, t3_idx);
    code += mulmodx(t3_idx, t3_idx, t3_idx);
    code += mulmodx(t3_idx, t3_idx, t3_idx);
    code += mulmodx(t3_idx, t3_idx, t3_idx);
    code += mulmodx(t3_idx, t3_idx, t3_idx);
    code += mulmodx(t3_idx, t3_idx, t3_idx);
    code += mulmodx(t3_idx, t3_idx, t3_idx);
    code += mulmodx(t3_idx, t3_idx, t3_idx);

    // Step 279: t2 = x^0x183227397098d014dc2822db40c0ac2ecbc0b548b438e5469e10460b6c3
    code += mulmodx(t2_idx, t2_idx, t3_idx);

    // Step 287: t2 = x^0x183227397098d014dc2822db40c0ac2ecbc0b548b438e5469e10460b6c300
    // for (int i = 0; i < 8; ++i)
    code += mulmodx(t2_idx, t2_idx, t2_idx);
    code += mulmodx(t2_idx, t2_idx, t2_idx);
    code += mulmodx(t2_idx, t2_idx, t2_idx);
    code += mulmodx(t2_idx, t2_idx, t2_idx);
    code += mulmodx(t2_idx, t2_idx, t2_idx);
    code += mulmodx(t2_idx, t2_idx, t2_idx);
    code += mulmodx(t2_idx, t2_idx, t2_idx);
    code += mulmodx(t2_idx, t2_idx, t2_idx);

    // Step 288: t1 = x^0x183227397098d014dc2822db40c0ac2ecbc0b548b438e5469e10460b6c3e7
    code += mulmodx(t1_idx, t1_idx, t2_idx);

    // Step 295: t1 = x^0xc19139cb84c680a6e14116da060561765e05aa45a1c72a34f082305b61f380
    // for (int i = 0; i < 7; ++i)
    code += mulmodx(t1_idx, t1_idx, t1_idx);
    code += mulmodx(t1_idx, t1_idx, t1_idx);
    code += mulmodx(t1_idx, t1_idx, t1_idx);
    code += mulmodx(t1_idx, t1_idx, t1_idx);
    code += mulmodx(t1_idx, t1_idx, t1_idx);
    code += mulmodx(t1_idx, t1_idx, t1_idx);
    code += mulmodx(t1_idx, t1_idx, t1_idx);

    // Step 296: t0 = x^0xc19139cb84c680a6e14116da060561765e05aa45a1c72a34f082305b61f3f5
    code += mulmodx(t0_idx, t0_idx, t1_idx);

    // Step 302: t0 = x^0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd40
    /// for (int i = 0; i < 6; ++i)
    code += mulmodx(t0_idx, t0_idx, t0_idx);
    code += mulmodx(t0_idx, t0_idx, t0_idx);
    code += mulmodx(t0_idx, t0_idx, t0_idx);
    code += mulmodx(t0_idx, t0_idx, t0_idx);
    code += mulmodx(t0_idx, t0_idx, t0_idx);
    code += mulmodx(t0_idx, t0_idx, t0_idx);

    // Step 303: z = x^0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd45
    code += mulmodx(z_idx, z_idx, t0_idx);
}
}  // namespace
