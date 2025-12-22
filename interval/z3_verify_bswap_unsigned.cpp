#include <z3++.h>
#include <iostream>
#include <chrono>
#include <ctime>
#include <unistd.h>

using namespace z3;

// 64位字节交换
expr bswap64(context& c, expr v) {
    return concat(
        v.extract(7, 0),
        concat(
            v.extract(15, 8),
            concat(
                v.extract(23, 16),
                concat(
                    v.extract(31, 24),
                    concat(
                        v.extract(39, 32),
                        concat(
                            v.extract(47, 40),
                            concat(
                                v.extract(55, 48),
                                v.extract(63, 56)
                            )
                        )
                    )
                )
            )
        )
    );
}

// 计算前导零个数
expr leading_zeros64(context& c, expr x) {
    expr count = c.bv_val(0, 64);
    
    // 检查高32位是否全为0
    expr high32 = lshr(x, 32);
    expr high32_zero = (high32 == c.bv_val(0, 64));
    count = ite(high32_zero, count + c.bv_val(32, 64), count);
    x = ite(high32_zero, shl(x, 32), x);
    
    // 检查高16位是否全为0
    expr high16 = lshr(x, 48);
    expr high16_zero = (high16 == c.bv_val(0, 64));
    count = ite(high16_zero, count + c.bv_val(16, 64), count);
    x = ite(high16_zero, shl(x, 16), x);
    
    // 检查高8位是否全为0
    expr high8 = lshr(x, 56);
    expr high8_zero = (high8 == c.bv_val(0, 64));
    count = ite(high8_zero, count + c.bv_val(8, 64), count);
    x = ite(high8_zero, shl(x, 8), x);
    
    // 检查高4位是否全为0
    expr high4 = lshr(x, 60);
    expr high4_zero = (high4 == c.bv_val(0, 64));
    count = ite(high4_zero, count + c.bv_val(4, 64), count);
    x = ite(high4_zero, shl(x, 4), x);
    
    // 检查高2位是否全为0
    expr high2 = lshr(x, 62);
    expr high2_zero = (high2 == c.bv_val(0, 64));
    count = ite(high2_zero, count + c.bv_val(2, 64), count);
    x = ite(high2_zero, shl(x, 2), x);
    
    // 检查最高位是否为0
    expr high1 = lshr(x, 63);
    expr high1_zero = (high1 == c.bv_val(0, 64));
    count = ite(high1_zero, count + c.bv_val(1, 64), count);
    
    return count;
}

// bswap_max_unsigned
expr bswap_max_unsigned(context& c, expr x, expr y) {
    expr xor_val = x ^ y;
    expr lz = leading_zeros64(c, xor_val);
    expr same_bytes = lz / c.bv_val(8, 64);
    
    expr result = bswap64(c, y); //（same_bytes >= 8 时）
    
    // same_bytes < 8 的情况
    expr has_diff = same_bytes < c.bv_val(8, 64);
    
    // n1 = 7 - same_bytes
    expr n1 = c.bv_val(7, 64) - same_bytes;
    expr bi = n1 * c.bv_val(8, 64);
    
    // 低位掩码：(2^bi - 1)
    expr low_mask = (shl(c.bv_val(1, 64), bi)) - c.bv_val(1, 64);
    
    // 检查 y 的低位是否全为 1
    expr low_all_ones = ((y & low_mask) == low_mask);
    
    // 低位全为1：直接返回 bswap(y)
    expr result_all_ones = bswap64(c, y);
    
    // 低位不全为1：y 的第 n 个字节减 1，低位全部置为 0xff
    expr result_not_all_ones = bswap64(c, shl((lshr(y, bi) - c.bv_val(1, 64)), bi) | low_mask);
    
    expr result_has_diff = ite(low_all_ones, result_all_ones, result_not_all_ones);
    
    return ite(has_diff, result_has_diff, result);
}

// bswap_min_unsigned 
expr bswap_min_unsigned(context& c, expr x, expr y) {
    expr xor_val = x ^ y;
    expr lz = leading_zeros64(c, xor_val);
    expr same_bytes = lz / c.bv_val(8, 64);
    
    expr result = bswap64(c, x); // 默认值（same_bytes >= 8 时）
    
    // same_bytes < 8 的情况
    expr has_diff = same_bytes < c.bv_val(8, 64);
    
    // n1 = 7 - same_bytes
    expr n1 = c.bv_val(7, 64) - same_bytes;
    expr bi = n1 * c.bv_val(8, 64);
    
    // 低位掩码：(2^bi - 1)
    expr low_mask = (shl(c.bv_val(1, 64), bi)) - c.bv_val(1, 64);
    
    // 检查 x 的低位是否全为 0
    expr low_all_zeros = ((x & low_mask) == c.bv_val(0, 64));
    
    // 低位全为0：直接返回 bswap(x)
    expr result_all_zeros = bswap64(c, x);
    
    // 低位不全为0：x 的第 n 个字节加 1，低位全部置为 0
    expr result_not_all_zeros = bswap64(c, shl((lshr(x, bi) + c.bv_val(1, 64)), bi));
    
    expr result_has_diff = ite(low_all_zeros, result_all_zeros, result_not_all_zeros);
    
    return ite(has_diff, result_has_diff, result);
}

int main() {
    std::cout.setf(std::ios::unitbuf);
    std::cerr.setf(std::ios::unitbuf);

    std::cout << "进程ID: " << getpid() << "\n";
    std::cout << "开始时间: " << std::chrono::system_clock::to_time_t(std::chrono::system_clock::now()) << "\n\n";
    
    auto start_time = std::chrono::high_resolution_clock::now();
    
    context c;
    
    params p(c);
    p.set("timeout", 72000000u);  // 20小时
    p.set("threads", 256u);       // 256线程
    
    solver s(c, "QF_BV");
    s.set(p);
    
    
    // 定义符号变量
    expr lb = c.bv_const("lb", 64);
    expr ub = c.bv_const("ub", 64);
    expr x = c.bv_const("x", 64);
    
    // 约束：lb <= ub (无符号比较)
    s.add(ule(lb, ub));
    s.add(uge(x, lb));
    s.add(ule(x, ub));
    
    // 计算算法结果
    std::cout << "计算无符号 bswap 的结果范围...\n";
    expr algo_min = bswap_min_unsigned(c, lb, ub);
    expr algo_max = bswap_max_unsigned(c, lb, ub);
    std::cout << "完成\n\n";
    
    // 实际的bswap(x)
    expr swapped_x = bswap64(c, x);
    
    // 验证：检查 algo_min <= bswap(x) <= algo_max (无符号比较)
    std::cout << "验证：检查所有 x ∈ [lb, ub] 的 bswap(x) 是否满足：\n";
    std::cout << "  algo_min <= bswap(x) <= algo_max (无符号比较)\n\n";
    
    s.push();
    std::cout << "添加否定约束（寻找反例）...\n";
    s.add(ugt(algo_min, swapped_x) || ult(algo_max, swapped_x));
    std::cout << "完成\n\n";
    
    std::cout << "开始求解...\n";
    std::cout << "  线程: 256\n";
    std::cout << "  超时: 72000秒 (20小时)\n";
    std::cout << "  监控: htop -p " << getpid() << "\n\n";
    std::cout.flush();
    
    check_result result = s.check();
    
    std::cout << "\n求解完成\n\n";
    
    auto end_time = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::seconds>(end_time - start_time);
    
    if (result == sat) {
        std::cout << "✗ 发现反例！算法有误\n\n";
        model m = s.get_model();
        
        std::cout << "反例：\n";
        std::cout << "  lb = " << m.eval(lb) << "\n";
        std::cout << "  ub = " << m.eval(ub) << "\n";
        std::cout << "  x  = " << m.eval(x) << "\n";
        std::cout << "  bswap(x) = " << m.eval(swapped_x) << "\n\n";
        
        std::cout << "算法计算的范围：\n";
        std::cout << "  algo_min = " << m.eval(algo_min) << "\n";
        std::cout << "  algo_max = " << m.eval(algo_max) << "\n";
        
        s.pop();
        return 1;
    } else if (result == unsat) {
        std::cout << "✓ 验证通过！\n\n";
        s.pop();
        std::cout << "总耗时: " << duration.count() << " 秒\n";
        return 0;
    } else {
        s.pop();
        
        std::cout << "\n验证未完成\n";
        std::cout << "总耗时: " << duration.count() << " 秒\n";
        return 2;
    }
}
