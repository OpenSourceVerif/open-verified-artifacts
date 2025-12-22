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

// 二分计算前导零个数
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

// bswap_min_signed_aux
expr bswap_min_signed_aux_impl(context& c, expr x, expr y, int n) {
    expr xor_val = x ^ y;
    expr lz = leading_zeros64(c, xor_val);
    expr same_bytes = lz / c.bv_val(8, 64);
    
    expr result = bswap64(c, x);
    
    expr has_diff = same_bytes < c.bv_val(8, 64);
    
    expr n1 = c.bv_val(7, 64) - same_bytes;
    expr bi = n1 * c.bv_val(8, 64);
    
    // n1 == 0 的情况
    expr is_n1_zero = (n1 == c.bv_val(0, 64));
    expr val_n1_zero = shl(lshr(x, 8), 8) | c.bv_val(0x80, 64);
    
    // n1 > 0 的情况
    expr low_mask = shl(c.bv_val(1, 64), bi) - c.bv_val(1, 64);
    expr x_low = x & low_mask;
    expr cross = ule(x_low, c.bv_val(0x80, 64));
    expr val_when_cross = shl(lshr(x, 8), 8) | c.bv_val(0x80, 64);  // (x >> 8) << 8 | 0x80
    expr val_when_not_cross = shl((lshr(x, bi) + c.bv_val(1, 64)), bi) | c.bv_val(0x80, 64);
    expr val_n1_nonzero = ite(cross, val_when_cross, val_when_not_cross);
    
    expr val = ite(is_n1_zero, val_n1_zero, val_n1_nonzero);
    
    return ite(has_diff, bswap64(c, val), result);
}

// bswap_min_signed
expr bswap_min_signed(context& c, expr x, expr y) {
    // 高(n-1)字节 + bswap(x)的符号位
    expr sx = lshr(x, 7);
    expr sy = lshr(y, 7);
    expr cross_signed = (sx != sy);
    
    expr aux_result = bswap_min_signed_aux_impl(c, x, y, 8);
    expr simple_result = bswap64(c, x);
    
    return ite(cross_signed, aux_result, simple_result);
}

// bswap_max_signed_aux
expr bswap_max_signed_aux_impl(context& c, expr x, expr y, int n) {
    expr xor_val = x ^ y;
    expr lz = leading_zeros64(c, xor_val);
    expr same_bytes = lz / c.bv_val(8, 64);
    
    expr result = bswap64(c, y); 
    
    expr has_diff = same_bytes < c.bv_val(8, 64);
    
    expr n1 = c.bv_val(7, 64) - same_bytes;
    expr bi = n1 * c.bv_val(8, 64);
    
    // n1 == 0 的情况
    expr is_n1_zero = (n1 == c.bv_val(0, 64));
    expr val_n1_zero = shl(lshr(y, 8), 8) | c.bv_val(0x7f, 64);
    
    // n1 > 0 的情况
    expr low_mask = shl(c.bv_val(1, 64), bi) - c.bv_val(1, 64);
    expr y_low = y & low_mask;
    expr cross = uge(y_low, low_mask ^ c.bv_val(0x80, 64));
    expr val_when_cross = shl(lshr(y, 8), 8) | c.bv_val(0x7f, 64);
    expr val_when_not_cross = (shl(lshr(y, bi), bi) - c.bv_val(1, 64)) ^ c.bv_val(0x80, 64);
    expr val_n1_nonzero = ite(cross, val_when_cross, val_when_not_cross);
    
    expr val = ite(is_n1_zero, val_n1_zero, val_n1_nonzero);
    
    return ite(has_diff, bswap64(c, val), result);
}

// bswap_max_signed
expr bswap_max_signed(context& c, expr x, expr y) {
    // 高(n-1)字节 + bswap(x)的符号位
    expr sx = lshr(x, 7);
    expr sy = lshr(y, 7);
    expr cross_signed = (sx != sy);
    
    expr aux_result = bswap_max_signed_aux_impl(c, x, y, 8);
    expr simple_result = bswap64(c, y);
    
    return ite(cross_signed, aux_result, simple_result);
}

// bswap_signed
std::pair<expr, expr> bswap_signed(context& c, expr x, expr y) {
    expr zero = c.bv_val(0, 64);
    expr x_negative = x < zero;
    expr y_non_negative = y >= zero;
    expr crosses_zero = x_negative && y_non_negative;
    
    // 情况1: 同符号区间
    expr same_sign_min = bswap_min_signed(c, x, y);
    expr same_sign_max = bswap_max_signed(c, x, y);
    
    // 情况2: 跨越0的区间，分割成 [x, -1] 和 [0, y]
    expr neg_one = c.bv_val((uint64_t)~0ULL, 64);
    
    expr neg_min = bswap_min_signed(c, x, neg_one);
    expr neg_max = bswap_max_signed(c, x, neg_one);
    
    expr pos_min = bswap_min_signed(c, zero, y);
    expr pos_max = bswap_max_signed(c, zero, y);
    
    expr split_min = ite(neg_min < pos_min, neg_min, pos_min);
    expr split_max = ite(neg_max > pos_max, neg_max, pos_max);
    
    expr result_min = ite(crosses_zero, split_min, same_sign_min);
    expr result_max = ite(crosses_zero, split_max, same_sign_max);
    
    return std::make_pair(result_min, result_max);
}

int main() {
    std::cout.setf(std::ios::unitbuf);
    std::cerr.setf(std::ios::unitbuf);
    
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
    
    // 约束：lb <= ub 
    s.add(lb <= ub);
    s.add(x >= lb);
    s.add(x <= ub);
    
    // 计算算法结果
    std::cout << "计算 bswap_signed 的结果范围...\n";
    auto [algo_min, algo_max] = bswap_signed(c, lb, ub);
    std::cout << "完成\n\n";
    
    // bswap(x)
    expr swapped_x = bswap64(c, x);
    
    s.push();
    std::cout << "添加否定约束（寻找反例）...\n";
    s.add(swapped_x < algo_min || swapped_x > algo_max);
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
        std::cout << "? Z3 返回 UNKNOWN\n";
        std::cout << "问题可能过于复杂或超时\n";
        s.pop();
        
        std::cout << "\n验证未完成\n";
        std::cout << "总耗时: " << duration.count() << " 秒\n";
        return 2;
    }
}
