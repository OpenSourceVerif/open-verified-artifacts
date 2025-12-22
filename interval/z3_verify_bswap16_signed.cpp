#include <z3++.h>
#include <iostream>
#include <chrono>
#include <ctime>

using namespace z3;

// 16位字节交换
expr bswap16(context& c, expr v) {
    return concat(v.extract(7, 0), v.extract(15, 8));
}

// __bswap_max_s16 的 z3 实现（修正版）
expr bswap_max_s16(context& c, expr x, expr y) {
    expr low_byte_x = x & c.bv_val(0x00FF, 16);
    expr low_byte_y = y & c.bv_val(0x00FF, 16);
    expr high_byte_x = lshr(x & c.bv_val(0xFF00, 16), 8);
    expr high_byte_y = lshr(y & c.bv_val(0xFF00, 16), 8);
    
    // 关键修正：右移整个数，而不只是低字节
    // x >> 7 包含高字节和低字节的第7位（符号位）
    expr sx = lshr(x, 7);
    expr sy = lshr(y, 7);
    
    // if(sx == sy) return __builtin_bswap16(y);
    expr sign_same_result = bswap16(c, y);
    
    // if(low_byte_y >= 0x7f)
    expr cond2 = uge(low_byte_y, c.bv_val(0x7F, 16));
    
    // return __builtin_bswap16(high_byte_y << 8 | 0x7f);
    expr then_val = shl(high_byte_y, 8) | c.bv_val(0x7F, 16);
    expr then_result = bswap16(c, then_val);
    
    // else return __builtin_bswap16((high_byte_y - 1) << 8 | 0x7f);
    expr else_val = shl(high_byte_y - c.bv_val(1, 16), 8) | c.bv_val(0x7F, 16);
    expr else_result = bswap16(c, else_val);
    
    expr sign_diff_result = ite(cond2, then_result, else_result);
    
    return ite(sx == sy, sign_same_result, sign_diff_result);
}

// __bswap_min_s16 的 z3 实现（修正版）
expr bswap_min_s16(context& c, expr x, expr y) {
    expr low_byte_x = x & c.bv_val(0x00FF, 16);
    expr low_byte_y = y & c.bv_val(0x00FF, 16);
    expr high_byte_x = lshr(x & c.bv_val(0xFF00, 16), 8);
    expr high_byte_y = lshr(y & c.bv_val(0xFF00, 16), 8);
    
    // 关键修正：右移整个数，而不只是低字节
    // x >> 7 包含高字节和低字节的第7位（符号位）
    expr sx = lshr(x, 7);
    expr sy = lshr(y, 7);
    
    // if(sx == sy) return __builtin_bswap16(x);
    expr sign_same_result = bswap16(c, x);
    
    // if(low_byte_x <= 0x80)
    expr cond2 = ule(low_byte_x, c.bv_val(0x80, 16));
    
    // return __builtin_bswap16(high_byte_x << 8 | 0x80);
    expr then_val = shl(high_byte_x, 8) | c.bv_val(0x80, 16);
    expr then_result = bswap16(c, then_val);
    
    // else return __builtin_bswap16((high_byte_x + 1) << 8 | 0x80);
    expr else_val = shl(high_byte_x + c.bv_val(1, 16), 8) | c.bv_val(0x80, 16);
    expr else_result = bswap16(c, else_val);
    
    expr sign_diff_result = ite(cond2, then_result, else_result);
    
    return ite(sx == sy, sign_same_result, sign_diff_result);
}

// 判断区间是否跨越0（变号）
// 返回: x < 0 && y >= 0
expr crosses_zero(context& c, expr x, expr y) {
    return slt(x, c.bv_val(0, 16)) && sge(y, c.bv_val(0, 16));
}

// 带区间拆分的 bswap_max（支持跨越0的情况）
expr bswap_max_s16_split(context& c, expr x, expr y) {
    // 判断是否跨越0
    expr crosses = crosses_zero(c, x, y);
    
    // 不跨越0：直接计算
    expr normal_max = bswap_max_s16(c, x, y);
    
    // 跨越0：拆分成 [x, -1] 和 [0, y]
    expr neg_one = c.bv_val(0xFFFF, 16);  // -1 的16位表示
    expr zero = c.bv_val(0, 16);
    
    // [x, -1] 的最大值
    expr max1 = bswap_max_s16(c, x, neg_one);
    
    // [0, y] 的最大值
    expr max2 = bswap_max_s16(c, zero, y);
    
    // 取两个区间的最大值（并集的上界）
    expr split_max = ite(sgt(max1, max2), max1, max2);
    
    // 根据是否跨越0选择结果
    return ite(crosses, split_max, normal_max);
}

// 带区间拆分的 bswap_min
expr bswap_min_s16_split(context& c, expr x, expr y) {
    // 判断是否跨越0
    expr crosses = crosses_zero(c, x, y);
    
    // 不跨越0：直接计算
    expr normal_min = bswap_min_s16(c, x, y);
    
    // 跨越0：拆分成 [x, -1] 和 [0, y]
    expr neg_one = c.bv_val(0xFFFF, 16);  // -1 的16位表示
    expr zero = c.bv_val(0, 16);
    
    // [x, -1] 的最小值
    expr min1 = bswap_min_s16(c, x, neg_one);
    
    // [0, y] 的最小值
    expr min2 = bswap_min_s16(c, zero, y);
    
    // 取两个区间的最小值
    expr split_min = ite(slt(min1, min2), min1, min2);
    
    // 根据是否跨越0选择结果
    return ite(crosses, split_min, normal_min);
}

int main() {
    std::cout.setf(std::ios::unitbuf);
    std::cerr.setf(std::ios::unitbuf);

    std::cout << "================================================\n";
    std::cout << "  16位有符号 bswap Z3 验证（支持区间拆分）\n";
    std::cout << "================================================\n\n";
    
    std::cout << "新特性：\n";
    std::cout << "  - 检测区间是否跨越0（从负数到正数）\n";
    std::cout << "  - 如果跨越，自动拆分为 [x, -1] 和 [0, y]\n";
    std::cout << "  - 分别计算后取并集\n\n";
    
    auto start_time = std::chrono::high_resolution_clock::now();
    
    context c;
    
    params p(c);
    p.set("timeout", 3600000u);  // 1小时超时
    p.set("threads", 16u);       // 16线程
    
    solver s(c, "QF_BV");
    s.set(p);
    
    // 定义符号变量
    expr lb = c.bv_const("lb", 16);
    expr ub = c.bv_const("ub", 16);
    expr x = c.bv_const("x", 16);
    
    // 约束：lb <= x <= ub (有符号比较)
    std::cout << "添加约束条件：lb <= x <= ub (有符号比较)\n";
    s.add(sle(lb, ub));
    s.add(sge(x, lb));
    s.add(sle(x, ub));
    std::cout << "完成\n\n";
    
    // 计算算法结果（带区间拆分）
    std::cout << "计算 bswap_min_s16_split 和 bswap_max_s16_split...\n";
    expr algo_min = bswap_min_s16_split(c, lb, ub);
    expr algo_max = bswap_max_s16_split(c, lb, ub);
    std::cout << "完成\n\n";
    
    // 实际的bswap(x)
    expr swapped_x = bswap16(c, x);
    
    // 验证：检查 algo_min <= bswap(x) <= algo_max (有符号比较)
    std::cout << "验证目标：\n";
    std::cout << "  对于所有 x ∈ [lb, ub]，证明：\n";
    std::cout << "  bswap_min_s16_split(lb, ub) <= bswap16(x) <= bswap_max_s16_split(lb, ub)\n";
    std::cout << "  (有符号比较，支持跨越0的区间)\n\n";
    
    s.push();
    std::cout << "添加否定约束（寻找反例）...\n";
    s.add(sgt(algo_min, swapped_x) || slt(algo_max, swapped_x));
    std::cout << "完成\n\n";
    
    std::cout << "开始求解...\n";
    std::cout << "  线程数: 16\n";
    std::cout << "  超时: 3600秒 (1小时)\n\n";
    std::cout.flush();
    
    check_result result = s.check();
    
    std::cout << "求解完成\n\n";
    
    auto end_time = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end_time - start_time);
    
    if (result == sat) {
        std::cout << "✗ 验证失败！发现反例\n\n";
        model m = s.get_model();
        
        std::cout << "反例详情：\n";
        std::cout << "  lb = " << m.eval(lb) << " (有符号: " << m.eval(lb).as_int64() << ")\n";
        std::cout << "  ub = " << m.eval(ub) << " (有符号: " << m.eval(ub).as_int64() << ")\n";
        std::cout << "  x  = " << m.eval(x) << " (有符号: " << m.eval(x).as_int64() << ")\n";
        std::cout << "  bswap16(x) = " << m.eval(swapped_x) << "\n\n";
        
        std::cout << "算法计算的范围：\n";
        std::cout << "  algo_min = " << m.eval(algo_min) << "\n";
        std::cout << "  algo_max = " << m.eval(algo_max) << "\n\n";
        
        std::cout << "区间是否跨越0：\n";
        expr crosses = crosses_zero(c, lb, ub);
        std::cout << "  crosses_zero(lb, ub) = " << m.eval(crosses) << "\n\n";
        
        std::cout << "验证条件失败：\n";
        if (m.eval(sgt(algo_min, swapped_x)).is_true()) {
            std::cout << "  algo_min > bswap16(x)\n";
        }
        if (m.eval(slt(algo_max, swapped_x)).is_true()) {
            std::cout << "  algo_max < bswap16(x)\n";
        }
        
        s.pop();
        std::cout << "\n总耗时: " << duration.count() << " 毫秒\n";
        return 1;
    } else if (result == unsat) {
        std::cout << "✓ 验证通过！\n\n";
        std::cout << "证明结论：\n";
        std::cout << "  对于所有有符号16位整数 x ∈ [lb, ub]：\n";
        std::cout << "  （包括跨越0的区间）\n";
        std::cout << "  bswap_min_s16_split(lb, ub) <= bswap16(x) <= bswap_max_s16_split(lb, ub)\n";
        std::cout << "  (有符号比较)\n\n";
        
        s.pop();
        std::cout << "总耗时: " << duration.count() << " 毫秒\n";
        return 0;
    } else {
        s.pop();
        
        std::cout << "? 验证未完成（超时或未知）\n\n";
        std::cout << "总耗时: " << duration.count() << " 毫秒\n";
        return 2;
    }
}

