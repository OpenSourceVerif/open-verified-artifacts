#include <z3++.h>
#include <iostream>
#include <chrono>
#include <ctime>

using namespace z3;

// 16位字节交换
expr bswap16(context& c, expr v) {
    // 交换高字节和低字节
    return concat(v.extract(7, 0), v.extract(15, 8));
}

// __bswap_max_u16 的 z3 实现
expr bswap_max_u16(context& c, expr x, expr y) {
    // u16 low_byte_y = y & 0x00FF;
    expr low_byte_y = y & c.bv_val(0x00FF, 16);
    
    // u16 high_byte_x = (x & 0xFF00) >> 8
    expr high_byte_x = lshr(x & c.bv_val(0xFF00, 16), 8);
    
    // u16 high_byte_y = (y & 0xFF00) >> 8
    expr high_byte_y = lshr(y & c.bv_val(0xFF00, 16), 8);
    
    // if(high_byte_x == high_byte_y || low_byte_y == 0x00FF)
    expr cond = (high_byte_x == high_byte_y) || (low_byte_y == c.bv_val(0x00FF, 16));
    
    // return __builtin_bswap16(y);
    expr then_branch = bswap16(c, y);
    
    // else return __builtin_bswap16((high_byte_y - 1) << 8 | 0x00FF);
    expr else_val = shl(high_byte_y - c.bv_val(1, 16), 8) | c.bv_val(0x00FF, 16);
    expr else_branch = bswap16(c, else_val);
    
    return ite(cond, then_branch, else_branch);
}

// __bswap_min_u16 的 z3 实现
expr bswap_min_u16(context& c, expr x, expr y) {
    // u16 low_byte_x = x & 0x00FF;
    expr low_byte_x = x & c.bv_val(0x00FF, 16);
    
    // u16 high_byte_x = (x & 0xFF00) >> 8
    expr high_byte_x = lshr(x & c.bv_val(0xFF00, 16), 8);
    
    // u16 high_byte_y = (y & 0xFF00) >> 8
    expr high_byte_y = lshr(y & c.bv_val(0xFF00, 16), 8);
    
    // if(high_byte_x == high_byte_y || low_byte_x == 0x0000)
    expr cond = (high_byte_x == high_byte_y) || (low_byte_x == c.bv_val(0x0000, 16));
    
    // return __builtin_bswap16(x);
    expr then_branch = bswap16(c, x);
    
    // else return __builtin_bswap16((high_byte_x + 1) << 8 | 0x0000);
    expr else_val = shl(high_byte_x + c.bv_val(1, 16), 8) | c.bv_val(0x0000, 16);
    expr else_branch = bswap16(c, else_val);
    
    return ite(cond, then_branch, else_branch);
}

int main() {
    std::cout.setf(std::ios::unitbuf);
    std::cerr.setf(std::ios::unitbuf);

    std::cout << "======================================\n";
    std::cout << "  16位 bswap 函数 Z3 形式化验证\n";
    std::cout << "======================================\n\n";
    
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
    
    // 约束：lb <= x <= ub (无符号比较)
    std::cout << "添加约束条件：lb <= x <= ub (无符号比较)\n";
    s.add(ule(lb, ub));
    s.add(uge(x, lb));
    s.add(ule(x, ub));
    std::cout << "完成\n\n";
    
    // 计算算法结果
    std::cout << "计算 bswap_min_u16 和 bswap_max_u16...\n";
    expr algo_min = bswap_min_u16(c, lb, ub);
    expr algo_max = bswap_max_u16(c, lb, ub);
    std::cout << "完成\n\n";
    
    // 实际的bswap(x)
    expr swapped_x = bswap16(c, x);
    
    // 验证：检查 algo_min <= bswap(x) <= algo_max (无符号比较)
    std::cout << "验证目标：\n";
    std::cout << "  对于所有 x ∈ [lb, ub]，证明：\n";
    std::cout << "  bswap_min_u16(lb, ub) <= bswap16(x) <= bswap_max_u16(lb, ub)\n";
    std::cout << "  (无符号比较)\n\n";
    
    s.push();
    std::cout << "添加否定约束（寻找反例）...\n";
    // 寻找反例：algo_min > swapped_x 或 algo_max < swapped_x
    s.add(ugt(algo_min, swapped_x) || ult(algo_max, swapped_x));
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
        std::cout << "  lb = " << m.eval(lb) << "\n";
        std::cout << "  ub = " << m.eval(ub) << "\n";
        std::cout << "  x  = " << m.eval(x) << "\n";
        std::cout << "  bswap16(x) = " << m.eval(swapped_x) << "\n\n";
        
        std::cout << "算法计算的范围：\n";
        std::cout << "  bswap_min_u16(lb, ub) = " << m.eval(algo_min) << "\n";
        std::cout << "  bswap_max_u16(lb, ub) = " << m.eval(algo_max) << "\n\n";
        
        std::cout << "验证条件失败：\n";
        if (m.eval(ugt(algo_min, swapped_x)).is_true()) {
            std::cout << "  algo_min > bswap16(x)\n";
        }
        if (m.eval(ult(algo_max, swapped_x)).is_true()) {
            std::cout << "  algo_max < bswap16(x)\n";
        }
        
        s.pop();
        std::cout << "\n总耗时: " << duration.count() << " 毫秒\n";
        return 1;
    } else if (result == unsat) {
        std::cout << "✓ 验证通过！\n\n";
        std::cout << "证明结论：\n";
        std::cout << "  对于所有无符号16位整数 x ∈ [lb, ub]：\n";
        std::cout << "  bswap_min_u16(lb, ub) <= bswap16(x) <= bswap_max_u16(lb, ub)\n";
        std::cout << "  (无符号比较)\n\n";
        
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

