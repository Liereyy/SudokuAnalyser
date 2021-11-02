#pragma once

#include "SolverAssist.hpp"
#include "SolverCoreBasic.hpp"
#include <deque>

#define NONE
#define ROW
#define COL
#define ALS_
#define dALS_BOX
#define dALS_ROW
#define dALS_COL
#define dDYNAMIC_CHAIN_MERGENODES

bool Solver::dynamic_chain_split(chain_node& cn_start, chain_node& new_node, bool can_be_used_as_normal_generalized_node)
{
    if (cn_equal_except_itype(cn_start, current_cn_head) || visited[getPos(new_node)])
        return false;

    if (split_times < Max_Split_times && !hasBranch && !ever_splited[getPos(new_node)] && new_node.vpos.size() == 2)  // 只考虑2分支
    {
        for (auto p : new_node.vpos)
        {
            chain_node branch_node(p, new_node.number, _Weak);
            // 必须每一个分裂之后的格都有效
            if (branch_node == current_cn_head)
                return false;
        }

        // cout << "split.\ncn_head: " << current_cn_head << new_node << endl << endl;
        ++split_times;
        hasBranch = true;
        ever_splited[getPos(new_node)] = true;
        us_visited_branch1.clear();
        us_visited_branch2.clear();
        us_visited_shared1.clear();
        us_visited_shared2.clear();
        memset(visited, false, sizeof(visited));

        // 选定主链，将_shared1的其他分支抹除
        visited[getPos(new_node)] = true;
        int last_pos = getPos(cn_start);
        while (parent[last_pos] != -1)
        {
            us_visited_shared1.insert(last_pos);
            visited[last_pos] = true;
            last_pos = parent[last_pos];
        }
        visited[last_pos] = true;
        us_visited_shared1.insert(last_pos);
        
        Fringe.clear();

        splitted_node = new_node;
        update_parent(cn_start, splitted_node);

        // 将这个广义节点分裂为几个单元格弱节点
        int s = 0;
        for (auto p : new_node.vpos)
        {
            chain_node branch_node(p, new_node.number, _Weak);
            btype[getPos(branch_node)] = s ? _branch2 : _branch1;
            split_pos[s] = getPos(branch_node);
            push_chain_node(branch_node, branch_node, false);
            if (s == 0)
            {
                parent_branch1[getPos(branch_node)] = getPos(cn_start);
                us_visited_branch1.insert(getPos(branch_node));
            }
            else
            {
                parent_branch2[getPos(branch_node)] = getPos(cn_start);
                us_visited_branch2.insert(getPos(branch_node));
            }
            ++s;
        }
        return true;
    }
    else if ((!hasBranch || new_node != splitted_node) && can_be_used_as_normal_generalized_node)  // 作为普通广义节点使用
        push_chain_node(cn_start, new_node);
    return false;
}

bool Solver::dynamic_chain_split_inblock(chain_node& new_node)
{
    if (cn_equal_except_itype(new_node, current_cn_head) || visited[getPos(new_node)])
        return false;

    if (split_times < Max_Split_times && !hasBranch && !ever_splited[getPos(new_node)] && new_node.vpos.size() == 2)  // 只考虑2分支
    {
        for (auto p : new_node.vpos)
        {
            chain_node branch_node(p, new_node.number, _Weak);
            // 必须每一个分裂之后的格都有效
            if (branch_node == current_cn_head)
                return false;
        }

        // cout << "split.\ncn_head: " << current_cn_head << new_node << endl << endl;
        ++split_times;
        hasBranch = true;
        ever_splited[getPos(new_node)] = true;
        us_visited_branch1.clear();
        us_visited_branch2.clear();
        us_visited_shared1.clear();
        us_visited_shared2.clear();
        memset(visited, false, sizeof(visited));

        // 选定主链，将_shared1的其他分支抹除
        visited[getPos(new_node)] = true;
        int last_pos = getPos(new_node);
        while (parent[last_pos] != -1)
        {
            us_visited_shared1.insert(last_pos);
            visited[last_pos] = true;
            last_pos = parent[last_pos];
        }
        visited[last_pos] = true;
        us_visited_shared1.insert(last_pos);
        
        Fringe.clear();

        // 将这个广义节点分裂为几个单元格弱节点
        int s = 0;
        for (int nx = 1; nx <= 9; ++nx)
            if (nx != new_node.number && getBit(new_node.vpos[0], nx))
            {
                chain_node branch_node(new_node.vpos[0], nx, _Weak);
                btype[getPos(branch_node)] = s ? _branch2 : _branch1;
                split_pos[s] = getPos(branch_node);
                push_chain_node(branch_node, branch_node, false);
                if (s == 0)
                {
                    parent_branch1[getPos(branch_node)] = getPos(new_node);
                    us_visited_branch1.insert(getPos(branch_node));
                }
                else
                {
                    parent_branch2[getPos(branch_node)] = getPos(new_node);
                    us_visited_branch2.insert(getPos(branch_node));
                }
                ++s;
            }
        return true;
    }
    return false;
}

void Solver::strongInference_dynamic(chain_node& cn_start)
{
    // cout << getPos(cn_start) << "strong called.\n";
    // if (hasBranch && !merged && btype[getPos(cn_start)] == _shared1)
    //     return;
    // if (merged && btype[getPos(cn_start)] != _shared2)
    //     return;

    // if (merged && btype[getPos(cn_start)] == _shared2)
    //     cout << "merged strong.\n";

    int n = cn_start.number;
    
    if (cn_start.dtype == _None)
    {
        #ifdef NONE
        pii head(cn_start.vpos[0], cn_start.number);
        // 共轭对强关系
        for (auto i : getStrongInferenceBlock_Conjugate_dynamic(cn_start, head))
        {
            chain_node new_node(i.first, i.second, _Weak);
            push_chain_node(cn_start, new_node);
            push_unit_node_expansion(cn_start, i.second, i.first);
        }
        // 格内强关系
        if (unit[head.first].left == 2 && !insideUnit[head.first])
        {
            int the_other_candidate = getOtherCandidate(head.first, head.second);
            chain_node new_node(head.first, the_other_candidate, _Weak);
            if (push_chain_node(cn_start, new_node))
                insideUnit[head.first] = true;
        }
        // 格内节点拆分
        if (unit[cn_start.vpos[0]].left == 3)
            dynamic_chain_split_inblock(cn_start);

        // 行内节点拆分
        if (r_count[cn_start.number][_r(cn_start.vpos[0])] == 3)
        {
            int  r = _r(cn_start.vpos[0]);
            vector<int> tmp;
            for (int j = 0; j < 9; ++j)
                if (_n(r, j) != cn_start.vpos[0] && getBit(_n(r, j), n))
                    tmp.push_back(_n(r, j));
            chain_node new_node(tmp, n, _Weak, _ALS_Row);
            dynamic_chain_split(cn_start, new_node, false);
        }
        // 列内节点拆分
        if (c_count[cn_start.number][_c(cn_start.vpos[0])] == 3)
        {
            int c = _c(cn_start.vpos[0]);
            vector<int> tmp;
            for (int i = 0; i < 9; ++i)
                if (_n(i, c) != cn_start.vpos[0] && getBit(_n(i, c), n))
                    tmp.push_back(_n(i, c));
            chain_node new_node(tmp, n, _Weak, _ALS_Column);
            dynamic_chain_split(cn_start, new_node, false);
        }
        // 宫内节点拆分
        if (b_count[cn_start.number][_b(cn_start.vpos[0])] == 3)
        {
            int b = _b(cn_start.vpos[0]);
            vector<int> tmp;
            for (int bx = 0; bx < 9; ++bx)
                if (_bij(b, bx / 3, bx % 3) != cn_start.vpos[0] && getBit(_bij(b, bx / 3, bx % 3), n))
                    tmp.push_back(_bij(b, bx / 3, bx % 3));
            chain_node new_node(tmp, n, _Weak, _ALS_Box);
            dynamic_chain_split(cn_start, new_node, false);
        }
        #endif
    }
    if (cn_start.dtype == _Row || cn_start.dtype == _None)
    {
        #ifdef ROW
        int b0 = _b(cn_start.vpos[0]);
        int bx0 = b0 / 3;
        int by0 = b0 % 3;
        int r = _r(cn_start.vpos[0]);
        int ix0 = _iinbox(r);
        int jx0 = _cinbox(cn_start.vpos[0]);

        // 1宫内其他位置的强链
        // 1.1宫内其他行的单元格
        if (cn_start.dtype == _Row)
            for (int ix = 0; ix < 3; ++ix)
                if (ix != ix0
                        && br_count[n][b0][ix] == 1
                        && br_count[n][b0][ix] + br_count[n][b0][ix0] == b_count[n][b0])
                    for (int jx = 0; jx < 3; ++jx)
                        if (getBit(_bij(b0, ix, jx), n))
                        {
                            int npos = _bij(b0, ix, jx);
                            chain_node new_node(npos, n, _Weak, _None);
                            push_chain_node(cn_start, new_node);
                            push_unit_node_expansion(cn_start, n, npos);
                            break;
                        }
        // 1.2宫内其他行的行广义节点
        for (int ix = 0; ix < 3; ++ix)
            if (ix != ix0
                    && br_count[n][b0][ix] + br_count[n][b0][ix0] == b_count[n][b0]
                    && br_count[n][b0][ix] >= 2
                    && (cn_start.dtype == _Row || (cn_start.dtype == _None && br_count[n][b0][ix0] == 1)))
            {
                vector<int> tmp;
                for (int jx = 0; jx < 3; ++jx)
                    if (getBit(_bij(b0, ix, jx), n))
                        tmp.push_back(_bij(b0, ix, jx));
                chain_node new_node(tmp, n, _Weak, _Row);
                if (dynamic_chain_split(cn_start, new_node))
                    return;
            }
        // 1.3宫内其他列的列广义节点
        for (int jx = 0; jx < 3; ++jx)
            if (bc_count[n][b0][jx] >= 2
                    && ((cn_start.dtype == _Row && br_count[n][b0][ix0] + bc_count[n][b0][jx] - (getBit(_bij(b0, ix0, jx), n) ? 1 : 0) == b_count[n][b0])
                            || (cn_start.dtype == _None && jx != jx0 && bc_count[n][b0][jx] + 1 == b_count[n][b0])))
            {
                vector<int> tmp;
                for (int ix = 0; ix < 3; ++ix)
                    if (getBit(_bij(b0, ix, jx), n))
                        tmp.push_back(_bij(b0, ix, jx));
                chain_node new_node(tmp, n, _Weak, _Column);
                if (dynamic_chain_split(cn_start, new_node))
                    return;
            }

        // 2该行其他宫的剩余该候选数的格及广义格
        for (int by = 0; by < 3; ++by)
            if (by != by0 && br_count[n][b0][_iinbox(r)] + br_count[n][3 * bx0 + by][_iinbox(r)] == r_count[n][r])
            {
                int b = 3 * bx0 + by;
                if (cn_start.dtype == _Row && br_count[n][b][_iinbox(r)] == 1)
                {
                    for (int jx = 0; jx < 3; ++jx)
                        if (getBit(_bij(b, _iinbox(r), jx), n))
                        {
                            int npos = _bij(b, _iinbox(r), jx);
                            chain_node new_node(npos, n, _Weak, _None);
                            push_chain_node(cn_start, new_node);
                        }
                }
                else if (br_count[n][b][_iinbox(r)] >= 2
                            && (cn_start.dtype == _Row || (cn_start.dtype == _None && br_count[n][b0][_iinbox(r)] == 1)))
                {
                    vector<int> tmp;
                    for (int jx = 0; jx < 3; ++jx)
                        if (getBit(_bij(b, _iinbox(r), jx), n))
                            tmp.push_back(_bij(b, _iinbox(r), jx));
                    chain_node new_node(tmp, n, _Weak, _Row);
                    if (dynamic_chain_split(cn_start, new_node))
                        return;
                }
            }
        #endif
    }
    if (cn_start.dtype == _Column || cn_start.dtype == _None)
    {
        #ifdef COL
        // 该列其他宫的剩余该候选数的格及广义格
        int b0 = _b(cn_start.vpos[0]);
        int bx0 = b0 / 3;
        int by0 = b0 % 3;
        int c = _c(cn_start.vpos[0]);
        int ix0 = _rinbox(cn_start.vpos[0]);
        int jx0 = _jinbox(c);

        // 1宫内其他位置的强链
        // 1.1宫内其他列的单元格
        if (cn_start.dtype == _Column)
            for (int jx = 0; jx < 3; ++jx)
                if (jx != jx0
                        && bc_count[n][b0][jx] == 1
                        && bc_count[n][b0][jx] + bc_count[n][b0][jx0] == b_count[n][b0])
                    for (int ix = 0; ix < 3; ++ix)
                        if (getBit(_bij(b0, ix, jx), n))
                        {
                            int npos = _bij(b0, ix, jx);
                            chain_node new_node(npos, n, _Weak, _None);
                            push_chain_node(cn_start, new_node);
                            push_unit_node_expansion(cn_start, n, npos);
                            break;
                        }
        // 1.2宫内其他列的列广义节点
        for (int jx = 0; jx < 3; ++jx)
            if (jx != jx0
                    && bc_count[n][b0][jx] + bc_count[n][b0][jx0] == b_count[n][b0]
                    && bc_count[n][b0][jx] >= 2
                    && (cn_start.dtype == _Column || (cn_start.dtype == _None && bc_count[n][b0][jx0] == 1)))
            {
                vector<int> tmp;
                for (int ix = 0; ix < 3; ++ix)
                    if (getBit(_bij(b0, ix, jx), n))
                        tmp.push_back(_bij(b0, ix, jx));
                chain_node new_node(tmp, n, _Weak, _Column);
                if (dynamic_chain_split(cn_start, new_node))
                    return;
            }
        // 1.3宫内其他行的行广义节点
        for (int ix = 0; ix < 3; ++ix)
            if (br_count[n][b0][ix] >= 2
                    && ((cn_start.dtype == _Column && bc_count[n][b0][jx0] + br_count[n][b0][ix] - (getBit(_bij(b0, ix, jx0), n) ? 1 : 0) == b_count[n][b0])
                            || (cn_start.dtype == _None && ix != ix0 && br_count[n][b0][ix] + 1 == b_count[n][b0])))
            {
                vector<int> tmp;
                for (int jx = 0; jx < 3; ++jx)
                    if (getBit(_bij(b0, ix, jx), n))
                        tmp.push_back(_bij(b0, ix, jx));
                chain_node new_node(tmp, n, _Weak, _Row);
                if (dynamic_chain_split(cn_start, new_node))
                    return;
            }

        // 2该行其他宫的剩余该候选数的格及广义格
        for (int bx = 0; bx < 3; ++bx)
            if (bx != bx0 && bc_count[n][b0][_jinbox(c)] + bc_count[n][3 * bx + by0][_jinbox(c)] == c_count[n][c])
            {
                int b = 3 * bx + by0;
                if (cn_start.dtype == _Column && bc_count[n][b][_jinbox(c)] == 1)
                {
                    for (int ix = 0; ix < 3; ++ix)
                        if (getBit(_bij(b, ix, _jinbox(c)), n))
                        {
                            int npos = _bij(b, ix, _jinbox(c));
                            chain_node new_node(npos, n, _Weak, _None);
                            push_chain_node(cn_start, new_node);
                            push_unit_node_expansion(cn_start, n, npos);
                        }
                }
                else if (bc_count[n][b][_jinbox(c)] >= 2
                            && (cn_start.dtype == _Column || (cn_start.dtype == _None && bc_count[n][b0][_jinbox(c)] == 1)))
                {
                    vector<int> tmp;
                    for (int ix = 0; ix < 3; ++ix)
                        if (getBit(_bij(b, ix, _jinbox(c)), n))
                            tmp.push_back(_bij(b, ix, _jinbox(c)));
                    chain_node new_node(tmp, n, _Weak, _Column);
                    if (dynamic_chain_split(cn_start, new_node))
                        return;
                }
            }
        #endif
    }
    
    // // ALS
    // // 尝试找ALS，如果发现有n格含有n+1个候选数，且cn_start恰好含于这个ALS中，则可形成新的ALS的强关系
    // #ifdef ALS_
    if (cn_start.dtype == _Row || cn_start.dtype == _None)
    {
        #ifdef dALS_ROW
        short als[512];  // 例：als[000_001_110]表示第123格的所有candidate的或

        // 找行内ALS
        int r = _r(cn_start.vpos[0]);
        // 自底而上的dp
        als[0] = 0;
        short flag = 0;  // flag记录行内已填数情况，为1代表已填数，如101_101_010指示行050_402_709(注意，flag右低位)
        for (int j = 0; j < 9; ++j)
            if (unit[9 * r + j].left == 0)
                flag |= 1 << j;
        for (short p = 1; p < 512; ++p)
            if ((p & flag) == 0)  // 选中的格都未填数
            {
                int last_pos = 0;
                short tmp = p;
                while ((tmp & 1) == 0)
                {
                    ++last_pos;
                    tmp >>= 1;
                }
                als[p] = als[p & (p - 1)] | unit[9 * r + last_pos].candidate;
                if (_count_bit1(p) > 1 && _count_bit1(als[p]) == _count_bit1(p) + 1  // p+1个候选数恰出现在p格中，且p>1
                        && (als[p] & (1 << (n - 1)))  // 这p格含有候选数n
                        )
                {
                    vector<int> selected_pos;
                    int j = 0;
                    short tmp = p;
                    while (tmp)
                    {
                        if (tmp & 1) selected_pos.push_back(9 * r + j);
                        tmp >>= 1;
                        ++j;
                    }

                    vector<int> v;
                    for (auto pos : selected_pos)
                        if (getBit(pos, n))
                            v.push_back(pos);
                    if (v != cn_start.vpos) continue;

                    for (int nx = 1; nx <= 9; ++nx)
                        if (nx != n && (als[p] & (1 << (nx - 1))))
                        {
                            vector<int> v;
                            for (auto pos : selected_pos)
                                if (getBit(pos, nx))
                                    v.push_back(pos);
                            chain_node new_node(v, nx, _Weak, _ALS_Row);
                            if (v.size() == 1)
                                new_node.dtype = _None;
                            else if (getPos(new_node) < 2430)  // 退化为基本行节点
                                new_node.dtype = _Row;
                            if (!gained[getPos(new_node)] && !visited[getPos(new_node)])
                            {
                                ++technique_count.ALS;
                                gained[getPos(new_node)] = true;
                                push_chain_node(cn_start, new_node);
                                // for (auto pos : selected_pos)
                                // {
                                //     cout << ntorc(pos) << ":   ";
                                //     for (int n = 1; n <= 9; ++n)
                                //         if (getBit(pos, n))
                                //             cout << n << ' ';
                                //     cout << endl;
                                // }
                                // cout << cn_start << new_node << endl;
                                // system("pause");
                            }
                        }
                }
            }
        #endif
    }

    if (cn_start.dtype == _Column || cn_start.dtype == _None)
    {
        #ifdef dALS_COL
        // 找列内ALS
        int c = _c(cn_start.vpos[0]);
        // 自底而上的dp
        short als[512];  // 例：als[000_001_110]表示第123格的所有candidate的或
        als[0] = 0;
        short flag = 0;  // flag记录列内已填数情况，为1代表已填数，如101_101_010指示列050_402_709(注意，flag右低位)
        for (int i = 0; i < 9; ++i)
            if (unit[9 * i + c].left == 0)
                flag |= 1 << i;
        for (short p = 1; p < 512; ++p)
            if ((p & flag) == 0)  // 选中的格都未填数
            {
                int last_pos = 0;
                short tmp = p;
                while ((tmp & 1) == 0)
                {
                    ++last_pos;
                    tmp >>= 1;
                }
                als[p] = als[p & (p - 1)] | unit[9 * last_pos + c].candidate;
                if (_count_bit1(p) > 1 && _count_bit1(als[p]) == _count_bit1(p) + 1  // p+1个候选数恰出现在p格中，且p>1
                        && (als[p] & (1 << (n - 1)))  // 这p格含有候选数n
                        )
                {
                    vector<int> selected_pos;
                    int i = 0;
                    short tmp = p;
                    while (tmp)
                    {
                        if (tmp & 1) selected_pos.push_back(9 * i + c);
                        tmp >>= 1;
                        ++i;
                    }

                    vector<int> v;
                    for (auto pos : selected_pos)
                        if (getBit(pos, n))
                            v.push_back(pos);
                    if (v != cn_start.vpos) continue;

                    for (int nx = 1; nx <= 9; ++nx)
                        if (nx != n && (als[p] & (1 << (nx - 1))))
                        {
                            vector<int> v;
                            for (auto pos : selected_pos)
                                if (getBit(pos, nx))
                                    v.push_back(pos);
                            chain_node new_node(v, nx, _Weak, _ALS_Column);
                            if (v.size() == 1)
                                new_node.dtype = _None;
                            else if (getPos(new_node) < 2430)  // 退化为基本列节点
                                new_node.dtype = _Column;
                            if (!gained[getPos(new_node)] && !visited[getPos(new_node)])
                            {
                                ++technique_count.ALS;
                                gained[getPos(new_node)] = true;
                                push_chain_node(cn_start, new_node);
                            }
                        }
                }
            }
        #endif
    }

    if (cn_start.dtype == _None || cn_start.dtype == _Row || cn_start.dtype == _Column)
    {
        #ifdef dALS_BOX
        // 找宫内ALS
        int b = _b(cn_start.vpos[0]);
        // 自底而上的dp
        short als[512];  // 例：als[000_001_110]表示第123格的所有candidate的或
        als[0] = 0;
        short flag = 0;  // flag记录宫内已填数情况，为1代表已填数，如101_101_010指示宫050_402_709(注意，flag右低位)
        for (int ix = 0; ix < 3; ++ix)
            for (int jx = 0; jx < 3; ++jx)
                if (unit[_bij(b, ix, jx)].left == 0)
                    flag |= 1 << (3 * ix + jx);
        for (int p = 1; p < 512; ++p)
            if ((p & flag) == 0)
            {
                int last_pos = 0;
                short tmp = p;
                while ((tmp & 1) == 0)
                {
                    ++last_pos;
                    tmp >>= 1;
                }
                als[p] = als[p & (p - 1)] | unit[_bij(b, last_pos / 3, last_pos % 3)].candidate;
                if (_count_bit1(p) > 1 && _count_bit1(als[p]) == _count_bit1(p) + 1  // p+1个候选数恰出现在p格中，且p>1
                        && (als[p] & (1 << (n - 1)))  // 这p格含有候选数n
                        )
                {
                    vector<int> selected_pos;
                    int px = 0;
                    short tmp = p;
                    while (tmp)
                    {
                        if (tmp & 1) selected_pos.push_back(_bij(b, px / 3, px % 3));
                        tmp >>= 1;
                        ++px;
                    }

                    vector<int> v;
                    for (auto pos : selected_pos)
                        if (getBit(pos, n))
                            v.push_back(pos);
                    if (v != cn_start.vpos) continue;

                    for (int nx = 1; nx <= 9; ++nx)
                        if (nx != n && (als[p] & (1 << (nx - 1))))
                        {
                            vector<int> v;
                            for (auto pos : selected_pos)
                                if (getBit(pos, nx))
                                    v.push_back(pos);
                            chain_node new_node(v, nx, _Weak, _ALS_Box);
                            if (v.size() == 1)
                                new_node.dtype = _None;
                            else if (getPos(new_node) < 2430)  // 退化为基本行列节点
                                new_node.dtype = get_id(getPos(new_node)) < 3 ? _Row : _Column;
                            if (!gained[getPos(new_node)] && !visited[getPos(new_node)])
                            {
                                ++technique_count.ALS;
                                gained[getPos(new_node)] = true;
                                push_chain_node(cn_start, new_node);
                            }
                        }
                }
            }
        #endif
    }
    // #endif
}

void Solver::dynamic_chain_merge(chain_node& merged_node)
{
    if (merged) return;
    // cout << "merge called.\n";
    this->merged_node = merged_node;
    merged = true;
    ever_merged[getPos(merged_node)] = true;
    ++merge_times;
    memset(visited, false, sizeof(visited));
    memset(gained, false, sizeof(gained));
    memset(btype, _shared2, sizeof(btype));

    // 回溯将沿途的节点均设置为访问过
    int last1 = merge_subpos[0];
    while (last1 != split_pos[0])
    {
        visited[last1] = true;
        btype[last1] = _branch1;
        last1 = parent_branch1[last1];
    }
    btype[last1] = _branch1;

    int last2 = merge_subpos[1];
    while (last2 != split_pos[1])
    {
        visited[last2] = true;
        btype[last2] = _branch2;
        last2 = parent_branch2[last2];
    }
    btype[last2] = _branch1;

    int pos = getPos(splitted_node);
    while (parent[pos] != -1)
    {
        visited[pos] = true;
        btype[pos] = _shared1;
        pos = parent[pos];
    }
    visited[pos] = true;
    btype[pos] = _shared1;
    Fringe.clear();

    btype[getPos(merged_node)] = _shared2;
    push_chain_node(merged_node, merged_node);
}

void Solver::weakInference_dynamic(chain_node& cn_start)
{
    // cout << getPos(cn_start) << "weak called.\n";
    // if (hasBranch && !merged && btype[getPos(cn_start)] == _shared1)
    //     return;
    // if (merged && btype[getPos(cn_start)] != _shared2)
    //     return;

    // if (merged && btype[getPos(cn_start)] == _shared2)
    //     cout << "merged weak.\n";

    int n = cn_start.number;

    if (cn_start.dtype == _None)
    {
        #ifdef NONE
        vector<chain_node> new_strong_nodes;
        // 格内弱关系
        if (!insideUnit[cn_start.vpos[0]])
        {
            for (int nx = 1; nx <= 9; ++nx)
                if (getBit(cn_start.vpos[0], nx) && nx != cn_start.number)
                {
                    chain_node new_node(cn_start.vpos[0], nx, _Strong);
                    if (push_chain_node(cn_start, new_node))
                    {
                        new_strong_nodes.push_back(new_node);
                        insideUnit[cn_start.vpos[0]] = true;
                    }
                }
        }
        else if (hasBranch && !merged)
            for (int nx = 1; nx <= 9; ++nx)
            {
                chain_node tmp(cn_start.vpos[0], nx, _Strong);
                if (btype[getPos(tmp)] != _shared1 && (visited[getPos(tmp)] || find(Fringe.begin(), Fringe.end(), tmp) != Fringe.end()))
                    if (cn_not_equal_except_itype(tmp, splitted_node)
                            && ((btype[getPos(cn_start)] == _branch1 && is_visited_branch2(getPos(tmp)))
                                    || (btype[getPos(cn_start)] == _branch2 && is_visited_branch1(getPos(tmp)))))
                    {
                        if (btype[getPos(tmp)] == _branch1)
                            parent_branch2[getPos(tmp)] = getPos(cn_start);
                        else
                            parent_branch1[getPos(tmp)] = getPos(cn_start);
                        merge_subpos[0] = merge_subpos[1] = getPos(tmp);
                        dynamic_chain_merge(tmp);
                        return;
                    }
            }
        // 同区域弱关系
        for (auto i : getWeakInferenceBlock_dynamic(cn_start, pii(cn_start.vpos[0], cn_start.number)))
        {
            chain_node new_node(i.first, i.second, _Strong);
            if (push_chain_node(cn_start, new_node))
                new_strong_nodes.push_back(new_node);
        }
        #endif

        #ifdef dDYNAMIC_CHAIN_MERGENODES
        // 合并节点
        if (hasBranch)
            for (chain_node& new_cn : new_strong_nodes)
            {
                int b = _b(new_cn.vpos[0]), rx = _rinbox(new_cn.vpos[0]), cx = _cinbox(new_cn.vpos[0]), number = new_cn.number;
                // 合并为基本行广义节点
                int count = 0;
                bool mergeable = true;
                chain_node other_cnode;
                for (int jx = 0; jx < 3; ++jx)
                {
                    int p = _bij(b, rx, jx);
                    chain_node tmp(p, number, _Strong);
                    if (getBit(p, number))
                    {
                        ++count;
                        if (tmp != new_cn)
                            other_cnode = tmp;
                        if (!is_visited(getPos(tmp)))
                        {
                            mergeable = false;
                            break;
                        }
                    }
                }
                if (mergeable && count == 2)
                {
                    vector<int> vpos_tmp;
                    for(int jx = 0; jx < 3; ++jx)
                        if (getBit(_bij(b, rx, jx), number))
                            vpos_tmp.push_back(_bij(b, rx, jx));
                    chain_node new_node(vpos_tmp, number, _Strong, _Row);

                    bool has_btype1 = false, has_btype2 = false, has_sharedx_type = false;
                    for (auto p : new_node.vpos)
                    {
                        chain_node cn_tmp(p, number, _Strong);
                        if (is_visited_branch1(getPos(cn_tmp)))
                            has_btype1 = true;
                        if (is_visited_branch2(getPos(cn_tmp)))
                            has_btype2 = true;
                        if (is_visited_sharedx(getPos(cn_tmp)))
                            has_sharedx_type = true;
                    }

                    if (!has_sharedx_type && has_btype1 && has_btype2)
                    {
                        // cout << "mergeablde.\n";
                        if (merge_times < Max_Merge_Times && !merged && !ever_merged[getPos(new_node)])
                        {
                            bool ok = false;
                            if (is_visited_branch1(getPos(new_cn)) && is_visited_branch1(getPos(other_cnode))
                                && is_visited_branch2(getPos(new_cn)) && is_visited_branch2(getPos(other_cnode)))
                            {
                                merge_subpos[0] = getPos(new_cn);
                                merge_subpos[1] = getPos(other_cnode);
                                ok = true;
                            }
                            if (ok && cn_not_equal_except_itype(new_node, splitted_node))
                            {
                                dynamic_chain_merge(new_node);
                                return;
                            }
                        }
                    }
                    else if (merged && has_sharedx_type && !has_btype1 && !has_btype2)
                        push_chain_node(cn_start, new_node);
                }

                // 合并为基本列广义节点
                count = 0;
                mergeable = true;
                for (int ix = 0; ix < 3; ++ix)
                {
                    int p = _bij(b, ix, cx);
                    chain_node tmp(p, number, _Strong);
                    if (getBit(p, number))
                    {
                        ++count;
                        if (tmp != new_cn)
                            other_cnode = tmp;
                        if (!is_visited(getPos(tmp)))
                        {
                            mergeable = false;
                            break;
                        }
                    }
                }
                if (mergeable && count == 2)
                {
                    vector<int> vpos_tmp;
                    for(int ix = 0; ix < 3; ++ix)
                        if (getBit(_bij(b, ix, cx), number))
                            vpos_tmp.push_back(_bij(b, ix, cx));
                    chain_node new_node(vpos_tmp, number, _Strong, _Column);

                    bool has_btype1 = false, has_btype2 = false, has_sharedx_type = false;
                    for (auto p : new_node.vpos)
                    {
                        chain_node cn_tmp(p, number, _Strong);
                        if (is_visited_branch1(getPos(cn_tmp)))
                            has_btype1 = true;
                        if (is_visited_branch2(getPos(cn_tmp)))
                            has_btype2 = true;
                        if (is_visited_sharedx(getPos(cn_tmp)))
                            has_sharedx_type = true;
                    }

                    if (!has_sharedx_type && has_btype1 && has_btype2)
                    {
                        // cout << "mergeablde.\n";
                        if (merge_times < Max_Merge_Times && !merged && !ever_merged[getPos(new_node)])
                        {
                            bool ok = false;
                            if (is_visited_branch1(getPos(new_cn)) && is_visited_branch1(getPos(other_cnode))
                                && is_visited_branch2(getPos(new_cn)) && is_visited_branch2(getPos(other_cnode)))
                            {
                                merge_subpos[0] = getPos(new_cn);
                                merge_subpos[1] = getPos(other_cnode);
                                ok = true;
                            }
                            if (ok && cn_not_equal_except_itype(new_node, splitted_node))
                            {
                                dynamic_chain_merge(new_node);
                                return;
                            }
                        }
                    }
                    else if (merged && has_sharedx_type && !has_btype1 && !has_btype2)
                        push_chain_node(cn_start, new_node);
                }
            }
        #endif
    }
    if (cn_start.dtype == _Row || cn_start.dtype == _None)
    {
        #ifdef ROW
        int b0 = _b(cn_start.vpos[0]);
        int bx0 = b0 / 3;
        int by0 = b0 % 3;
        int r = _r(cn_start.vpos[0]);
        int ix0 = _iinbox(r);
        int jx0 = _cinbox(cn_start.vpos[0]);

        // 1宫内其他位置的弱链
        // 1.1宫内其他行的单元格
        if (cn_start.dtype == _Row)
            for (int ix = 0; ix < 3; ++ix)
                if (ix != ix0 && br_count[n][b0][ix] == 1)
                    for (int jx = 0; jx < 3; ++jx)
                        if (getBit(_bij(b0, ix, jx), n))
                        {
                            chain_node new_node(_bij(b0, ix, jx), n, _Strong, _None);
                            push_chain_node(cn_start, new_node);
                            break;
                        }
        // 1.2宫内其他行的行广义节点
        for (int ix = 0; ix < 3; ++ix)
            if (ix != ix0 && br_count[n][b0][ix] >= 2)
            {
                vector<int> tmp;
                for (int jx = 0; jx < 3; ++jx)
                    if (getBit(_bij(b0, ix, jx), n))
                        tmp.push_back(_bij(b0, ix, jx));
                chain_node new_node(tmp, n, _Strong, _Row);
                push_chain_node(cn_start, new_node);
            }
        // 1.3宫内其他列的列广义节点
        if (cn_start.dtype == _None)
            for (int jx = 0; jx < 3; ++jx)
                if (jx != jx0 && bc_count[n][b0][jx] >= 2)
                {
                    vector<int> tmp;
                    for (int ix = 0; ix < 3; ++ix)
                        if (getBit(_bij(b0, ix, jx), n))
                            tmp.push_back(_bij(b0, ix, jx));
                    chain_node new_node(tmp, n, _Strong, _Column);
                    push_chain_node(cn_start, new_node);
                }

        // 2该行其他宫的剩余该候选数的格及广义格
        for (int by = 0; by < 3; ++by)
            if (by != by0)
            {
                int b = 3 * bx0 + by;
                if (cn_start.dtype == _Row && br_count[n][b][_iinbox(r)] == 1)
                {
                    for (int jx = 0; jx < 3; ++jx)
                        if (getBit(_bij(b, _iinbox(r), jx), n))
                        {
                            chain_node new_node(_bij(b, _iinbox(r), jx), n, _Strong, _None);
                            push_chain_node(cn_start, new_node);
                        }
                }
                else if (br_count[n][b][_iinbox(r)] >= 2
                            && (cn_start.dtype == _Row || (cn_start.dtype == _None && br_count[n][b0][_iinbox(r)] == 1)))
                {
                    vector<int> tmp;
                    for (int jx = 0; jx < 3; ++jx)
                        if (getBit(_bij(b, _iinbox(r), jx), n))
                            tmp.push_back(_bij(b, _iinbox(r), jx));
                    chain_node new_node(tmp, n, _Strong, _Row);
                    push_chain_node(cn_start, new_node);
                }
            }
        #endif
    }
    if (cn_start.dtype == _Column || cn_start.dtype == _None)
    {
        #ifdef COL
        // 该列其他宫的剩余该候选数的格及广义格
        int b0 = _b(cn_start.vpos[0]);
        int bx0 = b0 / 3;
        int by0 = b0 % 3;
        int c = _c(cn_start.vpos[0]);
        int ix0 = _rinbox(cn_start.vpos[0]);
        int jx0 = _jinbox(c);

        // 1宫内其他位置的强链
        // 1.1宫内其他列的单元格
        if (cn_start.dtype == _Column)
            for (int jx = 0; jx < 3; ++jx)
                if (jx != jx0 && bc_count[n][b0][jx] == 1)
                    for (int ix = 0; ix < 3; ++ix)
                        if (getBit(_bij(b0, ix, jx), n))
                        {
                            chain_node new_node(_bij(b0, ix, jx), n, _Strong, _None);
                            push_chain_node(cn_start, new_node);
                            break;
                        }
        // 1.2宫内其他列的列广义节点
        for (int jx = 0; jx < 3; ++jx)
            if (jx != jx0
                    && bc_count[n][b0][jx] >= 2
                    && (cn_start.dtype == _Column || (cn_start.dtype == _None && bc_count[n][b0][jx0] == 1)))
            {
                vector<int> tmp;
                for (int ix = 0; ix < 3; ++ix)
                    if (getBit(_bij(b0, ix, jx), n))
                        tmp.push_back(_bij(b0, ix, jx));
                chain_node new_node(tmp, n, _Strong, _Column);
                push_chain_node(cn_start, new_node);
            }
        // 1.3宫内其他行的行广义节点
        if (cn_start.dtype == _None)
            for (int ix = 0; ix < 3; ++ix)
                if (ix != ix0 && br_count[n][b0][ix] >= 2)
                {
                    vector<int> tmp;
                    for (int jx = 0; jx < 3; ++jx)
                        if (getBit(_bij(b0, ix, jx), n))
                            tmp.push_back(_bij(b0, ix, jx));
                    chain_node new_node(tmp, n, _Strong, _Row);
                    push_chain_node(cn_start, new_node);
                }

        // 2该行其他宫的剩余该候选数的格及广义格
        for (int bx = 0; bx < 3; ++bx)
            if (bx != bx0)
            {
                int b = 3 * bx + by0;
                if (cn_start.dtype == _Column && bc_count[n][b][_jinbox(c)] == 1)
                {
                    for (int ix = 0; ix < 3; ++ix)
                        if (getBit(_bij(b, ix, _jinbox(c)), n))
                        {
                            chain_node new_node(_bij(b, ix, _jinbox(c)), n, _Strong, _None);
                            push_chain_node(cn_start, new_node);
                        }
                }
                else if (bc_count[n][b][_jinbox(c)] >= 2
                            && (cn_start.dtype == _Column || (cn_start.dtype == _None && bc_count[n][b0][_jinbox(c)] == 1)))
                {
                    vector<int> tmp;
                    for (int ix = 0; ix < 3; ++ix)
                        if (getBit(_bij(b, ix, _jinbox(c)), n))
                            tmp.push_back(_bij(b, ix, _jinbox(c)));
                    chain_node new_node(tmp, n, _Strong, _Column);
                    push_chain_node(cn_start, new_node);
                }
            }
        #endif
    }

    // 以ALS节点为头的弱关系
    if (cn_start.dtype == _ALS_Row)
    {
        #ifdef ALS_ROW
        int r = _r(cn_start.vpos[0]);
        short als_r = 0;
        for (auto p : cn_start.vpos)
            als_r |= 1 << _c(p);
        for (int j = 0; j < 9; ++j)
            if (unit[9 * r + j].left == 0)
                als_r |= 1 << j;
        // 单元格节点
        for (int j = 0; j < 9; ++j)
            if ((als_r & (1 << j)) == 0 && getBit(9 * r + j, n))
            {
                chain_node new_node(9 * r + j, n, _Strong);
                push_chain_node(cn_start, new_node);
            }
        // 基本广义节点
        for (int p = 0; p < 3; p++)
            if ((als_r & flag[p]) == 0)
            {
                vector<int> tmp;
                for (int jx = 0; jx < 3; ++jx)
                    if (getBit(9 * r + 3 * p + jx, n))
                        tmp.push_back(9 * r + 3 * p + jx);
                if (tmp.size() <= 1) continue;
                
                chain_node new_node(tmp, n, _Strong, _Row);
                push_chain_node(cn_start, new_node);
            }
        #endif
    }
    else if (cn_start.dtype == _ALS_Column)
    {
        #ifdef ALS_COL
        int c = _c(cn_start.vpos[0]);
        short als_c = 0;
        for (auto p : cn_start.vpos)
            als_c |= 1 << _r(p);
        for (int i = 0; i < 9; ++i)
            if (unit[9 * i + c].left == 0)
                als_c |= 1 << i;
        // 单元格节点
        for (int i = 0; i < 9; ++i)
            if ((als_c & (1 << i)) == 0 && getBit(9 * i + c, n))
            {
                chain_node new_node(9 * i + c, n, _Strong);
                push_chain_node(cn_start, new_node);
            }
        // 基本广义节点
        for (int p = 0; p < 3; p++)
            if ((als_c & flag[p]) == 0)
            {
                vector<int> tmp;
                for (int ix = 0; ix < 3; ++ix)
                    if (getBit(9 * (3 * p + ix) + c, n))
                        tmp.push_back(9 * (3 * p + ix) + c);
                if (tmp.size() <= 1) continue;
                
                chain_node new_node(tmp, n, _Strong, _Row);
                push_chain_node(cn_start, new_node);
            }
        #endif
    }
    else if (cn_start.dtype == _ALS_Box)
    {
        #ifdef ALS_BOX
        int b = _b(cn_start.vpos[0]);
        short als_b = 0;
        for (auto p : cn_start.vpos)
            als_b |= 1 << _ninbox(p);
        for (int ix = 0; ix < 3; ++ix)
            for (int jx = 0; jx < 3; ++jx)
                if (unit[_bij(b, ix, jx)].left == 0)
                    als_b |= 1 << (3 * ix + jx);
        // 单元格节点
        for (int ix = 0; ix < 3; ++ix)
            for (int jx = 0; jx < 3; ++jx)
                if ((als_b & (1 << (3 * ix + jx))) == 0 && getBit(_bij(b, ix, jx), n))
                {
                    chain_node new_node(_bij(b, ix, jx), n, _Strong);
                    push_chain_node(cn_start, new_node);
                }
        // 基本广义节点
        // 行
        for (int p = 0; p < 3; p++)
            if ((als_b & flag[p]) == 0)
            {
                vector<int> tmp;
                for (int jx = 0; jx < 3; ++jx)
                    if (getBit(_bij(b, p, jx), n))
                        tmp.push_back(_bij(b, p, jx));
                if (tmp.size() <= 1) continue;
                
                chain_node new_node(tmp, n, _Strong, _Row);
                push_chain_node(cn_start, new_node);
            }
        // 列
        for (int p = 3; p < 6; p++)
            if ((als_b & flag[p]) == 0)
            {
                vector<int> tmp;
                for (int ix = 0; ix < 3; ++ix)
                    if (getBit(_bij(b, ix, p - 3), n))
                        tmp.push_back(_bij(b, ix, p - 3));
                if (tmp.size() <= 1) continue;
                
                chain_node new_node(tmp, n, _Strong, _Column);
                push_chain_node(cn_start, new_node);
            }
        #endif
    }
}

bool Solver::chain_deleteCandidates_dynamic(chain_node& cn_head, chain_node& front)
{
    if (!hasBranch)
        return false;

    vector<pii> del_unit;
    
    // 动态链删数只考虑同数
    // 两种情形可能删数：
    // 1.分支后合并，删去头尾共同对应区域
    // 2.分支后未合并，删去链头、两个分支链尾共同影响区域
    if (merged)
    {
        if (btype[getPos(cn_head)] == _shared1 && btype[getPos(front)] == _shared2)
        {
            // 以下的条件判断始终最多只有一个被执行
            if (cn_head.dtype == _None && front.dtype == _None)
            {
                int head_pos = cn_head.vpos[0], head_n = cn_head.number;

                if (head_n == front.number && head_pos == front.vpos[0])
                {
                    ++technique_count.Chain;
                    
                    fillNumber(head_pos, head_n);

                    Fringe.clear();  // 此时外层循环也不满足条件，直接退出到更外层的for循环
                    return true;
                }
                // 首尾同数链
                else 
                    if (head_n == front.number && deleteSharedAffectBlock(head_n, head_pos, front.vpos[0], del_unit))
                    {
                        ++technique_count.Chain;
                        
                        #ifdef DEBUG
                        cout << "\ndynamic chain deleted called, merged.\n";
                        cout << "cn_head: " << cn_head;
                        cout << "split_node: " << getPos(splitted_node) << ", " << splitted_node;
                        cout << "merge_node: " << getPos(merged_node) << ", " << merged_node;
                        cout << "front: " << getPos(front) << ", "  << front;
                        
                        cout << "shared path2:\n";
                        int last = getPos(front);
                        while (last != getPos(merged_node))
                        {
                            cout << get_chain_node(last);
                            last = parent[last];
                        }
                        cout << get_chain_node(last);

                        cout << "branch1:\n";
                        int last1 = merge_subpos[0];
                        while (last1 != split_pos[0])
                        {
                            cout << get_chain_node(last1);
                            last1 = parent_branch1[last1];
                        }
                        cout << get_chain_node(last1) << endl;
                        
                        cout << "branch2:\n";
                        int last2 = merge_subpos[1];
                        while (last2 != split_pos[1])
                        {
                            cout << get_chain_node(last2);
                            last2 = parent_branch2[last2];
                        }
                        cout << get_chain_node(last2) << endl;
                        
                        cout << "shared path1:\n";
                        last = getPos(splitted_node);
                        while (last != getPos(cn_head))
                        {
                            cout << get_chain_node(last);
                            last = parent[last];
                        }
                        cout << get_chain_node(last);
                        #endif

                        vector<pii> tmp;
                        for (auto u : del_unit)
                            deleteCandidate(u.first, u.second, tmp, SU6);
                        autoFillNumber(del_unit);
                        Fringe.clear();  // 此时外层循环也不满足条件，直接退出到更外层的for循环
                        printAns();
                        return true;
                    }
            }
            else if (cn_head.vpos != front.vpos && cn_head.number == front.number
                    && deleteSharedAffectBlock(cn_head.number, cn_head.vpos, front.vpos, del_unit))
                {
                    ++technique_count.Chain;

                    #ifdef DEBUG
                        cout << "\ndynamic chain deleted called, merged.\n";
                        cout << "cn_head: " << cn_head;
                        cout << "split_node: " << getPos(splitted_node) << ", " << splitted_node;
                        cout << "merge_node: " << getPos(merged_node) << ", " << merged_node;
                        cout << "front: " << getPos(front) << ", "  << front;
                        
                        cout << "shared path2:\n";
                        int last = getPos(front);
                        while (last != getPos(merged_node))
                        {
                            cout << get_chain_node(last);
                            last = parent[last];
                        }
                        cout << get_chain_node(last);

                        cout << "branch1:\n";
                        int last1 = merge_subpos[0];
                        while (last1 != split_pos[0])
                        {
                            cout << get_chain_node(last1);
                            last1 = parent_branch1[last1];
                        }
                        cout << get_chain_node(last1) << endl;
                        
                        cout << "branch2:\n";
                        int last2 = merge_subpos[1];
                        while (last2 != split_pos[1])
                        {
                            cout << get_chain_node(last2);
                            last2 = parent_branch2[last2];
                        }
                        cout << get_chain_node(last2) << endl;
                        
                        cout << "shared path1:\n";
                        last = getPos(splitted_node);
                        while (last != getPos(cn_head))
                        {
                            cout << get_chain_node(last);
                            last = parent[last];
                        }
                        cout << get_chain_node(last);
                        #endif

                    vector<pii> tmp;
                    for (auto u : del_unit)
                        deleteCandidate(u.first, u.second, tmp, SU6);
                    autoFillNumber(del_unit);
                    Fringe.clear();  // 此时外层循环也不满足条件，直接退出到更外层的for循环
                    return true;
                }
        }
    }
    else if (cn_head.number == front.number && hasBranch && !merged && !ever_merged[getPos(front)] && btype[getPos(front)] != _shared1)  // 分裂但未合并，删除链头和两条分链的弱节点这3个节点共同影响的格的候选数
    {
        if (us_visited_branch1.find(getPos(front)) != us_visited_branch1.end())
        {
            for (auto i = us_visited_branch2.begin(); i != us_visited_branch2.end(); ++i)
                if (*i != getPos(front) && *i != getPos(cn_head) && get_chain_node(*i).number == front.number)
                {
                    chain_node tmp(get_chain_node(*i));
                    if (tmp.itype == _Weak
                            && deleteSharedAffectBlock(front.number, cn_head.vpos, front.vpos, tmp.vpos, del_unit))
                    {
                        ++technique_count.Chain;

                        #ifdef DEBUG
                        cout << "\ndynamic chain deleted called, not merged.\n";
                        cout << "cn_head: " << getPos(cn_head) << ": " << cn_head;
                        cout << "split_node: " << getPos(splitted_node) << ": " << splitted_node;
                        cout << "front: " << getPos(front) << ": " << front;
                        cout << "*i: " << *i << ": " << get_chain_node(*i);

                        cout << "shared path:\n";
                        int last = getPos(splitted_node);
                        while (last != getPos(cn_head))
                        {
                            cout << get_chain_node(last);
                            last = parent[last];
                        }
                        cout << get_chain_node(last);

                        cout << "branch1:\n";
                        last = getPos(front);
                        while (last != split_pos[0])
                        {
                            cout << get_chain_node(last);
                            last = parent_branch1[last];
                        }
                        cout << get_chain_node(last);

                        cout << "branch2:\n";
                        last = *i;
                        while (last != split_pos[1])
                        {
                            cout << get_chain_node(last);
                            last = parent_branch2[last];
                        }
                        cout << get_chain_node(last);
                        #endif

                        vector<pii> tmp;
                        for (auto u : del_unit)
                            deleteCandidate(u.first, u.second, tmp, SU6);
                        autoFillNumber(del_unit);
                        Fringe.clear();  // 此时外层循环也不满足条件，直接退出到更外层的for循环
                        return true;
                    }
                }
        }
        else if (us_visited_branch2.find(getPos(front)) != us_visited_branch2.end())
        {
            for (auto i = us_visited_branch1.begin(); i != us_visited_branch1.end(); ++i)
                if (*i != getPos(front) && *i != getPos(cn_head) && get_chain_node(*i).number == front.number)
                {
                    chain_node tmp(get_chain_node(*i));
                    if (tmp.itype == _Weak
                            && deleteSharedAffectBlock(front.number, cn_head.vpos, front.vpos, tmp.vpos, del_unit))
                    {
                        ++technique_count.Chain;

                        #ifdef DEBUG
                        cout << "\ndynamic chain deleted called, not merged.\n";
                        cout << "cn_head: " << getPos(cn_head) << ": " << cn_head;
                        cout << "split_node: " << getPos(splitted_node) << ": " << splitted_node;
                        cout << "front: " << getPos(front) << ": " << front;
                        cout << "*i: " << *i << ": " << get_chain_node(*i);

                        cout << "shared path:\n";
                        int last = getPos(splitted_node);
                        while (last != getPos(cn_head))
                        {
                            cout << get_chain_node(last) << ' ';
                            last = parent[last];
                        }
                        cout << get_chain_node(last);

                        cout << "branch1:\n";
                        last = getPos(front);
                        while (last != split_pos[1])
                        {
                            cout << get_chain_node(last);
                            last = parent_branch2[last];
                        }
                        cout << get_chain_node(last);

                        cout << "branch2:\n";
                        last = *i;
                        while (last != split_pos[0])
                        {
                            cout << get_chain_node(last);
                            last = parent_branch1[last];
                        }
                        cout << get_chain_node(last);
                        #endif

                        vector<pii> tmp;
                        for (auto u : del_unit)
                            deleteCandidate(u.first, u.second, tmp, SU6);
                        autoFillNumber(del_unit);
                        Fringe.clear();  // 此时外层循环也不满足条件，直接退出到更外层的for循环
                        return true;
                    }
                }
        }
    }
    return false;
}

void Solver::DynamicChain_Branch()
{
    if (solvedUnits == 81) return;

    if (level < 8) level = 8;
    
    for (int n = 1; n <= 9; ++n)
        for (int b = 0; b < 9; b++)  // 以宫为主序
        {
            deque<chain_node> begin_nodes;
            #ifdef NONE
            // 单元节点
            for (int ix = 0 ; ix < 3; ++ix)
                for (int jx = 0; jx < 3; ++jx)
                    if (getBit(_bij(b, ix, jx), n))
                        begin_nodes.push_back(chain_node(_bij(b, ix, jx), n, _Strong, _None));
            #endif
            #ifdef ROW
            // 基本组合节点
            // 行
            for (int ix = 0; ix < 3; ++ix)
                if (br_count[n][b][ix] >= 2)
                {
                    vector<int> tmp;
                    for (int jx = 0; jx < 3; ++jx)
                        if (getBit(_bij(b, ix, jx), n))
                            tmp.push_back(_bij(b, ix, jx));
                    begin_nodes.push_back(chain_node(tmp, n, _Strong, _Row));
                }
            #endif
            #ifdef COL
            // 列
            for (int jx = 0; jx < 3; ++jx)
                if (bc_count[n][b][jx] >= 2)
                {
                    vector<int> tmp;
                    for (int ix = 0; ix < 3; ++ix)
                        if (getBit(_bij(b, ix, jx), n))
                            tmp.push_back(_bij(b, ix, jx));
                    begin_nodes.push_back(chain_node(tmp, n, _Strong, _Column));
                }
            #endif

            while (!begin_nodes.empty())
            {
                auto cn_head = begin_nodes.front();
                
                // 以cn_head为头节点，不断循环直至无删数
                ever_splited = new bool[total_nodes];
                ever_merged = new bool[total_nodes];
                for (int p = 0; p < total_nodes; ++p)
                {
                    ever_splited[p] = ever_merged[p] = false;
                    btype[p] = _shared1;
                }
                split_times = merge_times = 0;
                mFlag = true;
                while (mFlag)
                {
                    mFlag = false;
                    if ((cn_head.dtype == _None && getBit(cn_head.vpos[0], cn_head.number))
                            || (cn_head.dtype == _Row && br_count[cn_head.number][_b(cn_head.vpos[0])][_rinbox(cn_head.vpos[0])] >= 2)
                            || (cn_head.dtype == _Column && bc_count[cn_head.number][_b(cn_head.vpos[0])][_cinbox(cn_head.vpos[0])] >= 2))
                    {
                        current_cn_head = cn_head;

                        memset(visited, false, sizeof(visited));
                        memset(gained, false,sizeof(gained));
                        memset(insideUnit, false, sizeof(insideUnit));
                        us_visited_branch1.clear();
                        us_visited_branch2.clear();
                        us_visited_shared1.clear();
                        us_visited_shared2.clear();

                        Fringe.clear();
                        // 路径为生成树，用双亲表示法记录，最多考虑2分支
                        parent = new int[total_nodes];
                        parent_branch1 = new int[total_nodes];
                        parent_branch2 = new int[total_nodes];

                        // 准备工作
                        // 以强链开始，先把头节点指出去的强链尾都加入Fringe集合
                        visited[getPos(cn_head)] = true;  // 由于从强关系开始，头结点可被视为一个弱关系节点尾
                        parent[getPos(cn_head)] = -1;  // 标志路径头
                        btype[getPos(cn_head)] = _shared1;
                        
                        hasBranch = merged = false;  // 只考虑2个分支
                        strongInference_dynamic(cn_head);

                        // 正式开始循环
                        while (!Fringe.empty())
                        {
                            auto front = Fringe.front();
                            Fringe.pop_front();
                            if (visited[getPos(front)])
                                continue;
                            visited[getPos(front)] = true;
                            
                            if (front.itype == _Strong)  // 弱关系尾，将加入新的强关系
                                strongInference_dynamic(front);
                            else  // 强关系尾，可以参与删数
                            {
                                if (chain_deleteCandidates_dynamic(cn_head, front))
                                {
                                    // cout << "actual deleted.\n";
                                    mFlag = true;
                                    break;
                                }
                                // 根据新的弱关系加入新的_Strong节点
                                weakInference_dynamic(front);
                            }
                        }
                        delete parent;
                        delete parent_branch1;
                        delete parent_branch2;
                    }
                }
                delete ever_splited;
                delete ever_merged;
                begin_nodes.pop_front();
            }
        }
}
