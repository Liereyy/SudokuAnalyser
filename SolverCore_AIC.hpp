#pragma once

#include "SolverAssist.hpp"
#include "SolverCoreBasic.hpp"
#include <deque>

void Solver::Chain()
{
    if (solvedUnits == 81) return;
    if (level < 7) level = 7;

    BasicChain(20);
}

#define NONE
#define ROW
#define COL
#define ALS_
#define ALS_BOX
#define ALS_ROW
#define ALS_COL
#define DYNAMIC_CHAIN_MERGENODES
#define AALS

void Solver::strongInference(chain_node& cn_start, deque<chain_node>& Fringe, int* parent)
{
    int n = cn_start.number;

    if (cn_start.dtype == _None)
    {
        #ifdef NONE
        pii head(cn_start.vpos[0], cn_start.number);
        // 共轭对强关系
        for (auto i : getStrongInferenceBlock_Conjugate(head))
        {
            chain_node new_node(i.first, i.second, _Weak);
            if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
            {
                Fringe.push_front(new_node);
                parent[getPos(new_node)] = getPos(cn_start);
            }
            new_node = construct_chain_node_by_nbid(i.second, _b(i.first), _rinbox(i.first), _Weak);
            if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
            {
                Fringe.push_front(new_node);
                parent[getPos(new_node)] = getPos(cn_start);
            }
            new_node = construct_chain_node_by_nbid(i.second, _b(i.first), 3 + _cinbox(i.first), _Weak);
            if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
            {
                Fringe.push_front(new_node);
                parent[getPos(new_node)] = getPos(cn_start);
            }
        }
        // 格内强关系
        if (unit[head.first].left == 2 && !insideUnit[head.first])
        {
            int the_other_candidate = getOtherCandidate(head.first, head.second);
            chain_node new_node(head.first, the_other_candidate, _Weak);
            if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
            {
                Fringe.push_front(new_node);
                parent[getPos(new_node)] = getPos(cn_start);
                insideUnit[head.first] = true;
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
                            if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                            {
                                Fringe.push_front(new_node);
                                parent[getPos(new_node)] = getPos(cn_start);
                            }
                            new_node = construct_chain_node_by_nbid(n, _b(npos), _rinbox(npos), _Weak);
                            if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                            {
                                Fringe.push_front(new_node);
                                parent[getPos(new_node)] = getPos(cn_start);
                            }
                            new_node = construct_chain_node_by_nbid(n, _b(npos), 3 + _cinbox(npos), _Weak);
                            if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                            {
                                Fringe.push_front(new_node);
                                parent[getPos(new_node)] = getPos(cn_start);
                            }
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
                if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                {
                    Fringe.push_front(new_node);
                    parent[getPos(new_node)] = getPos(cn_start);
                }
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
                if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                {
                    Fringe.push_front(new_node);
                    parent[getPos(new_node)] = getPos(cn_start);
                }
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
                            if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                            {
                                Fringe.push_front(new_node);
                                parent[getPos(new_node)] = getPos(cn_start);
                            }
                            new_node = construct_chain_node_by_nbid(n, _b(npos), _rinbox(npos), _Weak);
                            if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                            {
                                Fringe.push_front(new_node);
                                parent[getPos(new_node)] = getPos(cn_start);
                            }
                            new_node = construct_chain_node_by_nbid(n, _b(npos), 3 + _cinbox(npos), _Weak);
                            if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                            {
                                Fringe.push_front(new_node);
                                parent[getPos(new_node)] = getPos(cn_start);
                            }
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
                    if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                    {
                        Fringe.push_front(new_node);
                        parent[getPos(new_node)] = getPos(cn_start);
                    }
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
                            if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                            {
                                Fringe.push_front(new_node);
                                parent[getPos(new_node)] = getPos(cn_start);
                            }
                            new_node = construct_chain_node_by_nbid(n, _b(npos), _rinbox(npos), _Weak);
                            if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                            {
                                Fringe.push_front(new_node);
                                parent[getPos(new_node)] = getPos(cn_start);
                            }
                            new_node = construct_chain_node_by_nbid(n, _b(npos), 3 + _cinbox(npos), _Weak);
                            if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                            {
                                Fringe.push_front(new_node);
                                parent[getPos(new_node)] = getPos(cn_start);
                            }
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
                if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                {
                    Fringe.push_front(new_node);
                    parent[getPos(new_node)] = getPos(cn_start);
                }
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
                if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                {
                    Fringe.push_front(new_node);
                    parent[getPos(new_node)] = getPos(cn_start);
                }
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
                            chain_node new_node(_bij(b, ix, _jinbox(c)), n, _Weak, _None);
                            if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                            {
                                Fringe.push_front(new_node);
                                parent[getPos(new_node)] = getPos(cn_start);
                            }
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
                    if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                    {
                        Fringe.push_front(new_node);
                        parent[getPos(new_node)] = getPos(cn_start);
                    }
                }
            }
        #endif
    }
    
    // ALS
    // 尝试找ALS，如果发现有n格含有n+1个候选数，且cn_start恰好含于这个ALS中，则可形成新的ALS的强关系
    #ifdef ALS_
    if (cn_start.dtype == _Row || cn_start.dtype == _None)
    {
        #ifdef ALS_ROW
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
                            if (!gained[getPos(new_node)] && !visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                            {
                                ++technique_count.ALS;
                                gained[getPos(new_node)] = true;
                                Fringe.push_front(new_node);
                                parent[getPos(new_node)] = getPos(cn_start);
                            }
                        }
                }
            }
        #endif
    }

    if (cn_start.dtype == _Column || cn_start.dtype == _None)
    {
        #ifdef ALS_COL
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
                            if (!gained[getPos(new_node)] && !visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                            {
                                ++technique_count.ALS;
                                gained[getPos(new_node)] = true;
                                Fringe.push_front(new_node);
                                parent[getPos(new_node)] = getPos(cn_start);
                            }
                        }
                }
            }
        #endif
    }
    #endif

    if (cn_start.dtype == _None || cn_start.dtype == _Row || cn_start.dtype == _Column)
    {
        #ifdef ALS_BOX
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
                            if (!gained[getPos(new_node)] && !visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                            {
                                ++technique_count.ALS;
                                gained[getPos(new_node)] = true;
                                Fringe.push_front(new_node);
                                parent[getPos(new_node)] = getPos(cn_start);
                            }
                        }
                }
            }
        #endif
    }
}

void Solver::weakInference(chain_node& cn_start, deque<chain_node>& Fringe, int* parent)
{
    int n = cn_start.number;

    if (cn_start.dtype == _None)
    {
        #ifdef NONE
        vector<chain_node> new_strong_nodes;
        // 格内弱关系
        if (!insideUnit[cn_start.vpos[0]])
            for (int nx = 1; nx <= 9; ++nx)
                if (getBit(cn_start.vpos[0], nx) && nx != cn_start.number)
                {
                    chain_node new_node(cn_start.vpos[0], nx, _Strong);
                    if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                    {
                        Fringe.push_front(new_node);
                        new_strong_nodes.push_back(new_node);
                        parent[getPos(new_node)] = getPos(cn_start);
                    }
                    insideUnit[cn_start.vpos[0]] = true;
                }
        // 同区域弱关系
        for (auto i : getWeakInferenceBlock(pii(cn_start.vpos[0], cn_start.number)))
        {
            chain_node new_node(i.first, i.second, _Strong);
            if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
            {
                Fringe.push_front(new_node);
                new_strong_nodes.push_back(new_node);
                parent[getPos(new_node)] = getPos(cn_start);
            }
        }
        #endif

        #ifdef DYNAMIC_CHAIN_MERGENODES
        // 合并节点，DynamicChain()
        for (chain_node& new_cn : new_strong_nodes)
        {
            int b = _b(new_cn.vpos[0]), rx = _rinbox(new_cn.vpos[0]), cx = _cinbox(new_cn.vpos[0]), number = new_cn.number;
            // 合并为基本行广义节点
            int count = 0;
            bool mergeable = true;
            for (int jx = 0; jx < 3; ++jx)
            {
                int p = _bij(b, rx, jx);
                chain_node tmp(p, number, _Strong);
                if (getBit(p, number))
                {
                    ++count;
                    if (!visited[getPos(tmp)] && find(Fringe.begin(), Fringe.end(), tmp) == Fringe.end())
                    {
                        mergeable = false;
                        break;
                    }
                }
            }
            if (mergeable && count >= 2)
            {
                vector<int> vpos_tmp;
                for(int jx = 0; jx < 3; ++jx)
                    if (getBit(_bij(b, rx, jx), number))
                        vpos_tmp.push_back(_bij(b, rx, jx));
                chain_node new_node(vpos_tmp, number, _Strong, _Row);
                if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                {
                    Fringe.push_front(new_node);
                    parent[getPos(new_node)] = -2;  // -2表示有分支，且对每个单元格分别求父节点
                }
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
                    if (!visited[getPos(tmp)] && find(Fringe.begin(), Fringe.end(), tmp) == Fringe.end())
                    {
                        mergeable = false;
                        break;
                    }
                }
            }
            if (mergeable && count >= 2)
            {
                vector<int> vpos_tmp;
                for(int ix = 0; ix < 3; ++ix)
                    if (getBit(_bij(b, ix, cx), number))
                        vpos_tmp.push_back(_bij(b, ix, cx));
                chain_node new_node(vpos_tmp, number, _Strong, _Column);
                if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                {
                    Fringe.push_front(new_node);
                    parent[getPos(new_node)] = -2;  // -2表示有分支，且对每个单元格分别求父节点
                }
            }

            // 2次ALS，更高次的ALS不予考虑
            #ifdef AALS
            // 行
            vector<pii> v_tmp;

            deleteCandidate(new_cn.vpos[0], new_cn.number, v_tmp, 0);  // 假装删除，此时简化为1次ALS，之后恢复即可
            int r = _r(new_cn.vpos[0]);
            // 自底而上的dp
            short als[512];
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
                    if ((p & (1 << _c(new_cn.vpos[0]))) == 0 || (als[p] & (1 << (new_cn.number - 1))))  // new_cn.vpos[0]必选，且不包括数字new_cn.number
                        continue;

                    if (_count_bit1(p) > 1 && _count_bit1(als[p]) == _count_bit1(p) + 1)  // p+1个候选数恰出现在p格中，且p>1
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
                        
                        for (int n = 1; n <= 9; ++n)
                            if (als[p] & (1 << (n - 1)))  // 选中的格中含有数n
                            {
                                vector<int> appear_pos;
                                for (auto pos : selected_pos)
                                    if (getBit(pos, n))
                                        appear_pos.push_back(pos);

                                chain_node tmp(appear_pos, n, _Strong, _ALS_Row);
                                if (appear_pos.size() == 1)
                                    tmp.dtype = _None;
                                else if (getPos(tmp) < 2430)
                                    tmp.dtype = _Row;

                                if (visited[getPos(tmp)] || find(Fringe.begin(), Fringe.end(), tmp) != Fringe.end())
                                {
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

                                            if (tmp.dtype == _None && new_node.dtype == _None && new_node.vpos[0] == tmp.vpos[0])
                                                insideUnit[new_node.vpos[0]] = true;

                                            if (!gained[getPos(new_node)] && !visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                                            {
                                                ++technique_count.ALS;
                                                gained[getPos(new_node)] = true;
                                                Fringe.push_front(new_node);
                                                parent[getPos(new_node)] = getPos(new_cn) - 2 - total_nodes;  // getPos(new_cn) < total_nodes => 右边的值 < -2
                                            }
                                        }
                                }
                            }
                    }
                }

            // 列
            int c = _c(new_cn.vpos[0]);
            // 自底而上的dp
            als[0] = 0;
            flag = 0;  // flag记录行内已填数情况，为1代表已填数，如101_101_010指示行050_402_709(注意，flag右低位)
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
                    if ((p & (1 << _r(new_cn.vpos[0]))) == 0 || (als[p] & (1 << (new_cn.number - 1))))  // new_cn.vpos[0]必选，且不包括数字new_cn.number
                        continue;

                    if (_count_bit1(p) > 1 && _count_bit1(als[p]) == _count_bit1(p) + 1)  // p+1个候选数恰出现在p格中，且p>1
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
                        
                        for (int n = 1; n <= 9; ++n)
                            if (als[p] & (1 << (n - 1)))  // 选中的格中含有数n
                            {
                                vector<int> appear_pos;
                                for (auto pos : selected_pos)
                                    if (getBit(pos, n))
                                        appear_pos.push_back(pos);

                                chain_node tmp(appear_pos, n, _Strong, _ALS_Column);
                                if (appear_pos.size() == 1)
                                    tmp.dtype = _None;
                                else if (getPos(tmp) < 2430)
                                    tmp.dtype = _Column;

                                if (visited[getPos(tmp)] || find(Fringe.begin(), Fringe.end(), tmp) != Fringe.end())
                                {
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
                                            else if (getPos(new_node) < 2430)  // 退化为基本行节点
                                                new_node.dtype = _Column;

                                            if (tmp.dtype == _None && new_node.dtype == _None && new_node.vpos[0] == tmp.vpos[0])
                                                insideUnit[new_node.vpos[0]] = true;

                                            if (!gained[getPos(new_node)] && !visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                                            {
                                                ++technique_count.ALS;
                                                gained[getPos(new_node)] = true;
                                                Fringe.push_front(new_node);
                                                parent[getPos(new_node)] = getPos(new_cn) - 2 - total_nodes;  // getPos(new_cn) < total_nodes => 右边的值 < -2
                                            }
                                        }
                                }
                            }
                    }
                }

            // 宫
            // 自底而上的dp
            als[0] = 0;
            flag = 0;  // flag记录行内已填数情况，为1代表已填数，如101_101_010指示行050_402_709(注意，flag右低位)
            for (int bx = 0; bx < 9; ++bx)
                if (unit[_bij(b, bx / 3, bx % 3)].left == 0)
                    flag |= 1 << bx;
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
                    als[p] = als[p & (p - 1)] | unit[_bij(b, last_pos / 3, last_pos % 3)].candidate;
                    if ((p & (1 << _ninbox(new_cn.vpos[0]))) == 0 || (als[p] & (1 << (new_cn.number - 1))))  // new_cn.vpos[0]必选，且不包括数字new_cn.number
                        continue;

                    if (_count_bit1(p) > 1 && _count_bit1(als[p]) == _count_bit1(p) + 1)  // p+1个候选数恰出现在p格中，且p>1
                    {
                        vector<int> selected_pos;
                        int bx = 0;
                        short tmp = p;
                        while (tmp)
                        {
                            if (tmp & 1) selected_pos.push_back(_bij(b, bx / 3, bx % 3));
                            tmp >>= 1;
                            ++bx;
                        }
                        
                        for (int n = 1; n <= 9; ++n)
                            if (als[p] & (1 << (n - 1)))  // 选中的格中含有数n
                            {
                                vector<int> appear_pos;
                                for (auto pos : selected_pos)
                                    if (getBit(pos, n))
                                        appear_pos.push_back(pos);

                                chain_node tmp(appear_pos, n, _Strong, _ALS_Box);
                                if (appear_pos.size() == 1)
                                    tmp.dtype = _None;
                                else if (getPos(tmp) < 2430)
                                    tmp.dtype = get_id(getPos(tmp)) < 3 ? _Row : _Column;
                                if (visited[getPos(tmp)] || find(Fringe.begin(), Fringe.end(), tmp) != Fringe.end())
                                {
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
                                            else if (getPos(new_node) < 2430)  // 退化为基本行节点
                                                new_node.dtype = get_id(getPos(new_node)) < 3 ? _Row : _Column;

                                            if (tmp.dtype == _None && new_node.dtype == _None && new_node.vpos[0] == tmp.vpos[0])
                                                insideUnit[new_node.vpos[0]] = true;

                                            if (!gained[getPos(new_node)] && !visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                                            {
                                                ++technique_count.ALS;
                                                gained[getPos(new_node)] = true;
                                                Fringe.push_front(new_node);
                                                parent[getPos(new_node)] = getPos(new_cn) - 2 - total_nodes;  // getPos(new_cn) < total_nodes => 右边的值 < -2
                                            }
                                        }
                                }
                            }
                    }
                }
            resumeCandidate(new_cn.vpos[0], new_cn.number);  // 恢复
            #endif
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
                            if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                            {
                                Fringe.push_front(new_node);
                                parent[getPos(new_node)] = getPos(cn_start);
                            }
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
                if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                {
                    Fringe.push_front(new_node);
                    parent[getPos(new_node)] = getPos(cn_start);
                }
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
                    if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                    {
                        Fringe.push_front(new_node);
                        parent[getPos(new_node)] = getPos(cn_start);
                    }
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
                            if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                            {
                                Fringe.push_front(new_node);
                                parent[getPos(new_node)] = getPos(cn_start);
                            }
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
                    if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                    {
                        Fringe.push_front(new_node);
                        parent[getPos(new_node)] = getPos(cn_start);
                    }
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
                            if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                            {
                                Fringe.push_front(new_node);
                                parent[getPos(new_node)] = getPos(cn_start);
                            }
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
                if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                {
                    Fringe.push_front(new_node);
                    parent[getPos(new_node)] = getPos(cn_start);
                }
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
                    if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                    {
                        Fringe.push_front(new_node);
                        parent[getPos(new_node)] = getPos(cn_start);
                    }
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
                            if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                            {
                                Fringe.push_front(new_node);
                                parent[getPos(new_node)] = getPos(cn_start);
                            }
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
                    if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                    {
                        Fringe.push_front(new_node);
                        parent[getPos(new_node)] = getPos(cn_start);
                    }
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
                if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                {
                    Fringe.push_front(new_node);
                    parent[getPos(new_node)] = getPos(cn_start);
                }
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
                if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                {
                    Fringe.push_front(new_node);
                    parent[getPos(new_node)] = getPos(cn_start);
                }
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
                if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                {
                    Fringe.push_front(new_node);
                    parent[getPos(new_node)] = getPos(cn_start);
                }
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
                if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                {
                    Fringe.push_front(new_node);
                    parent[getPos(new_node)] = getPos(cn_start);
                }
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
                    if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                    {
                        Fringe.push_front(new_node);
                        parent[getPos(new_node)] = getPos(cn_start);
                    }
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
                if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                {
                    Fringe.push_front(new_node);
                    parent[getPos(new_node)] = getPos(cn_start);
                }
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
                if (!visited[getPos(new_node)] && find(Fringe.begin(), Fringe.end(), new_node) == Fringe.end())
                {
                    Fringe.push_front(new_node);
                    parent[getPos(new_node)] = getPos(cn_start);
                }
            }
        #endif
    }
}

bool Solver::chain_deleteCandidates(chain_node& cn_head, chain_node& front, deque<chain_node>& Fringe, int* parent, int max_length)
{
    vector<pii> del_unit;
    // if (chain_length(parent, getPos(front)) > max_length)
    //     return false;

    // 以下的条件判断始终最多只有一个被执行
    if (cn_head.dtype == _None && front.dtype == _None)
    {
        int head_pos = cn_head.vpos[0], head_n = cn_head.number;

        if (head_n == front.number && head_pos == front.vpos[0])
        {
            ++technique_count.Chain;
            
            #ifdef DEBUG
            printPath(parent, getPos(front), true);
            cout << "del ";
            for (auto u : del_unit)
                cout << ntorc(u.first) << "(" << u.second << ") ";;
            cout << endl;
            #endif
            fillNumber(head_pos, head_n);

            Fringe.clear();  // 此时外层循环也不满足条件，直接退出到更外层的for循环
            return true;
        }
        // 首尾同数链
        else if (head_n == front.number && deleteSharedAffectBlock(head_n, head_pos, front.vpos[0], del_unit))
        {
            ++technique_count.Chain;
            
            #ifdef DEBUG
            printPath(parent, getPos(front));
            cout << "del ";
            for (auto u : del_unit)
                cout << ntorc(u.first) << "(" << u.second << ") ";;
            cout << endl;
            #endif

            vector<pii> tmp;
            for (auto u : del_unit)
                deleteCandidate(u.first, u.second, tmp, SU6);
            autoFillNumber(del_unit);
            Fringe.clear();  // 此时外层循环也不满足条件，直接退出到更外层的for循环
            return true;
        }
        // 首尾异数链
        else if (head_pos != front.vpos[0] && head_n != front.number && inTheSameArea(head_pos, front.vpos[0])
            && (deleteCandidate(head_pos, front.number, del_unit, SU7, false) || deleteCandidate(front.vpos[0], head_n, del_unit, SU7, false)))
        {
            deleteCandidate(front.vpos[0], head_n, del_unit, SU7);  // 这句话可能被截断，再执行一次，即使未被截断也只增加一次判断的开销

            #ifdef DEBUG
            printPath(parent, getPos(front));
            cout << "del ";
            for (auto u : del_unit)
                cout << ntorc(u.first) << "(" << u.second << ") ";;
            cout << endl;
            #endif

            vector<pii> tmp;
            for (auto u : del_unit)
                deleteCandidate(u.first, u.second, tmp, SU6);
            autoFillNumber(head_pos, front.number);
            autoFillNumber(front.vpos[0], head_n);
            ++technique_count.Chain;

            Fringe.clear();  // 此时外层循环也不再满足条件，直接退出到更外层的for循环
            return true;
        }
    }
    else if (cn_head.vpos != front.vpos && cn_head.number == front.number
                && deleteSharedAffectBlock(cn_head.number, cn_head.vpos, front.vpos, del_unit))
    {
        ++technique_count.Chain;

        #ifdef DEBUG
        printPath(parent, getPos(front));
        cout << "del ";
            for (auto u : del_unit)
                cout << ntorc(u.first) << "(" << u.second << ") ";;
        cout << endl;
        #endif

        vector<pii> tmp;
        for (auto u : del_unit)
            deleteCandidate(u.first, u.second, tmp, SU6);
        autoFillNumber(del_unit);
        Fringe.clear();  // 此时外层循环也不满足条件，直接退出到更外层的for循环
        return true;
    }
    else if (cn_head.vpos != front.vpos && cn_head.number != front.number
                && inTheSameArea(cn_head.vpos, front.vpos) && noIntersection(cn_head.vpos, front.vpos)
                && ((cn_head.vpos.size() == 1 && deleteCandidate(cn_head.vpos[0], front.number, del_unit, SU7, false))
                    || (front.vpos.size() == 1 && deleteCandidate(front.vpos[0], cn_head.number, del_unit, SU7, false))))
    {
        ++technique_count.Chain;

        #ifdef DEBUG
        printPath(parent, getPos(front));
        cout << "del ";
            for (auto u : del_unit)
                cout << ntorc(u.first) << "(" << u.second << ") ";;
        cout << endl;
        #endif

        vector<pii> tmp;
        for (auto u : del_unit)
            deleteCandidate(u.first, u.second, tmp, SU6);
        autoFillNumber(del_unit);
        Fringe.clear();  // 此时外层循环也不满足条件，直接退出到更外层的for循环
        return true;
    }
    return false;
}

void Solver::BasicChain(int max_length)  // DFS，Fringe框架
{
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
                mFlag = true;
                while (mFlag)
                {
                    mFlag = false;
                    if ((cn_head.dtype == _None && getBit(cn_head.vpos[0], cn_head.number))
                            || (cn_head.dtype == _Row && br_count[cn_head.number][_b(cn_head.vpos[0])][_rinbox(cn_head.vpos[0])] >= 2)
                            || (cn_head.dtype == _Column && bc_count[cn_head.number][_b(cn_head.vpos[0])][_cinbox(cn_head.vpos[0])] >= 2))
                    {
                        chain_node t_cn_head(cn_head);  // cn_head可能被析构，保存一个copy

                        memset(visited, false, sizeof(visited));
                        memset(gained, false,sizeof(gained));
                        memset(insideUnit, false, sizeof(insideUnit));
                        deque<chain_node> Fringe;
                        
                        // 路径为生成树，用双亲表示法记录，最多考虑2分支
                        parent = new int[total_nodes];

                        // 准备工作
                        // 以强链开始，先把头节点指出去的强链尾都加入Fringe集合
                        visited[getPos(cn_head)] = true;  // 由于从强关系开始，头结点可被视为一个弱关系节点尾
                        parent[getPos(cn_head)] = -1;  // 标志路径头
                        
                        strongInference(cn_head, Fringe, parent);

                        // 正式开始循环
                        while (!Fringe.empty())
                        {
                            auto front = Fringe.front();
                            Fringe.pop_front();
                            if (visited[getPos(front)])
                                continue;
                            visited[getPos(front)] = true;
                            
                            if (front.itype == _Strong)  // 弱关系尾，将加入新的强关系
                                strongInference(front, Fringe, parent);
                            else  // 强关系尾，可以参与删数
                            {
                                if (chain_deleteCandidates(t_cn_head, front, Fringe, parent, max_length))
                                {
                                    mFlag = true;
                                    break;
                                }
                                // 根据新的弱关系加入新的_Strong节点
                                weakInference(front, Fringe, parent);
                            }
                        }
                        delete parent;
                    }
                }
                begin_nodes.pop_front();
            }
        }
}
