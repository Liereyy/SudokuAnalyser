// SolverCoreBasic.hpp -- implementing Solver methods

#pragma once

#include "SolverAssist.hpp"

// #define UR_LOG


// 核心方法

// Algo 1.1
void Solver::NakedSingle(int pos)
{
    if (unit[pos].left == 1)
        for (int n = 1; n <= 9; ++n)
            if (getBit(pos, n))
            {
                fillNumber(pos, n);
                return;
            }
}

// Algo 1.2
void Solver::HiddenSingle_deleteCandidatesOnly(int pos)
{
    int number = unit[pos].ans;
    resetRelatedBlock(pos);
    vector<pii> del_unit;
    for (int pos1 = 0; pos1 < 20; pos1++)
        deleteCandidate(related[pos1], number, del_unit);
}

// Algo 1.3
void Solver::HiddenSingle(int pos)
{
    int number = unit[pos].ans;
    resetRelatedBlock(pos);
    bool flag;
    flag = false;
    vector<pii> del_unit;
    for (int pos1 = 0; pos1 < 20; pos1++)
        if (deleteCandidate(related[pos1], number, del_unit))
            flag = true;
    for (auto d : del_unit)
        autoFillNumber(d.first, d.second);
    if (flag)
        ++technique_count.HiddenSingle;
}

#define POINTING
#define CLAIMING_IN_ROW
#define CLAIMING_IN_COLUMN

// 对默认参数pos=-1的处理和pos！=-1的对特定单元格填数后的处理两种情况
// pos == -1 则对所有格进行； pos != -1则对第pos格进行
void Solver::LockedCandidates(int pos) 
{
    if (solvedUnits == 81) return;

    if (level < 2) level = 2;

    // Pointing宫区块
    #ifdef POINTING
    for (int b = 0; b < 9; b++)
        if (pos == -1 || b == _b(pos))
            for (int number = 1; number <= 9; number++)
            {
                if (solvedUnits == 81) return;

                for (int rx = 0; rx < 3; ++rx)
                    if (br_count[number][b][rx] >= 2 && br_count[number][b][rx] == b_count[number][b])  // 宫b中的候选数number全在rx行
                    {
                        vector<pii> del_unit;
                        for (int j = 0; j < 9; j++)
                            if (j / 3 != b % 3 && deleteCandidate(_n(b / 3 * 3 + rx, j), number, del_unit, SU2))
                                ++technique_count.LockedCandidates;
                        autoFillNumber(del_unit);
                    }
                for (int cx = 0; cx < 3; ++cx)
                    if (bc_count[number][b][cx] >= 2 && bc_count[number][b][cx] == b_count[number][b])  // 宫b中的候选数number全在cx列
                    {
                        vector<pii> del_unit;
                        for (int i = 0; i < 9; i++)
                            if (i / 3 != b / 3 && deleteCandidate(_n(i, b % 3 * 3 + cx), number, del_unit, SU2))
                                ++technique_count.LockedCandidates;
                        autoFillNumber(del_unit);
                    }
            }
    #endif

    // Claiming 行列区块，宫排除效应
    // Claiming in Row 行区块
    #ifdef CLAIMING_IN_ROW
    for (int i = 0; i < 9; i++)
        if (pos == -1 || i ==_r(pos))
            for (int number = 1; number <= 9; number++)
            {
                if (solvedUnits == 81) return;

                for (int by = 0; by < 3; ++by)
                {
                    int b = i / 3 * 3 + by;
                    if (r_count[number][i] >= 2 && r_count[number][i] == br_count[number][b][_iinbox(i)])  // 行i中的候选数number全在宫b中
                    {
                        vector<pii> del_unit;
                        for (int ix = 0; ix < 3; ix++)
                            if (ix != _iinbox(i))
                                for (int jx = 0; jx < 3; jx++)
                                    if (deleteCandidate(_n(_bu(b) + ix, _bl(b) + jx), number, del_unit, SU2))
                                        ++technique_count.LockedCandidates;
                        autoFillNumber(del_unit);
                        break;
                    }
                }
            }
    #endif

    // Claiming in Column 列区块
    #ifdef CLAIMING_IN_COLUMN
    for (int j = 0; j < 9; j++)
        if (pos == -1 || j ==_c(pos))
            for (int number = 1; number <= 9; number++)
            {
                if (solvedUnits == 81) return;

                for (int bx = 0; bx < 3; ++bx)
                {
                    int b = bx * 3 + j / 3;
                    if (c_count[number][j] >= 2 && c_count[number][j] == bc_count[number][b][_jinbox(j)])  // 列j中的候选数number全在宫b中
                    {
                        vector<pii> del_unit;
                        for (int jx = 0; jx < 3; jx++)
                            if (jx != _jinbox(j))
                                for (int ix = 0; ix < 3; ix++)
                                    if (deleteCandidate(_n(_bu(b) + ix, _bl(b) + jx), number, del_unit, SU2))
                                        ++technique_count.LockedCandidates;
                        autoFillNumber(del_unit);
                        break;
                    }
                }
            }
    #endif
}

void Solver::Subset()
{
// 数组的实质是相关联的格的占位效应
    if (solvedUnits == 81) return;
    
    if (level < 3) level = 3;

    HiddenSubsetInRow();
    HiddenSubsetInColumn();
    HiddenSubsetInBox();
    for (int size = 2; size <= 4; size++)
    {
        NakedSubset(size, 0);
        NakedSubset(size, 1);
        NakedSubset(size, 2);
    }
}

void Solver::HiddenSubsetInRow()
{
    if (solvedUnits == 81) return;

    for (int size = 2; size <= 4; size++)
        for (int r = 0; r < 9; r++)
        {
            vector<int> qualified_num;
            for (int n = 1; n <= 9; n++)
                if (r_count[n][r] >= 2 && r_count[n][r] <= size)
                    qualified_num.push_back(n);
            int len = qualified_num.size();
            if (len < size) continue;

            int index[size];  // size阶数组的严格递增下标序列，如3阶：(0, 1, 2) -> (0, 1, 3) -> ...
            for (int p = 0; p < size; p++)
                index[p] = p;
            
            while (index[0] <= len - size)
            {
                if (solvedUnits == 81) return;

                // 由于各个参数手是在动态变化的，
                // 可能执行到这里的时候qualified_num中的有的数不再满足条件，需加以判断
                bool excluded = false;
                for (int p = 0; p < size; p++)
                    if (r_count[qualified_num[index[p]]][r] < 2)
                        excluded = true;
                if (!excluded)
                {
                    bitset<9> r_union;
                    for (int p = 0; p < size; p++)
                        r_union |= bs_r[qualified_num[index[p]]][r];
                    // 计算选定的size个候选数共出现过的格数count
                    int count = r_union.count();

                    if (count == size)
                    {
                        vector<int> del_column;
                        for (int j = 0; j < 9; j++)
                            if (r_union.test(j))
                                del_column.push_back(j);
                        bool del_num[10];
                        memset(del_num, true, sizeof(del_num));
                        for (int p = 0; p < size; p++)
                            del_num[qualified_num[index[p]]] = false;
                        vector<pii> del_unit;
                        for (int j : del_column)
                            for (int n = 1; n <= 9; n++)
                                if (del_num[n])
                                    if (deleteCandidate(_n(r, j), n, del_unit, SU3))
                                        ++technique_count.Subset;
                        autoFillNumber(del_unit);
                    }
                }
                // index[size - 1]加1并进位（并保证后一个数大于前一个数）
                ++index[size - 1];
                for (int p = size - 1; p > 0; p--)
                    if (index[p] > len - size + p)
                    {
                        index[p] -= len - size + p;
                        ++index[p - 1];
                    }
                for (int p = 1; p < size; p++)
                    if (index[p] <= index[p - 1])
                        index[p] = index[p - 1] + 1;
            }
        }
}

void Solver::HiddenSubsetInColumn()
{
    if (solvedUnits == 81) return;

    for (int size = 2; size <= 4; size++)
        for (int c = 0; c < 9; c++)
        {
            vector<int> qualified_num;
            for (int n = 1; n <= 9; n++)
                if (c_count[n][c] >= 2 && c_count[n][c] <= size)
                    qualified_num.push_back(n);
            int len = qualified_num.size();
            if (len < size) continue;

            int index[size];  // 存储要遍历的size阶数组的候选数，如3阶：(0, 1, 2) -> (0, 1, 3) -> ...
            for (int p = 0; p < size; p++)
                index[p] = p;
            
            while (index[0] <= len - size)
            {
                if (solvedUnits == 81) return;

                bool excluded = false;
                for (int p = 0; p < size; p++)
                    if (c_count[qualified_num[index[p]]][c] < 2)
                        excluded = true;
                if (!excluded)
                {
                    bitset<9> c_union;
                    for (int p = 0; p < size; p++)
                        c_union |= bs_c[qualified_num[index[p]]][c];
                    // 计算选定的size个候选数共出现过的格数count
                    int count = c_union.count();

                    if (count == size)
                    {
                        vector<int> del_row;
                        for (int i = 0; i < 9; i++)
                            if (c_union.test(i))
                                del_row.push_back(i);
                        bool del_num[10];
                        memset(del_num, true, sizeof(del_num));
                        for (int p = 0; p < size; p++)
                            del_num[qualified_num[index[p]]] = false;
                        vector<pii> del_unit;
                        for (int i : del_row)
                            for (int n = 1; n <= 9; n++)
                                if (del_num[n])
                                    if (deleteCandidate(_n(i, c), n, del_unit, SU3))
                                        ++technique_count.Subset;
                        autoFillNumber(del_unit);
                    }
                }
                
                // index[size - 1]加1并进位（并保证后一个数大于前一个数）
                ++index[size - 1];
                for (int p = size - 1; p > 0; p--)
                    if (index[p] > len - size + p)
                    {
                        index[p] -= len - size + p;
                        ++index[p - 1];
                    }
                for (int p = 1; p < size; p++)
                    if (index[p] <= index[p - 1])
                        index[p] = index[p - 1] + 1;
            }
        }
}

void Solver::HiddenSubsetInBox()
{
    if (solvedUnits == 81) return;

    for (int size = 2; size <= 4; size++)
        for (int b = 0; b < 9; b++)
        {
            vector<int> qualified_num;
            for (int n = 1; n <= 9; n++)
                if (b_count[n][b] >= 2 && b_count[n][b] <= size)
                    qualified_num.push_back(n);
            int len = qualified_num.size();
            if (len < size) continue;

            int index[size];  // 存储要遍历的size阶数组的候选数，如3阶：(0, 1, 2) -> (0, 1, 3) -> ...
            for (int p = 0; p < size; p++)
                index[p] = p;
            
            while (index[0] <= len - size)
            {
                if (solvedUnits == 81) return;
    
                bool excluded = false;
                for (int p = 0; p < size; p++)
                    if (b_count[qualified_num[index[p]]][b] < 2)
                        excluded = true;
                if (!excluded)
                {
                    bitset<9> b_union;
                    for (int p = 0; p < size; p++)
                        b_union |= bs_b[qualified_num[index[p]]][b];
                    // 计算选定的size个候选数共出现过的格数count
                    int count = b_union.count();

                    if (count == size)
                    {
                        vector<int> del_box;
                        for (int px = 0; px < 9; px++)
                            if (b_union.test(px))
                                del_box.push_back(px);
                        bool del_num[10];
                        memset(del_num, true, sizeof(del_num));
                        for (int p = 0; p < size; p++)
                            del_num[qualified_num[index[p]]] = false;
                        vector<pii> del_unit;
                        for (int px : del_box)
                            for (int n = 1; n <= 9; n++)
                                if (del_num[n])
                                    if (deleteCandidate(_bij(b, px / 3, px % 3), n, del_unit, SU3))
                                        ++technique_count.Subset;
                        autoFillNumber(del_unit);
                    }
                }
                
                // index[size - 1]加1并进位（并保证后一个数大于前一个数）
                ++index[size - 1];
                for (int p = size - 1; p > 0; p--)
                    if (index[p] > len - size + p)
                    {
                        index[p] -= len - size + p;
                        ++index[p - 1];
                    }
                for (int p = 1; p < size; p++)
                    if (index[p] <= index[p - 1])
                        index[p] = index[p - 1] + 1;
            }
        }
}

// mode : 0宫，1行，2列
void Solver::NakedSubset(int size, int mode)
{
    if (solvedUnits == 81) return;

    int temp[size];  // 存储要遍历的size阶数组的候选数，如3阶：(1, 2, 3) -> (1, 2, 4) -> ... -> (7, 8, 9)
    vector<int> blank;
    for (int u = 0; u < 9; u++)
    {
        for (int p = 0; p < size; p++)
            temp[p] = p + 1;
        switch (mode)
        {
        case 0:
            blank = boxBlank(u);
            break;
        case 1:
            blank = rowBlank(u);
            break;
        case 2:
            blank = columnBlank(u);
            break;
        }

        while (temp[0] <= 10 - size)
        {
            if (solvedUnits == 81) return;
            
            int assist = 0;
            for (int p = 0; p < size; p++)
                assist |= 1 << (temp[p] - 1);
            int count = 0;
            for (int pos : blank)
                if (unit[pos].left >= 2 && (unit[pos].candidate & assist) && 
                    !(unit[pos].candidate & ~assist))  // 每个格子剩余候选数应是assist包含候选数的子集
                // 至少含有其中的两个数，且不含其它候选数
                    ++count;
            if (count == size)
            {
                vector<pii> del_unit;
                // 显性数组(步分SU3)
                for (int pos : blank)
                    if (unit[pos].candidate & ~assist) // 含有其他候选数，也就不是产生效应的这几格，防止误删
                        for (int p = 0; p < size; p++)
                            if (deleteCandidate(pos, temp[p], del_unit, SU3))
                                ++technique_count.Subset;
                autoFillNumber(del_unit);
            }
                
                        
            // temp[size - 1]加1并进位（并保证后一个数大于前一个数）
            ++temp[size - 1];
            for (int p = size - 1; p > 0; p--)
                if (temp[p] > 10 - size + p)
                {
                    temp[p] -= 10 - size + p;
                    ++temp[p - 1];
                }
            for (int p = 1; p < size; p++)
                if (temp[p] < temp[p - 1])
                    temp[p] = temp[p - 1] + 1;
        }
    }
}

void Solver::Fish()
{
    if (solvedUnits == 81) return;

    if (level < 4) level = 4;
    // 行
    for (int number = 1; number <= 9; number++)
        if (solvedNum[number] <= 5)
            for (int size = 2; size <= 4; size++)
            {
                if (solvedUnits == 81) continue;
                if (solvedNum[number] >= 4 && size >= 3) continue;  // 确定值>=4时只能出现二链列
                else if (solvedNum[number] >= 2 && size == 4) continue;  // 确定值>=2时只能出现二或三链列
                
                vector<int> selectedRow;
                for (int r = 0; r < 9; r++)
                    if (r_count[number][r] >= 2 && r_count[number][r] <= size)
                        selectedRow.push_back(r);
                int len = int(selectedRow.size());
                if (len < size) continue;

                int index[size];  // 产生用于遍历的递增序列，如：(0, 1, 2) -> (0, 1, 3) -> ... -> (6, 7, 8)
                for (int p = 0; p < size; p++)
                    index[p] = p;

                while (index[0] <= len - size)
                {
                    if (solvedUnits == 81) return;

                    bool excluded = false;
                    for (int p = 0; p < size; p++)
                        if (r_count[number][selectedRow[index[p]]] < 2)
                            excluded = true;
                    if (!excluded)
                    {
                        bitset<9> result;
                        for (int p = 0; p < size; p++)
                            result |= bs_r[number][selectedRow[index[p]]];
                        if (int(result.count()) == size)
                        {
                            bool selectedRow2[9];
                            memset(selectedRow2, false, sizeof(selectedRow2));
                            for (int p = 0; p < size; p++)
                                selectedRow2[selectedRow[index[p]]] = true;
                            vector<pii> del_unit;
                            for (int j = 0; j < 9; j++)
                                if (result.test(j))
                                    for (int i = 0; i < 9; i++)
                                        if (!selectedRow2[i])
                                            if (deleteCandidate(_n(i, j), number, del_unit, SU4))
                                                ++technique_count.Fish_Fin;
                            autoFillNumber(del_unit);
                            TechPack();
                        }
                    }

                    // index[size - 1]加1并进位（并保证后一个数大于前一个数）
                    ++index[size - 1];
                    for (int p = size - 1; p > 0; p--)
                        if (index[p] > len - size + p)
                        {
                            index[p] -= len - size + p;
                            ++index[p - 1];
                        }
                    for (int p = 1; p < size; p++)
                        if (index[p] <= index[p - 1])
                            index[p] = index[p - 1] + 1;
                }
            }
    
    // 列
    for (int number = 1; number <= 9; number++)
        if (solvedNum[number] <= 5)
            for (int size = 2; size <= 4; size++)
            {
                if (solvedUnits == 81) continue;
                if (solvedNum[number] >= 4 && size >= 3) continue;  // 确定值>=4时只能出现二链列
                else if (solvedNum[number] >= 2 && size == 4) continue;  // 确定值>=2时只能出现二或三链列
                
                vector<int> selectedColumn;
                for (int c = 0; c < 9; c++)
                    if (c_count[number][c] >= 2 && c_count[number][c] <= size)
                        selectedColumn.push_back(c);
                int len = int(selectedColumn.size());
                if (len < size) continue;

                int index[size];  // 产生用于遍历的递增序列，如：(0, 1, 2) -> (0, 1, 3) -> ... -> (6, 7, 8)
                for (int p = 0; p < size; p++)
                    index[p] = p;

                while (index[0] <= len - size)
                {
                    bool excluded = false;
                    for (int p = 0; p < size; p++)
                        if (c_count[number][selectedColumn[index[p]]] < 2)
                            excluded = true;
                    if (!excluded)
                    {
                        bitset<9> result;
                        for (int p = 0; p < size; p++)
                            result |= bs_c[number][selectedColumn[index[p]]];
                        if (int(result.count()) == size)
                        {
                            bool selectedColumn2[9];
                            memset(selectedColumn2, false, sizeof(selectedColumn2));
                            for (int p = 0; p < size; p++)
                                selectedColumn2[selectedColumn[index[p]]] = true;
                            vector<pii> del_unit;
                            for (int i = 0; i < 9; i++)
                                if (result.test(i))
                                    for (int j = 0; j < 9; j++)
                                        if (!selectedColumn2[j])
                                            if (deleteCandidate(_n(i, j), number, del_unit, SU4))
                                                ++technique_count.Fish_Fin;
                            autoFillNumber(del_unit);
                            TechPack();
                        }
                    }

                    // index[size - 1]加1并进位（并保证后一个数大于前一个数）
                    ++index[size - 1];
                    for (int p = size - 1; p > 0; p--)
                        if (index[p] > len - size + p)
                        {
                            index[p] -= len - size + p;
                            ++index[p - 1];
                        }
                    for (int p = 1; p < size; p++)
                        if (index[p] <= index[p - 1])
                            index[p] = index[p - 1] + 1;
                }
            }
}

void Solver::Fin()
{
    if (solvedUnits == 81) return;
    if (level < 5) level = 5;

    // 行
    for (int number = 1; number <= 9; number++)
        if (solvedNum[number] <= 5)
            for (int size = 2; size <= 4; size++)
            {
                if (solvedUnits == 81) continue;
                if (solvedNum[number] >= 4 && size >= 3) continue;  // 确定值>=4时只能出现二链列
                else if (solvedNum[number] >= 2 && size == 4) continue;  // 确定值>=2时只能出现二或三链列
                
                vector<int> selectedRow;
                for (int r = 0; r < 9; r++)
                    if (r_count[number][r] >= 2 && r_count[number][r] <= size + 1)  // 只考虑一个鱼鳍
                        selectedRow.push_back(r);
                int len = int(selectedRow.size());
                if (len < size) continue;

                int index[size];  // 产生用于遍历的递增序列，如：(0, 1, 2) -> (0, 1, 3) -> ... -> (6, 7, 8)
                for (int p = 0; p < size; p++)
                    index[p] = p;

                while (index[0] <= len - size)
                {
                    bool excluded = false;
                    for (int p = 0; p < size; p++)
                        if (r_count[number][selectedRow[index[p]]] < 2)
                            excluded = true;
                    if (!excluded)
                    {
                        bool selectedRow2[9];
                        memset(selectedRow2, false, sizeof(selectedRow2));
                        for (int p = 0; p < size; p++)
                            selectedRow2[selectedRow[index[p]]] = true;
                        
                        bitset<9> result;
                        for (int p = 0; p < size; p++)
                            result |= bs_r[number][selectedRow[index[p]]];
                        if (int(result.count()) == size + 1)
                        {
                            bitset<9> all_union;
                            for (int p = 0; p < size; p++)
                                all_union |= bs_r[number][selectedRow[index[p]]];
                            if (int(all_union.count()) == size + 1)
                            {
                                vector<int> appearedColumn;
                                for (int c = 0; c < 9; c++)
                                    if (all_union.test(c))
                                        appearedColumn.push_back(c);
                                for (int c : appearedColumn)
                                {
                                    int count = 0, selected_r;
                                    for (int p = 0; p < size; p++)
                                        if (bs_r[number][selectedRow[index[p]]].test(c))
                                        {
                                            ++count;
                                            selected_r = selectedRow[index[p]];
                                        }
                                    if (count == 1)
                                    {
                                        vector<int> deleted;
                                        int fin = _n(selected_r, c);  // 鱼鳍
                                        int box = _b(fin);
                                        vector<pii> del_unit;
                                        for (int ix = 0; ix < 3; ix++)
                                            if (!selectedRow2[_bu(box) + ix])
                                                for (int cx : appearedColumn)
                                                    if (cx != c && cx / 3 == box % 3)
                                                        if (deleteCandidate(_n(_bu(box) + ix, cx), number, del_unit, SU4_1))
                                                        {
                                                            ++technique_count.Fish_Fin;
                                                            deleted.push_back(_n(_bu(box) + ix, cx));
                                                            #ifdef DEBUG
                                                            cout << "fin: ";
                                                            cout << "r " << number << " fin" << ntorc(fin) << ' ';
                                                            for (int p = 0; p < size; p++)
                                                                cout << selectedRow[index[p]] << ' ';
                                                            cout << 'd' << ntorc(_n(_bu(box) + ix, cx)) << endl;
                                                            #endif
                                                        }
                                        autoFillNumber(del_unit);
                                        TechPack();
                                    }
                                }
                            }
                        }
                    }
                    
                    // index[size - 1]加1并进位（并保证后一个数大于前一个数）
                    ++index[size - 1];
                    for (int p = size - 1; p > 0; p--)
                        if (index[p] > len - size + p)
                        {
                            index[p] -= len - size + p;
                            ++index[p - 1];
                        }
                    for (int p = 1; p < size; p++)
                        if (index[p] <= index[p - 1])
                            index[p] = index[p - 1] + 1;
                }
            }
    
    // 列
    for (int number = 1; number <= 9; number++)
        if (solvedNum[number] <= 5)
            for (int size = 2; size <= 4; size++)
            {
                if (solvedUnits == 81) continue;
                if (solvedNum[number] >= 4 && size >= 3) continue;  // 确定值>=4时只能出现二链列
                else if (solvedNum[number] >= 2 && size == 4) continue;  // 确定值>=2时只能出现二或三链列
                
                vector<int> selectedColumn;
                for (int c = 0; c < 9; c++)
                    if (c_count[number][c] >= 2 && c_count[number][c] <= size + 1)  // 只考虑一个鱼鳍
                        selectedColumn.push_back(c);
                int len = int(selectedColumn.size());
                if (len < size) continue;

                int index[size];  // 产生用于遍历的递增序列，如：(0, 1, 2) -> (0, 1, 3) -> ... -> (6, 7, 8)
                for (int p = 0; p < size; p++)
                    index[p] = p;

                while (index[0] <= len - size)
                {
                    bool excluded = false;
                    for (int p = 0; p < size; p++)
                        if (c_count[number][selectedColumn[index[p]]] < 2)
                            excluded = true;
                    if (!excluded)
                    {
                        bool selectedColumn2[9];
                        memset(selectedColumn2, false, sizeof(selectedColumn2));
                        for (int p = 0; p < size; p++)
                            selectedColumn2[selectedColumn[index[p]]] = true;

                        bitset<9> result;
                        for (int p = 0; p < size; p++)
                            result |= bs_c[number][selectedColumn[index[p]]];
                        if (int(result.count()) == size + 1)
                        {
                            bitset<9> all_union;
                            for (int p = 0; p < size; p++)
                                all_union |= bs_c[number][selectedColumn[index[p]]];
                            if (int(all_union.count()) == size + 1)
                            {
                                vector<int> appearedRow;
                                for (int r = 0; r < 9; r++)
                                    if (all_union.test(r))
                                        appearedRow.push_back(r);
                                for (int r : appearedRow)
                                {
                                    int count = 0, selected_c;
                                    for (int p = 0; p < size; p++)
                                        if (bs_c[number][selectedColumn[index[p]]].test(r))
                                        {
                                            ++count;
                                            selected_c = selectedColumn[index[p]];
                                        }
                                    if (count == 1)
                                    {
                                        int fin = _n(r, selected_c);  // 找到鱼鳍
                                        int box = _b(fin);
                                        vector<pii> del_unit;
                                        
                                        for (int jx = 0; jx < 3; jx++)
                                            if (!selectedColumn2[_bl(box) + jx])
                                                for (int rx : appearedRow)
                                                    if (rx != r && rx / 3 == box / 3)
                                                        if (deleteCandidate(_n(rx, _bl(box) + jx), number, del_unit, SU4_1))
                                                        {
                                                            #ifdef DEBUG
                                                            cout << "fin: ";
                                                            cout << "c " << number << " fin" << ntorc(fin) << ' ';
                                                            for (int p = 0; p < size; p++)
                                                                cout << selectedColumn[index[p]] << ' ';
                                                            cout << 'd' << ntorc(_n(rx, _bl(box) + jx)) << endl;
                                                            #endif
                                                        }
                                        autoFillNumber(del_unit);
                                        if(del_unit.size())
                                            ++technique_count.Fish_Fin;
                                        TechPack();
                                    }
                                }
                            }
                        }
                    }

                    // index[size - 1]加1并进位（并保证后一个数大于前一个数）
                    ++index[size - 1];
                    for (int p = size - 1; p > 0; p--)
                        if (index[p] > len - size + p)
                        {
                            index[p] -= len - size + p;
                            ++index[p - 1];
                        }
                    for (int p = 1; p < size; p++)
                        if (index[p] <= index[p - 1])
                            index[p] = index[p - 1] + 1;
                }
            }
}

void Solver::Wings()
{
    if (solvedUnits == 81) return;
    if (level < 6) level = 6;

    for (int size = 2; size <= 5; size++)
        for (int pos = 0; pos < 81; pos++)
            if (unit[pos].left == size || unit[pos].left == size + 1)  // 两种情形
            {
                resetRelatedBlock(pos);
                vector<int> leftTwo;
                for (int i = 0 ; i < 20; i++)
                    if (unit[related[i]].left == 2)
                        leftTwo.push_back(related[i]);
                int len = int(leftTwo.size());
                if (len < size) continue;
                
                int index[size];  // 产生用于遍历的递增序列，如：(0, 1, 2) -> (0, 1, 3) -> ... -> (6, 7, 8)
                for (int p = 0; p < size; p++)
                    index[p] = p;

                while (index[0] <= len - size)
                {
                    short intersection = 0x01FF;  // 交集
                    for (int p = 0; p < size; p++)
                        intersection &= unit[leftTwo[index[p]]].candidate;
                    int count = 0, intersect = 0;
                    while (intersection)
                    {
                        ++intersect;
                        if (intersection & 1) ++count;
                        intersection >>= 1;
                    }
                    if (count == 1)  // 交集有且只有一个数字，此时intersect即为那个所有集合交集的那个数字
                    {
                        short _union = 0;
                        for (int p = 0; p < size; p++)
                            _union |= unit[leftTwo[index[p]]].candidate;
                        if (_union == (unit[pos].candidate | (1 << (intersect - 1))))
                        {
                            // 交集只有一个数字，并集为该数字并上pos格剩余候选数
                            vector<int> vect_related[size];
                            for (int p = 0; p < size; p++)
                            {
                                vect_related[p] = getRelatedBlock(leftTwo[index[p]]);
                                sort(vect_related[p].begin(), vect_related[p].end());
                            }
                            // 求size个vector的交集v
                            vector<int> v = vect_related[0], temp;
                            for (int p = 1; p < size; p++)
                            {
                                temp = v;
                                v.clear();
                                set_intersection(temp.begin(), temp.end(),
                                                vect_related[p].begin(), vect_related[p].end(),
                                                back_inserter(v));
                            }
                            if (getBit(pos, intersect) == 1)  // 普通高阶Wings，再求一次交集
                            {
                                vector<int> posRelated = getRelatedBlock(pos);
                                sort(posRelated.begin(), posRelated.end());
                                temp = v;
                                v.clear();
                                set_intersection(temp.begin(), temp.end(),
                                                posRelated.begin(), posRelated.end(),
                                                back_inserter(v));
                            }
                            
                            vector<pii> del_unit;
                            for (int del : v)
                                if (del != pos)
                                    if (deleteCandidate(del, intersect, del_unit, SU5))
                                    {
                                        #ifdef DEBUG
                                        cout << "Wings: " << size << ' ' << ntorc(pos) << ' ' << intersect << " d" << ntorc(del) << endl;
                                        #endif
                                    }
                            autoFillNumber(del_unit);
                            if (del_unit.size())
                                ++technique_count.Wings;
                            TechPack();
                        }
                    }

                    // index[size - 1]加1并进位（并保证后一个数大于前一个数）
                    ++index[size - 1];
                    for (int p = size - 1; p > 0; p--)
                        if (index[p] > len - size + p)
                        {
                            index[p] -= len - size + p;
                            ++index[p - 1];
                        }
                    for (int p = 1; p < size; p++)
                        if (index[p] <= index[p - 1])
                            index[p] = index[p - 1] + 1;
                }
            }
}


void Solver::UniqueRectangle()
{
    if (solvedUnits == 81) return;

    if (level < 4) level = 4;

    // 18 * 36 = 648个矩形
    // 行
    for (int bx = 0; bx < 3; ++bx)
        for (int br1 = 0; br1 < 2; ++br1)
            for (int br2 = br1 + 1; br2 < 3; ++br2)
                for (int c1 = 0; c1 < 8; ++c1)
                    for (int c2 = c1 + 1; c2 < 9; ++c2)
                        if (c1 / 3 != c2 / 3)
                            for (int URType = 1; URType <= 9; ++URType)
                                switch (URType)
                                {
                                case 1:
                                {
                                    // UR Type 1 (标准类型)
                                    //    0 3
                                    //    1 2
                                    int pos[4] = {_n(3 * bx + br1, c1), _n(3 * bx + br2, c1), _n(3 * bx + br2, c2), _n(3 * bx + br1, c2)};
                                    
                                    // 必须要同一行/列的两个都只含两个候选数且相同，4种情形
                                    int u = 0, v = 1;  // 产生01, 12, 23, 30序列
                                    for (int t = 0; t < 4; ++t)
                                    {
                                        if (unit[pos[u]].left == 2 && unit[pos[u]].candidate == unit[pos[v]].candidate)
                                        {
                                            short flag = unit[pos[u]].candidate;
                                            bool ok = true;
                                            for (int p = 0; p < 4; ++p)
                                                if (p != u && p != v)
                                                    if ((unit[pos[p]].candidate & flag) != flag)  // u,v之外两格均含有u,v这两格的两个候选数
                                                    {
                                                        ok = false;
                                                        break;
                                                    }
                                            if (ok)
                                            {
                                                int opos[2] = {-1, -1};  // 保存除uv外另两格的序号
                                                int number[2] = {-1, -1};  // 保存共有的那两个候选数

                                                for (int p = 0; p < 4; ++p)
                                                    if (pos[p] != pos[u] && pos[p] != pos[v])
                                                    {
                                                        if (opos[0] == -1) opos[0] = pos[p];
                                                        else opos[1] = pos[p];
                                                    }
                                                int n = 1;
                                                short tmp = flag;
                                                while (tmp)
                                                {
                                                    if (tmp & 1)
                                                    {
                                                        if (number[0] == -1) number[0] = n;
                                                        else number[1] = n;
                                                    }
                                                    tmp >>= 1;
                                                    ++n;
                                                }

                                                // UR Type 1 (标准类型)
                                                if (unit[opos[0]].left == 2)
                                                {
                                                    vector<pii> del_unit;
                                                    deleteCandidate(opos[1], number[0], del_unit);
                                                    deleteCandidate(opos[1], number[1], del_unit);
                                                    
                                                    if (del_unit.size())
                                                    {
                                                        #ifdef UR_LOG
                                                        cout << "UR1.\n";
                                                        #endif
                                                        ++technique_count.UniqueRectangle;
                                                        autoFillNumber(del_unit);
                                                    }
                                                }
                                                else if (unit[opos[1]].left == 2)
                                                {
                                                    vector<pii> del_unit;
                                                    deleteCandidate(opos[0], number[0], del_unit);
                                                    deleteCandidate(opos[0], number[1], del_unit);

                                                    if (del_unit.size())
                                                    {
                                                        #ifdef UR_LOG
                                                        cout << "UR1.\n";
                                                        #endif
                                                        ++technique_count.UniqueRectangle;
                                                        autoFillNumber(del_unit);
                                                    }
                                                }
                                            }
                                        }
                                        // 为了用循环产生序列简化代码
                                        u = v;
                                        v = (v + 1) % 4;
                                    }
                                }
                                break;
                                case 2:
                                {
                                    // UR Type 2 (区块类型)
                                    //    0 3
                                    //    1 2
                                    int pos[4] = {_n(3 * bx + br1, c1), _n(3 * bx + br2, c1), _n(3 * bx + br2, c2), _n(3 * bx + br1, c2)};
                                    
                                    // 除了UR Type 5之外的唯一性测试
                                    // 必须要同一行/列的两个都只含两个候选数且相同，4种情形
                                    int u = 0, v = 1;  // 产生01, 12, 23, 30序列
                                    for (int t = 0; t < 4; ++t)
                                    {
                                        if (unit[pos[u]].left == 2 && unit[pos[u]].candidate == unit[pos[v]].candidate)
                                        {
                                            short flag = unit[pos[u]].candidate;
                                            bool ok = true;
                                            for (int p = 0; p < 4; ++p)
                                                if (p != u && p != v)
                                                    if ((unit[pos[p]].candidate & flag) != flag)  // u,v之外两格均含有u,v这两格的两个候选数
                                                    {
                                                        ok = false;
                                                        break;
                                                    }
                                            if (ok)
                                            {
                                                int opos[2] = {-1, -1};  // 保存除uv外另两格的序号
                                                int number[2] = {-1, -1};  // 保存共有的那两个候选数

                                                for (int p = 0; p < 4; ++p)
                                                    if (pos[p] != pos[u] && pos[p] != pos[v])
                                                    {
                                                        if (opos[0] == -1) opos[0] = pos[p];
                                                        else opos[1] = pos[p];
                                                    }
                                                int n = 1;
                                                short tmp = flag;
                                                while (tmp)
                                                {
                                                    if (tmp & 1)
                                                    {
                                                        if (number[0] == -1) number[0] = n;
                                                        else number[1] = n;
                                                    }
                                                    tmp >>= 1;
                                                    ++n;
                                                }

                                                if (unit[opos[0]].left == 3 && unit[opos[0]].candidate == unit[opos[1]].candidate)
                                                {
                                                    int lockedCandi_number;
                                                    int n = 1;
                                                    short tmp = unit[opos[0]].candidate;
                                                    while (tmp)
                                                    {
                                                        if ((tmp & 1) && n != number[0] && n != number[1])
                                                            lockedCandi_number = n;
                                                        tmp >>= 1;
                                                        ++n;
                                                    }
                                                    
                                                    vector<pii> del_unit;
                                                    if (deleteSharedAffectBlock(lockedCandi_number, opos[0], opos[1], del_unit))
                                                    {
                                                        #ifdef UR_LOG
                                                        cout << "UR2.\n";
                                                        #endif
                                                    }
                                                }
                                            }
                                        }
                                        // 为了用循环产生序列简化代码
                                        u = v;
                                        v = (v + 1) % 4;
                                    }
                                }
                                break;
                                case 3:
                                {
                                    // UR Type 3 (数组类型)
                                    // 显性n数组, n = 2, 3, 4
                                    //    0 3
                                    //    1 2
                                    int pos[4] = {_n(3 * bx + br1, c1), _n(3 * bx + br2, c1), _n(3 * bx + br2, c2), _n(3 * bx + br1, c2)};
                                    
                                    // 除了UR Type 5之外的唯一性测试
                                    // 必须要同一行/列的两个都只含两个候选数且相同，4种情形
                                    int u = 0, v = 1;  // 产生01, 12, 23, 30序列
                                    for (int t = 0; t < 4; ++t)
                                    {
                                        if (unit[pos[u]].left == 2 && unit[pos[u]].candidate == unit[pos[v]].candidate)
                                        {
                                            short flag = unit[pos[u]].candidate;
                                            bool ok = true;
                                            for (int p = 0; p < 4; ++p)
                                                if (p != u && p != v)
                                                    if ((unit[pos[p]].candidate & flag) != flag)  // u,v之外两格均含有u,v这两格的两个候选数
                                                    {
                                                        ok = false;
                                                        break;
                                                    }
                                            if (ok)
                                            {
                                                int opos[2] = {-1, -1};  // 保存除uv外另两格的序号
                                                int number[2] = {-1, -1};  // 保存共有的那两个候选数

                                                for (int p = 0; p < 4; ++p)
                                                    if (pos[p] != pos[u] && pos[p] != pos[v])
                                                    {
                                                        if (opos[0] == -1) opos[0] = pos[p];
                                                        else opos[1] = pos[p];
                                                    }
                                                int n = 1;
                                                short tmp = flag;
                                                while (tmp)
                                                {
                                                    if (tmp & 1)
                                                    {
                                                        if (number[0] == -1) number[0] = n;
                                                        else number[1] = n;
                                                    }
                                                    tmp >>= 1;
                                                    ++n;
                                                }

                                                if (unit[opos[0]].left == 3 && unit[opos[1]].left == 3
                                                        && unit[opos[0]].candidate != unit[opos[1]].candidate)
                                                {
                                                    vector<int> blank;
                                                    if (_r(opos[0]) == _r(opos[1]))
                                                        blank = rowBlank_except_v(_r(opos[0]), vector<int>{opos[0], opos[1]});
                                                    else
                                                        blank = columnBlank_except_v(_c(opos[0]), vector<int>{opos[0], opos[1]});
                                                    
                                                    short flag = 0;
                                                    for (int i = 0; i < 2; ++i)
                                                    {
                                                        int n = 1;
                                                        short tmp = unit[opos[i]].candidate;
                                                        while (tmp)
                                                        {
                                                            if ((tmp & 1) && n != number[0] && n != number[1])
                                                                flag |= 1 << (n - 1);
                                                            tmp >>= 1;
                                                            ++n;
                                                        }
                                                    }
                                                    // 此时flag记录有opos两格可参与到数组组成的两个数字

                                                    for (int size = 2; size <= 4; ++size)
                                                    {
                                                        int temp[size];  // 存储要遍历的size阶数组的候选数，如3阶：(1, 2, 3) -> (1, 2, 4) -> ... -> (7, 8, 9)
                                                        for (int p = 0; p < size; p++)
                                                            temp[p] = p + 1;
                                                        while (temp[0] <= 10 - size)
                                                        {
                                                            if (solvedUnits == 81) return;
                                                            
                                                            int assist = 0;
                                                            for (int p = 0; p < size; p++)
                                                                assist |= 1 << (temp[p] - 1);
                                                            if ((assist & flag) == flag)  // 选择的数中包括flag的两个数
                                                            {
                                                                int count = 0;
                                                                for (int pos : blank)
                                                                    if (unit[pos].left >= 2 && (unit[pos].candidate & assist) && 
                                                                        !(unit[pos].candidate & ~assist))  // 每个格子剩余候选数应是assist包含候选数的子集
                                                                    // 至少含有其中的两个数，且不含其它候选数
                                                                        ++count;
                                                                if (count == size - 1)
                                                                {
                                                                    vector<pii> del_unit;
                                                                    // 显性数组(步分SU3)
                                                                    for (int pos : blank)
                                                                        if (unit[pos].candidate & ~assist) // 含有其他候选数，也就不是产生效应的这几格，防止误删
                                                                            for (int p = 0; p < size; p++)
                                                                                if (deleteCandidate(pos, temp[p], del_unit, SU3))
                                                                                    ++technique_count.UniqueRectangle;
                                                                    if (del_unit.size())
                                                                    {
                                                                        autoFillNumber(del_unit);
                                                                        #ifdef UR_LOG
                                                                        cout << "UR3.\n";
                                                                        #endif
                                                                    }
                                                                }
                                                            }
                                                            
                                                            // temp[size - 1]加1并进位（并保证后一个数大于前一个数）
                                                            ++temp[size - 1];
                                                            for (int p = size - 1; p > 0; p--)
                                                                if (temp[p] > 10 - size + p)
                                                                {
                                                                    temp[p] -= 10 - size + p;
                                                                    ++temp[p - 1];
                                                                }
                                                            for (int p = 1; p < size; p++)
                                                                if (temp[p] < temp[p - 1])
                                                                    temp[p] = temp[p - 1] + 1;
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                        // 为了用循环产生序列简化代码
                                        u = v;
                                        v = (v + 1) % 4;
                                    }
                                }
                                break;
                                case 4:
                                {
                                    // 隐性n数组, n = 2, 3, 4
                                    // 首先需要满足pos[u]与pos[v]的那两个候选数不可同假
                                    //    0 3
                                    //    1 2
                                    int pos[4] = {_n(3 * bx + br1, c1), _n(3 * bx + br2, c1), _n(3 * bx + br2, c2), _n(3 * bx + br1, c2)};
                                    
                                    // 除了UR Type 5之外的唯一性测试
                                    // 必须要同一行/列的两个都只含两个候选数且相同，4种情形
                                    int u = 0, v = 1;  // 产生01, 12, 23, 30序列
                                    for (int t = 0; t < 4; ++t)
                                    {
                                        if (unit[pos[u]].left == 2 && unit[pos[u]].candidate == unit[pos[v]].candidate)
                                        {
                                            short flag = unit[pos[u]].candidate;
                                            bool ok = true;
                                            for (int p = 0; p < 4; ++p)
                                                if (p != u && p != v)
                                                    if ((unit[pos[p]].candidate & flag) != flag)  // u,v之外两格均含有u,v这两格的两个候选数
                                                    {
                                                        ok = false;
                                                        break;
                                                    }
                                            if (ok)
                                            {
                                                int opos[2] = {-1, -1};  // 保存除uv外另两格的序号
                                                int number[2] = {-1, -1};  // 保存共有的那两个候选数

                                                for (int p = 0; p < 4; ++p)
                                                    if (pos[p] != pos[u] && pos[p] != pos[v])
                                                    {
                                                        if (opos[0] == -1) opos[0] = pos[p];
                                                        else opos[1] = pos[p];
                                                    }
                                                int n = 1;
                                                short tmp = flag;
                                                while (tmp)
                                                {
                                                    if (tmp & 1)
                                                    {
                                                        if (number[0] == -1) number[0] = n;
                                                        else number[1] = n;
                                                    }
                                                    tmp >>= 1;
                                                    ++n;
                                                }

                                                vector<int> vpos;
                                                
                                                vector<int> vblank;
                                                bool has_number0 = false, has_number1 = false;

                                                if (_r(opos[0]) == _r(opos[1]))
                                                    vblank = rowBlank_except_v(_r(opos[0]), vector<int>{opos[0], opos[1]});
                                                else
                                                    vblank = columnBlank_except_v(_c(opos[0]), vector<int>{opos[0], opos[1]});
                                                
                                                int count = 0;
                                                for (auto p : vblank)
                                                    if (unit[p].candidate & flag)
                                                    {
                                                        ++count;
                                                        if (getBit(p, number[0])) has_number0 = true;
                                                        if (getBit(p, number[1])) has_number1 = true;
                                                        vpos.push_back(p);
                                                    }
                                                if (count == 1
                                                        || (count >= 2 && ((has_number0 && !has_number1) || (!has_number0 && has_number1))))
                                                {
                                                    // 至此，不可同假条件满足，可视作一格参与隐性n数组结构
                                                    // 行
                                                    if (_r(opos[0]) == _r(opos[1]))
                                                        for (int size = 2; size <= 4; ++size)
                                                        {
                                                            int r = _r(opos[0]);
                                                            vector<int> qualified_num = {number[0], number[1]};
                                                            for (int n = 1; n <= 9; n++)
                                                                if (n != number[0] && n != number[1]
                                                                        && r_count[n][r] >= 2 && r_count[n][r] <= size)
                                                                    qualified_num.push_back(n);
                                                            int len = qualified_num.size();
                                                            if (len < size) continue;
                                                            
                                                            int index[size];  // size阶数组的严格递增下标序列，如3阶：(0, 1, 2) -> (0, 1, 3) -> ...
                                                            for (int p = 0; p < size; p++)
                                                                index[p] = p;
                                                            
                                                            while (index[0] == 0 && index[1] == 1
                                                                    && (size <= 2 || index[2] <= len - size + 2))
                                                            {
                                                                if (solvedUnits == 81) return;
                                                                
                                                                // 由于各个参数手是在动态变化的，
                                                                // 可能执行到这里的时候qualified_num中的有的数不再满足条件，需加以判断
                                                                bool excluded = false;
                                                                for (int p = 0; p < size; p++)
                                                                    if (r_count[qualified_num[index[p]]][r] < 2)
                                                                        excluded = true;
                                                                if (!excluded)
                                                                {
                                                                    bitset<9> r_union;
                                                                    for (int p = 0; p < size; p++)
                                                                        r_union |= bs_r[qualified_num[index[p]]][r];
                                                                    // 计算选定的size个候选数共出现过的格数count
                                                                    int count = r_union.count();
                                                                    bool ok = true;  // opos[0,1]除了number[0,1]外不含有其他选中的数
                                                                    for (int p = 2; p < size; ++p)
                                                                        if (getBit(opos[0], qualified_num[index[p]])
                                                                                || getBit(opos[1], qualified_num[index[p]]))
                                                                        {
                                                                            ok = false;
                                                                            break;
                                                                        }
                                                                        
                                                                    if (count == size + 1 && ok)
                                                                    {
                                                                        vector<int> del_column;
                                                                        for (int j = 0; j < 9; j++)
                                                                            if (r_union.test(j) && j != _c(opos[0]) && j != _c(opos[1]))
                                                                                del_column.push_back(j);
                                                                        bool del_num[10];
                                                                        memset(del_num, true, sizeof(del_num));
                                                                        for (int p = 0; p < size; p++)
                                                                            del_num[qualified_num[index[p]]] = false;
                                                                        vector<pii> del_unit;
                                                                        for (int j : del_column)
                                                                            for (int n = 1; n <= 9; n++)
                                                                                if (del_num[n])
                                                                                    deleteCandidate(_n(r, j), n, del_unit, SU3);
                                                                        if (del_unit.size())
                                                                        {
                                                                            ++technique_count.UniqueRectangle;
                                                                            #ifdef UR_LOG
                                                                            cout << "UR4.\n";
                                                                            #endif
                                                                            // cout << "size = " << size << "\nnumbers:  ";
                                                                            // for (int p = 0; p < size; ++p)
                                                                            //     cout << qualified_num[index[p]] << ' ';
                                                                            // cout << "opos: " << ntorc(opos[0]) << ' ' << ntorc(opos[1]) << endl;
                                                                            // cout << "numbers: " << number[0] << ' ' << number[1] << endl;
                                                                            // cout << endl << "details:\n";
                                                                            // for (int j = 0; j < 9; ++j)
                                                                            //     if (r_union.test(j))
                                                                            //     {
                                                                            //         cout << ntorc(_n(r, j)) << ":  ";
                                                                            //         for (int n = 1; n <= 9; ++n)
                                                                            //             if (getBit(_n(r, j), n))
                                                                            //                 cout << n << ' ';
                                                                            //         cout << endl;
                                                                            //     }
                                                                            // cout << "del:   ";
                                                                            // for (auto i : del_unit)
                                                                            //     cout << ntorc(i.first) << ' ' << i.second << ' ';
                                                                            // cout << endl;
                                                                            // system("pause");
                                                                            autoFillNumber(del_unit);
                                                                        }
                                                                    }
                                                                }
                                                                // index[size - 1]加1并进位（并保证后一个数大于前一个数）
                                                                ++index[size - 1];
                                                                for (int p = size - 1; p > 0; p--)
                                                                    if (index[p] > len - size + p)
                                                                    {
                                                                        index[p] -= len - size + p;
                                                                        ++index[p - 1];
                                                                    }
                                                                for (int p = 1; p < size; p++)
                                                                    if (index[p] <= index[p - 1])
                                                                        index[p] = index[p - 1] + 1;
                                                            }
                                                        }
                                                }
                                            }
                                        }
                                        // 为了用循环产生序列简化代码
                                        u = v;
                                        v = (v + 1) % 4;
                                    }
                                }
                                case 5:
                                {
                                    // UR Type 4 (共轭对类型)
                                    //    0 3
                                    //    1 2
                                    int pos[4] = {_n(3 * bx + br1, c1), _n(3 * bx + br2, c1), _n(3 * bx + br2, c2), _n(3 * bx + br1, c2)};
                                    
                                    // 必须要同一行/列的两个都只含两个候选数且相同，4种情形
                                    int u = 0, v = 1;  // 产生01, 12, 23, 30序列
                                    for (int t = 0; t < 4; ++t)
                                    {
                                        if (unit[pos[u]].left == 2 && unit[pos[u]].candidate == unit[pos[v]].candidate)
                                        {
                                            const short flag = unit[pos[u]].candidate;
                                            
                                            bool ok = true;
                                            for (int p = 0; p < 4; ++p)
                                                if (p != u && p != v)
                                                    if ((unit[pos[p]].candidate & flag) != flag)  // u,v之外两格均含有u,v这两格的两个候选数
                                                    {
                                                        ok = false;
                                                        break;
                                                    }
                                            if (ok)
                                            {
                                                int opos[2] = {-1, -1};  // 保存除uv外另两格的序号
                                                int number[2] = {-1, -1};  // 保存共有的那两个候选数

                                                for (int p = 0; p < 4; ++p)
                                                    if (pos[p] != pos[u] && pos[p] != pos[v])
                                                    {
                                                        if (opos[0] == -1) opos[0] = pos[p];
                                                        else opos[1] = pos[p];
                                                    }
                                                int n = 1;
                                                short tmp = flag;
                                                while (tmp)
                                                {
                                                    if (tmp & 1)
                                                    {
                                                        if (number[0] == -1) number[0] = n;
                                                        else number[1] = n;
                                                    }
                                                    tmp >>= 1;
                                                    ++n;
                                                }

                                                vector<pii> del_unit;
                                                if (_r(opos[0]) == _r(opos[1]))
                                                {
                                                    for (int i = 0; i < 2; ++i)
                                                        if (r_count[number[i]][_r(opos[0])] == 2)
                                                        {
                                                            for (int p = 0; p < 2; ++p)
                                                                deleteCandidate(opos[p], number[1 - i], del_unit, SU3);
                                                            break;
                                                        }
                                                }
                                                else if (_c(opos[0]) == _c(opos[1]))
                                                {
                                                    for (int i = 0; i < 2; ++i)
                                                        if (c_count[number[i]][_c(opos[0])] == 2)
                                                        {
                                                            for (int p = 0; p < 2; ++p)
                                                                deleteCandidate(opos[p], number[1 - i], del_unit, SU3);
                                                            break;
                                                        }
                                                }
                                                if (del_unit.size())
                                                {
                                                    ++technique_count.UniqueRectangle;
                                                    autoFillNumber(del_unit);
                                                }
                                            }
                                        }
                                        // 为了用循环产生序列简化代码
                                        u = v;
                                        v = (v + 1) % 4;
                                    }
                                }
                                break;
                                case 6:
                                {
                                    // UR Type 4 (共轭对类型)
                                    //    0 3
                                    //    1 2
                                    int pos[4] = {_n(3 * bx + br1, c1), _n(3 * bx + br2, c1), _n(3 * bx + br2, c2), _n(3 * bx + br1, c2)};

                                    // UR Type 5
                                    short all_or = unit[pos[0]].candidate;
                                    short all_and = unit[pos[0]].candidate;
                                    for (int i = 1; i < 4; ++i)
                                    {
                                        all_or |= unit[pos[i]].candidate;
                                        all_and &= unit[pos[i]].candidate;
                                    }
                                    if (_count_bit1(all_or) == 3 && _count_bit1(all_and) == 2)
                                    {
                                        short tmp = all_or & ~all_and;
                                        int onumber = 1;
                                        while (tmp)
                                        {
                                            if (tmp & 1)
                                                break;
                                            tmp >>= 1;
                                            ++onumber;
                                        }
                                        vector<int> spos;;
                                        for (int i = 0; i < 4; ++i)
                                            if (getBit(pos[i], onumber))
                                                spos.push_back(pos[i]);
                                        // 删除spos的所有元素相关格的交集
                                        vector<int> v = getRelatedBlock(spos[0]), temp, vtmp;
                                        sort(v.begin(), v.end());
                                        for (size_t p = 1; p < spos.size(); ++p)
                                        {
                                            temp = v;
                                            v.clear();
                                            vtmp = getRelatedBlock(spos[p]);
                                            sort(vtmp.begin(), vtmp.end());
                                            set_intersection(temp.begin(), temp.end(),
                                                            vtmp.begin(), vtmp.end(),
                                                            back_inserter(v));
                                        }
                                        vector<pii> del_unit;
                                        for (auto pos : v)
                                            deleteCandidate(pos, onumber, del_unit);
                                        if (del_unit.size())
                                        {
                                            #ifdef UR_LOG
                                            cout << "UR6.\n";
                                            #endif
                                            ++technique_count.UniqueRectangle;
                                            autoFillNumber(del_unit);
                                        }
                                    }
                                }
                                break;
                                case 7:
                                {
                                    // URType 6 (二链列类型)
                                    //    0 3
                                    //    1 2
                                    int pos[4] = {_n(3 * bx + br1, c1), _n(3 * bx + br2, c1), _n(3 * bx + br2, c2), _n(3 * bx + br1, c2)};

                                    short all_and = unit[pos[0]].candidate;
                                    for (int i = 1; i < 4; ++i)
                                        all_and &= unit[pos[i]].candidate;
                                    
                                    short tmp = all_and;
                                    int n = 1;
                                    if (tmp && _count_bit1(all_and) == 2)
                                        while (tmp)
                                        {
                                            if ((tmp & 1)  // 此时n为4格共有的候选数
                                                    && r_count[n][_r(pos[0])] == 2 && r_count[n][_r(pos[1])] == 2
                                                    && c_count[n][_c(pos[0])] == 2 && c_count[n][_c(pos[3])] == 2)
                                            {
                                                if (unit[pos[0]].left == 2 && unit[pos[2]].left == 2)
                                                {
                                                    #ifdef UR_LOG
                                                    cout << "UR7.\n";
                                                    #endif
                                                    fillNumber(pos[0], n);
                                                    fillNumber(pos[2], n);
                                                    ++technique_count.UniqueRectangle;
                                                    break;
                                                }
                                                else if (unit[pos[1]].left == 2 && unit[pos[3]].left == 2)
                                                {
                                                    #ifdef UR_LOG
                                                    cout << "UR7.\n";
                                                    #endif
                                                    fillNumber(pos[1], n);
                                                    fillNumber(pos[3], n);
                                                    ++technique_count.UniqueRectangle;
                                                    break;
                                                }
                                            }
                                            tmp >>= 1;
                                            ++n;
                                        }
                                }
                                break;
                                case 8:
                                {
                                    // URType 7 (隐性唯一矩形)
                                    //    0 3
                                    //    1 2
                                    int pos[4] = {_n(3 * bx + br1, c1), _n(3 * bx + br2, c1), _n(3 * bx + br2, c2), _n(3 * bx + br1, c2)};

                                    short all_and = unit[pos[0]].candidate;
                                    for (int i = 1; i < 4; ++i)
                                        all_and &= unit[pos[i]].candidate;
                                    
                                    short tmp = all_and;
                                    int n = 1;
                                    if (tmp && _count_bit1(all_and) == 2)
                                        while (tmp)
                                        {
                                            bool interrupt = false;
                                            if (tmp & 1)  // 此时n为4格共有的候选数
                                            {
                                                for (int i = 0; i < 4; ++i)
                                                {
                                                    vector<pii> del_unit;
                                                    if (r_count[n][_r(pos[i])] == 2 && c_count[n][_c(pos[i])] == 2
                                                            && unit[pos[(i + 2) % 4]].left == 2)  // 加2模4取对角线位置
                                                    {
                                                        int nx = 1, del_num;
                                                        short ntmp = all_and;
                                                        while (ntmp)
                                                        {
                                                            if ((ntmp & 1) && nx != n)
                                                                del_num = nx;
                                                            ntmp >>= 1;
                                                            ++nx;
                                                        }
                                                        deleteCandidate(pos[i], del_num, del_unit, SU3);
                                                    }
                                                    if (del_unit.size())
                                                    {
                                                        #ifdef UR_LOG
                                                        cout << "UR8.\n";
                                                        #endif
                                                        ++technique_count.UniqueRectangle;
                                                        autoFillNumber(del_unit);
                                                        interrupt = true;
                                                        break;
                                                    }
                                                }
                                            }
                                            tmp >>= 1;
                                            ++n;
                                            if (interrupt)
                                                break;
                                        }
                                }
                                break;
                                case 9:
                                {
                                    // Locked UR Type 1and2 (死锁唯一矩形)
                                    //    0 3
                                    //    1 2
                                    int pos[4] = {_n(3 * bx + br1, c1), _n(3 * bx + br2, c1), _n(3 * bx + br2, c2), _n(3 * bx + br1, c2)};

                                    short all_and = unit[pos[0]].candidate;
                                    for (int i = 1; i < 4; ++i)
                                        all_and &= unit[pos[i]].candidate;
                                    
                                    int flag_number = -1, func_number = -1;  // flag_number:行列均只剩2格的数，fun_number:决定删数的
                                    vector<int> func_vpos;  // 决定删数的格

                                    short tmp = all_and;
                                    if (tmp && _count_bit1(all_and) == 2)
                                    {
                                        int n = 1;
                                        while (tmp)
                                        {
                                            if (tmp & 1)  // 此时n为4格共有的候选数
                                            {
                                                if (r_count[n][_r(pos[0])] == 2 && r_count[n][_r(pos[1])] == 2
                                                    && c_count[n][_c(pos[0])] == 2 && c_count[n][_c(pos[3])] == 2)
                                                    flag_number = n;
                                            }
                                            tmp >>= 1;
                                            ++n;
                                        }
                                        n = 1;
                                        tmp = all_and;
                                        while (tmp)
                                        {
                                            if (tmp & 1)  // 此时n为4格共有的候选数
                                                if (n != flag_number)
                                                    func_number = n;
                                            tmp >>= 1;
                                            ++n;
                                        }
                                    }
                                    
                                    if (flag_number != -1 && func_number != -1)
                                    {
                                        for (int i = 0; i < 2; ++i)
                                            for (int j = 0; j < 9; ++j)
                                                if (j != _c(pos[0]) && j != _c(pos[3]) && getBit(_n(_r(pos[i]), j), func_number))
                                                    func_vpos.push_back(_n(_r(pos[i]), j));
                                        if (func_vpos.size() == 1)
                                        {
                                            // Locked UR Type 1 (标准类型)
                                            #ifdef UR_LOG
                                            cout << "UR9_1.\n";
                                            #endif
                                            fillNumber(func_vpos[0], func_number);
                                            ++technique_count.UniqueRectangle;
                                        }
                                        else if (func_vpos.size())
                                        {
                                            // Locked UR Type 2 (区块类型)
                                            // 删去func_vpos所有位置的共同影响格
                                            vector<int> v = getRelatedBlock(func_vpos[0]), temp, tmp;
                                            sort(v.begin(), v.end());
                                            for (size_t p = 1; p < func_vpos.size(); ++p)
                                            {
                                                temp = v;
                                                v.clear();
                                                tmp = getRelatedBlock(func_vpos[p]);
                                                sort(tmp.begin(), tmp.end());
                                                set_intersection(temp.begin(), temp.end(),
                                                                tmp.begin(), tmp.end(),
                                                                back_inserter(v));
                                            }
                                            vector<pii> del_unit;
                                            for (auto p : v)
                                                deleteCandidate(p, func_number, del_unit, SU3);
                                            if (del_unit.size())
                                            {
                                                #ifdef UR_LOG
                                                cout << "UR9_2.\n";
                                                #endif
                                                ++technique_count.UniqueRectangle;

                                                autoFillNumber(del_unit);
                                            }
                                            
                                        }
                                    }
                                }
                                break;
                                default:
                                    break;
                                }
}