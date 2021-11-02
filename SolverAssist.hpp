// SolverAssist.hpp -- implementing Solver methods

#pragma once

#include "sudoku.hpp"
#include <cmath>
using namespace Sudoku;

// 构造函数

Solver::Solver(const string& pro) 
    : problem(pro), hintUnits(0), solvedUnits(0), level(1), score(0)
{
    if (pro.size() != 81)
    {
        cerr << "input error.\n";
        system("pause");
        exit(EXIT_FAILURE);
    }
    DLX dlx;
    dlx.solve(true, pro);
    if (dlx.get_ans_property() == 0)
        cerr << "no solution.\n";
    QueryPerformanceFrequency(&nFreq);  // 获取系统时钟频率
    QueryPerformanceCounter(&nBeginTime);  // 获取开始时刻计数值

    // 初始化
    memset(solvedNum, 0, sizeof(solvedNum));
    for (int n = 1; n <= 9; n++)
        for (int p = 0; p < 9; p++)
        {
            r_count[n][p] = c_count[n][p] = b_count[n][p] = 9;
            for (int i = 0; i < 3; ++i)
                br_count[n][p][i] = bc_count[n][p][i] = 3;
            bs_r[n][p].set();
            bs_c[n][p].set();
            bs_b[n][p].set();
        }

    for (int pos = 0; pos < 81; pos++)
    {
        unit[pos].hint = unit[pos].ans = problem[pos] - '0';
        if (unit[pos].hint == 0)
            continue;

        ++hintUnits;
        ++solvedUnits;
        ++solvedNum[unit[pos].ans];
        unit[pos].left = 0;
        update_xcount_bsx_add(pos, unit[pos].ans);  // 更新count和bs，用到getBit()
        unit[pos].candidate = 0;
        HiddenSingle_deleteCandidatesOnly(pos);  // 删除pos相关格的ans候选数
    }
    // printDetails();
    for (int pos = 0; pos < 81; pos++)
        NakedSingle(pos);
    for (int n = 1; n <= 9; ++n)
        for (int p = 0; p < 9; ++p)
        {
            if (solvedUnits == 81) break;

            if (r_count[n][p] == 1)
                for (int j = 0; j < 9; ++j)
                    if (bs_r[n][p][j])
                    {
                        score += SU1;
                        fillNumber(_n(p, j), n);
                        break;
                    }
            if (c_count[n][p] == 1)
                for (int i = 0; i < 9; ++i)
                    if (bs_c[n][p][i])
                    {
                        score += SU1;
                        fillNumber(_n(i, p), n);
                        break;
                    }
            if (b_count[n][p] == 1)
                for (int bx = 0; bx < 9; ++bx)
                    if (bs_b[n][p][bx])
                    {
                        score += SU1;
                        fillNumber(_bij(p, bx / 3, bx % 3), n);
                        break;
                    }
        }
    solve();

    QueryPerformanceCounter(&nEndTime);  // 获取停止时刻计数值
	time_consumed = (double)(nEndTime.QuadPart - nBeginTime.QuadPart) / (double)nFreq.QuadPart;// 精确到小数点后7位
    time_consumed *= 1000;
}

// 辅助方法

// Algo 0.1
void Solver::HiddenSingle_unit(int pos, int number)  // HiddenSingle的单元格操作
{
    // 行只剩一格剩余候选数number
    if (r_count[number][_r(pos)] == 1)
        for (int j = 0; j < 9; ++j)
            if (bs_r[number][_r(pos)][j])
            {
                score += SU1;
                fillNumber(_n(_r(pos), j), number);
                return;
            }

    // 列只剩一格剩余候选数number
    if (c_count[number][_c(pos)] == 1)
        for (int i = 0; i < 9; ++i)
            if (bs_c[number][_c(pos)][i])
            {
                score += SU1;
                fillNumber(_n(i, _c(pos)), number);
                return;
            }

    // 宫只剩一格剩余候选数number
    if (b_count[number][_b(pos)] == 1)
        for (int bx = 0; bx < 9; ++bx)
            if (bs_b[number][_b(pos)][bx])
            {
                score += SU1;
                fillNumber(_nij(pos, bx / 3, bx % 3), number);
                return;
            }
}

// Algo 0.2
void Solver::placeSideEffect(int pos)  // 在fillNumber()方法内
{
    for (int n = 1; n <= 9; n++)
        if (n != unit[pos].ans && getBit(pos, n))
            HiddenSingle_unit(pos, n);            
}

// Algo 0.3
void Solver::fillNumber(int pos, int number)
{
    if (unit[pos].left == 0)
        return;
    ++solvedUnits;
    ++solvedNum[number];
    unit[pos].ans = number;
    unit[pos].left = 0;

    update_xcount_bsx_add(pos, number);
    placeSideEffect(pos);  // 行列排除法，宫内排除法
    unit[pos].candidate = 0;
    HiddenSingle(pos);

    if (level >= 2) LockedCandidates(pos);
}

// Algo 0.4
void Solver::update_xcount_bsx_delete(int pos, int number)
{
    if (r_count[number][_r(pos)])
    {
        --r_count[number][_r(pos)];
        bs_r[number][_r(pos)].reset(_c(pos));
    }
    if (c_count[number][_c(pos)])
    {
        --c_count[number][_c(pos)];
        bs_c[number][_c(pos)].reset(_r(pos));
    }
    if (b_count[number][_b(pos)])
    {
        --b_count[number][_b(pos)];
        bs_b[number][_b(pos)].reset(_ninbox(pos));
    }
    if (br_count[number][_b(pos)][_rinbox(pos)])
        --br_count[number][_b(pos)][_rinbox(pos)];
    if (bc_count[number][_b(pos)][_cinbox(pos)])
        --bc_count[number][_b(pos)][_cinbox(pos)];
    setBit0(pos, number);
}

void Solver::update_xcount_bsx_resume(int pos, int number)
{
    ++r_count[number][_r(pos)];
    bs_r[number][_r(pos)].set(_c(pos));
    ++c_count[number][_c(pos)];
    bs_c[number][_c(pos)].set(_r(pos));
    ++b_count[number][_b(pos)];
    bs_b[number][_b(pos)].set(_ninbox(pos));
    ++br_count[number][_b(pos)][_rinbox(pos)];
    ++bc_count[number][_b(pos)][_cinbox(pos)];
    setBit1(pos, number);
}

// Algo 0.5
void Solver::update_xcount_bsx_add(int pos, int number)
{
    r_count[number][_r(pos)] = 0;
    c_count[number][_c(pos)] = 0;
    b_count[number][_b(pos)] = 0;
    br_count[number][_b(pos)][_rinbox(pos)] = 0;
    bc_count[number][_b(pos)][_cinbox(pos)] = 0;
    bs_r[number][_r(pos)].reset();
    bs_c[number][_c(pos)].reset();
    bs_b[number][_b(pos)].reset();
    for (int n = 1; n <= 9; n++)
        if (n != number && getBit(pos, n))
            update_xcount_bsx_delete(pos, n);
}

// Algo 0.6
// 尝试删除pos格的候选数number
bool Solver::deleteCandidate(int pos, int number, vector<pii>& del_unit, int addScore, bool actually_delete)
{
    if (!getBit(pos, number))
        return false;

    if (actually_delete)
    {
        setBit0(pos, number);
        --unit[pos].left;
        update_xcount_bsx_delete(pos, number);
        score += addScore;
    }

    del_unit.push_back(pii(pos, number));

    return true;
}

void Solver::resumeCandidate(int pos, int number)
{
    if (getBit(pos, number))
        return;
    
    ++unit[pos].left;
    update_xcount_bsx_resume(pos, number);
}

// Algo 0.7
// pos格未填数，被删去候选数number，搜索pos关联的格看是否有可以填数的格
void Solver::autoFillNumber(int pos, int number)
{
    if (unit[pos].left)
    {
        NakedSingle(pos);
        HiddenSingle_unit(pos, number);
    }
}

void Solver::autoFillNumber(vector<pii>& del_unit)
{
    for (auto d : del_unit)
        if (unit[d.first].left)
        {
            NakedSingle(d.first);
            HiddenSingle_unit(d.first, d.second);
        }
}

// Algo 0.9
void Solver::resetRelatedBlock(int n)
{
    int pos = 0;
    for (int i = 0; i < 9; i++)
    {
        if (i != _r(n)) related[pos++] = _n(i, _c(n));
        if (i != _c(n)) related[pos++] = _n(_r(n), i);
    }
    for (int ix = 0; ix < 3; ix++)
        for (int jx = 0; jx < 3; jx++)
            if (ix != _rinbox(n) && jx != _cinbox(n))
                related[pos++] = _nij(n, ix, jx);
}

bool Solver::get_opnbidv(int pos, int& opos, int& number, int& b, int& id, bool& is_ALS_node, vector<int>& vpos, int& als_type)
{
    bool itype = false;
    if (pos < 2430)  // 单元格节点以及基本广义节点
    {
        is_ALS_node = false;
        itype = pos >= 1215;

        pos %= 1215;
        number = 1 + pos / 135;
        pos %= 135;
        if (pos < 81)
        {
            opos = pos;
            b = -1;  // 标记，表示为单格
        }
        else
        {
            opos = 80;
            pos %= 81;
            b = pos / 6;
            id = pos % 6;
        }
    }
    else  // ALS节点
    {
        is_ALS_node = true;
        vpos.clear();

        pos = (pos - 2430) % (9 * 3 * 9 * 512);
        number = 1 + pos / (3 * 9 * 512);
        itype = pos >= 3 * 9 * 512;

        pos %= 3 * 9 * 512;
        if (pos < 9 * 512)
        {
            // 宫
            int _b = pos / 512;
            pos %= 512;
            int px = 0;
            while (pos)
            {
                if (pos & 1) vpos.push_back(_bij(_b, px / 3, px % 3));
                pos >>= 1;
                ++px;
            }
            als_type = 0;
        }
        else if (pos < 2 * 9 * 512)
        {
            // 行
            pos %= 9 * 512;
            int _r = pos / 512;
            pos %= 512;
            int px = 0;
            while (pos)
            {
                if (pos & 1) vpos.push_back(9 * _r + px);
                pos >>= 1;
                ++px;
            }
            als_type = 1;
        }
        else
        {
            // 列
            pos %= 9 * 512;
            int _c = pos / 512;
            pos %= 512;
            int px = 0;
            while (pos)
            {
                if (pos & 1) vpos.push_back(9 * px + _c);
                pos >>= 1;
                ++px;
            }
            als_type = 2;
        }
    }
    return itype;
}

int Solver::get_id(int pos)
{
    if (pos >= 2430) return -1;

    pos %= 1215;
    pos %= 135;
    if (pos >= 81)
    {
        pos %= 81;
        return pos % 6;
    }
    return -1;
}

bool Solver::deleteSharedAffectBlock(int number, int pos1, int pos2, vector<pii>& del_unit)
{
    del_unit.clear();
    if (pos1 == pos2 || unit[pos1].left == 0 || unit[pos2].left == 0)
        return false;
    vector<int> pos1Related = getRelatedBlock(pos1), v;
    for (int p : pos1Related)
        if (p != pos2 && inTheSameArea(p, pos2))
            v.push_back(p);
    for (int p : v)
        if (getBit(p, number))
            deleteCandidate(p, number, del_unit, SU6, false);
    if (del_unit.size())
        return true;
    return false;
}

bool Solver::deleteSharedAffectBlock(int number, vector<int>& vpos1, vector<int>& vpos2, vector<pii>& del_unit)
{
    del_unit.clear();
    if (vpos1 == vpos2)
        return false;

    vector<int> v = getRelatedBlock(vpos1[0]), temp, tmp;
    sort(v.begin(), v.end());
    for (size_t p = 1; p < vpos1.size(); ++p)
    {
        temp = v;
        v.clear();
        tmp = getRelatedBlock(vpos1[p]);
        sort(tmp.begin(), tmp.end());
        set_intersection(temp.begin(), temp.end(),
                        tmp.begin(), tmp.end(),
                        back_inserter(v));
    }
    for (size_t p = 0; p < vpos2.size(); ++p)
    {
        temp = v;
        v.clear();
        tmp = getRelatedBlock(vpos2[p]);
        sort(tmp.begin(), tmp.end());
        set_intersection(temp.begin(), temp.end(),
                        tmp.begin(), tmp.end(),
                        back_inserter(v));
    }

    for (int p : v)
        if (getBit(p, number))
            deleteCandidate(p, number, del_unit, SU6, false);
    
    if (del_unit.size())
        return true;
    return false;
}

bool Solver::deleteSharedAffectBlock(int number, vector<int>& vpos1, vector<int>& vpos2, vector<int>& vpos3, vector<pii>& del_unit)
{
    del_unit.clear();
    if (vpos1 == vpos2 || vpos2 == vpos3 || vpos1 == vpos3)
        return false;

    vector<int> v = getRelatedBlock(vpos1[0]), temp, tmp;
    sort(v.begin(), v.end());
    for (size_t p = 1; p < vpos1.size(); ++p)
    {
        temp = v;
        v.clear();
        tmp = getRelatedBlock(vpos1[p]);
        sort(tmp.begin(), tmp.end());
        set_intersection(temp.begin(), temp.end(),
                        tmp.begin(), tmp.end(),
                        back_inserter(v));
    }
    for (size_t p = 0; p < vpos2.size(); ++p)
    {
        temp = v;
        v.clear();
        tmp = getRelatedBlock(vpos2[p]);
        sort(tmp.begin(), tmp.end());
        set_intersection(temp.begin(), temp.end(),
                        tmp.begin(), tmp.end(),
                        back_inserter(v));
    }
    for (size_t p = 0; p < vpos3.size(); ++p)
    {
        temp = v;
        v.clear();
        tmp = getRelatedBlock(vpos3[p]);
        sort(tmp.begin(), tmp.end());
        set_intersection(temp.begin(), temp.end(),
                        tmp.begin(), tmp.end(),
                        back_inserter(v));
    }

    for (int p : v)
        if (getBit(p, number))
            deleteCandidate(p, number, del_unit, SU6, false);
    
    if (del_unit.size())
        return true;
    return false;
}

void Solver::printPath(int* parent, int last, bool is_loop)
{
    // path均作为栈使用
    stack<int> post_path;
    int j = 0;
    vector<vector<int> > multi_path;

    while (parent[last] > -1)  // 获得分链合并点
    {
        post_path.push(last);
        last = parent[last];
    }
    post_path.push(last);  // 分支起始点也加入

    if (parent[last] == -2)  // 分支点为基本广义节点
    {
        chain_node cn = get_chain_node(last);
        for (auto pos : cn.vpos)
            if (getBit(pos, cn.number))
                multi_path.push_back(vector<int>(1, getPos(cn.number, pos, cn.itype)));
        // 以multi_path[0]作为主链，其他为附链
        int last1 = multi_path[0][0];
        while (parent[last1] != -1)
        {
            multi_path[0].push_back(last1);
            last1 = parent[last1];
        }
        multi_path[0].push_back(last1);

        for (size_t i = 1; i < multi_path.size(); ++i)
        {
            last1 = multi_path[i][0];
            while (find(multi_path[0].begin(), multi_path[0].end(), last1) == multi_path[0].end())  // multi_path[0]中不含有last1
            {
                multi_path[i].push_back(last1);
                last1 = parent[last1];
            }
            multi_path[i].push_back(last1);
        }
    }

    // print
    chain_node cn = get_chain_node(post_path.top());;
    if (parent[last] == -1)  // 无分支
    {
        while (post_path.size() >= 2)
        {
            cn = get_chain_node(post_path.top());
            print_ntorc(ntorc(cn));
            cout << "(" << cn.number << ")" << (++j % 2 ? '=' : '-');
            post_path.pop();
        }
        cn = get_chain_node(post_path.top());
        print_ntorc(ntorc(cn));
    }
    // cout << "(" << cn.number << "),len=" << j << " => ";
    // if (is_loop)
    //     cout << "  ->loop  ";
}

vector<int> Solver::getRelatedBlock(int n)
{
    vector<int> vect_related;
    for (int i = 0; i < 9; i++)
    {
        if (i != _r(n)) vect_related.push_back(_n(i, _c(n)));
        if (i != _c(n)) vect_related.push_back(_n(_r(n), i));
    }
    for (int ix = 0; ix < 3; ix++)
        for (int jx = 0; jx < 3; jx++)
            if (ix != _rinbox(n) && jx != _cinbox(n))
                vect_related.push_back(_nij(n, ix, jx));
    return vect_related;
}

vector<int> Solver::rowBlank(int i)
{
    vector<int> rvect;
    for (int j = 0; j < 9; j++)
        if (unit[_n(i, j)].left)
            rvect.push_back(_n(i, j));
    return rvect;
}

vector<int> Solver::columnBlank(int j)
{
    vector<int> cvect;
    for (int i = 0; i < 9; i++)
        if (unit[_n(i, j)].left)
            cvect.push_back(_n(i, j));
    return cvect;
}

vector<int> Solver::rowBlank_except_v(int i, vector<int> v)
{
    vector<int> rvect;
    for (int j = 0; j < 9; j++)
        if (unit[_n(i, j)].left && find(v.begin(), v.end(), _n(i, j)) == v.end())
            rvect.push_back(_n(i, j));
    return rvect;
}

vector<int> Solver::columnBlank_except_v(int j, vector<int> v)
{
    vector<int> cvect;
    for (int i = 0; i < 9; i++)
        if (unit[_n(i, j)].left && find(v.begin(), v.end(), _n(i, j)) == v.end())
            cvect.push_back(_n(i, j));
    return cvect;
}


vector<int> Solver::boxBlank(int b)
{
    vector<int> bvect;
    for (int ix = 0; ix < 3; ix++)
        for (int jx = 0; jx < 3; jx++)
            if (unit[_bij(b, ix, jx)].left)
                bvect.push_back(_bij(b, ix, jx));
    return bvect;
}

vector<pii> Solver::getStrongInferenceBlock_Conjugate(pii prior)
{
    vector<pii> vect;
    int pos = prior.first, n = prior.second;
    if (unit[pos].left == 0) return vect;
    
    if (c_count[n][_c(pos)] == 2)
        for (int i = 0; i < 9; i++)
            if (i != _r(pos) && bs_c[n][_c(pos)].test(i))
                if (!visited[getPos(chain_node(_n(i, _c(pos)), n, _Weak, _None))])
                    vect.push_back(pii(_n(i, _c(pos)), n));
    if (r_count[n][_r(pos)] == 2)
        for (int j = 0; j < 9; j++)
            if (j != _c(pos) && bs_r[n][_r(pos)].test(j))
                if (!visited[getPos(chain_node(_n(_r(pos), j), n, _Weak, _None))])
                    vect.push_back(pii(_n(_r(pos), j), n));
    if (b_count[n][_b(pos)] == 2)
        for (int bx = 0; bx < 9; bx++)
            if (bx != _ninbox(pos) && bs_b[n][_b(pos)].test(bx))
               if (!visited[getPos(chain_node(_bij(_b(pos), bx / 3, bx % 3), n, _Weak, _None))])
                    vect.push_back(pii(_bij(_b(pos), bx / 3, bx % 3), n));
    
    return vect;
}

vector<pii> Solver::getStrongInferenceBlock_Conjugate_dynamic(chain_node& cn_start, pii prior)
{
    vector<pii> vect;
    int pos = prior.first, n = prior.second;
    if (unit[pos].left == 0) return vect;
    
    if (c_count[n][_c(pos)] == 2)
        for (int i = 0; i < 9; i++)
            if (i != _r(pos) && bs_c[n][_c(pos)].test(i))
                if (!visited[getPos(chain_node(_n(i, _c(pos)), n, _Weak, _None))])
                    vect.push_back(pii(_n(i, _c(pos)), n));
    if (r_count[n][_r(pos)] == 2)
        for (int j = 0; j < 9; j++)
            if (j != _c(pos) && bs_r[n][_r(pos)].test(j))
                if (!visited[getPos(chain_node(_n(_r(pos), j), n, _Weak, _None))])
                    vect.push_back(pii(_n(_r(pos), j), n));
    if (b_count[n][_b(pos)] == 2)
        for (int bx = 0; bx < 9; bx++)
            if (bx != _ninbox(pos) && bs_b[n][_b(pos)].test(bx))
               if (!visited[getPos(chain_node(_bij(_b(pos), bx / 3, bx % 3), n, _Weak, _None))])
                    vect.push_back(pii(_bij(_b(pos), bx / 3, bx % 3), n));
    
    return vect;
}

vector<pii> Solver::getWeakInferenceBlock(pii prior)
{
    vector<pii> vect;
    if (unit[prior.first].left == 0) return vect;

    for (int p : getRelatedBlock(prior.first))
        if (getBit(p, prior.second))
            if (!visited[getPos(chain_node(p, prior.second, _Strong, _None))])
                vect.push_back(pii(p, prior.second));

    // random_shuffle(vect.begin(), vect.end());
    return vect;
}

vector<pii> Solver::getWeakInferenceBlock_dynamic(chain_node& cn_start, pii prior)
{
    vector<pii> vect;
    if (unit[prior.first].left == 0) return vect;

    for (int p : getRelatedBlock(prior.first))
        if (getBit(p, prior.second))
            if (!visited[getPos(chain_node(p, prior.second, _Strong, _None))])
                vect.push_back(pii(p, prior.second));

    // random_shuffle(vect.begin(), vect.end());
    return vect;
}

void Solver::update_same_to_dlx()
{
    DLX dlx;
    dlx.solve(false, problem);
    string stdAns = dlx.get_ans();
    bool right = true;
    for (int pos = 0; pos < 81; pos++)
        if (unit[pos].ans != 0 && unit[pos].ans != stdAns[pos] - '0')
            right = false;
    same_to_dlx = right;
}

void Solver::printProblem() const
{
    std::cout << "problem: \n";
    std::cout << "hint units: " << hintUnits << endl;
    for (int i = 0; i < 81; i++)
        if (unit[i].hint)
            std::cout << unit[i].hint << ((i + 1) % 9 ? ' ' : '\n');
        else std::cout << " " << ((i + 1) % 9 ? ' ' : '\n');
}

string Solver::getAns() const
{
    string s_ans;
    for (int pos = 0; pos < 81; pos++)
        s_ans.push_back(unit[pos].ans + '0');
    return s_ans;
}

void Solver::printCount()
{
    cout << "HiddenSingle: " << technique_count.HiddenSingle << endl
        << "LockedCandidates: " << technique_count.LockedCandidates << endl
        << "Subset: " << technique_count.Subset << endl
        << "Fish&Fin: " << technique_count.Fish_Fin << endl
        << "Wings: " << technique_count.Wings << endl
        << "UR: " << technique_count.UniqueRectangle << endl
        << "Chain: " << technique_count.Chain << endl
        << "ALS: " << technique_count.ALS << endl << endl;
}

void Solver::printAns()
{
    cout << "pro: " << problem << endl;
    cout << "Answer: \n";
    cout << "solved units: " << solvedUnits << endl;
    cout << "Difficulty level = " << level << endl;
    cout << "time consumed = " << time_consumed << "ms." << endl;
    for (int i = 0; i < 81; i++)
        if (unit[i].ans != 0)
        {
            if (unit[i].hint)
                SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE),FOREGROUND_INTENSITY |
                     FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_BLUE);  // 白字
            else
                SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE),FOREGROUND_INTENSITY |
                     FOREGROUND_BLUE);  // 蓝字
            std::cout << unit[i].ans << ((i + 1) % 9 ? ' ' : '\n');
        }
        else std::cout << " " << ((i + 1) % 9 ? ' ' : '\n');
    SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE),FOREGROUND_INTENSITY |
         FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_BLUE);  // 白字
    // for (int u = 1; u <= 9; u++)
    //     cout << u << ":  " << solvedAmount[u] << endl;
    cout << "score: " << score << endl;
    cout.setf(ios_base::boolalpha);
    update_same_to_dlx();
    cout << "same to DLX?  " << same_to_dlx << endl << endl;
    printCount();
}

void Solver::printSudoku()
{
    for (int i = 0; i < 81; i++)
        if (unit[i].ans != 0)
        {
            if (unit[i].hint)
                SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE),FOREGROUND_INTENSITY |
                     FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_BLUE);  // 白字
            else
                SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE),FOREGROUND_INTENSITY |
                     FOREGROUND_BLUE);  // 蓝字
            std::cout << unit[i].ans << ((i + 1) % 9 ? ' ' : '\n');
        }
        else std::cout << " " << ((i + 1) % 9 ? ' ' : '\n');
    SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE),FOREGROUND_INTENSITY |
         FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_BLUE);  // 白字
}

void Solver::solve()
{
    LockedCandidates();  // level_2
    Subset();  // level_3
    UniqueRectangle();  // level_4
    Fish();  // level_4
    Fin();  // level_5
    Wings();  // level_6
    Chain();  // level_7
    DynamicChain_Branch();  //level_8
    if (solvedUnits != 81) level = 9;
    update_same_to_dlx();
}