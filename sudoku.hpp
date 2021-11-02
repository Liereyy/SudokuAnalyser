// sudoku.hpp -- Sudoku namespace declaration

#pragma once

#include <iostream>
#include <string>
#include <cstring>
#include <sstream>
#include <bitset>
#include <crtdefs.h>
#include <windows.h>
#include <algorithm>

#include <vector>
#include <stack>
#include <unordered_set>

using namespace std;

namespace Sudoku
{
    typedef pair<int, int> pii;  // (pos, n)对

    class DLX
    {
    private:
        enum {MAXN = 3241, MCOL = 325};// 初盘全空时324 + 9 * 81 * 4 = 3240
        LARGE_INTEGER nFreq;//LARGE_INTEGER在64位系统中是LONGLONG，在windows.h中通过预编译宏作定义
        LARGE_INTEGER nBeginTime;//记录开始时的计数器的值
        LARGE_INTEGER nEndTime;//记录停止时的计数器的值
        int cur_n, head;
        int dance_times, ans_property;  // 0无解，1唯一解，大于1多解
        int r[MAXN], l[MAXN], u[MAXN], d[MAXN], col[MAXN], Size[MCOL];
        bool flag, multi_judge;
        bool set_once;  // 解数独未启用多解性判断时保证只保存一次数独答案用
        int problem[81], sudo[81];  // 保存题目初盘和现在的数独盘面
        char ans[82], ans2[82];  //  保存答案
        double time_consumed;  // 单位是ms
        // private methods
        void link(int c);  // c为列数
        void make(int i, int j, int n);  // 往01矩阵添加一行，i行，j列，填入n
        void remove(int c);  // c列
        void resume(int c); // c列
        void dance();
        void save_ans(char* a);
    public:
        double solve(bool multi, const string& pro);  // 参数multi指出是否启用多解判断(true启用)，pro是数独题字符串
        string create_sudoku(const int tip_num);  // 生成一个有tip_exist_num个提示数的有唯一解的数独初盘
        char* c_create_sudoku(const int tip_num, char* c_pro);
        char* get_ans() { return ans; }
        char* get_ans2() { return ans2; }
        int get_ans_property() { return ans_property; }
        float get_dance_times() { return dance_times; }
        float get_time_consumed() { return time_consumed; }
        void print_ans();  // 打印数独答案和相关信息
    };

    int _r(int n) { return n / 9; }
    int _c(int n) { return n % 9; }
    int _b(int n) { return n / 9 / 3 * 3 + n % 9 / 3; }
    int _iinbox(int i) { return i - i / 3 * 3; }
    int _jinbox(int j) { return j - j / 3 * 3; }
    int _rinbox(int n) { return _r(n) - _b(n) / 3 * 3; }
    int _cinbox(int n) { return _c(n) - _b(n) % 3 * 3; }
    int _ninbox(int n) { return _rinbox(n) * 3 + _cinbox(n); }
    int _bl(int b) { return b % 3 * 3; }
    int _bu(int b) { return b / 3 * 3; }
    int _bij(int b, int i, int j) { return 9 * (b / 3 * 3 + i) + b % 3 * 3 + j; }
    int _nij(int n, int i, int j) { return 9 * (n / 9 / 3 * 3 + i) + n % 9 / 3 * 3 + j; }
    int _n(int r, int c) { return 9 * r + c; }
    
    enum inference_type{_Strong, _Weak, _StrongWeak};
    enum direction_type{_None, _Row, _Column, _ALS_Box, _ALS_Row, _ALS_Column};
    typedef pair<int, inference_type>    pin;
    struct chain_node
    {
        direction_type dtype;
        inference_type itype;
        int number;
        vector<int> vpos;

        chain_node() {}
        chain_node(int p, int n, inference_type it, direction_type dt=_None)
                : dtype(dt), itype(it), number(n), vpos()
            { vpos.push_back(p); }
        chain_node(const vector<int>& p, int n, inference_type it, direction_type dt=_None)
                : dtype(dt), itype(it), number(n), vpos(p)
            {}

        bool operator==(const chain_node& t) { return vpos == t.vpos && number == t.number && itype == t.itype && dtype == t.dtype; }
        bool operator!=(const chain_node& t) { return vpos != t.vpos || number != t.number || itype != t.itype || dtype != t.dtype; }
        
        friend bool operator!=(pii& x, chain_node& y) { return x.first != y.vpos[0] || x.second != y.number; }
        friend bool operator!=(chain_node& x, pii& y) { return y != x; }
    };
    
    class ntorc
    {
    public:
        int number;
        // 三类节点

        // 1.单元格节点
        int pos;

        // 2.基本广义节点
        int b;
        int id;

        // 3.ALS广义节点
        vector<int> vpos;

        ntorc(int p) : pos(p) {}
        ntorc(int _number, int _b, int _id)
            : number(_number), pos(-1), b(_b), id(_id) {}
        ntorc(int _number, vector<int>& v)
            : number(_number), pos(-1), b(-1), vpos(v) {}
        ntorc(chain_node& cn)
        {
            switch (cn.dtype)
            {
            case _None:
                pos = cn.vpos[0];
                break;
            case _Row:
            {
                pos = -1;
                number = cn.number;
                b = _b(cn.vpos[0]);
                id = _rinbox(cn.vpos[0]);
            }
            break;
            case _Column:
            {
                pos = -1;
                number = cn.number;
                b = _b(cn.vpos[0]);
                id = 3 + _cinbox(cn.vpos[0]);
            }
            break;
            case _ALS_Box:
            case _ALS_Row:
            case _ALS_Column:
            {
                pos = b = -1;
                number = cn.number;
                vpos = cn.vpos;
            }
            break;
            default:
                break;
            }
        }
        
        friend ostream& operator<<(ostream& os, ntorc cn)
        {
            os << 'r' << (cn.pos / 9 + 1) << 'c' << (cn.pos % 9 + 1);
            return os;
        }
    };

    class Solver
    {
        friend class ntoc;
    private:
        string problem;
        int hintUnits;
        int solvedUnits;
        int level;
        int score;
        bool same_to_dlx;  // 是否与dlx得到的解一致
        double time_consumed;

        struct Counter
        {
            int HiddenSingle;
            int LockedCandidates;
            int Subset;
            int Fish_Fin;
            int Wings;
            int UniqueRectangle;
            int Chain;
            int ALS;
            Counter() : HiddenSingle(0), LockedCandidates(0), Subset(0),
                        Fish_Fin(0), Wings(0), UniqueRectangle(0), Chain(0), ALS(0) {}
        };
        Counter technique_count;

        LARGE_INTEGER nFreq;  // LARGE_INTEGER在64位系统中是LONGLONG，在windows.h中通过预编译宏作定义
        LARGE_INTEGER nBeginTime;  // 记录开始时的计数器的值
        LARGE_INTEGER nEndTime;  // 记录停止时的计数器的值

        int r_count[10][9];  // 第一个表示数字1~9，第二个表示行数0~8
        int c_count[10][9];  // 第一个表示数字1~9，第二个表示列数0~8
        int b_count[10][9];  // 第一个表示数字1~9，第二个表示宫数0~8
        // 例:r_count[8][7] = 2 表示第7行剩余2格含有候选数8

        int br_count[10][9][3];
        int bc_count[10][9][3];
        // 例:br_count[8][3][0]表示第3宫第0行的那三格含有的候选数8的个数

        bitset<9> bs_r[10][9];
        bitset<9> bs_c[10][9];
        bitset<9> bs_b[10][9];

        // 例:bs_r[8][7].first = 001 011 001 表示候选数8在第7行的剩余状况，1表示剩余 
        // second表示如果这个区域只剩一个候选数的时候最后一个候选数的位置，若剩多个为-1

        enum {SU0 = 1, SU1 = 10, SU2 = 60, SU3 = 90,
                SU4 = 150, SU4_1 = 275, SU5 = 325, SU6 = 400, SU7 = 500};

        // 这里把单元格节点、基本广义节点和ALS广义节点分为三类节点
        enum {total_nodes = 2 * 9 * (81 + 9 * (3 + 3)) + 2 * 9 * 3 * 9 * 512};  // = 251262

    public:
        struct Unit
        {
            int hint;  // 提示数
            int left;  // 剩余候选数个数
            int ans;  // 答案
            short candidate;  // 候选数，每个bit表示一个候选数，1表示剩余
            
            Unit() : hint(0), left(9), ans(0), candidate(0x01FF) {}
            // candidate初始化为0000 0001 1111 1111，有意义的仅为最后9位
        };
    private:
        Unit unit[81];
        int related[20];  // 这个数组会不断更新
        int solvedNum[10];  // 记录盘面已填的1~9数目

        bool visited[total_nodes];
        bool gained[total_nodes];
        bool insideUnit[81];  // 单元格内关系

    // 坐标(row,col)和宫box与序号n之间的内联转换函数
        
        int _count_bit1(short a)
        {
            int n = 0;
            while (a)
            {
                ++n;
                a &= a - 1;
            }
            return n;
        }
        int getPos(int number, int opos) { return (number - 1) * 135 + opos; }
        // 根据b和id快速定位到相应的pos
        int getPos(int number, int b, int id) { return (number - 1) * 135 + 81 + 6 * b + id; }
        
        // return: true->strong, false->weak
        bool get_opnbidv(int pos, int& opos, int& number, int& b, int& id, bool& is_ALS_node, vector<int>& vpos, int& als_type);
        int get_id(int pos);

    // 辅助方法
    // 取pos格候选数number状态
        bool getBit(int pos, int number) { return unit[pos].candidate >> (number - 1) & 1; }
        void setBit0(int pos, int number) { unit[pos].candidate &= ~(1 << (number - 1)); }
        void setBit1(int pos, int number) { unit[pos].candidate |= 1 << (number - 1); }
        void update_same_to_dlx();
        inline void update_xcount_bsx_add(int pos, int number);  // 在pos格填入数number后更新r(cb)_count和bs_r(cb)
        inline void update_xcount_bsx_delete(int pos, int number);  // 在pos格删除候选数number后更新r(cb)_count和bs_r(cb)
        inline void update_xcount_bsx_resume(int pos, int number);  // 在pos格恢复候选数number后更新r(cb)_count和bs_r(cb)
        bool deleteSharedAffectBlock(int number, int pos1, int pos2, vector<pii>& del_unit);
        bool deleteSharedAffectBlock(int number, vector<int>& pos1, vector<int>& pos2, vector<pii>& del_unit);
        bool deleteSharedAffectBlock(int number, vector<int>& vpos1, vector<int>& vpos2, vector<int>& vpos3, vector<pii>& del_unit);
        void HiddenSingle_unit(int pos, int number);
        void autoFillNumber(int pos, int number);  // pos格被删去候选数number，搜索是否有可以填数的格
        void autoFillNumber(vector<pii>& del_unit);
        void fillNumber(int pos, int number);  // 已经确定在pos填入number
        void resetRelatedBlock(int n);
        int getOtherCandidate(int pos, int number)
        {
            for (int n = 1; n <= 9; ++n)
                if (getBit(pos, n) && n != number)
                    return n;
            return -1;
        }
        void printPath(int* parent, int last, bool is_loop = false);
        bool inTheSameArea(int pos1, int pos2) { return _r(pos1) == _r(pos2) || _c(pos1) == _c(pos2) || _b(pos1) == _b(pos2); }
        bool inTheSameArea(vector<int> vpos1, vector<int> vpos2)
        {
            for (auto pos1 : vpos1)
                for (auto pos2 : vpos2)
                    if (!inTheSameArea(pos1, pos2))
                        return false;
            return true;
        }
        bool noIntersection(vector<int> vpos1, vector<int> vpos2)
        {
            sort(vpos1.begin(), vpos1.end());
            sort(vpos2.begin(), vpos2.end());
            vector<int> v;
            set_intersection(vpos1.begin(), vpos1.end(),
                        vpos2.begin(), vpos2.end(),
                        back_inserter(v));
            return v.empty();
        }
        inline bool deleteCandidate(int pos, int number, vector<pii>& del_unit, int addScore=SU0, bool actually_delete=true);
        inline void resumeCandidate(int pos, int number);
        void placeSideEffect(int pos);  // 填入一个数产生的占位效果
        
        vector<int> getRelatedBlock(int n);
        vector<int> rowBlank(int i);
        vector<int> columnBlank(int j);
        
        vector<int> rowBlank_except_v(int i, vector<int> v);
        vector<int> columnBlank_except_v(int j, vector<int> v);
        vector<int> boxBlank(int b);

        void printDetails();
        void print_ntorc(ntorc cn);
    // 核心方法
        void NakedSingle(int n);  // 唯一余数法
        void HiddenSingle(int n);  // 行列宫排除法
        void HiddenSingle_deleteCandidatesOnly(int pos);
        void LockedCandidates(int n = -1);  // 区块排除法
        void Subset(); // 数组
            void HiddenSubsetInRow();
            void HiddenSubsetInColumn();
            void HiddenSubsetInBox();
            // mode : 0宫，1行，2列
            void NakedSubset(int size, int mode);
        void UniqueRectangle();  // level 4

        void TechPack()
        {
            LockedCandidates();
            UniqueRectangle();
        }
        void Fish();  // 鱼
        void Fin();  // 鱼鳍
        void Wings();  // 分支匹配
        void Chain();
            
            friend bool operator==(const chain_node& cn1, const chain_node& cn2) 
            { return cn1.vpos == cn2.vpos && cn1.number == cn2.number && cn1.itype == cn2.itype && cn1.dtype == cn2.dtype; }
            friend ostream& operator<<(ostream& os, chain_node& cn)
            {
                os << "dtype(" << cn.dtype << "), itype(" << cn.itype << "), number(" << cn.number << "), vpos(";
                for (auto pos : cn.vpos)
                    os << ntorc(pos) << ' ';
                os << ")\n";
                return os;
            }

            const int flag[6] = {0b111111000, 0b111000111, 0b000111111, 0b110110110, 0b101101101, 0b011011011};
            int getPos(int number, vector<int> vpos, inference_type it, direction_type dt)  // ALS节点用
            {
                int id = 0;
                switch (dt)
                {
                    case _ALS_Box:
                    {
                        for (auto pos : vpos)
                            id |= 1 << _ninbox(pos);
                        // 如果可以转化为基本广义节点则转化过去，防止重复
                        for (int i = 0; i < 6; ++i)
                            if ((id & flag[i]) == 0)
                                return getPos(number, _b(vpos[0]), i) + (it == _Strong ? 1215 : 0);
                        return 2430 + 3 * 9 * 512 * (number - 1) + 512 * _b(vpos[0]) + id + (it == _Strong ? 9 * 3 * 9 * 512 : 0);
                    }
                    break;
                    
                    case _ALS_Row:
                    {
                        for (auto pos : vpos)
                            id |= 1 << (pos % 9);
                        // 如果可以转化为基本广义节点则转化过去，防止重复
                        for (int i = 0; i < 3; ++i)
                            if ((id & flag[i]) == 0)
                                return getPos(number, _b(vpos[0]), i) + (it == _Strong ? 1215 : 0);
                        return 2430 + 3 * 9 * 512 * (number - 1) + 512 * _r(vpos[0]) + 512 * 9 + id + (it == _Strong ? 9 * 3 * 9 * 512 : 0);
                    }
                    break;

                    case _ALS_Column:
                    {
                        for (auto pos : vpos)
                            id |= 1 << (pos / 9);
                        // 如果可以转化为基本广义节点则转化过去，防止重复
                        for (int i = 0; i < 3; ++i)
                            if ((id & flag[i]) == 0)
                                return getPos(number, _b(vpos[0]), 3 + i) + (it == _Strong ? 1215 : 0);
                        return 2430 + 3 * 9 * 512 * (number - 1) + 512 * _c(vpos[0]) + 512 * 9 * 2 + id + (it == _Strong ? 9 * 3 * 9 * 512 : 0);
                    }
                    break;

                    default:
                    break;
                }
                return -1;
            }
            int getPos(const chain_node& cn)
            {
                switch (cn.dtype)
                {
                    case _None:
                        return getPos(cn.number, cn.vpos[0]) + (cn.itype == _Strong ? 1215 : 0);
                        break;
                    case _Row:
                        return getPos(cn.number, _b(cn.vpos[0]), _rinbox(cn.vpos[0])) + (cn.itype == _Strong ? 1215 : 0);
                        break;
                    case _Column:
                        return getPos(cn.number, _b(cn.vpos[0]), 3 + _cinbox(cn.vpos[0])) + (cn.itype == _Strong ? 1215 : 0);
                        break;
                    case _ALS_Box:
                    case _ALS_Row:
                    case _ALS_Column:
                        return getPos(cn.number, cn.vpos, cn.itype, cn.dtype);
                        break;
                    default:
                        break;
                }
                return -1;
            }

            chain_node get_chain_node(int pos)
            {
                int opos, number, b, id, als_type;
                bool is_ALS_node;
                vector<int> vpos;
                inference_type itype = get_opnbidv(pos, opos, number, b, id, is_ALS_node, vpos, als_type) ? _Strong : _Weak;
                if (b == -1)
                    return chain_node(opos, number, itype, _None);
                else if (!is_ALS_node)
                {
                    if (id < 3)  // 基本行节点
                    {
                        vector<int> v;
                        for (int jx = 0; jx < 3; ++jx)
                            if (getBit(_bij(b, id, jx), number))
                                v.push_back(_bij(b, id, jx));
                        return chain_node(v, number, itype, _Row);
                    }
                    else  // 基本列节点
                    {
                        vector<int> v;
                        for (int ix = 0; ix < 3; ++ix)
                            if (getBit(_bij(b, ix, id - 3), number))
                                v.push_back(_bij(b, ix, id - 3));
                        return chain_node(v, number, itype, _Column);
                    }
                }
                else  // ALS节点
                {
                    switch (als_type)
                    {
                    case 0:
                        return chain_node(vpos, number, itype, _ALS_Box);
                    case 1:
                        return chain_node(vpos, number, itype, _ALS_Row);
                    case 2:
                        return chain_node(vpos, number, itype, _ALS_Column);
                    default:
                        break;
                    }
                }
                return chain_node();
            }
            
            inline vector<pii> getStrongInferenceBlock_Conjugate(pii prior);  // 共轭对
            inline vector<pii> getWeakInferenceBlock(pii prior);

            bool mFlag;
            deque<chain_node> Fringe;

            void strongInference(chain_node& cn_start, deque<chain_node>& Fringe, int* parent);
            void weakInference(chain_node& cn_start, deque<chain_node>& Fringe, int* parent);
            bool chain_deleteCandidates(chain_node& cn_head, chain_node& front, deque<chain_node>& Fringe, int* parent, int max_length);
            int chain_length(int* parent, int last)
            {
                int length = 0;
                while (parent[last] != -1)
                {
                    ++length;
                    last = parent[last];
                }
                ++length;
                return length;
            }
            void BasicChain(int max_length);
            int* parent;

            void DynamicChain_Branch();
            void strongInference_dynamic(chain_node& cn_start);
            void weakInference_dynamic(chain_node& cn_start);
            bool chain_deleteCandidates_dynamic(chain_node& cn_head, chain_node& front);
            enum branch_type{_shared1, _branch1, _branch2, _shared2};
            branch_type btype[total_nodes];
            bool* ever_splited;
            bool* ever_merged;
            int merge_subpos[2];

            void update_parent(chain_node& cn_start, chain_node& new_node)  // 根据btype类型更新相应的parent
            {
                switch (btype[getPos(cn_start)])
                {
                case _shared1:
                case _shared2:
                    parent[getPos(new_node)] = getPos(cn_start);
                    break;
                case _branch1:
                    parent_branch1[getPos(new_node)] = getPos(cn_start);
                    break;
                case _branch2:
                    parent_branch2[getPos(new_node)] = getPos(cn_start);
                    break;
                default:
                    break;
                }
            }
            bool push_chain_node(chain_node& cn_start, chain_node& new_node, bool examine=true)
            {
                if (examine)
                    if (visited[getPos(new_node)] || find(Fringe.begin(), Fringe.end(), new_node) != Fringe.end())
                        return false;
                btype[getPos(new_node)] = btype[getPos(cn_start)];
                update_parent(cn_start, new_node);
                switch (btype[getPos(new_node)])
                {
                case _shared1:
                    us_visited_shared1.insert(getPos(new_node));
                    break;
                case _branch1:
                    us_visited_branch1.insert(getPos(new_node));
                    break;
                case _branch2:
                    us_visited_branch2.insert(getPos(new_node));
                    break;
                case _shared2:
                    us_visited_shared2.insert(getPos(new_node));
                    break;
                default:
                    break;
                }
                if (!hasBranch || merged)
                    Fringe.push_front(new_node);
                else
                    Fringe.push_back(new_node);

                // if (hasBranch && !merged && (btype[getPos(cn_start)] == _branch1 || btype[getPos(cn_start)] == _branch2))
                // {
                //     cout << getPos(cn_start) << "(" << btype[getPos(cn_start)] << ") " << getPos(new_node) << "(" << btype[getPos(new_node)] << ")\n";
                //     if (btype[getPos(cn_start)] == _branch1)
                //     {
                //         cout << "split_pos[0] = " << split_pos[0] << endl;
                //         int last1 = getPos(new_node);
                //         while (last1 != split_pos[0])
                //         {
                //             cout << last1 << ' ';
                //             last1 = parent_branch1[last1];
                //         }
                //         cout << last1 << endl;
                //     }
                //     if (btype[getPos(cn_start)] == _branch2)
                //     {
                //         cout << "split_pos[1] = " << split_pos[1] << endl;
                //         int last2 = getPos(new_node);
                //         while (last2 != split_pos[1])
                //         {
                //             cout << last2 << ' ';
                //             last2 = parent_branch2[last2];
                //         }
                //         cout << last2 << endl;
                //     }
                //     // system("pause");
                // }
                return true;
            }
            
            bool is_visited_branch1(int pos)
            {
                return us_visited_branch1.find(pos) != us_visited_branch1.end();
            }
            bool is_visited_branch2(int pos)
            {
                return us_visited_branch2.find(pos) != us_visited_branch2.end();
            }
            bool is_visited_branchx(int pos)
            {
                return is_visited_branch1(pos) || is_visited_branch2(pos);
            }
            bool is_visited_shared1(int pos)
            {
                return us_visited_shared1.find(pos) != us_visited_shared1.end();
            }
            bool is_visited_shared2(int pos)
            {
                return us_visited_shared2.find(pos) != us_visited_shared2.end();
            }
            bool is_visited_sharedx(int pos)
            {
                return is_visited_shared1(pos) || is_visited_shared2(pos);
            }
            bool is_visited(int pos)
            {
                return is_visited_branchx(pos) || is_visited_sharedx(pos);
            }
            
            bool cn_not_equal_except_itype(chain_node& cn1, chain_node& cn2)
            {
                return !inTheSameArea(cn1.vpos, cn2.vpos);
            }
            bool cn_equal_except_itype(chain_node& cn1, chain_node& cn2)
            {
                return cn1.dtype == cn2.dtype && cn1.number == cn2.number && cn1.vpos == cn2.vpos;
            }
            int split_times;
            int merge_times;

            enum {Max_Split_times = INT_MAX, Max_Merge_Times = INT_MAX};
            
            bool dynamic_chain_split(chain_node& cn_start, chain_node& new_node, bool can_be_used_as_normal_generalized_node=true);
            bool dynamic_chain_split_inblock(chain_node& new_node);
            void dynamic_chain_merge(chain_node& merged_node);
            void push_unit_node_expansion(chain_node& cn_start, int n, int npos)
            {
                chain_node new_node = construct_chain_node_by_nbid(n, _b(npos), _rinbox(npos), _Weak);
                push_chain_node(cn_start, new_node);
                new_node = construct_chain_node_by_nbid(n, _b(npos), 3 + _cinbox(npos), _Weak);
                push_chain_node(cn_start, new_node);
            }
            chain_node splitted_node;
            chain_node merged_node;
            int split_pos[2];

            int* parent_branch1;
            int* parent_branch2;
            
            unordered_set<int> us_visited_shared1;
            unordered_set<int> us_visited_branch1;
            unordered_set<int> us_visited_branch2;
            unordered_set<int> us_visited_shared2;

            bool merged;
            bool hasBranch;  // 记录此时是否已有分支
            chain_node current_cn_head;
            int count_for_any_use;

            inline vector<pii> getStrongInferenceBlock_Conjugate_dynamic(chain_node& cn_start, pii prior);  // 共轭对
            inline vector<pii> getWeakInferenceBlock_dynamic(chain_node& cn_start, pii prior);

            chain_node construct_chain_node_by_nbid(int number, int b, int id, inference_type it)
            {
                chain_node new_node;
                new_node.number = number;
                new_node.dtype = id < 3 ? _Row : _Column;
                new_node.itype = it;
                if (new_node.dtype == _Row)
                {
                    for (int jx = 0; jx < 3; ++jx)
                        if (unit[_bij(b, id, jx)].candidate >> (number - 1) & 1)
                            new_node.vpos.push_back(_bij(b, id, jx));
                }
                else
                    for (int ix = 0; ix < 3; ++ix)
                        if (unit[_bij(b, ix, id - 3)].candidate >> (number - 1) & 1)
                            new_node.vpos.push_back(_bij(b, ix, id - 3));
                return new_node;
            }
    public:
        Solver(const string& pro);
        void solve();
        void printProblem() const;
        string getAns() const;
        void printAns();
        void printSudoku();
        void printCount();
        Counter getCount() { return technique_count; }
        int getScore() const { return score; }
        int getLevel() const { return level; }
        bool getRight() { return same_to_dlx; }
        double getTimeConsumed() { return time_consumed; }
    };

    void Solver::print_ntorc(ntorc cn)
    {
        if (cn.pos != -1)
            cout << ntorc(cn.pos);
        else if (cn.b != -1)  // 基本广义节点
        {
            if (cn.id < 3)
            {
                cout << "r" << _bu(cn.b) + cn.id + 1 << "c";
                for (int jx = 0; jx < 3; ++jx)
                    if (getBit(_bij(cn.b, cn.id, jx), cn.number))
                        cout << _bl(cn.b) + jx + 1;
            }
            else
            {
                cout << "c" << _bl(cn.b) + cn.id - 3 + 1 << "r";
                for (int ix = 0; ix < 3; ++ix)
                    if (getBit(_bij(cn.b, ix, cn.id - 3), cn.number))
                        cout << _bu(cn.b) + ix + 1;
            }
        }
        else  // ALS节点
        {
            for (auto p : cn.vpos)
                cout << ntorc(p) << ' ';
        }
    }

    void printString(const string& pro)
    {
        if (pro.size() == 81)
            for (int i = 0; i < 81; i ++)
                cout << pro[i] << ((i + 1) % 9 == 0 ? '\n' : ' ');
    }

    template <typename T>
    ostream& operator<<(ostream& os, vector<T> v)
    {
        for (auto p : v)
            cout << ntorc(p) << ' ';
        cout << endl;
        return os;
    }

    ostream& operator<<(ostream& os, const chain_node& cn)
    {
        cout << cn.dtype << ' ' << cn.itype << ' ' << cn.number << ' ';
        cout << cn.vpos;
        return os;
    }
}