// DLX.hpp -- implementing DLX methods
// solve sudoku using dancingLinksX
#pragma once

#include "sudoku.hpp"
#include <cstdlib>  // rand(), srand(), prototype
#include <ctime>  // time() prototype
using namespace Sudoku;

// DLX methods

inline void DLX::link(int c)  // c为列数
{
    // 1 <= c <= 324
    ++cur_n; ++Size[c];
    u[cur_n] = u[c], d[cur_n] = c, col[cur_n] = c;
    u[c] = d[u[c]] = cur_n;
    if (!head) head = cur_n;  // 如果是一行的第一个元素
    else l[cur_n] = cur_n - 1, r[cur_n - 1] = cur_n;
}

void DLX::make(int i, int j, int n)  // 往01矩阵添加一行，i行，j列，填入n
{
    // 0 <= i, j <= 8, 1 <= n <= 9
    head = 0;
    link(i * 9 + j + 1);    // (i, j)填了一个数
    link(81 + i * 9 + n);   // 第i行填了数n
    link(162 + j * 9 + n);  // 第j列填了数n
    link(243 + (i / 3 * 3 + j / 3) * 9 + n);  // 第 i / 3 * 3 + j / 3宫填了数n
    l[head] = cur_n; r[cur_n] = head;
}

void DLX::remove(int c)  // c列
{
    // 标记行（第一行）
    l[r[c]] = l[c], r[l[c]] = r[c];
    // 遍历从下到上，从左到右
    for (int i = u[c]; i != c; i = u[i])
        for (int j = r[i]; j != i; j = r[j])
            u[d[j]] = u[j], d[u[j]] = d[j], --Size[col[j]];
}

void DLX::resume(int c) // c列
{
    // 标记行（第一行）
    l[r[c]] = r[l[c]] = c;
    // 遍历从下到上，从左到右
    for (int i = u[c]; i != c; i = u[i])
        for (int j = r[i]; j != i; j = r[j])
            u[d[j]] = d[u[j]] = j, ++Size[col[j]];
}

void DLX::save_ans(char* ans)
{
    for(int i = 0; i < 81; i++)
        ans[i] = sudo[i] + '0';
    ans[81] = '\0';
}

void DLX::dance()
{
    ++dance_times;
    if (flag) return;
    if (!r[0]) { /*r[0]=0找到一个解，递归结束*/ flag = true; return; }
    int c = r[0], pos=0, val=0;
    for (int i = r[c]; i; i = r[i])
        if (Size[i] < Size[c]) c = i;  // 找到元素最少列
    remove(c);
    // 选取列c为基准列，从c所含有元素的行一个个尝试
    for (int i = u[c]; i != c; i = u[i])
    {
        // 选择i所在的行
        if (col[i] > 0 && col[i] <= 81) pos = col[i];
        else if (col[i] > 81 && col[i] <= 162) val = col[i];
        // 删除与i所在行有共同列的行，实现方法是remove(j)，其中j是i所在行含有的元素的列数
        for (int j = r[i]; j != i; j = r[j])
        {
            remove(col[j]);
            if (col[j] > 0 && col[j] <= 81) pos = col[j];
            else if (col[j] > 81 && col[j] <= 162) val = col[j];
            // 以上两个if-elif:由于i所在的行有4个元素，其中必有两个分别出现在1~81列和82~162列
        }
        sudo[pos - 1] = (val - 1) % 9 + 1;  // 根据选定了i所在的行的尝试得到的结论
        dance();
        if (flag)
        {
            if(multi_judge)  // 启用多解性判断
            {
                if (ans_property == 0)
                {
                    flag = false, ans_property = 1;  // 假装未找到这个解，重置flag为false
                    save_ans(ans);
                }
                else
                {
                    ++ans_property;
                    if (ans_property == 2) save_ans(ans2);  // 只save一次
                    return;
                }
            }
            else  // 关闭多解性判断
            {
                if (!set_once)
                {
                    ans_property = 1;
                    save_ans(ans);  // 只save一次
                    set_once = true;
                }
                return;
            }
        }
        // 回溯，恢复i所在的行所含有元素所在的列
        for (int j = r[i]; j != i; j = r[j]) resume(col[j]); 
    }
    // 恢复列c
    resume(c);
}

double DLX::solve(bool multi, const std::string& pro)
{
    // 每解一次数独之前都重置所有的值，这样每解完一次之后相应信息仍保存在DLX对象中
    cur_n = 324, head = dance_times = 0, flag = set_once = false, ans_property = 0, multi_judge = multi;
    memset(Size, 0, sizeof(Size));  // sizeof(Size) = 4 * MCOL

    QueryPerformanceFrequency(&nFreq);//获取系统时钟频率
    QueryPerformanceCounter(&nBeginTime);//获取开始时刻计数值

    for (int i = 0; i <= cur_n; i++)
        l[i] = i - 1, r[i] = i + 1, u[i] = d[i] = i;
    l[0] = cur_n, r[cur_n] = 0;

    for (int i = 0; i < 9; i++)
        for (int j = 0; j < 9; j++)
        {
            int place = 9 * i + j;
            problem[place] = sudo[place] = pro[place] - '0';
            if (sudo[place]) make(i, j, sudo[place]);  // sudo[place]有数，只增加一行
            else for (int k = 1; k <= 9; k++) make(i, j, k);  // sudo[place]为空，每个数字都假设填一遍
        }
    dance();

	QueryPerformanceCounter(&nEndTime);//获取停止时刻计数值
	time_consumed = (double)(nEndTime.QuadPart - nBeginTime.QuadPart) / (double)nFreq.QuadPart;// 精确到小数点后7位
    time_consumed *= 1000;

    return time_consumed;
}

void DLX::print_ans()
{
    using std::cout;
    // 打印数独初盘
    cout << "problem:\n";
    for (int i = 0; i < 81; i ++)
        cout << problem[i] << ((i + 1) % 9 == 0 ? '\n' : ' ');
    cout << endl;

    if (ans_property)
    {
        cout << "answer:\n";
        for (int i = 0; i < 81; i ++)
        {
            if (problem[i])
                SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE),FOREGROUND_INTENSITY |
                    FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_BLUE);  // 白字
            else
                SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE),FOREGROUND_INTENSITY |
                    FOREGROUND_BLUE);  // 蓝字
            cout << ans[i] << ((i + 1) % 9 == 0 ? '\n' : ' ');
            // cout << ans[i];
        }
        SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE),FOREGROUND_INTENSITY |
            FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_BLUE);  // 白字
    }
    else
        cout << "No solution.\n";
    if (multi_judge)
    {
        if (ans_property > 1)
        {
            cout << "\nThe answer is not unique.The second answer is:\n";
            for (int i = 0; i < 81; i ++)
            {
                if (problem[i])
                    SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE),FOREGROUND_INTENSITY |
                        FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_BLUE);  // 白字
                else
                    SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE),FOREGROUND_INTENSITY |
                        FOREGROUND_BLUE);  // 蓝字
                cout << ans2[i] << ((i + 1) % 9 == 0 ? '\n' : ' ');
            }
            SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE),FOREGROUND_INTENSITY |
                FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_BLUE);  // 白字
        }
        else if (ans_property == 1)
            cout << "The answer is unique.\n";
    }
    cout << "time consumed = " << time_consumed << "ms, dance_times = " << dance_times << std::endl;
}

string DLX::create_sudoku(const int tip_num)
{
    QueryPerformanceCounter(&nBeginTime);//获取开始时刻计数值
    QueryPerformanceFrequency(&nFreq);//获取系统时钟频率
    int n = 81 - tip_num;
    // 随机生成一个数独终盘
    int store[9] = {1, 2, 3, 4, 5, 6, 7, 8, 9};
    memset(sudo, 0, sizeof(sudo));
    for(int k = 0; k < 3; k++)
    {
        random_shuffle(store, store + 9);
        // 将store数组填入sudo数组的第1,5,9宫
		for(int u = 0; u < 3; u++)
	        for(int v = 0; v < 3; v++)
	            sudo[9 * (3 * k + u) + 3 * k + v] = store[3 * u + v];
	}
    string _temp_pro;
    for (int i = 0; i < 81; i++)
        _temp_pro.push_back(sudo[i] + '0');
    solve(false, _temp_pro);
    string created_pro;
    for (int i = 0; i < 81; i++)
        created_pro.push_back(sudo[i] + '0');

    // 挖洞法
    while(n)
    {
        // 微秒级种子
        LARGE_INTEGER nStartCounter;
        QueryPerformanceCounter(&nStartCounter);
        srand((unsigned)nStartCounter.LowPart);

		int k = rand() % 81;
		if (created_pro[k] != '0') 
        {
			char temp = created_pro[k];
			created_pro[k] = '0';
            solve(true, created_pro);
			if(ans_property != 1)  // 保证数独有唯一解
                created_pro[k] = temp;
			else n--;
		}
	}
    QueryPerformanceCounter(&nEndTime);//获取停止时刻计数值

	// cout << "Creating time: " << (double)(nEndTime.QuadPart - nBeginTime.QuadPart) * 1000 / (double)nFreq.QuadPart << "ms.\n";
    return created_pro;
}

char* DLX::c_create_sudoku(const int tip_num, char* c_pro)
{
    string _created_pro = create_sudoku(tip_num);
    for (int i = 0; i < 81; i++)
        c_pro[i] = _created_pro[i];
    c_pro[81] = '\0';
    return c_pro;
}