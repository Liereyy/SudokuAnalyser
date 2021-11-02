#include "problemDatabase.hpp"
#include <cstdlib>
#include <iomanip>
#include <cstdio>

void SudokuProblem::update(const char* p)
{
    Solver solver(p);
    level = solver.getLevel();
    score = solver.getScore();
    right = solver.getRight();
    strncpy(pro, p, 81);
    pro[81] = '\0';
}

ostream& operator<<(ostream& os, const SudokuProblem& sp)
{
    os << "pro: " << sp.pro << " (level:" 
        << sp.level << ", score: " << sp.score<< ")" << endl;
    return os;
}

istream& operator>>(istream& is, SudokuProblem& sp)
{
    cout << "Input a problem string: ";
    char tpro[82];
    is >> tpro;
    sp = SudokuProblem(tpro);
    return is;
}

template<class T>
Database<T>::Database()
    : amount(0), MaxLevel(8), unsolved(0)
{
    strcpy(fname, "database.dat");
    memset(difficulty_level, 0, sizeof(difficulty_level));
    
    ifstream fin("D:/vscode/Microsoft VS Code/SudokuAnalyser/info.txt");
    fin >> amount;
    for (int i = 1; i <= MaxLevel; i++)
        fin >> difficulty_level[i];
    fin >> unsolved;
    fin.close();

    database.open(fname, ios_base::in | ios_base::binary);
    database.seekg(0);
    database.close();
}

template<class T>
void Database<T>::add(bool examine, T& data)
{
    if (examine)
        if (find(data))
        {
            cout << "problem exist.\n";
            return;
        }
    ++amount;
    try
    {
        SudokuProblem sp(data.getProblem());
        if (sp.getRight() == false)
        {
            cerr << "wrong solution!" << endl;
            cout << sp.getProblem() << endl;
        }
        if (sp.getLevel() <= MaxLevel)
            ++difficulty_level[sp.getLevel()];
        else
            ++unsolved;
    }
    catch(const std::exception& e)
    {
        std::cerr << e.what() << '\n';
    }
    database.clear();
    database.open(fname, ios_base::out | ios_base::app | ios_base::binary);
    database.write((char*) &data, sizeof(data));
    ofstream fout("D:/vscode/Microsoft VS Code/SudokuAnalyser/info.txt");
    fout << amount << ' ';
    for (int i = 1; i <= MaxLevel; i++)
        fout << difficulty_level[i] << ' ';
    fout << unsolved;
    fout.close();
    database.close();
}

template<class T>
void Database<T>::modify(T& data)
{
    T tmp;
    database.open(fname, ios_base::in |ios_base::out | ios_base::binary);
    while (database.read((char*) &tmp, sizeof(tmp)))
        if (strcmp(tmp.getProblem(), data.getProblem()) == 0)
        {
            cin >> tmp;
            database.seekg(-sizeof(data), ios_base::cur);
            database.write((char*) &tmp, sizeof(tmp));
            database.close();
            return;
        }
    database.close();
    cout << "The record to de modified is not in the database";
}

template<class T>
bool Database<T>::find(T& data)
{
    if (amount == 0) return false;
    T tmp;
    database.open(fname, ios_base::in | ios_base::binary);
    database.seekg(0);
    while (!database.eof())
    {
        database.read((char*) &tmp, sizeof(tmp));
        if (strcmp(tmp.getProblem(), data.getProblem()) == 0)
        {
            database.close();
            return true;
        }
    }
    database.close();
    return false;
}

template<class T>
ostream& Database<T>::print(ostream& os)
{
    if (amount == 0) { cout << "database is empty.\n"; return os; }
    char option;
    cout << "输入字符a全部打印, 数字n(1~" << MaxLevel << ")指定难度数独:('u'打印未解决的数独) ";
    cin >> option;
    if (option == 'u') option = char(MaxLevel + 1 + '0');
    T tmp;
    database.clear();
    database.open(fname, ios_base::in | ios_base::out | ios_base::binary);
    database.seekg(0);
    int _count = 0;
    while (database.read((char*) &tmp, sizeof(tmp)))
    {
        if (option == 'a')
            os << tmp;
        else if (option >= '1' && option <= char(MaxLevel + 1 + '0'))
        {
            try
            {
                if (tmp.getLevel() == option - '0')
                {
                    os << tmp;
                    ++_count;
                }
            }
            catch(const std::exception& e)
            {
                std::cerr << e.what() << '\n';
            }
        }
    }
    if (option == 'a')
        cout << "Total sudoku problems: " << amount << endl;
    else if (option >= '1' && option <= char(MaxLevel + '0'))
        cout << "number of level " << option << ": " << _count << endl;
    else if (option == char(MaxLevel + 1 + '0'))
        cout << "number of unsolved: " << _count << endl;
    else
        cout << "invalid.\n";
    database.close();
    return os;
}

template<class T>
void Database<T>::clear()
{
    amount = unsolved = 0;
    memset(difficulty_level, 0, sizeof(difficulty_level));
    ofstream fout("E:/vscode/sudo/info.txt");
    fout << 0 << ' ';
    for (int i = 1; i <= MaxLevel; i++)
        fout << 0 << ' ';
    fout << 0;
    fout.close();
    remove(fname);
    database.open(fname, ios_base::out | ios_base::binary);
    database.close();
}

template<class T>
void Database<T>::getTargetProblem(int index)
{
    if (index < 0 || index >= amount)
    {
        cout << "invalid target.\n";
        return;
    }
    T tmp;
    streampos place = index * sizeof(tmp);
    database.open(fname, ios_base::in | ios_base::binary);
    database.seekg(place);
    database.read((char *) &tmp, sizeof(tmp));
    cout << tmp;
    database.close();
}

template<class T>
void Database<T>::generateSudoku(int param, int mode)
{
    database.clear();
    database.open(fname, ios_base::out | ios_base::app | ios_base::binary);
    
    if (mode == 0)
    {
        DLX dlx;
        char g_pro[82];
        for (int i = 0; i < param; i++)
        {
            SudokuProblem sp(dlx.c_create_sudoku(30, g_pro));
            if (sp.getLevel() <= MaxLevel)
                ++difficulty_level[sp.getLevel()];
            else
                ++unsolved;
            ++amount;
            if (sp.getRight() == false)
                cerr << "wrong solution!" << endl;
            database.write((char*) &sp, sizeof(sp));
        }
        cout << param << " sudoku generated.\n";
    }
    else if (mode == 1)
    {
        LARGE_INTEGER nFreq;  //LARGE_INTEGER在64位系统中是LONGLONG，在windows.h中通过预编译宏作定义
        LARGE_INTEGER nBeginTime;  //记录开始时的计数器的值
        LARGE_INTEGER nEndTime;  //记录停止时的计数器的值
        QueryPerformanceCounter(&nBeginTime);  //获取开始时刻计数值
        QueryPerformanceFrequency(&nFreq);  //获取系统时钟频率
        int count = 0;
        DLX dlx;
        char g_pro[82];
        QueryPerformanceCounter(&nEndTime);  //获取停止时刻计数值
        while ((double)(nEndTime.QuadPart - nBeginTime.QuadPart) / (double)nFreq.QuadPart < param)
        {
            SudokuProblem sp(dlx.c_create_sudoku(30, g_pro));
            if (sp.getLevel() <= MaxLevel)
                ++difficulty_level[sp.getLevel()];
            else
                ++unsolved;
            ++amount;
            if (sp.getRight() == false)
            {
                cerr << "wrong solution!" << endl;
                cout << sp.getProblem() << endl;
                system("pause");
                exit(EXIT_FAILURE);
            }
            database.write((char*) &sp, sizeof(sp));
            ++count;
            QueryPerformanceCounter(&nEndTime);  //获取停止时刻计数值
        }
        cout << count << " sudoku generated.\n";
    }

    ofstream fout("D:/vscode/Microsoft VS Code/SudokuAnalyser/info.txt");
    fout << amount << ' ';
    for (int i = 1; i <= MaxLevel; i++)
        fout << difficulty_level[i] << ' ';
    fout << unsolved;
    fout.close();

    database.close();
}

void printMenu()
{
    cout << "command    explanation\n";
    cout << "   sp\tsolve problem解一个数独题（长81的字符串，空格用0代替）\n";
    cout << "   an\tanalyse分析一个数独题（长81的字符串，空格用0代替）\n";
    cout << "   p\tprint,打印所有数独\n";
    cout << "   d\tdistribution,打印难度分布情况\n";
    cout << "   a\tadd,增加一个数独\n";
    cout << "   gl\tgenerate by level,随机生成指定难度的数独\n";
    cout << "   gn\tgenerate by num,随机生成指定数量的数独\n";
    cout << "   gt\tgenerate by time(second),随机生成second秒的数独\n";
    cout << "   f\tfind,查找数独是否存在\n";
    cout << "   t\ttarget,获得题库第index个数独(从0计数)\n";
    cout << "   s\tsize,获得题库的总数独数\n";
    cout << "   m\tmodify,修改一个数独\n";
    cout << "   c\tclear,清空数独\n";
    cout << "   q\tquit,退出\n";
}

template<class T>
void Database<T>::run()
{
    T rec;
    char option;
    string t_pro;
    DLX dlx;
    SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), FOREGROUND_INTENSITY);
    cout << "problemDatabase('h' for help): ";
    SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), FOREGROUND_INTENSITY | FOREGROUND_RED |
		FOREGROUND_GREEN | FOREGROUND_BLUE);
    while (cin.get(option) && option != 'q')
    {
        switch (option)
        {
        case 'p':
            cout << *this;
            while (cin.get() != '\n');
            break;
        case 'a':
            if (cin.get() == 'n')
            {
                cout << "Input a sudoku problem: ";
                cin >> t_pro;
                if (t_pro.length() == 81)
                {
                    Solver solver(t_pro);
                    dlx.solve(false, t_pro);
                    solver.printProblem();
                    solver.printAns();
                    if (dlx.get_ans_property() == 1)
                    {
                        cout << "do you want to save it? (y/n)\n";
                        char w;
                        cin >> w;
                        if (w == 'y')
                        {
                            SudokuProblem sp(t_pro.c_str());
                            add(true, sp);
                            cout << "done.\n";
                        }
                    }
                }
            }
            else
            {
                cin >> rec;
                add(true, rec);
            }
            while (cin.get() != '\n');
            break;
        case 'd':
            if (amount)
            {
                cout << "amount: " << amount << endl;
                for (int i = 1; i <= MaxLevel; i++)
                    cout << "level " << i << ": " << difficulty_level[i] << "\t(" 
                        << setiosflags(ios::fixed) << setprecision(2) << difficulty_level[i] * 100.0 / amount << "%)" << endl;
                cout << "unsolved: " << unsolved << "\t(" 
                        << setiosflags(ios::fixed) << setprecision(2) << unsolved * 100.0 / amount << "%)" << endl;
            }
            else
                cout << "empty.\n";
            while (cin.get() != '\n');
            break;
        case 'f':
            cin >> rec;
            cout << "The record is ";
            if (!find(rec)) cout << "not ";
            cout << "in the database.\n";
            while (cin.get() != '\n');
            break;
        case 'm':
            cin >> rec;
            modify(rec);
            while (cin.get() != '\n');
            break;
        case 's':
            if (cin.get() == 'p')
            {
                cout << "Input a sudoku problem: ";
                cin >> t_pro;
                if (t_pro.length() == 81)
                {
                    dlx.solve(true, t_pro);
                    dlx.print_ans();
                    if (dlx.get_ans_property() == 1)
                    {
                        cout << "do you want to save it? (y/n)\n";
                        char w;
                        cin >> w;
                        if (w == 'y')
                        {
                            SudokuProblem sp(t_pro.c_str());
                            add(true, sp);
                            cout << "done.\n";
                        }
                    }
                    while (cin.get() != '\n');
                }
            }
            else
                cout << amount << " sudoku in the database" << endl;
            break;
        case 'c':
            clear();
            while (cin.get() != '\n');
            break;
        case 't':
            int index;
            cout << "Input index: ";
            cin >> index;
            if (amount == 0) cout << "database is empty.\n";
            else getTargetProblem(index);
            while (cin.get() != '\n');
            break;
        case 'g':
            option = cin.get();
            if (option == 'n')
            {
                int num;
                cout << "generate num: ";
                cin >> num;
                cout << "generating...\n";
                generateSudoku(num, 0);
            }
            else if (option == 't')
            {
                int time_sec;
                cout << "generate time: ";
                cin >> time_sec;
                cout << "generating...\n";
                generateSudoku(time_sec, 1);
            }
            else if (option == 'l')
            {
                int lev;
                cout << "level: ";
                cin >> lev;
                if (difficulty_level[lev] != 0)
                {
                    database.clear();
                    database.open(fname, ios_base::in | ios_base::out | ios_base::binary);
                    database.seekg(0);
                    T tmp;
                    srand(time(0));
                    int _random = rand() % difficulty_level[lev];
                    while (database.read((char*) &tmp, sizeof(tmp)))
                    {
                        try
                        {
                            if (tmp.getLevel() == lev)
                            {
                                if (_random-- > 0)
                                    continue;
                                cout << tmp;
                                break;
                            }
                        }
                        catch(const std::exception& e)
                        {
                            std::cerr << e.what() << '\n';
                        }
                    }
                    database.close();
                }
                
            }
            while (cin.get() != '\n');
            break;
        case 'h':
            printMenu();
            while (cin.get() != '\n');
            break;
        case '\n':
            break;
        default:
            cout << "command not valid.\n";
            printMenu();
            while (cin.get() != '\n');
            break;
        }
        SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), FOREGROUND_INTENSITY);
        cout << "problemDatabase('h' for help): ";
        SetConsoleTextAttribute(GetStdHandle(STD_OUTPUT_HANDLE), FOREGROUND_INTENSITY | FOREGROUND_RED |
            FOREGROUND_GREEN | FOREGROUND_BLUE);
    }
}