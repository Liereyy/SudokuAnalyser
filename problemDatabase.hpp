#ifndef PROBLEM_DATABASE_HPP
#define PROBLEM_DATABASE_HPP

#include <fstream>
#include <string>
#include "DLX.hpp"
#include "SolverCore_AIC.hpp"
#include "SolverCore_DynamicChain.hpp"
using namespace std;
using namespace Sudoku;

const char* depro = "000985072200730001009600500760003020000000040021070005690010703310090000002000000";

class SudokuProblem
{
private:
    char pro[82];
    int level;
    int score;
    bool right;
public:
    SudokuProblem() :level(0), score(0) { update(depro); }
    SudokuProblem(const char* p) : level(0), score(0) { update(p); }
    ~SudokuProblem() {}
    void update(const char*);
    char* getProblem() { return pro; }
    int getLevel() { return level; }
    int getScore() { return score; }
    bool getRight() { return right; }
    friend ostream& operator<<(ostream& os, const SudokuProblem& sp);
    friend istream& operator>>(istream& is, SudokuProblem& sp);
};

template<typename T>
class Database
{
private:
    int amount;
    const int MaxLevel;  // 能确定的最大难度
    int unsolved;

    fstream database;
    char fname[40];
    int difficulty_level[21];  // 存储每个难度的数独数量,level取值区间1~MaxLevel
    ostream& print(ostream&);
    friend ostream& operator<<(ostream& os, Database& db) { return db.print(os); }
public:
    Database();
    void add(bool examine, T&);
    bool find(T&);
    void modify(T&);
    void clear();
    void getTargetProblem(int rec);
    void generateSudoku(int param, int mode);
    void run();
};

#endif