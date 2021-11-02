# Sudoku Analyser

## 变量域

```c++
    string problem;  // 81个字符
    int solvedUnits;  // 已填的格数，包括提示数
    struct Unit
    {
        int hint;  // 提示数
        int left;  // 剩余候选数个数
        int ans;  // 答案
        short candidate;  // 候选数，每个bit表示一个候选数，1表示剩余
        Unit() : hint(0), left(9), ans(0), candidate(0x01FF) {}
        // candidate初始化为0000 0001 1111 1111，有意义的仅为最后9位
    };
    Unit unit[81];
    int level;
    int solvedAmount[10];  // 记录盘面已填的1~9数目  

    int r_count[10][9];  // 第一个表示数字1~9，第二个表示行数0~8
    int c_count[10][9];  // 第一个表示数字1~9，第二个表示列数0~8
    int b_count[10][9];  // 第一个表示数字1~9，第二个表示宫数0~8
    // 例:r_count[8][7] = 2 表示第7行剩余2格含有候选数8  

    pair<bitset<9>, int> bs_r[10][9];
    pair<bitset<9>, int> bs_c[10][9];
    pair<bitset<9>, int> bs_b[10][9];
    // 例:bs_r[8][7].first = 001 011 001 表示候选数8在第7行的剩余状况，1表示剩余  
    // second表示如果这个区域只剩一个候选数的时候最后一个候选数的位置

    // 辅助变量
    int related[20];
```

---

## Part1. 辅助函数

### Algo 0.0 &emsp; void HiddenSingle_unit (pos, number)

> based based algo  
> HiddenSingle的单元格版本  
> 调用这个函数已约定pos格排除了候选数number

行：若pos格的r_count[number][pos/9]为1，则该行只剩一格含有候选数number，此时bs_r[number][*].second标记这一格，在这格填数number，调用addNumber(pos, number)  
对列，宫同样判断

---

### Algo 0.1 &emsp; void placeEffect (pos)

> pos格填数之后的占位效应

相当于pos格排除了所有的候选数，  
对每个候选数a（除了pos格填入的数）调用HiddenSingle_unit算法

---

### Algo 0.2 &emsp; void addNumber (pos, number)

> 在pos格填数number之后进行的变量更新操作

++solvedUnites;  
++solvedAmount[number];  
pos格的left和candidate置为0  
pos格的ans置为number  
调用(Algo 1.2) HiddenSingle(pos);  
调用(Algo 0.4) update_rcbcount_bsrcb_add(pos, number);  
placeEffect(pos);  

以下根据level等级决定额外调用哪些方法：  
level >= 2:&emsp; LockedCandidates(pos);

---

### Algo 0.3 &emsp; void update_rcbcount_bsrcb_delete (int pos, int number)

> 在pos格删除候选数number后，更新x_count和bs_x，x=r, c, b  

行：  
if r_count[number][_r(pos)] > 0  
&emsp;&emsp;--r_count[number][_r(pos)];  
&emsp;&emsp;如果减至1，则表明该行只剩pos格含有候选数number，将bs_r[number][_r(pos)].first置为pos  
bs_r[number][_r(pos)].first的_c(pos)列置为0，表示pos格删去候选数number  
列，宫同样处理

---

### Algo 0.4 &emsp; void update_rcbcount_bsrcb_add (int pos, int number)

> 在pos格填数number之后，更新x_count和bs_x，x=r, c, b  

行列宫计数r(cb)_count均置为0，表示该行（列，宫）的候选数number剩余0个
bs_r(cb)的first均置为0，表示该行（列，宫）每格都不含候选数number  
for n = 1 to 9  
&emsp;&emsp;if n != number && pos格剩余候选数n  
&emsp;&emsp;&emsp;&emsp;update_rcbcount_bsrcb_delete(pos, n);  

---

### Algo 0.5 &emsp; void autoAddNumber (pos, number)

> pos格删去候选数number后，搜索pos关联的格看是否有可以填数的格

if pos格未填数  
&emsp;&emsp;pos格是否只剩一个候选数&emsp;(Algo 1.1) NakedSingle(pos);  
&emsp;&emsp;pos格被删去候选数number后，该行列宫是否只剩某格剩余某候选数&emsp;(Algo 0.0) HiddenSingle_unit(pos, number);

---

### Algo 0.6 &emsp; bool deleteCandidate (pos, number)

> 尝试删除pos格的候选数number，不含有number则什么也不做  
> 返回是否的确删除了这个候选数  
> 只是删除候选数，不自动填数版本

if pos格含有候选数  
&emsp;&emsp;将pos格的candidate的number候选数置为0  
&emsp;&emsp;更新x_count和bs_x (Algo 0.3) update_rcbcount_bsrcb_delete(pos, number);  
&emsp;&emsp;--unit[pos].left;  
&emsp;&emsp;return ture  
default:return false;

---

### Algo 0.7 &emsp; bool deleteCandidate2 (pos, number)

> 尝试删除pos格的候选数number，不含有number则什么也不做  
> 返回是否的确删除了这个候选数  
> 删除候选数，并自动填数版本

if pos格含有候选数  
&emsp;&emsp;将pos格的candidate的number候选数置为0  
&emsp;&emsp;更新x_count和bs_x (Algo 0.3) update_rcbcount_bsrcb_delete(pos, number);  
&emsp;&emsp;--unit[pos].left;  
&emsp;&emsp;尝试填数 (Algo 0.5) autoAddNumber(pos, number);  
&emsp;&emsp;return ture  
default:return false;

---

### Algo 0.8 &emsp; void resetRelatedBlock (pos)

> 将related[]数组更新为与pos关联格（即同行，列或宫），有20格
