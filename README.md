# Neutral-subpopulations-in-two-layer-coupled-network-enhance-the-cooperation-rate.

// Prisoners Dilemma game on a small-world graph constructed from a square lattice
// Some players are blocked to give their strategy (other players cannot adopt their strategy)

#define  _CRT_SECURE_NO_WARNINGS

// standard include
#include <iostream>
#include <fstream>
#include <cstdlib>
#include <cstdio>
#include <cmath>
#include <ctime>
#include <vector>
#include <algorithm>
#include <sstream>
#include <iomanip>
#include <system_error>  // 用于获取系统错误信息
#include <windows.h>     // 用于获取Windows系统错误消息


using namespace std;

// define priority classes
#define NORMAL_PRIORITY_CLASS       0x00000020
#define IDLE_PRIORITY_CLASS         0x00000040
#define HIGH_PRIORITY_CLASS         0x00000080
#define REALTIME_PRIORITY_CLASS     0x00000100

// define parameters
#define L           100     /* lattice size                   */
#define SIZE        (L*L)    /* number of sites                */
#define MC_STEPS    100000   /* run-time in MCS     */
#define OUT_STEPS    5000   /* Last 5000 steps  */
//#define r               /* temptation to defect */
#define K           0.1      /* temperature */
#define Q           0      /* Q portion of links are rewired */
#define NAMEOUT     "K4b075r5Q2"
#define RANDOMIZE   3145215
#define NEIMUN      8
#define GROUP_SIZE  4 //每组的人数
#define GROUP_NUM   (SIZE/GROUP_SIZE)  //一共能分多少组
double b;
double para_a = 0.15;  //上层对于下层的影响参数
double payoff_matrix[2][2] = { {1, 0},
							   {b, 0} };
int changetype_down[4] = { 0,0,0,0 };//0CC,1CD,2DC,3DD,记录上一轮C这一轮还是C的人数
int changetype_up[4] = { 0,0,0,0 };//0CC,1CD,2DC,3DD,记录上一轮C这一轮还是C的人数

#define update_payoff_matrix(b) payoff_matrix[1][0] = b;

typedef int       tomb1[SIZE];
typedef long int  tomb3[SIZE][NEIMUN];
typedef double    tomb4[SIZE];

tomb1 age_up;  //用不上的数组
tomb1 age_down;  //用不上的数组
int age_T = 0;  //用不上的数组


tomb1 player_s_up;   //上层玩家的策略
tomb1 player_s_down;  //下层玩家的策略
tomb3 player_n;  //记录玩家的邻居序号

double p[SIZE];  //采用RL的一层各个结点的合作概率
double bt = 1;  //β
double A = 0.5;  //期望

int cnt_s_up[2];  //cnt_s_up[0]记录上层玩家中选择合作的人数，cnt_s_up[1]记录上层玩家中选择背叛的人数
int cnt_s_down[2];  //cnt_s_down[0]记录上层玩家中选择合作的人数，cnt_s_down[1]记录上层玩家中选择背叛的人数
int group[GROUP_NUM][GROUP_SIZE];  //group[i][j]这个数组记录第i组的四个玩家的序号
int player_group[SIZE];  //记录玩家x是哪一组的
int tag_up[SIZE];//记录标签
int tag_down[SIZE];
int same_down[SIZE];//记录周围标签相同的玩家的个数
int same_up[SIZE];
double pay_up[SIZE];//记录收益
double pay_down[SIZE];
double fit_up[SIZE];//记录适应度
double fit_down[SIZE];
double all_pay_up = 0;//记录上层玩家的总收益
double all_pay_down = 0;//记录下层玩家的总收益
double neutral_payoff = 0.5;

//ofstream outfile1;



//以下是随机数产生模块，不用管它,直接用就行，用randf()可以直接产生0-1满足均匀分布的随机数，randi(x),产生0---x-1的随机整数
/*************************** RNG procedures ****************************************/
#define NN 624
#define MM 397
#define MATRIX_A 0x9908b0df   /* constant vector a */
#define UPPER_MASK 0x80000000 /* most significant w-r bits */
#define LOWER_MASK 0x7fffffff /* least significant r bits */
#define TEMPERING_MASK_B 0x9d2c5680
#define TEMPERING_MASK_C 0xefc60000
#define TEMPERING_SHIFT_U(y)  (y >> 11)
#define TEMPERING_SHIFT_S(y)  (y << 7)
#define TEMPERING_SHIFT_T(y)  (y << 15)
#define TEMPERING_SHIFT_L(y)  (y >> 18)

static unsigned long mt[NN]; /* the array for the state vector  */
static int mti = NN + 1; /* mti==NN+1 means mt[NN] is not initialized */
void sgenrand(unsigned long seed)
{
	int i;
	for (i = 0; i < NN; i++) {
		mt[i] = seed & 0xffff0000; seed = 69069 * seed + 1;
		mt[i] |= (seed & 0xffff0000) >> 16; seed = 69069 * seed + 1;
	}
	mti = NN;
}
void lsgenrand(unsigned long seed_array[])
{
	int i; for (i = 0; i < NN; i++) mt[i] = seed_array[i]; mti = NN;
}
double genrand()
{
	unsigned long y;
	static unsigned long mag01[2] = { 0x0, MATRIX_A };
	if (mti >= NN)
	{
		int kk;
		if (mti == NN + 1) sgenrand(4357);
		for (kk = 0; kk < NN - MM; kk++) {
			y = (mt[kk] & UPPER_MASK) | (mt[kk + 1] & LOWER_MASK);
			mt[kk] = mt[kk + MM] ^ (y >> 1) ^ mag01[y & 0x1];
		}
		for (; kk < NN - 1; kk++) {
			y = (mt[kk] & UPPER_MASK) | (mt[kk + 1] & LOWER_MASK);
			mt[kk] = mt[kk + (MM - NN)] ^ (y >> 1) ^ mag01[y & 0x1];
		}
		y = (mt[NN - 1] & UPPER_MASK) | (mt[0] & LOWER_MASK);
		mt[NN - 1] = mt[MM - 1] ^ (y >> 1) ^ mag01[y & 0x1];
		mti = 0;
	}
	y = mt[mti++]; y ^= TEMPERING_SHIFT_U(y); y ^= TEMPERING_SHIFT_S(y) & TEMPERING_MASK_B;
	y ^= TEMPERING_SHIFT_T(y) & TEMPERING_MASK_C; y ^= TEMPERING_SHIFT_L(y);
	return y;
}

double randf() { return ((double)genrand() * 2.3283064370807974e-10); }
long randi(unsigned long LIM) { return((unsigned long)genrand() % LIM); }

bool create_directories_win(const std::string& path) // 专用Windows路径创建函数
{
	std::string current_path;

	// 替换路径中的正斜杠为反斜杠（Windows原生风格）
	std::string win_path = path;
	std::replace(win_path.begin(), win_path.end(), '/', '\\');

	// 逐级创建目录
	for (size_t i = 0; i < win_path.length(); ++i) {
		current_path += win_path[i];
		if (win_path[i] == '\\' || i == win_path.length() - 1) {
			// 跳过盘符根目录（如C:\）
			if (current_path.size() == 3 && current_path[1] == ':') continue;

			// 创建当前层目录
			if (!CreateDirectoryA(current_path.c_str(), NULL)) {
				DWORD err = GetLastError();
				if (err != ERROR_ALREADY_EXISTS) {
					return false;
				}
			}
		}
	}
	return true;
}


/********************** END of RNG ************************************/

//up对应BM
//down对应费米
void initial(void)  //初始化策略和合作概率
{
	cnt_s_up[0] = cnt_s_up[1] = 0;  //上下层的合作背叛人数初始化为0
	cnt_s_down[0] = cnt_s_down[1] = 0;
	all_pay_up = 0;
	all_pay_down = 0;
	for (int i = 0; i < SIZE; i++)  //遍历每一个玩家
	{
		int j = randi(3);//随机生成0/1/2
		tag_down[i] = j; //初始化下层标签
		tag_up[i] = j; //初始化上层标签
		player_s_up[i] = randi(2);  //初始化上层玩家的策略
		player_s_down[i] = randi(2);  //初始化下层玩家的策略
		cnt_s_up[player_s_up[i]]++;  //数组下标记数法分别统计上下层的合作背叛人数
		cnt_s_down[player_s_down[i]]++;
		pay_up[i] = 0;
		pay_down[i] = 0;
		fit_up[i] = 0;
		fit_down[i] = 0;
		p[i] = 0.5;  //初始概率初始化为0.5
	}
}

void spical_initial(void)  //初始化策略和合作概率
{

	all_pay_up = 0;
	all_pay_down = 0;
	cnt_s_up[0] = SIZE / 2;
	cnt_s_down[0] = SIZE / 2;
	cnt_s_up[1] = SIZE / 2;
	cnt_s_down[1] = SIZE / 2;

	for (int i = 0; i < SIZE; i++)  //遍历每一个玩家
	{
		pay_up[i] = 0;
		pay_down[i] = 0;
		fit_up[i] = 0;
		fit_down[i] = 0;
		p[i] = 0.5;  //初始概率初始化为0.5
	}

	for (int i = 0; i < L / 2; i++)  //遍历每一个玩家
	{
		for (int j = 0; j < L / 2; j++)
		{
			player_s_up[i * L + j] = 1;  //初始化上层玩家的策略
			player_s_down[i * L + j] = 1;  //初始化下层玩家的策略
			tag_down[i * L + j] = 1; //初始化下层标签
			tag_up[i * L + j] = 1; //初始化上层标签
		}
	}

	for (int i = L / 2; i < L; i++)  //遍历每一个玩家
	{
		for (int j = 0; j < L / 2; j++)
		{
			player_s_up[i * L + j] = 1;  //初始化上层玩家的策略
			player_s_down[i * L + j] = 1;  //初始化下层玩家的策略
			tag_down[i * L + j] = 0; //初始化下层标签
			tag_up[i * L + j] = 0; //初始化上层标签
		}
	}

	for (int i = L / 2; i < L; i++)  //遍历每一个玩家
	{
		for (int j = L / 2; j < L; j++)
		{
			player_s_up[i * L + j] = 0;  //初始化上层玩家的策略
			player_s_down[i * L + j] = 0;  //初始化下层玩家的策略
			tag_down[i * L + j] = 1; //初始化下层标签
			tag_up[i * L + j] = 1; //初始化上层标签
		}
	}

	for (int i = 0; i < L / 2; i++)  //遍历每一个玩家
	{
		for (int j = L / 2; j < L; j++)
		{
			player_s_up[i * L + j] = 0;  //初始化上层玩家的策略
			player_s_down[i * L + j] = 0;  //初始化下层玩家的策略
			tag_down[i * L + j] = 0; //初始化下层标签
			tag_up[i * L + j] = 0; //初始化上层标签
		}
	}
}


//找到所有玩家的邻居序号
void prodgraph(void)
{
	int x;
	int i, j;
	for (i = 0; i < L; i++)  //第i行
	{
		for (j = 0; j < L; j++)  //第j列
		{
			x = i * L + j;//（从0开始）在网格内从左往右，从上往下的第几个
			player_n[x][0] = i * L + ((j - 1 + L) % L);   //左邻居的序号
			player_n[x][1] = ((i - 1 + L) % L) * L + j;	  //上邻居的序号
			player_n[x][2] = ((i + 1) % L) * L + j;  	  //下邻居的序号
			player_n[x][3] = i * L + ((j + 1) % L);	      //右邻居的序号

			//用下面这些
			//player_n[x][4] = ((i - 1 + L) % L) * L + ((j - 1 + L) % L);
			//player_n[x][5] = ((i + 1) % L) * L + ((j - 1 + L) % L);
			//player_n[x][6] = ((i - 1 + L) % L) * L + ((j + 1) % L);
			//player_n[x][7] = ((i + 1) % L) * L + ((j + 1) % L);
		}
	}
}

void payoff_up(int x)
{//上层更新收益
	double pay = 0;
	if (tag_up[x] == 0) //如果这个上层玩家标签为0
	{
		for (int i = 0; i < 4; i++) //在他的四个邻居里
		{
			if (tag_up[player_n[x][i]] == 0)  //找到标签也是0的玩家进行交互
			{
				pay += payoff_matrix[player_s_up[x]][player_s_up[player_n[x][i]]];
				same_up[x]++;
			}
			else
			{
				pay = pay + neutral_payoff;
			}
		}
		pay_up[x] = pay;
	}
	if (tag_up[x] == 1)
	{
		for (int i = 0; i < 4; i++)
		{
			if (tag_up[player_n[x][i]] == 1)
			{
				pay += payoff_matrix[player_s_up[x]][player_s_up[player_n[x][i]]];
				same_up[x]++;
			}
			else
			{
				pay = pay + neutral_payoff;
			}
		}
		pay_up[x] = pay;
	}
	if (tag_up[x] == 2)
	{
		for (int i = 0; i < 4; i++)
		{
			if (tag_up[player_n[x][i]] == 2)
			{
				pay += payoff_matrix[player_s_up[x]][player_s_up[player_n[x][i]]];
				same_up[x]++;
			}
			else
			{
				pay = pay + neutral_payoff;
			}
		}
		pay_up[x] = pay;
	}
}

void payoff_down(int x)
{//下层更新收益
	double pay = 0;
	if (tag_down[x] == 0)
	{
		for (int i = 0; i < 4; i++)
		{
			if (tag_down[player_n[x][i]] == 0)
			{
				pay += payoff_matrix[player_s_down[x]][player_s_down[player_n[x][i]]];
				same_down[x]++;
			}
			else
			{
				pay = pay + neutral_payoff;
			}
		}
		pay_down[x] = pay;
	}
	if (tag_down[x] == 1)
	{
		for (int i = 0; i < 4; i++)
		{
			if (tag_down[player_n[x][i]] == 1)
			{
				pay += payoff_matrix[player_s_down[x]][player_s_down[player_n[x][i]]];
				same_down[x]++;
			}
			else
			{
				pay = pay + neutral_payoff;
			}
		}
		pay_down[x] = pay;
	}
	if (tag_down[x] == 2)
	{
		for (int i = 0; i < 4; i++)
		{
			if (tag_down[player_n[x][i]] == 1)
			{
				pay += payoff_matrix[player_s_down[x]][player_s_down[player_n[x][i]]];
				same_down[x]++;
			}
			else
			{
				pay = pay + neutral_payoff;
			}
		}
		pay_down[x] = pay;
	}
}

void fitness_up(int x)  //上层的适应度，返回收益的加权平均数
{
	fit_up[x] = para_a * pay_down[x] / 4 + (1 - para_a) * pay_up[x] / 4;
}

double stimu(int x)
{
	double s, r;
	r = fit_up[x];
	s = tanh(bt * (r - A));
	return s;
}

//计算x更新策略的概率
void calcul(int x)
{
	int i;
	double s;
	i = x;
	s = stimu(i);
	if ((s >= 0) && player_s_up[i] == 0)
	{
		p[i] = p[i] + (1 - p[i]) * s;
	}
	else if ((s < 0) && player_s_up[i] == 0)
	{
		p[i] = p[i] + p[i] * s;
	}
	else if ((s >= 0) && player_s_up[i] == 1)
	{
		p[i] = p[i] - p[i] * s;
	}
	else
	{
		p[i] = p[i] - (1 - p[i]) * s;
	}
}

void fitness_down(int x)    //计算下层的适应度,只有标签一致才进行影响
{
	double r, t;
	double pay = 0;
	int same = 0;
	for (int i = 0; i < 4; i++) //找四个邻居里的非孤立节点
	{
		if (same_up[player_n[x][i]] != 0)
		{
			pay = pay + pay_up[player_n[x][i]];
			same++;
		}

	}
	if (same_up[x] != 0) //找自己是不是孤立节点
	{
		pay = pay + pay_up[x] / 4;
		same++;
	}
	if (same == 0) //如果对应的下层的这个是一个孤立节点，那么适应度就是自身的收益
	{
		r = pay_down[x] / 4;
	}
	else //不然适应度就是上下收益的加权平均数
	{
		t = pay / same; //上层的平均收益
		r = para_a * t + (1 - para_a) * pay_down[x] / 4;
	}
	all_pay_down = all_pay_down + r;
	fit_down[x] = r;
}

void update_up(int x)  //上层BM进行策略更新
{
	calcul(x);
	if (randf() <= p[x]) //策略更新
	{
		if (player_s_up[x] == 0)
		{//C->C
			changetype_up[0]++;
		}
		else
		{//D->C
			changetype_up[2]++;
		}
		cnt_s_up[player_s_up[x]]--;
		player_s_up[x] = 0;
		cnt_s_up[player_s_up[x]]++;
	}
	else
	{
		if (player_s_up[x] == 0)
		{//C->D
			changetype_up[1]++;
		}
		else
		{//D->D
			changetype_up[3]++;
		}
		cnt_s_up[player_s_up[x]]--;
		player_s_up[x] = 1;
		cnt_s_up[player_s_up[x]]++;
	}
	int y;
	double prob_down = 0;
	y = player_n[x][int(randi(4))];
	if (tag_up[x] != tag_up[y])
	{
		prob_down = 1 / (1 + exp((fit_up[x] - fit_up[y]) / K));
		if (randf() < prob_down)
			tag_up[x] = tag_up[y]; //标签更新
	}
	return;
}

void update_down(int x)  //下层费米进行策略更新
{
	int y;
	double prob_down = 0;	// Probability of updating, initial not update
	y = player_n[x][int(randi(4))];
	if (player_s_down[x] != player_s_down[y])
	{//如果和随机选择的邻居的策略是不一样的，则考虑是否进行模仿
		prob_down = 1 / (1 + exp((pay_down[x] - pay_down[y]) / K));
		if (randf() < prob_down)//策略发生变化
		{
			if (player_s_down[x] == 0)
			{//C->D
				changetype_down[1]++;
			}
			else
			{//D->C
				changetype_down[2]++;
			}
			cnt_s_down[player_s_down[x]]--;	// Old strategy
			player_s_down[x] = player_s_down[y];
			cnt_s_down[player_s_down[x]]++;	// New strategy
			tag_down[x] = tag_down[y];  //学习标签
		}
		else//策略没变
		{
			if (player_s_down[x] == 0)
			{//C->C
				changetype_down[0]++;
			}
			else
			{//D->D
				changetype_down[3]++;
			}
		}
	}
	else//如果和随机选择的邻居的策略是一样的
	{
		if (player_s_down[x] == 0)
		{//C->C
			changetype_down[0]++;
		}
		else
		{//D->D
			changetype_down[3]++;
		}
	}
}

void game(void) //进行博弈
{
	//生成随机数
	int n = SIZE;
	vector<int> nums(n);
	for (int i = 0; i < n; ++i)
	{
		nums[i] = i;
	}
	srand(time(0));
	for (int i = n - 1; i > 0; --i)
	{
		int j = rand() % (i + 1);
		swap(nums[i], nums[j]);
	}

	for (int i = 0; i < SIZE; i++)
	{
		//int x = i;
		int x = nums[i];  //随机选择一个位置
		payoff_up(x);
		payoff_down(x);
		fitness_up(x);
		//fitness_down(x);
		update_up(x);  //更新上层
		update_down(x);  //更新下层
	}
}

void draw_up(int step)
{
	if (step == 0 || step == 1 || step == 10 || step == 100 || step == 1000 || step == 10000 || step == MC_STEPS - 1)
	{
		// 定义目标文件夹路径
		const string target_dir = "../数据/BM斑图/";
		if (!create_directories_win(target_dir)) {
			DWORD error = GetLastError();
			std::cerr << "目录创建失败 (错误码: 0x" << std::hex << error << ")" << std::endl;
			return;
		}
		ostringstream filename;
		filename << target_dir << "第" << step << "步的斑图_BM_a=" << para_a << "_b=" << b << ".txt";

		// 打开文件并写入数据
		std::ofstream file(filename.str());
		if (!file.is_open()) {
			std::cerr << "错误：无法创建文件 " << filename.str() << std::endl;
			return;
		}

		// 写入斑图数据
		for (int i = 0; i < L; i++)
		{
			for (int j = 0; j < L; j++)
			{
				int idx = i + j * L;  // 计算索引
				int tag = tag_up[idx];
				int player = player_s_up[idx];

				// 六种组合状态编码
				if (tag == 0 && player == 0)       file << 0;
				else if (tag == 0 && player == 1)  file << 1;
				else if (tag == 1 && player == 0)  file << 2;
				else if (tag == 1 && player == 1)  file << 3;
				else if (tag == 2 && player == 0)  file << 4;
				else if (tag == 2 && player == 1)  file << 5;
				if (j != L - 1)  // 非行末添加空格
					file << " ";
			}
			file << "\n";  // 行结束换行
		}
		file.close();
	}
}

void draw_down(int step)//在耦合强度a和社会困境强度b的情况下，第step步的斑图
{//std::ostringstream 是 C++ 中专门用于构建格式化字符串的流类
	if (step == 0 || step == 1 || step == 10 || step == 100 || step == 1000 || step == 10000 || step == MC_STEPS - 1)
	{
		const string target_dir = "../数据/费米斑图/";

		if (!create_directories_win(target_dir)) {
			DWORD error = GetLastError();
			std::cerr << "目录创建失败 (错误码: 0x" << std::hex << error << ")" << std::endl;
			return;
		}

		ostringstream filename;
		filename << target_dir << "第" << step << "步的斑图_费米" << "_a=" << para_a << "_b=" << b << ".txt";
		ofstream file(filename.str(), ios::app);
		for (int i = 0; i < L; i++)
		{
			for (int j = 0; j < L; j++)
			{
				int idx = i + j * L;  // 计算索引
				int tag = tag_down[idx];
				int player = player_s_down[idx];

				// 六种组合状态编码
				if (tag == 0 && player == 0)       file << 0;
				else if (tag == 0 && player == 1)  file << 1;
				else if (tag == 1 && player == 0)  file << 2;
				else if (tag == 1 && player == 1)  file << 3;
				else if (tag == 2 && player == 0)  file << 4;
				else if (tag == 2 && player == 1)  file << 5;
				if (j != L - 1)  // 非行末添加空格
					file << " ";
			}
			file << "\n";  // 行结束换行
		}
		file.close(); // 手动关闭
	}
}

void C1C2C3D1D2D3_up(int step)
{
	const string target_dir = "../数据/BM的C1C2C3D1D2D3的比例/";

	if (!create_directories_win(target_dir)) {
		DWORD error = GetLastError();
		std::cerr << "目录创建失败 (错误码: 0x" << std::hex << error << ")" << std::endl;
		return;
	}

	ostringstream filename;
	filename << target_dir << "c1c2c3d1d2d3的比例" << "_a=" << para_a << "_b=" << b << ".txt";

	ofstream file(filename.str(), ios::app);

	// 初始化六种状态的计数器
	int C1 = 0, C2 = 0, C3 = 0, D1 = 0, D2 = 0, D3 = 0;

	for (int i = 0; i < SIZE; i++)
	{
		if (tag_up[i] == 0 && player_s_up[i] == 0) C1++;
		else if (tag_up[i] == 0 && player_s_up[i] == 1) D1++;
		else if (tag_up[i] == 1 && player_s_up[i] == 0) C2++;
		else if (tag_up[i] == 1 && player_s_up[i] == 1) D2++;
		else if (tag_up[i] == 2 && player_s_up[i] == 0) C3++;
		else if (tag_up[i] == 2 && player_s_up[i] == 1) D3++;
	}

	// 计算比例
	double total = static_cast<double>(SIZE);
	double C1_ratio = static_cast<double>(C1) / total;
	double C2_ratio = static_cast<double>(C2) / total;
	double C3_ratio = static_cast<double>(C3) / total;
	double D1_ratio = static_cast<double>(D1) / total;
	double D2_ratio = static_cast<double>(D2) / total;
	double D3_ratio = static_cast<double>(D3) / total;

	// 写入文件：步数和六种比例
	file << step << " "
		<< C1_ratio << " " << C2_ratio << " " << C3_ratio << " "
		<< D1_ratio << " " << D2_ratio << " " << D3_ratio << "\n";

	if (step == MC_STEPS - 1) {
		file.close();
	}
}

void CtoC_CtoD_DtoC_DtoD_down(int step) {
	// 目标目录路径
	const string target_dir = "../数据/BM的CCCDDCDD/";

	if (!create_directories_win(target_dir)) {
		DWORD error = GetLastError();
		std::cerr << "目录创建失败 (错误码: 0x" << std::hex << error << ")" << std::endl;
		return;
	}

	// 构建文件名
	ostringstream filename;
	filename << target_dir << "CCCDDCDD的比例随步数变化_费米_"
		<< "a=" << para_a << "_b=" << b << ".txt";

	// 打开文件（追加模式）
	ofstream file(filename.str(), std::ios::app);

	// 写入数据：步数 + 四种状态转换比例
	file << step << " "
		<< changetype_down[0] / static_cast<double>(SIZE) << " "
		<< changetype_down[1] / static_cast<double>(SIZE) << " "
		<< changetype_down[2] / static_cast<double>(SIZE) << " "
		<< changetype_down[3] / static_cast<double>(SIZE) << "\n";

	if (step == MC_STEPS - 1) {
		file.close();
	}
}

void CtoC_CtoD_DtoC_DtoD_up(int step) {
	// 目标目录路径
	const string target_dir = "../数据/BM的CCCDDCDD/";

	if (!create_directories_win(target_dir)) {
		DWORD error = GetLastError();
		std::cerr << "目录创建失败 (错误码: 0x" << std::hex << error << ")" << std::endl;
		return;
	}

	// 构建文件名
	ostringstream filename;
	filename << target_dir << "CCCDDCDD的比例随步数变化_BM_"
		<< "a=" << para_a << "_b=" << b << ".txt";

	// 打开文件（追加模式）
	ofstream file(filename.str(), std::ios::app);

	// 写入数据：步数 + 四种状态转换比例
	file << step << " "
		<< changetype_up[0] / static_cast<double>(SIZE) << " "
		<< changetype_up[1] / static_cast<double>(SIZE) << " "
		<< changetype_up[2] / static_cast<double>(SIZE) << " "
		<< changetype_up[3] / static_cast<double>(SIZE) << "\n";

	if (step == MC_STEPS - 1) {
		file.close();
	}
}



ofstream create_timestamped_file(const string& base_filename)
{
	// 获取当前时间
	time_t now = std::time(nullptr);
	tm* local_time = std::localtime(&now);

	// 将时间格式化为字符串
	char time_buffer[20];
	strftime(time_buffer, sizeof(time_buffer), "%Y%m%d_%H%M%S", local_time);

	// 构造文件名
	ostringstream filename_stream;
	filename_stream << time_buffer << "_" << base_filename;
	string filename = filename_stream.str();

	// 打开文件并返回文件流
	ofstream outfile;
	outfile.open(filename);
	return outfile;
}
// the main program
int main()
{
	int steps;
	double fc_up, fc_down, last_sum_up, last_sum_down, avg_fc_up, avg_fc_down;
	double last_pay_up;//上层最后五千步的收益和
	double last_pay_down;//下层最后五千步的收益和
	double average_all_pay_up;//上层收益平均值
	double average_all_pay_down;//下层收益平均值
	double cc, cd, dc, dd;
	double CC, CD, DC, DD;

	ofstream outfile2 = create_timestamped_file("average.txt");
	ofstream outfile3 = create_timestamped_file("average_payoff.txt");
	ofstream outfile4 = create_timestamped_file("average_cccddcdd.txt");
	ofstream outfile5 = create_timestamped_file("CCCDDCDD.txt");
	ofstream outfile6 = create_timestamped_file("beta_fc.txt");
	// initialize the random number generation
	sgenrand(RANDOMIZE);
	prodgraph();//找到所有玩家的邻居的序号并存储在数组里
	//sectionalization();
	//para_a = 0.5;
	for (para_a = 0; para_a <= 1.01; para_a += 0.1)
	//for (b = 1.00; b <= 2.01; b += 0.1)
	{
		//for (para_a = 0; para_a <= 1.01; para_a += 0.01)
		for (b = 1.00; b <= 2.01; b += 0.1)
		{
			avg_fc_up = 0;
			last_sum_up = 0;
			avg_fc_down = 0;
			last_sum_down = 0;
			last_pay_up = 0;
			last_pay_down = 0;
			cc = cd = dc = dd = 0;
			CC = CD = DC = DD = 0;
			update_payoff_matrix(b);
			initial();

			const string target_dir = "../数据/上下层合作率随步数变化/";
			if (!create_directories_win(target_dir))
			{
				DWORD error = GetLastError();
				std::cerr << "目录创建失败 (错误码: 0x" << std::hex << error << ")" << std::endl;
				return 0;
			}
			ostringstream filename_stream;
			filename_stream << target_dir << "上下层合作率随步数变化_" << "_b=" << b << "_a=" << para_a << ".txt";
			// 使用 C++ 文件流打开文件
			ofstream outfile1(filename_stream.str());

			for (steps = 0; steps < MC_STEPS; steps++)
			{
				memset(same_up, 0, sizeof(same_up));
				memset(same_down, 0, sizeof(same_down));
				changetype_down[0] = changetype_down[1] = changetype_down[2] = changetype_down[3] = 0;
				changetype_up[0] = changetype_up[1] = changetype_up[2] = changetype_up[3] = 0;
				game();
				fc_up = (double)cnt_s_up[0] / SIZE;	// OLD: tongji()
				fc_down = (double)cnt_s_down[0] / SIZE;

				average_all_pay_down = all_pay_down / SIZE;
				average_all_pay_up = all_pay_up / SIZE;

				all_pay_down = 0;
				all_pay_up = 0;

				outfile1 << steps << "\t" << fc_up << "\t" << fc_down << "\n";

				if (steps < 10000)
				{
					CC = CC + changetype_up[0] / static_cast<double>(SIZE);
					CD = CD + changetype_up[1] / static_cast<double>(SIZE);
					DC = DC + changetype_up[2] / static_cast<double>(SIZE);
					DD = DD + changetype_up[3] / static_cast<double>(SIZE);
				}

				if (steps > MC_STEPS - OUT_STEPS - 1)
				{
					cc = cc + changetype_up[0] / static_cast<double>(SIZE);
					cd = cd + changetype_up[1] / static_cast<double>(SIZE);
					dc = dc + changetype_up[2] / static_cast<double>(SIZE);
					dd = dd + changetype_up[3] / static_cast<double>(SIZE);

					last_sum_up += fc_up;
					last_sum_down += fc_down;

					last_pay_down = last_pay_down + average_all_pay_down;
					last_pay_up = last_pay_up + average_all_pay_up;
				}

				draw_up(steps);
				draw_down(steps);
				C1C2C3D1D2D3_up(steps);
				CtoC_CtoD_DtoC_DtoD_up(steps);
			}

			avg_fc_up = (double)last_sum_up / OUT_STEPS;
			avg_fc_down = (double)last_sum_down / OUT_STEPS;

			last_pay_down = last_pay_down / OUT_STEPS;
			last_pay_up = last_pay_up / OUT_STEPS;

			cc = cc / OUT_STEPS;
			cd = cd / OUT_STEPS;
			dc = dc / OUT_STEPS;
			dd = dd / OUT_STEPS;

			CC = CC / 10000;
			CD = CD / 10000;
			DC = DC / 10000;
			DD = DD / 10000;

			cout << b << "\t" << para_a << "\t" << avg_fc_up << '\t' << avg_fc_down << endl;
			cout << b << "\t" << para_a << "\t" << last_pay_down << '\t' << last_pay_up << endl;

			outfile2 << b << "\t" << para_a << "\t" << avg_fc_up << '\t' << avg_fc_down << endl;
			outfile3 << b << "\t" << para_a << "\t" << last_pay_up << '\t' << last_pay_down << endl;
			outfile4 << b << "\t" << para_a << "\t" << cc << "\t" << cd << "\t" << dc << "\t" << dd << endl;
			outfile5 << b << "\t" << para_a << "\t" << CC << "\t" << CD << "\t" << DC << "\t" << DD << endl;
			outfile6 << b << "\t" << bt << avg_fc_up << '\t' << avg_fc_down << '\t' << avg_fc_down << bt << endl;
			outfile1.close(); // 手动关闭
		}
	}

	outfile2.close();
	outfile3.close();
	outfile4.close();
	outfile5.close();
	outfile6.close();
	return 0;
}

