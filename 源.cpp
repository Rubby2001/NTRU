#include<vector>
#include <random>
#include <chrono>
#include <set>
#include<iostream>
#include <cmath>
#include<bitset>
#include<string>
#include<sstream>
using namespace std;
char base64[] = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz+=";
class NTRU {
public:
    // 构造函数，使用默认参数集生成公共参数
    NTRU();
    // 构造函数，使用给定参数集生成公共参数
    NTRU(int N, int p, int q, int Df, int Dg, int Dr);
    // 生成公钥和私钥
    void generate_keys();
    vector<int> get_public_key();
    pair<vector<int>, vector<int>> get_private_key();
    // 加密
    vector<int> encrypt(const vector<int>& plaintext, const vector<int>& public_key);
    string encrypt(const string& plaintext, string public_key);
    // 解密
    vector<int> decrypt(const vector<int>& ciphertext, const pair<vector<int>, vector<int>>& private_key);
    string decrypt(string result, string private_key);

private:
    int N;   //多项式系数
    int p;   //系数模量
    int q;   //算数模量
    int Df;     //加密过程多项式的特征参数
    int Dg;
    int Dr;
    vector<int> f;   //私钥
    vector<int> Fp;
    vector<int> Fq;
    vector<int> g;
    vector<int> h;  //公钥 
    vector<int> r;  //加密过程中用于置乱明文的小多项式

    // 一些辅助函数，如多项式生成和多项式运算函数
    vector<int> generate_poly(int N, int a, int b);  //随机生成属于环R（a，b）的N-1次多项式
    void rotateLeft(vector<int>& v, int k);     //多项式循环左移k位，用于求模逆算法中
    vector<int> convolution(vector<int> A, vector<int> B);  //多项式卷积运算

    vector<int> add_polynomials(const vector<int>& a, const vector<int>& b);      //多项式加法 
    vector<int> subtract_polynomials(const vector<int>& a, const vector<int>& b);//多项式减法
    void polynomial_division(vector<int> a, vector<int> b, vector<int>& q, vector<int>& r);    //多项式除法

    vector<int> inverse_qin_p(const vector<int>& a);  //秦九韶大衍求一术求多项式关于p的模逆，通常p=3
    vector<int> inverse_qin_q(const vector<int>& a);  //秦九韶大衍求一术求多项式关于q的模逆，通常q为2的指数幂

    void mod_p(vector<int>& a);  //多项式模p，系数调整在{-1，0，1}中
    void mod_2(vector<int>& a);  //多项式模2，系数调整在{0，1}中
    void mod_q(vector<int>& a);   //多项式模q，系数调整在 (-q/2，q/2)中
    void remove_zeros(vector<int>& a); //去掉多项式末尾的0

    vector<vector<int>> convert(const string& str);      //转换函数，将string明文转换为三进制，分为长度为N的组。
    string reverse_convert(vector<vector<int>> split);    //逆转换函数，将分组长度为N的数组，转换为string类型
};

NTRU::NTRU() {
    this->N = 107;
    this->p = 3;
    this->q = 64;
    this->Df = 15;
    this->Dg = 12;
    this->Dr = 5;
    f.resize(107);
    g.resize(107);
    Fp.resize(107);
    Fq.resize(107);
    h.resize(107);
    r.resize(107);
}

NTRU::NTRU(int N, int p, int q, int Df, int Dg, int Dr) {
    this->N = N;
    this->p = p;
    this->q = q;
    this->Df = Df;
    this->Dg = Dg;
    this->Dr = Dr;
    f.resize(N);
    g.resize(N);
    Fp.resize(N);
    Fq.resize(N);
    h.resize(N);
    r.resize(N);
}

vector<int> NTRU::generate_poly(int N, int a, int b) {
    vector<int> coeffs(N, 0);
    set<int> chosen_coeffs;
    random_device rd;
    mt19937 gen(rd());
    uniform_int_distribution<int> dist(0, N - 1);
    while (chosen_coeffs.size() < a + b) {
        int idx = dist(gen);
        if (chosen_coeffs.count(idx) == 0) {
            int sign = (chosen_coeffs.size() < a) ? 1 : -1;
            coeffs[idx] = sign;
            chosen_coeffs.insert(idx);
        }
    }
    return coeffs;
}

vector<int> NTRU::convolution(vector<int> A, vector<int> B) {
    int m = A.size();
    int n = B.size();
    vector<int> C(N, 0);
    for (int i = 0; i < m; i++) {
        for (int j = 0; j < n && i + j < N; j++) {
            C[i + j] += A[i] * B[j];
        }
        for (int j = max(0, N - i); j < n; j++) {
            C[i + j - N] += A[i] * B[j];
        }
    }
    return C;
}

void NTRU::polynomial_division(vector<int> a, vector<int> b, vector<int>& q, vector<int>& r) {
    int n = a.size() - 1;  // 多项式 a 的次数  
    int m = b.size() - 1;  // 多项式 b 的次数   

    //if (m < 0) throw std::invalid_argument("异常：除数多项式为0多项式");

    if (n < m) {       //a的次数低于b时
        q.clear();
        r = a;
        return;
    }

    q.resize(n - m + 1);   // 初始化商的系数向量 q       
    r.resize(m);           // 初始化余数的系数向量 r      

    for (int i = n - m; i >= 0; i--) {  // 从高次项到低次项逐步计算商的系数      
        q[i] = a[i + m] / b[m];         // 计算当前项的商              
        for (int j = i + m - 1, k = m - 1; k >= 0; j--, k--) {  // 用当前项的商更新余数    
            a[j] -= q[i] * b[k];        // 计算 a(x) - q(x) * b(x)     
        }
    }
    if (m == 0) r = vector<int>{ 0 };
    else {
        for (int i = 0; i < m; i++) {  // 复制余数的系数
            r[i] = a[i];
        }
    }
}


vector<int> NTRU::add_polynomials(const vector<int>& a, const vector<int>& b) {
    int m = a.size();
    int n = b.size();
    int size = max(m, n);
    vector<int> result(size, 0);
    for (int i = 0; i < m; i++) {
        result[i] = a[i];
    }
    for (int i = 0; i < n; i++) {
        result[i] = result[i] + b[i];
    }
    return result;
}


vector<int> NTRU::subtract_polynomials(const vector<int>& a, const vector<int>& b) {
    int m = a.size();
    int n = b.size();
    int size = max(m, n);
    vector<int> result(size, 0);
    for (int i = 0; i < m; i++) {
        result[i] = a[i];
    }
    for (int i = 0; i < n; i++) {
        result[i] = result[i] - b[i];
    }
    return result;
}
void NTRU::remove_zeros(vector<int>& a) {
    // 如果vector为空，直接返回
    if (a.empty()) return;
    if (a == vector<int> {0}) return;
    // 从vector的末尾开始遍历
    for (int i = a.size() - 1; i >= 1; i--) {
        // 如果当前元素是0，就删除它
        if (a[i] == 0) {
            a.pop_back();
        }
        //否则，退出循环
        else {
            break;
        }
    }

}

void NTRU::rotateLeft(vector<int>& v, int k) {
    v.resize(N);
    k %= N;
    for (int i = 0; i < k; i++) {
        v.push_back(v[i]);
    }
    v.erase(v.begin(), v.begin() + k);
}

void NTRU::mod_p(vector<int>& a) {
    for (int& i : a) {
        i %= 3;
        if (i < 0) i += 3;
        if (i > 3 / 2) i = -1;
    }
}
void NTRU::mod_2(vector<int>& a) {
    for (int& i : a) {
        i %= 2;
        if (i < 0) i += 2;
    }
}
void NTRU::mod_q(vector<int>& a) {
    for (int& i : a) {
        i %= q;
        if (i < 0) i += q;
        if (i > q / 2) i -= q;
    }
}
//秦九韶大衍求一术求多项式关于p的模逆，通常p=3
vector<int> NTRU::inverse_qin_p(const vector<int>& a) {
    //初始化状态矩阵
    vector<int> X_11 = { 1 };
    vector<int> X_12 = a;
    remove_zeros(X_12);
    vector<int> X_21 = { 0 };
    vector<int> X_22(N + 1, 0);
    X_22[0] = -1;
    X_22[N] = 1;
    vector<int> Q, R;

    //求模p的模逆多项式
    while (1) {
        if (X_22.size() > X_12.size()) {
            polynomial_division(X_22, X_12, Q, R);
            //这里模p、去头部的0，并对R进行可能的替换，是为了满足大衍求一术要求，将调整R为最小正剩余
            mod_p(Q);
            mod_p(R);
            remove_zeros(Q);
            remove_zeros(R);
            if (R == vector<int> {0}) {
                R = X_12;
                Q[0] = Q[0] - 1;
            }

            X_21 = add_polynomials(X_21, convolution(Q, X_11));
            X_22 = R;

            //将参数模p并去掉头部的0
            mod_p(X_21);
            mod_p(X_22);
            remove_zeros(X_12);
            remove_zeros(X_22);
            remove_zeros(X_11);
            remove_zeros(X_21);
        }
        else if (X_22.size() < X_12.size()) {
            polynomial_division(X_12, X_22, Q, R);
            //这里模p、去头部的0，并对R进行可能的替换，是为了满足大衍求一术要求，将调整R为最小正剩余
            mod_p(Q);
            mod_p(R);
            remove_zeros(Q);
            remove_zeros(R);
            if (R == vector<int> {0}) {
                R = X_22;
                Q[0] = Q[0] - 1;
            }

            X_11 = add_polynomials(X_11, convolution(Q, X_21));
            X_12 = R;

            //将参数模p并去掉头部的0
            mod_p(X_11);
            mod_p(X_12);
            remove_zeros(X_12);
            remove_zeros(X_22);
            remove_zeros(X_11);
            remove_zeros(X_21);
        }
        //大衍求一术求多项式模逆时，X_12参数可能为负数，所以对±1分开讨论
        if (X_12 == vector<int>{1}) {
            X_11.resize(N);
            return X_11;
        }
        else if (X_12 == vector<int>{-1}) {
            for (int& i : X_11) {
                i = -i;
            }
            X_11.resize(N);
            return X_11;
        }
    }
}

//秦九韶大衍求一术求多项式关于q的模逆，通常q为2的指数幂
vector<int> NTRU::inverse_qin_q(const vector<int>& a) {
    //初始化状态矩阵
    vector<int> X_11 = { 1 };
    vector<int> X_12 = a;
    remove_zeros(X_12);
    vector<int> X_21 = { 0 };
    vector<int> X_22(N + 1, 0);
    X_22[0] = -1;
    X_22[N] = 1;
    vector<int> Q, R;

    //求模2的模逆多项式
    while (1) {
        if (X_22.size() > X_12.size()) {
            polynomial_division(X_22, X_12, Q, R);
            //这里模2、去头部的0，并对R进行可能的替换，是为了满足大衍求一术要求，将调整R为最小正剩余
            mod_2(Q);
            mod_2(R);
            remove_zeros(Q);
            remove_zeros(R);
            if (R == vector<int> {0}) {
                R = X_12;
                Q[0] = Q[0] - 1;
            }

            X_21 = add_polynomials(X_21, convolution(Q, X_11));
            X_22 = R;
            //将参数模2并去掉头部的0
            mod_2(X_21);
            mod_2(X_22);
            remove_zeros(X_12);
            remove_zeros(X_22);
            remove_zeros(X_11);
            remove_zeros(X_21);

        }
        else if (X_22.size() < X_12.size()) {
            polynomial_division(X_12, X_22, Q, R);
            //这里模2、去头部的0，并对R进行可能的替换，是为了满足大衍求一术要求，将调整R为最小正剩余
            mod_2(Q);
            mod_2(R);
            remove_zeros(Q);
            remove_zeros(R);
            if (R == vector<int> {0}) {
                R = X_22;
                Q[0] = Q[0] - 1;
            }

            X_11 = add_polynomials(X_11, convolution(Q, X_21));
            X_12 = R;

            //将参数模2并去掉头部的0
            mod_2(X_11);
            mod_2(X_12);
            remove_zeros(X_12);
            remove_zeros(X_22);
            remove_zeros(X_11);
            remove_zeros(X_21);
        }
        //大衍求一术求多项式模逆时，X_12参数可能为负数，所以对±1分开讨论
        if (X_12 == vector<int>{1}) {
            break;
        }
        else if (X_12 == vector<int>{-1}) {
            for (int& i : X_11) {
                i = -i;
            }
            break;
        }
    }
    //牛顿迭代法，根据模2的模逆多项式X_12，求模q的模逆多项式
    vector<int> b = X_11;
    int v = 2;
    while (v < q) {
        v *= 2;
        vector<int> tmp = convolution(a, b);
        tmp = convolution(tmp, b);
        vector<int> tmp_2b(b.size(), 0);
        for (int i = 0; i < b.size(); i++) {
            tmp_2b[i] = 2 * b[i];
        }
        b = subtract_polynomials(tmp_2b, tmp);
        for (int& i : b) {
            i = i % v;
            if (i < 0) i += v;
            if (i >= v / 2) i -= v;
        }
    }
    b.resize(N);
    return b;
}
void NTRU::generate_keys() {

    vector<int> one(N, 0);
    one[0] = 1;

    while (1) {
        f = generate_poly(N, Df, Df - 1);
        remove_zeros(f);
        if (f == vector<int> {0}) continue;
        Fq = inverse_qin_q(f);
        Fp = inverse_qin_p(f);

        vector<int> tmp_q = convolution(f, Fq);
        mod_q(tmp_q);
        vector<int> tmp_p = convolution(f, Fp);
        mod_p(tmp_p);
        if (tmp_q == one and tmp_p == one) break;
    }

    g = generate_poly(N, Dg, Dg);
    h = convolution(Fq, g);
    for (int& i : h) {
        i = i * p;
    }
    mod_q(h);
}

vector<int> NTRU::get_public_key() {
    return h;
}

pair<vector<int>, vector<int>> NTRU::get_private_key() {
    return make_pair(f, Fp);
}

vector<int> NTRU::encrypt(const vector<int>& plaintext, const vector<int>& public_key) {

    r = generate_poly(N, Dr, Dr);
    vector<int> e;
    e = convolution(r, public_key);
    e = add_polynomials(e, plaintext);
    mod_q(e);
    return e;
}

vector<int> NTRU::decrypt(const vector<int>& ciphertext, const pair<vector<int>, vector<int>>& private_key) {
    vector<int> a = convolution(ciphertext, private_key.first);
    mod_q(a);
    vector<int> d = convolution(a, private_key.second);
    mod_p(d);
    d.resize(N);
    return d;
}

string NTRU::encrypt(const string& plaintext, string public_key) {
    vector<vector<int>> a = convert(plaintext);
    vector<int> h;
    istringstream ish(public_key);
    char c;
    while (ish.get(c)) {
        h.push_back(find(base64, base64 + 64, c) - base64 - 31);
    }

    vector<vector<int>> b;
    for (vector<int> i : a) {
        b.push_back(encrypt(i, h));
    }

    string result;
    ostringstream osresult;
    for (vector<int> i : b) {
        for (int j : i) {
            osresult << base64[j + 31];
        }
        osresult << " ";
    }
    result = osresult.str();
    return result;

}

string NTRU::decrypt(string result, string private_key) {

    string plaintext;
    vector<vector<int>> ciphertext;
    vector<int> part;
    istringstream iss(result);
    char word;
    while (iss.get(word)) {
        if (word == ' ') {
            ciphertext.push_back(part);
            part.clear();
            continue;
        }
        part.push_back(find(base64, base64 + 64, word) - base64 - 31);
    }




    pair<vector<int>, vector<int>> key;
    bool first = true;
    for (char i : private_key) {
        if (i == ' ') first = false;
        if (first) {
            if (i == '0') {
                key.first.push_back(0);
            }
            else if (i == '1') {
                key.first.push_back(1);
            }
            else if (i == '2') {
                key.first.push_back(-1);
            }
        }
        else {
            if (i == '0') {
                key.second.push_back(0);
            }
            else if (i == '1') {
                key.second.push_back(1);
            }
            else if (i == '2') {
                key.second.push_back(-1);
            }
        }
    }


    vector<vector<int>> c;
    for (vector<int> i : ciphertext) {
        c.push_back(decrypt(i, key));
    }


    plaintext = reverse_convert(c);
    return plaintext;
}


vector<vector<int>> NTRU::convert(const string& str) {
    string binary;
    for (char c : str) {
        // 使用std::bitset容器来获取字符的二进制表示
        bitset<8> bits(c);
        binary += bits.to_string();
    }

    vector<int> ternary;
    for (int i = 0; i < binary.size(); i++) {
        if (binary[i] == '1') {
            ternary.push_back(1);
        }
        else {
            ternary.push_back(0);
        }
    }


    vector<vector<int>> result;
    ternary.push_back(1);
    int i = 0;
    // 从最高位开始遍历
    while (i < ternary.size()) {
        // 创建一个新的vector<int>对象来存储当前的N个元素
        vector<int> part;
        for (int j = 0; j < N && i < ternary.size(); j++) {
            // 将当前元素添加到part中，并移动到下一个元素
            part.push_back(ternary[i]);
            i++;
        }
        if (part.size() < N) {
            for (int k = part.size(); k < N; k++) {
                part.push_back(0);
            }
        }
        // 将part添加到结果中
        result.push_back(part);
    }
    return result;


}


//逆函数，转换N长的三进制字符串为文字字符串
string NTRU::reverse_convert(vector<vector<int>> split) {
    vector<int> ternary;

    vector<int> tail = split.back();
    while (tail.back() == 0) {
        tail.pop_back();
    }
    tail.pop_back();

    if (tail.size() == 0) {
        split.pop_back();
        for (int i = 0; i < split.size(); i++) {
            ternary.insert(ternary.end(), split[i].begin(), split[i].end());
        }
    }
    else {
        if (split.size() == 1) {
            ternary = tail;
        }
        else {
            for (int i = 0; i < split.size() - 1; i++) {
                ternary.insert(ternary.end(), split[i].begin(), split[i].end());
            }
            ternary.insert(ternary.end(), tail.begin(), tail.end());
        }
    }

    string binary = "";
    for (int i = 0; i < ternary.size(); i++) {
        if (ternary[i] == 0) {
            binary += "0";
        }
        else {
            binary += "1";
        }
    }


    while (binary.size() % 8 != 0) {
        binary.insert(binary.begin(), '0');
    }
    string str;
    for (size_t i = 0; i < binary.size(); i += 8) {
        // 每8位一组，将其转化为对应的ASCII字符
        bitset<8> bits(binary.substr(i, 8));
        str += char(bits.to_ulong());
    }
    return str;
}
int main() {
    cout << "          ^欢迎使用NTRU加密软件^              " << endl;
    cout << "Welcome to NTRU Public-key Encryption Software" << endl;
    cout << "请选择您要使用的功能，请输入数字0或1或2并按回车确认" << endl;
    cout << "0. 密钥生成" << endl;
    cout << "1. 加密" << endl;
    cout << "2. 解密" << endl;

    string tmp;
    while (1) {
        cin >> tmp;
        if (tmp == "0") {
            NTRU ntru;
            ntru.generate_keys();
            vector<int> public_key = ntru.get_public_key();
            pair<vector<int>, vector<int>> private_key = ntru.get_private_key();

            string pubkey;
            string prikey;
            ostringstream ospubkey;
            ostringstream osprikey;
            for (int i : public_key) {
                ospubkey << base64[i + 31];
            }
            pubkey = ospubkey.str();
            for (int i : private_key.first) {
                if (i == 1) {
                    osprikey << i;
                }
                else if (i == 0) {
                    osprikey << i;
                }
                else if (i == -1) {
                    osprikey << 2;
                }
            }
            osprikey << " ";
            for (int i : private_key.second) {
                if (i == 1) {
                    osprikey << i;
                }
                else if (i == 0) {
                    osprikey << i;
                }
                else if (i == -1) {
                    osprikey << 2;
                }
            }
            prikey = osprikey.str();

            cout << "您的公钥为：" << endl;
            cout << pubkey << endl;
            cout << "您的私钥为：" << endl;
            cout << prikey << endl;
            cout << "请保管好您的密钥" << endl;
            cout << "欢迎再次使用！" << endl;
            cout << "      ----implemented by Rubby Tso" << endl;
            unsigned char* a = (unsigned char*)prikey.c_str();
            cout << strlen((char*)a) << endl;
            system("pause");
            break;
        }
        else if (tmp == "1") {
            string message,publickey;
            cin.ignore();
            cout << "请输入您要加密的消息：" << endl;
            getline(cin, message);
            cout << "请输入您的公钥" << endl;
            cin >> publickey;
            NTRU ntru;
            string ciphertext;
            ciphertext = ntru.encrypt(message, publickey);
            cout << "您的密文为：" << endl;
            cout << ciphertext << endl;
            cout << "请保管好您的密文! " << endl;
            cout << "欢迎再次使用！" << endl;
            cout << "      ----implemented by Rubby Tso" << endl;
            system("pause");
            break;

        }
        else if (tmp == "2") {
            string ciphertext, prikey;
            cin.ignore();
            cout << "请输入您的密文：" << endl;
            getline(cin, ciphertext);
            cout << "请输入您的私钥：" << endl;
            getline(cin, prikey);

            NTRU ntru;
            string plaintext;
            plaintext = ntru.decrypt(ciphertext, prikey);
            cout << "您的明文为：" << endl;
            cout << plaintext << endl;
            cout << "欢迎再次使用！" << endl;
            cout << "      ----implemented by Rubby Tso" << endl;
            system("pause");
            break;
        }
        else {
            cout << "请输入数字0或1或2并按回车确认"<<endl;
        }
    }
    
}
