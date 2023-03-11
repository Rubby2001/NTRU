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

class NTRU {
public:
    // ���캯����ʹ��Ĭ�ϲ��������ɹ�������
    NTRU();
    // ���캯����ʹ�ø������������ɹ�������
    NTRU(int N, int p, int q, int Df, int Dg, int Dr);
    // ���ɹ�Կ��˽Կ
    void generate_keys();
    vector<int> get_public_key();
    pair<vector<int>, vector<int>> get_private_key();
    // ����
    vector<int> encrypt(const vector<int>& plaintext, const vector<int>& public_key);
    string encrypt(const string& plaintext, string public_key);
    // ����
    vector<int> decrypt(const vector<int>& ciphertext, const pair<vector<int>, vector<int>>& private_key);
    string decrypt(string result, string private_key);

private:
    int N;   //����ʽϵ��
    int p;   //ϵ��ģ��
    int q;   //����ģ��
    int Df;     //���ܹ��̶���ʽ����������
    int Dg;
    int Dr;
    vector<int> f;   //˽Կ
    vector<int> Fp;
    vector<int> Fq;
    vector<int> g;
    vector<int> h;  //��Կ 
    vector<int> r;  //���ܹ����������������ĵ�С����ʽ

    // һЩ���������������ʽ���ɺͶ���ʽ���㺯��
    vector<int> generate_poly(int N, int a, int b);  //����������ڻ�R��a��b����N-1�ζ���ʽ
    void rotateLeft(vector<int>& v, int k);     //����ʽѭ������kλ��������ģ���㷨��
    vector<int> convolution(vector<int> A, vector<int> B);  //����ʽ�������

    vector<int> add_polynomials(const vector<int>& a, const vector<int>& b);      //����ʽ�ӷ� 
    vector<int> subtract_polynomials(const vector<int>& a, const vector<int>& b);//����ʽ����
    void polynomial_division(vector<int> a, vector<int> b, vector<int>& q, vector<int>& r);    //����ʽ����

    vector<int> inverse_qin_p(const vector<int>& a);  //�ؾ��ش�����һ�������ʽ����p��ģ�棬ͨ��p=3
    vector<int> inverse_qin_q(const vector<int>& a);  //�ؾ��ش�����һ�������ʽ����q��ģ�棬ͨ��qΪ2��ָ����

    void mod_p(vector<int>& a);  //����ʽģp��ϵ��������{-1��0��1}��
    void mod_2(vector<int>& a);  //����ʽģ2��ϵ��������{0��1}��
    void mod_q(vector<int>& a);   //����ʽģq��ϵ�������� (-q/2��q/2)��
    void remove_zeros(vector<int>& a); //ȥ������ʽĩβ��0

    vector<vector<int>> convert(const string& str);      //ת����������string����ת��Ϊ�����ƣ���Ϊ����ΪN���顣
    string reverse_convert(vector<vector<int>> split);    //��ת�������������鳤��ΪN�����飬ת��Ϊstring����
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
    int n = a.size() - 1;  // ����ʽ a �Ĵ���  
    int m = b.size() - 1;  // ����ʽ b �Ĵ���   

    //if (m < 0) throw std::invalid_argument("�쳣����������ʽΪ0����ʽ");

    if (n < m) {       //a�Ĵ�������bʱ
        q.clear();
        r = a;
        return;
    }

    q.resize(n - m + 1);   // ��ʼ���̵�ϵ������ q       
    r.resize(m);           // ��ʼ��������ϵ������ r      

    for (int i = n - m; i >= 0; i--) {  // �Ӹߴ���ʹ����𲽼����̵�ϵ��      
        q[i] = a[i + m] / b[m];         // ���㵱ǰ�����              
        for (int j = i + m - 1, k = m - 1; k >= 0; j--, k--) {  // �õ�ǰ����̸�������    
            a[j] -= q[i] * b[k];        // ���� a(x) - q(x) * b(x)     
        }
    }
    if (m == 0) r = vector<int>{ 0 };
    else {
        for (int i = 0; i < m; i++) {  // ����������ϵ��
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
    // ���vectorΪ�գ�ֱ�ӷ���
    if (a.empty()) return;
    if (a == vector<int> {0}) return;
    // ��vector��ĩβ��ʼ����
    for (int i = a.size() - 1; i >= 1; i--) {
        // �����ǰԪ����0����ɾ����
        if (a[i] == 0) {
            a.pop_back();
        }
        //�����˳�ѭ��
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
//�ؾ��ش�����һ�������ʽ����p��ģ�棬ͨ��p=3
vector<int> NTRU::inverse_qin_p(const vector<int>& a) {
    //��ʼ��״̬����
    vector<int> X_11 = { 1 };
    vector<int> X_12 = a;
    remove_zeros(X_12);
    vector<int> X_21 = { 0 };
    vector<int> X_22(N + 1, 0);
    X_22[0] = -1;
    X_22[N] = 1;
    vector<int> Q, R;

    //��ģp��ģ�����ʽ
    while (1) {
        if (X_22.size() > X_12.size()) {
            polynomial_division(X_22, X_12, Q, R);
            //����ģp��ȥͷ����0������R���п��ܵ��滻����Ϊ�����������һ��Ҫ�󣬽�����RΪ��С��ʣ��
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

            //������ģp��ȥ��ͷ����0
            mod_p(X_21);
            mod_p(X_22);
            remove_zeros(X_12);
            remove_zeros(X_22);
            remove_zeros(X_11);
            remove_zeros(X_21);
        }
        else if (X_22.size() < X_12.size()) {
            polynomial_division(X_12, X_22, Q, R);
            //����ģp��ȥͷ����0������R���п��ܵ��滻����Ϊ�����������һ��Ҫ�󣬽�����RΪ��С��ʣ��
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

            //������ģp��ȥ��ͷ����0
            mod_p(X_11);
            mod_p(X_12);
            remove_zeros(X_12);
            remove_zeros(X_22);
            remove_zeros(X_11);
            remove_zeros(X_21);
        }
        //������һ�������ʽģ��ʱ��X_12��������Ϊ���������Զԡ�1�ֿ�����
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

//�ؾ��ش�����һ�������ʽ����q��ģ�棬ͨ��qΪ2��ָ����
vector<int> NTRU::inverse_qin_q(const vector<int>& a) {
    //��ʼ��״̬����
    vector<int> X_11 = { 1 };
    vector<int> X_12 = a;
    remove_zeros(X_12);
    vector<int> X_21 = { 0 };
    vector<int> X_22(N + 1, 0);
    X_22[0] = -1;
    X_22[N] = 1;
    vector<int> Q, R;

    //��ģ2��ģ�����ʽ
    while (1) {
        if (X_22.size() > X_12.size()) {
            polynomial_division(X_22, X_12, Q, R);
            //����ģ2��ȥͷ����0������R���п��ܵ��滻����Ϊ�����������һ��Ҫ�󣬽�����RΪ��С��ʣ��
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
            //������ģ2��ȥ��ͷ����0
            mod_2(X_21);
            mod_2(X_22);
            remove_zeros(X_12);
            remove_zeros(X_22);
            remove_zeros(X_11);
            remove_zeros(X_21);

        }
        else if (X_22.size() < X_12.size()) {
            polynomial_division(X_12, X_22, Q, R);
            //����ģ2��ȥͷ����0������R���п��ܵ��滻����Ϊ�����������һ��Ҫ�󣬽�����RΪ��С��ʣ��
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

            //������ģ2��ȥ��ͷ����0
            mod_2(X_11);
            mod_2(X_12);
            remove_zeros(X_12);
            remove_zeros(X_22);
            remove_zeros(X_11);
            remove_zeros(X_21);
        }
        //������һ�������ʽģ��ʱ��X_12��������Ϊ���������Զԡ�1�ֿ�����
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
    //ţ�ٵ�����������ģ2��ģ�����ʽX_12����ģq��ģ�����ʽ
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
    int num;
    while (ish >> num) {
        h.push_back(num);
    }

    vector<vector<int>> b;
    for (vector<int> i : a) {
        b.push_back(encrypt(i, h));
    }

    string result;
    ostringstream osresult;
    for (vector<int> i : b) {
        for (int j : i) {
            osresult << j << " ";
        }
        osresult << "end" << " ";
    }
    result = osresult.str();

    return result;

}

string NTRU::decrypt(string result, string private_key) {

    string plaintext;
    vector<vector<int>> ciphertext;
    vector<int> part;
    istringstream iss(result);
    string word;
    while (iss >> word) {
        if (word == "end") {
            ciphertext.push_back(part);
            part.clear();
            continue;
        }
        int num = stoi(word);
        part.push_back(num);
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
        // ʹ��std::bitset��������ȡ�ַ��Ķ����Ʊ�ʾ
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
    // �����λ��ʼ����
    while (i < ternary.size()) {
        // ����һ���µ�vector<int>�������洢��ǰ��N��Ԫ��
        vector<int> part;
        for (int j = 0; j < N && i < ternary.size(); j++) {
            // ����ǰԪ����ӵ�part�У����ƶ�����һ��Ԫ��
            part.push_back(ternary[i]);
            i++;
        }
        if (part.size() < N) {
            for (int k = part.size(); k < N; k++) {
                part.push_back(0);
            }
        }
        // ��part��ӵ������
        result.push_back(part);
    }
    return result;


}


//�溯����ת��N�����������ַ���Ϊ�����ַ���
string NTRU::reverse_convert(vector<vector<int>> split) {
    vector<int> ternary;

    vector<int> tail = split.back();
    while (tail.back() == 0) {
        tail.pop_back();
    }
    tail.pop_back();

    if (split.size() == 1) {
        ternary = tail;
    }
    else {
        for (int i = 0; i < split.size() - 1; i++) {
            ternary.insert(ternary.end(), split[i].begin(), split[i].end());
        }
        ternary.insert(ternary.end(), tail.begin(), tail.end());
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
        // ÿ8λһ�飬����ת��Ϊ��Ӧ��ASCII�ַ�
        bitset<8> bits(binary.substr(i, 8));
        str += char(bits.to_ulong());
    }
    return str;
}
int main() {
    cout << "          ^��ӭʹ��NTRU�������^              " << endl;
    cout << "Welcome to NTRU Public-key Encryption Software" << endl;
    cout << "��ѡ����Ҫʹ�õĹ��ܣ�����������0��1��2�����س�ȷ��" << endl;
    cout << "0. ��Կ����" << endl;
    cout << "1. ����" << endl;
    cout << "2. ����" << endl;

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
                ospubkey << i << " ";
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

            cout << "���Ĺ�ԿΪ��" << endl;
            cout << pubkey << endl;
            cout << "����˽ԿΪ��" << endl;
            cout << prikey << endl;
            cout << "�뱣�ܺ�������Կ" << endl;
            cout << "��ӭ�ٴ�ʹ�ã�" << endl;
            cout << "      ----implemented by Rubby Tso" << endl;
            break;
        }
        else if (tmp == "1") {
            string message,publickey;
            cin.ignore();
            cout << "��������Ҫ���ܵ���Ϣ��" << endl;
            getline(cin, message);
            cout << "���������Ĺ�Կ" << endl;
            cin >> publickey;
            NTRU ntru;
            string ciphertext;
            ciphertext = ntru.encrypt(message, publickey);
            cout << "��������Ϊ��" << endl;
            cout << ciphertext << endl;
            cout << "�뱣�ܺ���������! " << endl;
            cout << "��ӭ�ٴ�ʹ�ã�" << endl;
            cout << "      ----implemented by Rubby Tso" << endl;
            break;

        }
        else if (tmp == "2") {
            string ciphertext, prikey;
            cin.ignore();
            cout << "�������������ģ�" << endl;
            getline(cin, ciphertext);
            cout << "����������˽Կ��" << endl;
            getline(cin, prikey);

            NTRU ntru;
            string plaintext;
            plaintext = ntru.decrypt(ciphertext, prikey);
            cout << "��������Ϊ��" << endl;
            cout << plaintext << endl;
            cout << "��ӭ�ٴ�ʹ�ã�" << endl;
            cout << "      ----implemented by Rubby Tso" << endl;
            break;
        }
        else {
            cout << "����������0��1��2�����س�ȷ��"<<endl;
        }
    }
    
}