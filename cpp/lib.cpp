#include <iostream>
#include <sstream>
#include <fstream>
#include <vector>
#include <set>
#include <list>
#include <unordered_set>
#include <map>
#include <unordered_map>
#include <deque>
#include <algorithm>
#include <cmath>
#include <string>
#include <numeric>
#include <float.h>
#include <climits>
#include <tuple>
#include <bitset>
#include <iomanip>
#include <queue>
#include <regex>
#include <cassert>

using namespace std;
using ll = long long;
using ull = unsigned long long;
using ld = long double;
constexpr double pi = 3.14159265358979323846;

#define all(itr) itr.begin(), itr.end()
#ifdef _DEBUG
#define dbg1(x) cout << #x << ": " << x << endl;
#define dbg2(x, y) cout << #x << ": " << x << ",  " << #y << ": " << y << endl;
#define dbg3(x, y, z) cout << #x << ": " << x << ",  " << #y << ": " << y << ",  " << #z << ": " << z << endl;
#define dbg4(a, b, c, d) cout << #a << ": " << a << ",  " << #b << ": " << b << ",  " << #c << ": " << c << ",  " << #d << ": " << d << endl;
#define dbg5(a, b, c, d, e) cout << #a << ": " << a << ",  " << #b << ": " << b << ",  " << #c << ": " << c << ",  " << #d << ": " << d << ",  " << #e << ": " << e << endl;
#define dbgend cout << endl;
#define label(x) cout << "=== " << #x << " ===" << endl;
#else
#define dbg1(x)
#define dbg2(x, y)
#define dbg3(x, y, z)
#define dbg4(a, b, c, d)
#define dbg5(a, b, c, d, e)
#define dbgend
#define label(x)
#endif

namespace MYLIB {

// 切り捨て
ll my_floor(ll A, ll B) {
    if (A >= 0 && B >= 0) {
        return A / B;
    }
    else {
        return A / B - (A % B < 0);
    }
}

// 素数かどうか
bool isPrime(ll N) {
    if (N < 2)        return false;

    for (ll n = 2; n * n <= N; n++) {
        if (N % n == 0)            return false;
    }

    return true;
}

// 素因数分解
using prime_ex = pair <ll, ll>;
vector<prime_ex> primeFactorize(ll N) {
    vector<prime_ex> ans;
    for (ll n = 2; n * n <= N; n++) {
        if (N % n != 0) continue;
        ll ex = 0;
        while (N % n == 0) {
            ex++;
            N /= n;
        }
        ans.push_back({ n, ex });
    }

    if (N != 1) ans.push_back({ N, 1 });

    return ans;
}

// N!の素因数分解におけるpの指数ep(N)
ll legendreTheory(ll N, ll p) {
    ll res = 0;
    while (N) {
        res += N / p;
        N /= p;
    }
    return res;
}

// エラトステネスのふるい(素数列挙)
vector<ll> eratos(ll n) {
    // 素数候補を管理
    vector<bool> isPrime(n + 1, true);
    for (ll i = 2; i * i <= n; i++) {
        if (isPrime[i]) {
            // 素数の倍数を素数候補から外す
            for (ll j = 2; i * j <= n; j++) {
                isPrime[i * j] = false;
            }
        }
    }

    vector<ll> ans;
    // 素数をpush_backして詰める
    for (ll i = 2; i <= n; i++) {
        if (isPrime[i])
            ans.push_back(i);
    }

    return ans;
}

// 約数列挙
vector<ll> enumDivisors(ll N) {
    vector<ll> ans;
    for (ll n = 1; n * n <= N; n++) {
        if (N % n != 0) continue;
        ans.push_back(n);
        if (n != N / n) ans.push_back(N / n);
    }
    sort(all(ans));

    return ans;
}

// 桁数確認
ll digit(ll N) {
    ll cnt = 1;
    while (N) {
        N /= 10;
        if (N != 0)
            cnt++;
    }
    return cnt;
}

// 平方数(整数の二乗)かどうか
bool isSquare(ll n) {
    ll d = (ll)sqrt(n) - 1;
    while (d * d < n) ++d;
    return d * d == n;
}

// 最小値更新
template <class T>
inline bool chmin(T& a, T b) {
    if (a > b) {
        a = b;
        return true;
    }
    return false;
}

// 最大値更新
template <class T>
inline bool chmax(T& a, T b) {
    if (a < b) {
        a = b;
        return true;
    }
    return false;
}

// charをllに変換
ll ctoll(const char c){
    return (ll)(c - '0');
}

// 整数判定
bool isInteger(const string& str) {
    bool ans = true;
    for (char const& c : str) {
        if (std::isdigit(c) == 0) {
            ans = false;
            break;
        }
    }
    return ans;
}

// n進数をK進数に変換
string convertBase(string value, ll base, ll target) {
    char hexBase = 'A'; // or 'a'
    ll x = 0;
    for (ll n = 0; n < (ll)value.size(); n++) {
        x *= base;
        ll offset = (ll)'0';
        if (value[n] > '9')
            offset = (ll)hexBase - 10;
        x += (ll)value[n] - offset;
    }
    string ans = "";
    while (x) {
        ll val = x % target;
        ll offset = (ll)'0';
        if (val > 9)
            offset = (ll)hexBase - 10;
        ans = (char)(val + offset) + ans;
        x /= target;
    }
    if (ans.empty())
        ans += '0';
    return ans;
}

// じゃんけん
ll R, S, P;
ll RSP(const char self, const char target) {
    if (self == 'r') {
        if (target == 'r') return R;
        if (target == 's') return S;
        if (target == 'p') return P;
        assert(false);
    }
    if (self == 's') {
        if (target == 'r') return R;
        if (target == 's') return S;
        if (target == 'p') return P;
        assert(false);
    }
    if (self == 'p') {
        if (target == 'r') return R;
        if (target == 's') return S;
        if (target == 'p') return P;
        assert(false);
    }
    assert(false);
    return -1;
}

// UnionFind
class UnionFind {
    /*
     * parで親の頂点番号と、サイズを同時に管理する
     * 根ではない頂点のparは親となる頂点の値が入ってる
     * 根にはサイズ数が入っている。区別できるようにサイズはマイナスの値で入っている
     * そのため、初期値はすべて-1になる(mergeの際にmergeされる側の根に、mergeする方の根が加算される)
     */
    vector<ll> parent_;
    ll groupe_num_;
    vector<ll> min_index_;
public:
    // 初期化
    UnionFind(const ll N) {
        this->parent_ = vector<ll>(N, -1);
        this->groupe_num_ = N;
        for (ll n = (ll)0; n < (ll)N; n++) {
            this->min_index_.push_back(n);
        }
    }

    // Aの根を調べる
    ll leader(const ll x) {
        if (this->parent_[x] < 0) return x;
        return this->parent_[x] = this->leader(this->parent_[x]);	// 根を代入することで経路圧縮(つながる親が根になる)
    }

    /*
    * 頂点xとyをマージする(1つのグループにする)
    * @param x : マージしたい頂点番号
    * @param y : マージしたい頂点番号
    * @return Bool値を返す, マージ成功した場合は`true`, すでに同じグループだった場合は`false`を返す
    */
    bool merge(const ll x, const ll y) {
        ll root_x = this->leader(x);
        ll root_y = this->leader(y);
        // すでに同じグループ
        if (root_x == root_y) return false;

        // サイズが大きいほうにマージする
        // 以下は必ずxが大きいほう(サイズはマイナスの値が入ってるので)にするように調整している
        ll sizeX = -1 * this->parent_[root_x];
        ll sizeY = -1 * this->parent_[root_y];
        if (sizeX < sizeY) {
            swap(root_x, root_y);
        }

        // サイズ加算
        this->parent_[root_x] += this->parent_[root_y];
        this->parent_[root_y] = root_x;

        // グループの数減る
        this->groupe_num_--;

        chmin(this->min_index_[root_x], this->min_index_[root_y]);

        return true;
    }

    ll size(const ll x) {
        return -1 * this->parent_[this->leader(x)];
    }

    ll groupe_num() {
        return this->groupe_num_;
    }

    bool same(const ll x, const ll y) {
        bool isSame = false;
        ll rootX = this->leader(x);
        ll rootY = this->leader(y);
        if (rootX == rootY) {
            isSame = true;
        }
        return isSame;
    }

    ll min_index(const ll leader) {
        return this->min_index_[leader];
    }
};

namespace nCr {
    namespace non_mod {
        // init(取りうるnの最大値)を実行してから、get(n, r)を使用すること)
        vector<vector<ll>> ncr;
        void init(ll last) {
            ncr.resize(last + 1, vector<ll>(last + 1));
            ncr[0][0] = 1;
            for (ll n = 1LL; n <= last; n++) {
                ncr[n][0] = 1;
                for (ll r = 1LL; r <= last; r++) {
                    ncr[n][r] = ncr[n - 1][r] + ncr[n - 1][r - 1];
                }
            }
        }

        ll get(ll n, ll r) {
            return ncr[n][r];
        }
    } // namespace non_mod

    // 何度もMOD計算する場合はこっち
    namespace mod {
        namespace internal {
            ll mod;
            vector<ll> fac, finv, inv;
            bool has_set_mod = false;
        } // namespace internal

        // nCrをmodで計算
        // init(取りうるnの最大値)を実行してから、run(n, r)を使用すること)

        void set_mod(const ll mod) {
            internal::mod = mod;
            internal::has_set_mod = true;
        }

        void init(ll last) {
            assert(internal::has_set_mod);

            internal::fac.resize(last + 1);
            internal::finv.resize(last + 1);
            internal::inv.resize(last + 1);

            internal::fac[0] = internal::fac[1] = 1;
            internal::finv[0] = internal::finv[1] = 1;
            internal::inv[1] = 1;

            for (ll i = 2; i <= last; i++) {
                internal::fac[i] = internal::fac[i - 1] * i % internal::mod;
                internal::inv[i] = internal::mod - internal::inv[internal::mod % i] * (internal::mod / i) % internal::mod;
                internal::finv[i] = internal::finv[i - 1] * internal::inv[i] % internal::mod;
            }
        }

        ll run(ll n, ll r) {
            assert(internal::has_set_mod);

            if (n < r) return 0;
            if (n < 0 || r < 0) return 0;
            return internal::fac[n] * (internal::finv[r] * internal::finv[n - r] % internal::mod) % internal::mod;
        }
    } // namespace mod

    // nが大きい(1e9)ときのnCrはこっち
    namespace big_n {
        template<typename T>
        T run(const ll n, const ll k) {
            // nCx
            T res = 1;
            for (ll i = 0; i < k; i++) res *= n - i; // 分子の階乗の計算
            for (ll i = 2; i <= k; i++) res /= i; // 分母の階乗を一個一個割る
            return res;
        }
    } // namespace big_n
} // namespace nCr

// BinarySearch
namespace BinarySearch {
    bool IsOk(

    ) {
        bool is_ok = false;

        return is_ok;
    }

    template<typename T>
    T Solve(

    ) {
        ld ok = 5000.0;
        ld ng = -1.0;

        // okとngの最小差
        ld min_diff = 10e-8;
        while (abs(ok - ng) > min_diff) {
            auto mid = (ok + ng) / 2.0;
            if (IsOk()) {
                ng = mid;
            }
            else {
                ok = mid;
            }
        }
        return ok;
    }
}


/* RMQ：[0,N-1] について、区間ごとの最小値を管理する構造体
    コンストラクタ: O(N)
    update(n, x): n 番目の要素を x に更新。O(log(N))
    query(begin,end): [begin, end) での最小の要素を取得。O(log(N))
*/
template <typename T>
class RMQ {
    const T INF = numeric_limits<T>::max();
    vector<T> data_;
    ll N_;

    ll get_parent_index(const ll index) {
        return (index - 1) / 2;
    }
    using child_indexes = pair<ll, ll>;
    child_indexes get_child_indexes(const ll index) {
        ll index1 = 2 * index + 1;
        ll index2 = 2 * index + 2;
        child_indexes indexes = make_pair(index1, index2);
        return indexes;
    };

    ll query_sub(const ll begin, const ll end, const ll current_index, const ll left, const ll right) {
        // current_index
        // => [left, right) data[current_index]が表している区間

        // 範囲外は考えない
        if (right <= begin || end <= left) {
            return INF;
        }
        // 範囲内なので自身の値を返す
        else if (begin <= left && right <= end) {
            return this->data_[current_index];
        }
        // 一部区間が被る→子の値を参照
        else {
            const auto [child1, child2] = this->get_child_indexes(current_index);
            const ll center = (left + right) / 2;
            const ll child1_val = this->query_sub(begin, end, child1, left, center);
            const ll child2_val = this->query_sub(begin, end, child2, center, right);

            return min(child1_val, child2_val);
        }
    }
public:
    RMQ(const ll N) : N_(), data_(N * 4, INF) {
        // 葉の数は 2^x の形
        ll cnt = 1;
        while (N > cnt) {
            cnt *= 2;
        }
        this->N_ = cnt;
    };

    void update(const ll n, const ll x) {
        ll index = this->N_ - 1 + n;
        this->data_[index] = x;
        while (index > 0) {
            index = this->get_parent_index(index);
            const auto [child1, child2] = this->get_child_indexes(index);
            this->data_[index] = min(this->data_[child1], this->data_[child2]);
        }
    };

    ll query(const ll begin, const ll end) {
        return this->query_sub(begin, end, 0, 0, this->N_);
    };
};

// ランレングス圧縮
vector<pair<char, ll>> RunLengthEncoding(string s) {
    ll N = s.length();

    vector<pair<char, ll>> res;
    char pre = s[0];
    ll cnt = 1;
    for (ll n = (ll)1; n < (ll)N; n++) {
        if (pre != s[n]) {
            res.push_back({ pre, cnt });
            pre = s[n];
            cnt = 1;
        }
        else cnt++;
    }

    res.push_back({ pre, cnt });
    return res;
}

//ll MOD = 998244353;
ll dx[4] = { 1,0,-1,0 };
ll dy[4] = { 0,1,0,-1 };

//std::ifstream in("1_016.txt");
//std::cin.rdbuf(in.rdbuf());

//priority_queue<
//    ll,                // 要素の型はint
//    std::vector<ll>,   // 内部コンテナはstd::vector (デフォルトのまま)
//    std::greater<ll>   // 昇順 (デフォルトはstd::less<T>)
//> q;

//cout << std::fixed << std::setprecision(15)
//cout << setfill('0') << std::setw(6)
//cout << setfill(' ') << std::setw(3)

}