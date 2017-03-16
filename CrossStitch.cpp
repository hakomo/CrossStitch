#include <algorithm>
#include <cmath>
#include <iostream>
#include <string>
#include <vector>
using namespace std;

double get_time() {
    unsigned long long a, d;
    __asm__ volatile ("rdtsc" : "=a" (a), "=d" (d));
    return (d << 32 | a) / 2500000.0;
}

unsigned rando() {
    static unsigned y = 2463534242;
    return y ^= (y ^= (y ^= y << 13) >> 17) << 5;
}

int ID_TO_COLOR[10020];
int id_to_index[20000];
vector<int*> INDEX_NEAR_ID[20000];
pair<int, int> XY[40080];
double DISTANCE[202][202];

#define D(i, j) DISTANCE[abs(XY[i].second - XY[j].second)][abs(XY[i].first - XY[j].first)]

namespace DP {

    vector<int>::const_iterator it;
    double dp[20002][2][2];
    int next[20002][2][2];

    double dfs(int i, int j, int k) {
        double& ret = dp[i][j][k];
        if (ret == 1e9) {
            int id1 = it[i - j - 1] ^ k;
            for (int l = 0; l < 2; ++l) {
                int id2 = it[i] ^ l;
                double s = D(id1, id2 ^ 1) + dfs(i + 1, 0, l);
                if (ret > s) {
                    ret = s;
                    next[i][j][k] = l;
                }
            }
            for (int l = 0; l < 4; ++l) {
                int id2 = it[i + 1] ^ (l >> 1 & 1);
                int id3 = it[i] ^ (l & 1);
                double s = D(id1, id2 ^ 1) + D(id2, id3 ^ 1) + dfs(i + 2, 1, l & 1);
                if (ret > s) {
                    ret = s;
                    next[i][j][k] = l + 2;
                }
            }
        }
        return ret;
    }

    double optimize(vector<int>& sol) {
        for (int i = 1; i < (int)sol.size(); ++i)
            dp[i][0][0] = dp[i][0][1] = dp[i][1][0] = dp[i][1][1] = 1e9;
        int i = sol.size() - 1;
        dp[i][0][0] = dp[i][0][1] = dp[i][1][0] = dp[i][1][1] = 0;
        --i;
        for (int j = 0; j < 2; ++j) {
            for (int k = 0; k < 2; ++k) {
                int id1 = sol[i - j - 1] ^ k;
                for (int l = 0; l < 2; ++l) {
                    int id2 = sol[i] ^ l;
                    if (dp[i][j][k] > D(id1, id2 ^ 1)) {
                        dp[i][j][k] = D(id1, id2 ^ 1);
                        next[i][j][k] = l;
                    }
                }
            }
        }
        it = sol.begin();
        dfs(1, 0, 0);
        int l = next[1][0][0];
        for (int i = 1; i < (int)sol.size() - 1; ) {
            if (l < 2) {
                sol[i] ^= l;
                i += 1;
                l = next[i][0][l];
            } else {
                l -= 2;
                sol[i] ^= l & 1;
                sol[i + 1] ^= l >> 1 & 1;
                swap(sol[i], sol[i + 1]);
                i += 2;
                l = next[i][1][l & 1];
            }
        }
        return dp[1][0][0];
    }
}

struct CrossStitch {

    void push_unless_share_point(int i, int j) const {
        if (XY[i] != XY[j] && XY[i ^ 1] != XY[j] && XY[i] != XY[j ^ 1] && XY[i ^ 1] != XY[j ^ 1])
            INDEX_NEAR_ID[i / 2].emplace_back(id_to_index + j / 2);
    }

    vector<string> embroider(const vector<string>& pattern) const {
        const double START_TIME = get_time();

        int S = pattern.size();
        int C = 0;
        vector<int> sols[20];
        vector<int> best_sols[20];
        double scores[20];
        double best_scores[20];
        vector<int**> index_to_bad_p[20];
        vector<int*> sol_bad_p;
        int* SOL_GOOD_P = nullptr;

        {
            vector<int> ID_BY_COLOR[20];
            int id = 0;
            for (int y = 0; y <= S; ++y)
                for (int x = 0; x <= S; ++x)
                    DISTANCE[y][x] = sqrt(x * x + y * y);
            for (int y = 0; y < S; ++y) {
                for (int x = 0; x < S; ++x) {
                    if (pattern[y][x] != '.') {
                        int color = pattern[y][x] - 'a';
                        C = max(C, color + 1);
                        auto& sol = sols[color];
                        if (sol.empty())
                            sol.emplace_back(-1);
                        sol.emplace_back(id);
                        sol.emplace_back(id + 2);
                        ID_TO_COLOR[id / 4] = color;
                        ID_BY_COLOR[color].emplace_back(id);
                        XY[id++] = { x, y };
                        XY[id++] = { x + 1, y + 1 };
                        XY[id++] = { x + 1, y };
                        XY[id++] = { x, y + 1 };
                    }
                }
            }
            for (int color = 0; color < C; ++color) {
                ID_TO_COLOR[id / 4 + color] = color;
                XY[id + color * 4] = XY[id + color * 4 + 1] = { S * 2 + 1, S * 2 + 1 };
                auto& sol = sols[color];
                sol[0] = id + color * 4;
                sol.emplace_back(id + color * 4);
                double& score = scores[color];
                score = 0;
                for (int i = 1; i < (int)sol.size() - 1; ++i) {
                    if (XY[sol[i - 1]] == XY[sol[i] ^ 1])
                        sol[i] ^= 1;
                    score += D(sol[i - 1], sol[i] ^ 1);
                    id_to_index[sol[i] / 2] = i;
                }
                best_sols[color] = sol;
                best_scores[color] = score;
            }
            for (int color = 0; color < C; ++color) {
                auto ids = ID_BY_COLOR[color];
                for (int id : ID_BY_COLOR[color]) {
                    int size = min(S * S / C > 300 ? 9 : 15, (int)ids.size());
                    partial_sort(ids.begin(), ids.begin() + size, ids.end(), [id](int i, int j) {
                        return D(id, i) < D(id, j);
                    });
                    INDEX_NEAR_ID[id / 2].reserve(size * 2 - 1);
                    INDEX_NEAR_ID[id / 2 + 1].reserve(size * 2 - 1);
                    for (int i = 0; i < size; ++i) {
                        int id2 = ids[i];
                        push_unless_share_point(id, id2 + 2);
                        push_unless_share_point(id + 2, id2);
                        if (i) {
                            push_unless_share_point(id, id2);
                            push_unless_share_point(id + 2, id2 + 2);
                        }
                    }
                }
            }
            sol_bad_p.reserve(id / 2 + C);
            for (int color = 0; color < C; ++color) {
                auto& sol = sols[color];
                index_to_bad_p[color].assign(sol.size(), &SOL_GOOD_P);
                for (int i = 1; i < (int)sol.size(); ++i) {
                    if (D(sol[i - 1], sol[i] ^ 1) != 1) {
                        sol_bad_p.emplace_back(&sol[i]);
                        index_to_bad_p[color][i] = &sol_bad_p.back();
                    }
                }
            }
            DISTANCE[0][0] = 1e9;
        }

        const double SA_START_TIME = get_time();
        const double TIME_LIMIT = 9850 - (SA_START_TIME - START_TIME);
        const double INITIAL_HEAT = min(2.1, S * C / 1000.0 + 0.7);
        const double FINAL_HEAT = 0.01;
        double heat_inv = 0;
        double th = 0;
        bool optimized = false;
        for (int an = -1; ; ) {
            if (!(++an & 0x7ff)) {
                double p = 1 - (get_time() - SA_START_TIME) / TIME_LIMIT;
                if (p <= 0) {
                    break;
                } else if (p < 0.1 && !optimized) {
                    optimized = true;
                    for (int color = 0; color < C; ++color) {
                        best_scores[color] = DP::optimize(best_sols[color]);
                        scores[color] = best_scores[color];
                        sols[color] = best_sols[color];
                        auto& sol = sols[color];
                        for (int i = 1; i < (int)sol.size() - 1; ++i)
                            id_to_index[sol[i] / 2] = i;
                    }
                    sol_bad_p.clear();
                    for (int color = 0; color < C; ++color) {
                        auto& sol = sols[color];
                        index_to_bad_p[color].assign(sol.size(), &SOL_GOOD_P);
                        for (int i = 1; i < (int)sol.size(); ++i) {
                            if (D(sol[i - 1], sol[i] ^ 1) != 1) {
                                sol_bad_p.emplace_back(&sol[i]);
                                index_to_bad_p[color][i] = &sol_bad_p.back();
                            }
                        }
                    }
                }
                heat_inv = 1 / (FINAL_HEAT + (INITIAL_HEAT - FINAL_HEAT) * p);
                th = 9 / heat_inv;
            }
            unsigned r = rando();
            auto sol_p = sol_bad_p[(r >> 16) % sol_bad_p.size()];
            int color = ID_TO_COLOR[*sol_p / 4];
            auto& sol = sols[color];
            int i = sol_p - &sol[0];
            int j = i == 1 || i != sol.size() - 1 && r >> 15 & 1
                ? *INDEX_NEAR_ID[sol_p[0] / 2][(r & 0x7fff) % INDEX_NEAR_ID[sol_p[0] / 2].size()]
                : *INDEX_NEAR_ID[sol_p[-1] / 2][(r & 0x7fff) % INDEX_NEAR_ID[sol_p[-1] / 2].size()] + 1;
            double diff = - D(sol[i - 1], sol[i] ^ 1) + D(sol[i - 1], sol[j - 1])
                - D(sol[j - 1], sol[j] ^ 1) + D(sol[j] ^ 1, sol[i] ^ 1);
            if (diff < th && rando() / 4294967296.0 < exp(-diff * heat_inv)) {
                if (i > j)
                    swap(i, j);
                int i2 = i;
                int j2 = j;
                int*** bad_pp = &index_to_bad_p[color][0];
                for (--j; i < j; ) {
                    id_to_index[sol[j] / 2] = i;
                    id_to_index[sol[i] / 2] = j;
                    sol[i] ^= 1;
                    sol[j] ^= 1;
                    swap(sol[i], sol[j]);
                    ++i;
                    *bad_pp[i] = &sol[j];
                    *bad_pp[j] = &sol[i];
                    swap(bad_pp[i], bad_pp[j]);
                    --j;
                }
                if (i == j)
                    sol[i] ^= 1;
                for (int i : { i2, j2 }) {
                    if ((bad_pp[i] != &SOL_GOOD_P) != (D(sol[i - 1], sol[i] ^ 1) != 1)) {
                        if (bad_pp[i] != &SOL_GOOD_P) {
                            *bad_pp[i] = sol_bad_p.back();
                            int c = ID_TO_COLOR[*sol_bad_p.back() / 4];
                            index_to_bad_p[c][sol_bad_p.back() - &sols[c][0]] = bad_pp[i];
                            bad_pp[i] = &SOL_GOOD_P;
                            sol_bad_p.pop_back();
                        } else {
                            sol_bad_p.emplace_back(&sol[i]);
                            bad_pp[i] = &sol_bad_p.back();
                        }
                    }
                }
                double& score = scores[color];
                score += diff;
                if (best_scores[color] > score) {
                    best_scores[color] = score;
                    best_sols[color] = sol;
                }
            }
        }

        vector<string> ret;
        for (int color = 0; color < C; ++color) {
            ret.emplace_back(1, 'a' + color);
            auto& sol = best_sols[color];
            DP::optimize(sol);
            for (int i = 1; i < (int)sol.size() - 1; ++i) {
                auto& p1 = XY[sol[i] ^ 1];
                auto& p2 = XY[sol[i]];
                ret.emplace_back(to_string(p1.second) + " " + to_string(p1.first));
                ret.emplace_back(to_string(p2.second) + " " + to_string(p2.first));
            }
        }
        return ret;
    }
};
