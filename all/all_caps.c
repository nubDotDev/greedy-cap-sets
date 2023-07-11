#include <stdbool.h>
#include <stdio.h>
#include <time.h>

#define N 4  // Number of dimensions
#define Q 3  // Size of the field

#if Q == 3
    #if N == 2
        #define QN 9
        #define MAX_DEPTH 5  // Must be at least one more than the size of a maximum cap set
    #elif N == 3
        #define QN 27
        #define MAX_DEPTH 10
    #elif N == 4
        #define QN 81
        #define MAX_DEPTH 21
    #elif N == 5
        #define QN 243
        #define MAX_DEPTH 46
    #elif N == 6
        #define QN 729
        #define MAX_DEPTH 113
    #elif N == 7
        #define QN 2187
        #define MAX_DEPTH 337
    #endif
#endif

#define QN1 (QN/Q)
#define ALPHA min(QN1, MAX_DEPTH)
#define NORMALS ((QN-1)/2)  // This doesn't work for fields other than F_3
#define HYPERPLANES (Q*NORMALS)
#define MAXN (QN+HYPERPLANES)  // Size of point-hyperplane incidence graph

#include "nauty.h"

#define min(a,b) (((a) < (b)) ? (a) : (b))
#define PMOD(x, n) ((x % n + n) % n)

// Element of Z_Q^n
typedef char card[N];

card cards[QN], normals[NORMALS];
int setter[Q][Q];

int cap[MAX_DEPTH], alpha[QN][ALPHA], invar_buff[MAXN];
int point_hyp[QN][NORMALS], hyp_point[HYPERPLANES][QN1], cap_count[HYPERPLANES];
bool in_cap[QN], elim[QN];

graph g[MAXN * MAXM], canon[MAXN * MAXM];
int lab[MAXN], ptn[MAXN], orbit[MAX_DEPTH][MAXN];
DEFAULTOPTIONS_GRAPH(options);
statsblk stats;

long long cases[MAX_DEPTH], tots[MAX_DEPTH], comps[MAX_DEPTH];

// TODO implement biguint
long long grp_size, glfqn_size;

void userlevelproc(
    int* lab, int* ptn, int level, int* orbits, statsblk* stats,
    int tv, int index, int tcellsize, int numcells, int childcount, int n
) {
    if (numcells == n) {
        grp_size = 1;
    } else {
        grp_size *= index;
    }
}

void invarproc(
    graph* g, int* lab, int* ptn, int level, int numcells, int tvpos,
    int* invar, int invararg, boolean digraph, int m, int n)
{
    // memset(invar, 0, sizeof(int) * MAXN);
    int i, j;

    for (i = 0; i < QN; i++) {
        invar[i] = 0;
        for (j = 1; j < ALPHA; j++)
            invar[i] += alpha[i][j] * j * j;
        if (alpha[i][0])
            invar[i] *= -1;
    }
    for (i = QN; i < MAXN; i++)
        invar[i] = 0;
}

// Returns the decimal value of a card interpreted in base-Q
int card_index(card c) {
    int res = c[N-1], i;
    
    for (i = N-2; i >= 0; i--)
        res = Q * res + c[i];
    return res;
}

// Returns the index of the card that completes a set
int third(int c1, int c2) {
    card res;
    int i;

    for (i = 0; i < N; i++)
        res[i] = setter[cards[c1][i]][cards[c2][i]];
    return card_index(res);
}

bool vec_eq(int* v1, int* v2, int n) {
    int i;

    for (i = 0; i < n; i++)
        if (v1[i] != v2[i]) return false;
    return true;
}

bool vec_geq(int* v1, int* v2, int n) {
    int i;

    for (i = 0; i < n; i++) {
        if (v1[i] > v2[i]) return true;
        if (v1[i] < v2[i]) return false;
    }
    return true;
}

void print_card(card c) {
    int i;

    printf("(");
    for (i = 0; i < N-1; i++)
        printf("%2d,", c[i]);
    printf("%2d )", c[N-1]);
}

void print_int_arr(int* arr, int n) {
    int i;

    for (i = 0; i < n-1; i++) {
        printf("%d, ", arr[i]);
    }
    printf("%d\n", arr[n-1]);
}

void print_data() {
    int i;

    printf(" N   | Cap(s)          | Case(s) | Complete\n");
    for (i = 0; i < MAX_DEPTH; i++)
        printf(" %3d | %15lld | %7lld | %8lld\n", i, tots[i], cases[i], comps[i]);
}

void init() {
    int i, j, k, hyp, hyp_ind[HYPERPLANES] = {0}, offset;
    card count = {0};

    // Setters
    for (i = 0; i < Q; i++) {
        for (j = 0; j < Q; j++)
            setter[i][j] = PMOD(2*i - j, Q);
    }

    // Card vectors
    for (i = 0; i < QN; i++) {
        for (j = 0; j < N; j++)
            cards[i][j] = count[j];
        for (j = 0; j < N; j++) {
            if (++count[j] != Q) break;
            count[j] = 0;
        }
    }

    // Normal vectors
    for (i = 0; i < NORMALS; i++) {
        for (j = 0; j < N; j++)
            normals[i][j] = count[j] - 1;
        for (j = 0; j < N; j++) {
            if (++count[j] != Q) break;
            count[j] = 0;
        }
    }

    // Affine point-hyperplane incidence graph
    nauty_check(WORDSIZE, MAXM, MAXN, NAUTYVERSIONID);
    EMPTYGRAPH(g, MAXM, MAXN);

    for (i = 0; i < QN; i++) {
        for (j = 0; j < NORMALS; j++) {
            offset = 0;
            for (k = 0; k < N; k++)
                offset += normals[j][k] * cards[i][k];
            hyp = Q*j + PMOD(offset, Q);
            ADDONEEDGE(g, i, hyp + QN, MAXM);
            point_hyp[i][j] = hyp;
            hyp_point[hyp][hyp_ind[hyp]] = i;
            hyp_ind[hyp]++;
        }
    }

    // alpha
    for (i = 0; i < QN; i++)
        alpha[i][0] = NORMALS;

    // Labeling
    for (i = 0; i < MAXN; i++)
        lab[i] = i;

    // Coloring
    for (i = 0; i < MAXN-1; i++)
        ptn[i] = 1;
    ptn[MAXN-1] = 0;

    // nauty options
    options.defaultptn = FALSE;
    options.getcanon = TRUE;
    options.userlevelproc = &userlevelproc;
    options.invarproc = &invarproc;
}

int itrs = 0;

void orderly(int lvl) {
    if (lvl == MAX_DEPTH) return;

    int i, j, k, l, cand[QN] = {0}, orbs = 0, rep;
    bool seen[QN] = {false}, max_alpha;

    tots[lvl] += glfqn_size / grp_size;
    cases[lvl]++;

    for (i = 0; i < QN; i++) {
        rep = orbit[lvl][i];
        
        // Only consider unique uneliminated orbit representatives 
        if (seen[rep] || elim[rep]) continue;
        seen[rep] = true;

        cand[orbs] = rep;
        orbs++;
    }

    for (i = 0; i < orbs; i++) {
        int unelim[QN] = {0};

        rep = cand[i];
        cap[lvl] = rep;
        in_cap[rep] = true;

        // Increment hyperplane intersections
        for (j = 0; j < NORMALS; j++) {
            l = cap_count[point_hyp[rep][j]]++;
            for (k = 0; k < QN1; k++) {
                alpha[hyp_point[point_hyp[rep][j]][k]][l]--;
                alpha[hyp_point[point_hyp[rep][j]][k]][l+1]++;
            }
        }

        max_alpha = true;
        for (j = 0; j < lvl; j++) {
            if (!vec_geq(alpha[rep], alpha[cap[j]], ALPHA)) {
                max_alpha = false;
                break;
            }
        }
        
        if (max_alpha) {
            // Initialize labelling and coloring
            for (j = QN; j < MAXN; j++)
                lab[j] = j;
            for (j = QN; j < MAXN-1; j++)
                ptn[j] = 1;
            ptn[MAXN-1] = 0;
            k = 0;
            for (j = 0; j < QN; j++) {
                if (in_cap[j]) {
                    lab[j] = lab[k];
                    lab[k] = j;
                    k++;
                } else {
                    lab[j] = j;
                }
                ptn[j] = 1;
            }
            ptn[lvl] = 0;

            densenauty(g, lab, ptn, orbit[lvl+1], &options, &stats, MAXM, MAXN, canon);

            // Check if rep is in theta(X + rep)
            for (j = 0; j < QN; j++) {
                if (in_cap[lab[j]] && vec_eq(alpha[rep], alpha[lab[j]], ALPHA)) {
                    if (orbit[lvl+1][lab[j]] == orbit[lvl+1][rep]) {
                        printf("%9d ", ++itrs);
                        for (k = 0; k < lvl; k++)
                            printf(".");
                        printf("%d (%d)\n", rep, lvl + 1);

                        // Eliminate cards that form a set with rep and another card in the cap
                        l = 0;
                        for (j = 0; j <= lvl; j++) {
                            k = third(rep, lab[j]);
                            if (!elim[k]) {
                                elim[k] = true;
                                unelim[l] = k;
                                l++;
                            }
                        }

                        orderly(lvl + 1);
                        
                        // Uneliminate cards
                        for (j = 0; unelim[j]; j++)
                            elim[unelim[j]] = 0;
                    }
                    break;
                }
            }
        }

        in_cap[rep] = false;

        // Decrement hyperplane intersections
        for (j = 0; j < NORMALS; j++) {
            l = cap_count[point_hyp[rep][j]]--;
            for (k = 0; k < QN1; k++) {
                alpha[hyp_point[point_hyp[rep][j]][k]][l]--;
                alpha[hyp_point[point_hyp[rep][j]][k]][l-1]++;
            }
        }
    }

    if (orbs == 0)
        comps[lvl]++;
}

void all_caps() {
    densenauty(g, lab, ptn, orbit[0], &options, &stats, MAXM, MAXN, canon);
    glfqn_size = grp_size;
    orderly(0);
}

int main() {
    clock_t start;

    printf("Initializing...\n");
    init();
    printf("Finding all caps...\n");
    start = clock();
    all_caps();
    printf("\nTime elapsed: %.5fs\n\n", (double) (clock() - start) / CLOCKS_PER_SEC);
    print_data();

    // int p[MAXN] = {1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0};
    // int lvl = 0;
    // p[lvl] = 0;
    // // int l[MAXN] = {2,1,0,3,6,5,4,8,7,17,15,16,12,13,14,10,11,9,19,18,20};
    // int l[MAXN] = {2,1,0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20};
    // printf("%d\n", lvl);
    // for (int i = 0; i < MAXN; i++) {
    //     printf("%d ", l[i]);
    // }
    // printf("\n");
    // densenauty(g, l, p, orbit[4], &options, &stats, MAXM, MAXN, canon);
    // // densenauty(canon, l, p, orbit[4], &options, &stats, MAXM, MAXN, g);
    // for (int i = 0; i < MAXN; i++) {
    //     printf("%d ", orbit[4][i]);
    // }
    // printf("\n");
    // for (int i = 0; i < MAXN; i++) {
    //     printf("%d ", l[i]);
    // }
    // printf("\n");

    // graph h[MAXN*MAXM];
    // int l1[MAXN] = {0,1,2,3}, p1[MAXN] = {1,1,1,0}, o1[MAXN];
    // int n = 4;
    // int m = SETWORDSNEEDED(n);
    // ADDONEEDGE(h, 0, 1, m);
    // ADDONEEDGE(h, 1, 2, m);
    // ADDONEEDGE(h, 2, 3, m);
    // // ADDONEEDGE(h, 3, 0, m);
    // densenauty(h, l1, p1, o1, &options, &stats, m, n, canon);

}