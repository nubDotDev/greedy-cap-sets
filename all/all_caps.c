#include <stdbool.h>
#include <stdio.h>
#include <time.h>

#define N 4  // Number of attributes/dimensions

#if N == 2
    #define TN 9  // 3^N
    #define NORMALS 4  // (TN - 1) / 2
    #define MAX_DEPTH 5  // Must be at least one more than the size of a maximum cap set
    #define MAXN 21  // Size of point-hyperplane incidence graph (TN + 3 * NORMALS) 
#elif N == 3
    #define TN 27
    #define NORMALS 13
    #define MAX_DEPTH 10
    #define MAXN 66
#elif N == 4
    #define TN 81
    #define NORMALS 40
    #define MAX_DEPTH 21
    #define MAXN 201
#elif N == 5
    #define TN 243
    #define NORMALS 121
    #define MAX_DEPTH 46
    #define MAXN 606
#elif N == 6
    #define TN 729
    #define NORMALS 364
    #define MAX_DEPTH 113
    #define MAXN 1821
#elif N == 7
    #define TN 2187
    #define NORMALS 1093
    #define MAX_DEPTH 337
    #define MAXN 5466
#else
    #define TN 0
    #define NORMALS 0
    #define MAX_DEPTH 0
    #define MAXN 0
#endif

#include "nauty.h"

#define PMOD(x, n) ((x % n + n) % n)

// Element of Z_3^n
typedef char card[N];

card cards[TN];
card normals[NORMALS];
int setter[3][3] = {{0, 2, 1}, {2, 1, 0}, {1, 0, 2}};

int lab[MAXN], ptn[MAXN], orbit[MAX_DEPTH][MAXN];
bool in_cap[TN], elim[TN];

graph g[MAXN * MAXM], canon[MAXN * MAXM];
DEFAULTOPTIONS_GRAPH(options);
statsblk stats;

long long cases[MAX_DEPTH], tots[MAX_DEPTH], comps[MAX_DEPTH];

// TODO implement biguint
long long grp_size, glf3n_size;

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

// Returns the decimal value of a card interpreted in base-3
int card_index(card c) {
    int res = c[N-1], i;
    
    for (i = N-2; i >= 0; i--)
        res = 3 * res + c[i];
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
    int i = 0, j;
    card count = {0};

    // Card vectors
    for (i = 0; i < TN; i++) {
        for (j = 0; j < N; j++)
            cards[i][j] = count[j];
        for (j = 0; j < N; j++) {
            if (++count[j] != 3) break;
            count[j] = 0;
        }
    }

    // Normal vectors
    for (i = 0; i < NORMALS; i++) {
        for (j = 0; j < N; j++)
            normals[i][j] = (count[j] + 2) % 3;
        for (j = 0; j < N; j++) {
            if (++count[j] != 3) break;
            count[j] = 0;
        }
    }

    int k, o;

    // Affine point-hyperplane incidence graph
    nauty_check(WORDSIZE, MAXM, MAXN, NAUTYVERSIONID);
    EMPTYGRAPH(g, MAXM, MAXN);

    for (i = 0; i < TN; i++) {
        for (j = 0; j < NORMALS; j++) {
            o = 0;
            for (k = 0; k < N; k++)
                o += normals[j][k] * cards[i][k];
            ADDONEEDGE(g, i, TN + 3*j + PMOD(o, 3), MAXM);
        }
    }

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
}

void orderly(int lvl) {
    if (lvl == MAX_DEPTH) return;

    int i, j, k, l, rep;
    bool seen[TN] = {false}, comp = true;

    tots[lvl] += glf3n_size / grp_size;
    cases[lvl]++;

    for (i = 0; i < TN; i++) {
        rep = orbit[lvl][i];

        // Only consider unique uneliminated orbit representatives 
        if (seen[rep] || elim[rep]) continue;
        seen[rep] = true;
        in_cap[rep] = true;
        comp = false;

        int unelim[TN] = {0};
        
        // Initialize labelling and coloring
        for (j = TN; j < MAXN; j++)
            lab[j] = j;
        for (j = TN; j < MAXN-1; j++)
            ptn[j] = 1;
        ptn[MAXN-1] = 0;
        k = 0;
        for (j = 0; j < TN; j++) {
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

        // TODO alpha invariant optimization
        densenauty(g, lab, ptn, orbit[lvl+1], &options, &stats, MAXM, MAXN, canon);

        // Check if rep is in theta(X + rep)
        for (j = 0; j < TN; j++) {
            if (in_cap[lab[j]]) {
                if (orbit[lvl+1][lab[j]] == orbit[lvl+1][rep]) {
                    printf("%3d: ", lvl + 1);
                    for (k = 0; k < lvl; k++)
                        printf(".");
                    printf("%d\n", rep);
                    orderly(lvl + 1);
                }
                break;
            }
        }

        // Uneliminate cards
        in_cap[rep] = false;
        for (j = 0; unelim[j] && j < TN; j++)
            elim[unelim[j]] = 0;
    }

    if (comp)
        comps[lvl]++;
}

void all_caps() {
    densenauty(g, lab, ptn, orbit[0], &options, &stats, MAXM, MAXN, canon);
    glf3n_size = grp_size;
    orderly(0);
}

int main() {
    clock_t start = clock();

    init();
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