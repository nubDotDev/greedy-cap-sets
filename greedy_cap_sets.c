/*
A cap set is a subset of Z_3^n with no three elements in a line
(or equivalently, an arithmetic progression).
This is a generalization of the popular card game SET.
The first few maximum cap set sizes are known: 1, 2, 4, 9, 20, 45, 112.
For the rest of the sequence, we have only a bound of b^n where 2.195 <= b <= 2.756.

This program uses a randomized greedy algorithm to find maximal cap sets in n dimensions.
From simple tests, this algorithm seems to have an expected cap set size of about 2.07^n,
but I do not know why yet.
There are also certain sizes that seem to never yield a maximal cap set (e.g. 19 when n=4).
An investigation into what maximal sizes are possible is warranted.
The standard deviation of the set sizes is also surprisingly low.

We define a card to be an element of Z_3^n, and say that card u eliminates card v if
there is a card w in the cap set so far such that (u, v, w) forms a line.
The eliminator relation is therefore symmetric.
In this algorithm, edge (u -> v) means card u is eliminated by card v.
Let third(u, v) be a function that returns the card w such that (u, v, w) forms a line.
Let a_n be the size of a maximum cap set in n dimensions.

Pseudo-code:

initialize 3^n cards and shuffle their order
G = (V, E) where every card corresponds to a node
cap = empty set
while |V| != 0 do                               O(a_n)
    v = node with the smallest in-degree        O(3^n)
    for each c in cap do                        O(a_n)
        delete node third(c, v)                 O(a_n)
    for each node u do                          O(3^n)
        build edge (third(u, v) -> u)           O(1)
    add v to cap                                O(1)
    delete node v                               O(a_n)

Using adjacency lists and in-degree counters, the runtime is O(a_n^3).
*/

#include <limits.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

// Powers of 3: 3, 9, 27, 81, 243, 729, 2187, 6561, 19683
#define n 4  // Number of attributes/dimensions
#define tn 81  // 3^n

#define trials 10000

#define map_size 256

// Element of Z_3^n
typedef char card[n];

// Linked list node
typedef struct list_node_struct {
    int data;
    struct list_node_struct* next;
} list_node;

// Double linked list node
typedef struct dbl_list_node_struct {
    int data;
    struct dbl_list_node_struct* next;
    struct dbl_list_node_struct* prev;
} dbl_list_node;

// Graph node that stores a card, an adjacency list, its in-degree, and if it has been eliminated
typedef struct graph_node_struct {
    card c;
    int in_deg;
    bool is_elim;
    list_node* neighbors;
} graph_node;

int setter[3][3] = {{0, 2, 1}, {2, 1, 0}, {1, 0, 2}};
int known_max[7] = {1, 2, 4, 9, 20, 45, 112};

graph_node nodes[tn];
dbl_list_node graph_list[tn], * graph_head;
int ord[tn];

int cap_set[tn], cap_set_len;

int data_keys[map_size], data_vals[map_size];
int max_cap_set[tn], max_cap_set_len;
int min_cap_set[tn], min_cap_set_len;

int data_get_index(int k) {
    int i;

    // Linear probing
    for (i = k % map_size; data_keys[i] != 0 && data_keys[i] != k; i = (i+1) % map_size) {
        if (i == (k - 1) % map_size) {
            printf("Map overflow!\n");
            return -1;
        }
    }
    if (data_keys[i] == 0)
        data_keys[i] = k;
    return i;
}

// Get data value corresponding to k (defaults to 0)
int data_get(int k) {
    return data_vals[data_get_index(k)];
}

// Set data value associated with k to v (k cannot be 0)
void data_set(int k, int v) {
    data_vals[data_get_index(k)] = v;
}

// Returns the decimal value of a card interpreted in base-3
int card_index(card c) {
    int res = c[n-1], i;
    
    for (i = n-2; i >= 0; i--)
        res = 3 * res + c[i];
    return res;
}

// Returns the index of the card that forms a set with i1 and i2
int third(int i1, int i2) {
    int i;
    card third_card;

    for (i = 0; i < n; i++)
        third_card[i] = setter[nodes[i1].c[i]][nodes[i2].c[i]];
    return card_index(third_card);
}

// Fisher-Yates shuffle
void shuffle(int* a, int l) {
    int i, j, t;

    for (i = l-1; i > 0; i--) {
        j = rand() % (i+1);
        t = a[j];
        a[j] = a[i];
        a[i] = t;
    }
}

// Initializes card vectors
void init() {
    int i = 0, j;
    int count[n] = {0};
    bool done = false;

    srand(time(NULL));

    while (!done) {
        for (j = 0; j < n; j++)
            nodes[i].c[j] = count[j];
        graph_list[i].data = i;
        ord[i] = i;
        i++;
        
        j = 0;
        count[j]++;
        while (count[j] == 3) {
            count[j] = 0;
            j++;
            if (j >= n) {
                done = true;
                break;
            }
            count[j]++;
        }
    }
}

// Resets graph
void reinit() {
    int i;

    graph_head = graph_list;
    cap_set_len = 0;
    
    for (i = 0; i < tn; i++) {
        nodes[i].is_elim = false;
        nodes[i].in_deg = 0;
        nodes[i].neighbors = NULL;

        graph_list[i].prev = i == 0 ? NULL : graph_list + (i-1);
        graph_list[i].next = i == tn-1 ? NULL : graph_list + (i+1);
    }
}

// Eliminates a node and updates the in-degrees of its neighbors
void elim(int i) {
    list_node* curr = nodes[i].neighbors, * prev;
    
    nodes[i].is_elim = true;
    while (curr) {
        nodes[curr->data].in_deg--;
        prev = curr;
        curr = curr->next;
        free(prev);
    }

    if (graph_list[i].prev)
        graph_list[i].prev->next = graph_list[i].next;
    else
        graph_head = graph_list[i].next;
    if (graph_list[i].next)
        graph_list[i].next->prev = graph_list[i].prev;
}

// Builds an edge between from and to
void add_neighbor(graph_node* from, int to_index) {
    list_node* to = (list_node*) malloc(sizeof(list_node));

    to->data = to_index;
    to->next = from->neighbors;
    from->neighbors = to;
    nodes[to_index].in_deg++;
}

void maximal_cap_set() {
    int i, o, best_count, best_index, to_elim, left = tn;
    dbl_list_node* curr;

    reinit();
    shuffle(ord, tn);
    while (left > 0) {
        // Find card that eliminates the fewest new cards
        best_count = INT_MAX;
        best_index = -1;
        for (i = 0; i < tn; i++) {
            o = ord[i];
            if (!nodes[o].is_elim && nodes[o].in_deg < best_count) {
                best_count = nodes[o].in_deg;
                best_index = o;
            }
        }

        // Eliminate cards that form a line with the card at best_index
        // and some other card in the cap set so far
        elim(best_index);
        left--;
        for (i = 0; i < cap_set_len; i++) {
            to_elim = third(best_index, cap_set[i]);
            if (!nodes[to_elim].is_elim) {
                elim(to_elim);
                left--;
            }
        }

        // Update eliminators/adjacency
        curr = graph_head;
        while (curr) {
            to_elim = third(best_index, curr->data);
            if (!nodes[to_elim].is_elim)
                add_neighbor(nodes + to_elim, curr->data);
            curr = curr->next;
        }

        cap_set[cap_set_len] = best_index;
        cap_set_len++;
    }
}

void run_trials() {
    int i;

    max_cap_set_len = 0;
    min_cap_set_len = INT_MAX;
    for (i = 0; i < trials; i++) {
        maximal_cap_set();
        data_set(cap_set_len, data_get(cap_set_len) + 1);
        if (cap_set_len > max_cap_set_len) {
            memcpy(max_cap_set, cap_set, tn * sizeof(int));
            max_cap_set_len = cap_set_len;
        }
        if (cap_set_len < min_cap_set_len) {
            memcpy(min_cap_set, cap_set, tn * sizeof(int));
            min_cap_set_len = cap_set_len;
        }
    }
}

void print_cap_set(int* cs, int csl) {
    int i, j;

    for (i = 0; i < csl; i++) {
        printf("(");
        for (j = 0; j < n; j++) {
            printf(j == n-1 ? "%d" : "%d, " , nodes[cs[i]].c[j]);
        }
        printf(i == csl - 1 ? ") " : "), ");
    }
    printf("[Length %d]\n", csl);
}

int main() {
    int i, sum = 0, max_occur = 0;
    char fname[100];
    FILE* fptr;
    clock_t start;

    printf("===== Maximal Cap Set (n=%d) =====\n", n);

    printf("Initializing...\n");
    init();

    printf("Starting %d trials...\n", trials);
    start = clock();
    run_trials();
    printf("Trials complete! (Time elapsed: %.5fs)\n", (double) (clock() - start) / CLOCKS_PER_SEC);

    printf("Smallest cap set found: %d\n", min_cap_set_len);
    printf("Largest cap set found: %d\n", max_cap_set_len);

    for (i = 0; i < map_size; i++) {
        sum += data_keys[i] * data_vals[i];
        if (n < 7 && data_keys[i] == known_max[n])
            max_occur += data_vals[i];
    }
    printf("Number of maximum cap sets: %d (probability %.5f)\n", max_occur, (float) max_occur / trials);
    printf("Average cap set size: %.5f\n", (float) sum / trials);

    snprintf(fname, 100, "data/n%d_t%d.txt", n, trials);
    fptr = fopen(fname, "w");
    for (i = 0; i < map_size; i++)
        if (data_keys[i] != 0)
            fprintf(fptr, "%d: %d\n", data_keys[i], data_vals[i]);
    fclose(fptr);
}