/* logic_tools.c
   Funções:
   - parser de fórmulas proposicionais
   - eliminação de -> e <->, NNF, CNF, DNF
   - SAT solver por backtracking (sem árvore)
   - modos: eq, cnf, dnf, sat
   Sintaxe de fórmula:
     - NOT:  ~
     - AND:  &
     - OR:   |
     - IMPLIES: >
     - BICONDITIONAL: =
     - Parênteses: ()
     - Variáveis: identificadores alfanuméricos (ex: p, q1, x)
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <ctype.h>
#include <math.h>

#define MAXVARS 200
#define MAXCLA 1000
#define MAXLIT 200

/**
 * @param 
 */
typedef struct {
    char name[32];
} VarMapEntry;
static VarMapEntry varmap[MAXVARS];
static int varcount = 0;

int var_index_of(const char *s) {
    for(int i=0;i<varcount;i++) if(strcmp(varmap[i].name,s)==0) return i;
    if(varcount>=MAXVARS) { fprintf(stderr,"Too many variables\n"); exit(1); }
    strcpy(varmap[varcount].name,s);
    return varcount++;
}
const char* var_name(int idx) { return varmap[idx].name; }

/* --- AST --- */
typedef enum { T_VAR, T_NOT, T_AND, T_OR } NodeType;
typedef struct Node {
    NodeType type;
    int var; // if VAR: index
    struct Node *l, *r; // children (r may be NULL for unary)
} Node;

Node* mkvar(int v) {
    Node *n = malloc(sizeof(Node));
    n->type = T_VAR; n->var = v; n->l = n->r = NULL; return n;
}
Node* mkun(NodeType t, Node *a) {
    Node *n = malloc(sizeof(Node)); n->type = t; n->l = a; n->r = NULL; return n;
}
Node* mkbin(NodeType t, Node *a, Node *b) {
    Node *n = malloc(sizeof(Node)); n->type = t; n->l = a; n->r = b; return n;
}
void freetree(Node *n){
    if(!n) return;
    freetree(n->l); freetree(n->r); free(n);
}

/* --- Printing AST --- */
void print_node(Node *n) {
    if(!n) { printf("NULL"); return; }
    if(n->type==T_VAR) { printf("%s", var_name(n->var)); return; }
    if(n->type==T_NOT) { printf("~"); 
        if(n->l->type==T_VAR) print_node(n->l); else { printf("("); print_node(n->l); printf(")"); }
        return;
    }
    printf("(");
    print_node(n->l);
    if(n->type==T_AND) printf(" & ");
    else if(n->type==T_OR) printf(" | ");
    print_node(n->r);
    printf(")");
}

/* --- Parser: Shunting-yard to postfix, then build AST.
   Operators: ~ (unary), & (binary), | (binary), > (implies), = (bicond)
   Precedence: ~ (5, right), & (4, left), | (3, left), > (2, right), = (1, right)
*/
typedef enum { TK_VAR, TK_OP, TK_LP, TK_RP, TK_END } TokType;
typedef struct { TokType type; char op; char sval[32]; } Token;

Token *tokenize(const char *s, int *n_out) {
    Token *toks = malloc(sizeof(Token)*1024);
    int ti=0;
    int i=0; int L=strlen(s);
    while(i<L){
        char c = s[i];
        if(isspace((unsigned char)c)) { i++; continue; }
        if(c=='(') { toks[ti].type=TK_LP; toks[ti++].op='('; i++; continue; }
        if(c==')') { toks[ti].type=TK_RP; toks[ti++].op=')'; i++; continue; }

        // Tratamento para -> e <-> e também para caracteres únicos '>', '='
        if(c=='-') {
            // possivelmente "->"
            if(i+1 < L && s[i+1] == '>') {
                toks[ti].type = TK_OP;
                toks[ti].op = '>'; // usamos '>' internamente para implicação
                ti++; i += 2;
                continue;
            } else {
                fprintf(stderr, "Token error at '-' (expected '->').\n");
                exit(1);
            }
        }
        if(c=='<' ) {
            // possivelmente "<->"
            if(i+2 < L && s[i+1]=='-' && s[i+2]=='>') {
                toks[ti].type = TK_OP;
                toks[ti].op = '='; // usamos '=' internamente para bicondicional
                ti++; i += 3;
                continue;
            } else {
                fprintf(stderr, "Token error at '<' (expected '<->').\n");
                exit(1);
            }
        }

        if(strchr("~&|>=", c)) { toks[ti].type=TK_OP; toks[ti].op=c; ti++; i++; continue; }

        if(isalnum((unsigned char)c) || c=='_') {
            int j=0;
            while(i<L && (isalnum((unsigned char)s[i])||s[i]=='_')) {
                if(j<31) toks[ti].sval[j++]=s[i];
                i++;
            }
            toks[ti].sval[j]=0; toks[ti].type=TK_VAR; ti++; continue;
        }
        fprintf(stderr,"Token error at '%c'\n", c); exit(1);
    }
    toks[ti].type=TK_END; *n_out = ti; return toks;
}

int prec(char op){
    if(op=='~') return 5;
    if(op=='&') return 4;
    if(op=='|') return 3;
    if(op=='>') return 2;
    if(op=='=') return 1;
    return 0;
}
bool right_assoc(char op){
    if(op=='~' || op=='>' || op=='=') return true;
    return false;
}

/* convert to postfix tokens (array of Token) */
Token* to_postfix(Token *toks, int ntoks, int *nout) {
    Token *out = malloc(sizeof(Token)*1024);
    Token opstack[1024]; int os=0; int oi=0;
    for(int i=0;i<ntoks;i++){
        Token tk = toks[i];
        if(tk.type==TK_END) break;
        if(tk.type==TK_VAR) { out[oi++]=tk; continue; }
        if(tk.type==TK_OP){
            char op = tk.op;
            if(op=='~'){ // unary
                // treat like normal operator with precedence
                while(os>0 && ((right_assoc(op)==false && prec(op)<=prec(opstack[os-1].op)) || (right_assoc(op)==true && prec(op)<prec(opstack[os-1].op)))) {
                    out[oi++]=opstack[--os];
                }
                opstack[os++]=tk;
            } else {
                while(os>0 && opstack[os-1].type==TK_OP && 
                      ((right_assoc(op)==false && prec(op)<=prec(opstack[os-1].op)) || (right_assoc(op)==true && prec(op)<prec(opstack[os-1].op)))) {
                    out[oi++]=opstack[--os];
                }
                opstack[os++]=tk;
            }
            continue;
        }
        if(tk.type==TK_LP) { opstack[os++]=tk; continue; }
        if(tk.type==TK_RP) {
            while(os>0 && opstack[os-1].type!=TK_LP) out[oi++]=opstack[--os];
            if(os==0) { fprintf(stderr,"Mismatched parentheses\n"); exit(1); }
            os--; // pop '('
        }
    }
    while(os>0) {
        if(opstack[os-1].type==TK_LP || opstack[os-1].type==TK_RP) { fprintf(stderr,"Mismatched parentheses\n"); exit(1); }
        out[oi++]=opstack[--os];
    }
    Token endtk; endtk.type=TK_END; out[oi++]=endtk; *nout=oi; return out;
}

/* build AST from postfix */
Node* build_ast_from_postfix(Token *post, int n) {
    Node *stack[1024]; int sp=0;
    for(int i=0;i<n;i++){
        Token tk = post[i];
        if(tk.type==TK_END) break;
        if(tk.type==TK_VAR) {
            int vid = var_index_of(tk.sval);
            stack[sp++]=mkvar(vid);
        } else if(tk.type==TK_OP) {
            char op = tk.op;
            if(op=='~') {
                if(sp<1){ fprintf(stderr,"parse error unary\n"); exit(1); }
                Node *a = stack[--sp];
                stack[sp++]=mkun(T_NOT, a);
            } else {
                if(sp<2){ fprintf(stderr,"parse error bin\n"); exit(1); }
                Node *b = stack[--sp]; Node *a = stack[--sp];
                if(op=='&') stack[sp++]=mkbin(T_AND, a, b);
                else if(op=='|') stack[sp++]=mkbin(T_OR, a, b);
                else if(op=='>' || op=='=') {
                    /* keep as markers: we'll eliminate -> and <-> immediately after parsing by rewriting
                       represents op '>' or '=' temporarily by special construction:
                       we will produce trees combining | and & after elimination step */
                    if(op=='>') {
                        // A -> B  === (~A) | B
                        Node *notA = mkun(T_NOT, a);
                        stack[sp++]=mkbin(T_OR, notA, b);
                    } else { // =
                        // A = B === (A->B) & (B->A) => ((~A | B) & (~B | A))
                        Node *notA = mkun(T_NOT, a);
                        Node *notB = mkun(T_NOT, b);
                        Node *imp1 = mkbin(T_OR, notA, b);
                        Node *imp2 = mkbin(T_OR, notB, a);
                        stack[sp++]=mkbin(T_AND, imp1, imp2);
                    }
                } else {
                    fprintf(stderr,"unknown operator %c\n", op); exit(1);
                }
            }
        } else {
            fprintf(stderr,"unexpected token type building AST\n"); exit(1);
        }
    }
    if(sp!=1){ fprintf(stderr,"parse produced %d nodes (expected 1)\n", sp); exit(1); }
    return stack[0];
}

/* Top-level parse */
Node* parse_formula(const char *s) {
    int ntoks;
    Token *toks = tokenize(s, &ntoks);
    int npf;
    Token *post = to_postfix(toks, ntoks, &npf);
    Node *ast = build_ast_from_postfix(post, npf);
    free(toks); free(post);
    return ast;
}

/* --- Transformations: push negations to get NNF --- */
Node* clone(Node *n) {
    if(!n) return NULL;
    Node *x = malloc(sizeof(Node));
    x->type = n->type; x->var = n->var;
    x->l = clone(n->l); x->r = clone(n->r);
    return x;
}

Node* to_nnf(Node *n) {
    if(!n) return NULL;
    if(n->type==T_VAR) return mkvar(n->var);
    if(n->type==T_NOT) {
        Node *c = n->l;
        if(c->type==T_VAR) return mkun(T_NOT, mkvar(c->var));
        if(c->type==T_NOT) {
            // ~~A => A
            return to_nnf(c->l->type==T_VAR ? mkvar(c->l->var) : clone(c->l));
        }
        if(c->type==T_AND) {
            // ~(A & B) => (~A) | (~B)
            Node *na = mkun(T_NOT, clone(c->l));
            Node *nb = mkun(T_NOT, clone(c->r));
            Node *or = mkbin(T_OR, na, nb);
            Node *res = to_nnf(or);
            freetree(or); return res;
        }
        if(c->type==T_OR) {
            // ~(A | B) => (~A) & (~B)
            Node *na = mkun(T_NOT, clone(c->l));
            Node *nb = mkun(T_NOT, clone(c->r));
            Node *andn = mkbin(T_AND, na, nb);
            Node *res = to_nnf(andn);
            freetree(andn); return res;
        }
    }
    // For binary AND/OR nodes
    if(n->type==T_AND) {
        Node *L = to_nnf(n->l);
        Node *R = to_nnf(n->r);
        return mkbin(T_AND, L, R);
    }
    if(n->type==T_OR) {
        Node *L = to_nnf(n->l);
        Node *R = to_nnf(n->r);
        return mkbin(T_OR, L, R);
    }
    // fallback
    return clone(n);
}

/* --- Utilities: flatten associative nodes --- */
void collect_or(Node *n, Node **arr, int *cnt) {
    if(n->type==T_OR) { collect_or(n->l, arr, cnt); collect_or(n->r, arr, cnt); }
    else arr[(*cnt)++] = n;
}
void collect_and(Node *n, Node **arr, int *cnt) {
    if(n->type==T_AND) { collect_and(n->l, arr, cnt); collect_and(n->r, arr, cnt); }
    else arr[(*cnt)++] = n;
}

/* --- Distribute OR over AND to get CNF: (A | (B & C)) => (A|B) & (A|C) --- */
Node* distribute_or(Node *a, Node *b) {
    // base: a OR b, where a and b are NNF
    // if a is AND: (a1 & a2) | b => (a1|b) & (a2|b)
    if(a->type==T_AND) {
        Node *left = distribute_or(a->l, b);
        Node *right = distribute_or(a->r, b);
        return mkbin(T_AND, left, right);
    }
    if(b->type==T_AND) {
        Node *left = distribute_or(a, b->l);
        Node *right = distribute_or(a, b->r);
        return mkbin(T_AND, left, right);
    }
    // otherwise just OR
    return mkbin(T_OR, clone(a), clone(b));
}

Node* to_cnf(Node *n) {
    // n assumed in NNF
    if(n->type==T_VAR || n->type==T_NOT) return clone(n);
    if(n->type==T_AND) {
        Node *L = to_cnf(n->l);
        Node *R = to_cnf(n->r);
        return mkbin(T_AND, L, R);
    }
    if(n->type==T_OR) {
        Node *L = to_cnf(n->l);
        Node *R = to_cnf(n->r);
        Node *res = distribute_or(L, R);
        return res;
    }
    return clone(n);
}

/* --- Distribute AND over OR to get DNF: (A & (B | C)) => (A&B) | (A&C) --- */
Node* distribute_and(Node *a, Node *b) {
    if(a->type==T_OR) {
        Node *left = distribute_and(a->l, b);
        Node *right = distribute_and(a->r, b);
        return mkbin(T_OR, left, right);
    }
    if(b->type==T_OR) {
        Node *left = distribute_and(a, b->l);
        Node *right = distribute_and(a, b->r);
        return mkbin(T_OR, left, right);
    }
    return mkbin(T_AND, clone(a), clone(b));
}

Node* to_dnf(Node *n) {
    if(n->type==T_VAR || n->type==T_NOT) return clone(n);
    if(n->type==T_OR) {
        Node *L = to_dnf(n->l);
        Node *R = to_dnf(n->r);
        return mkbin(T_OR, L, R);
    }
    if(n->type==T_AND) {
        Node *L = to_dnf(n->l);
        Node *R = to_dnf(n->r);
        Node *res = distribute_and(L, R);
        return res;
    }
    return clone(n);
}

/* --- CNF -> clause matrix for SAT solver
   Represent clause matrix as int formula[cla][lit] with:
     0 = literal not present in clause
     1 = positive literal present
    -1 = negative literal present
     2 = tautology marker (clause is tautology)
*/
typedef struct {
    int cla;
    int lit;
    int **mat; // mat[cla][lit]
} FormulaMat;

FormulaMat* alloc_formula(int cla, int lit) {
    FormulaMat *f = malloc(sizeof(FormulaMat));
    f->cla = cla; f->lit = lit;
    f->mat = malloc(sizeof(int*)*cla);
    for(int i=0;i<cla;i++){
        f->mat[i]=malloc(sizeof(int)*lit);
        for(int j=0;j<lit;j++) f->mat[i][j]=0;
    }
    return f;
}
void free_formula(FormulaMat *f){
    for(int i=0;i<f->cla;i++) free(f->mat[i]);
    free(f->mat); free(f);
}

/* Helper: flatten CNF into list of clauses (each clause is OR of literals). 
   CNF is a top-level AND of clauses; each clause is OR of literals/vars.
*/
typedef struct Clause {
    int len;
    int lits[256]; // store as signed ints: positive idx+1 for pos, negative -(idx+1) for neg
} Clause;
typedef struct ClauseList {
    Clause cls[1024];
    int n;
} ClauseList;

void collect_clauses(Node *n, ClauseList *out) {
    if(n->type==T_AND) { collect_clauses(n->l, out); collect_clauses(n->r, out); return; }
    // otherwise this node is a clause (OR of literals)
    Clause c; c.len=0;
    Node *arr[512]; int cnt=0;
    collect_or(n, arr, &cnt);
    bool taut=false;
    for(int i=0;i<cnt;i++){
        Node *lit = arr[i];
        if(lit->type==T_VAR) { c.lits[c.len++] = lit->var+1; }
        else if(lit->type==T_NOT && lit->l->type==T_VAR) { c.lits[c.len++] = -(lit->l->var+1); }
        else {
            // complex literal (e.g., nested). Try evaluate flatten if possible by recursion
            // For safety, fallback: convert literal to string and treat as unique var (not implemented)
            // Simpler: treat as tautology-suspect -> not marking taut, but this simplifies typical cases.
            // In practice our CNF building ensures literals are vars or neg vars.
            ;
        }
    }
    // detect tautology
    for(int i=0;i<c.len;i++){
        for(int j=0;j<c.len;j++){
            if(c.lits[i]==-c.lits[j]) taut=true;
        }
    }
    if(taut){
        // mark a clause as special: we'll set a single entry to 2 later
        Clause t; t.len = -1; out->cls[out->n++] = t;
    } else {
        out->cls[out->n++] = c;
    }
}

/* build matrix */
FormulaMat* cnf_to_matrix(Node *cnf) {
    ClauseList cl; cl.n=0;
    collect_clauses(cnf, &cl);
    int cla = cl.n;
    int lit = varcount;
    FormulaMat *F = alloc_formula(cla, lit);
    for(int i=0;i<cla;i++){
        Clause c = cl.cls[i];
        if(c.len==-1) { // tautology
            for(int j=0;j<lit;j++) F->mat[i][j]=0;
            F->mat[i][0]=2;
            continue;
        }
        for(int j=0;j<lit;j++) F->mat[i][j]=0;
        for(int k=0;k<c.len;k++){
            int v = c.lits[k];
            if(v>0) F->mat[i][v-1]=1;
            else F->mat[i][-v-1] = -1;
        }
    }
    return F;
}

/* --- SAT solver (backtracking on interp[]) ---
   interp values: 0 = unassigned, 1 = true, -1 = false
   Reuse the satisfies() and contradicts() logic from the provided template.
*/
bool satisfies_mat(FormulaMat *F, int interp[]) {
    for(int i=0;i<F->cla;i++){
        bool sat=false;
        for(int j=0;j<F->lit;j++){
            if(F->mat[i][j]==2) { sat=true; break; }
            if(F->mat[i][j]==interp[j] && interp[j]!=0) { sat=true; break; }
        }
        if(!sat) return false;
    }
    return true;
}

bool contradicts_mat(FormulaMat *F, int interp[]) {
    for(int i=0;i<F->cla;i++){
        bool contradicted = true;
        for(int j=0;j<F->lit;j++){
            if(F->mat[i][j]==2) { contradicted=false; break; }
            if(F->mat[i][j]!=0 && interp[j]==0) { contradicted=false; break; }
            if(F->mat[i][j]==interp[j] && interp[j]!=0) { contradicted=false; break; }
        }
        if(contradicted) return true;
    }
    return false;
}

bool sat_backtrack(FormulaMat *F, int interp[], int var_index) {
    if(satisfies_mat(F, interp)) return true;
    if(contradicts_mat(F, interp)) return false;
    if(var_index >= F->lit) return false;
    interp[var_index] = 1;
    if(sat_backtrack(F, interp, var_index+1)) return true;
    interp[var_index] = -1;
    if(sat_backtrack(F, interp, var_index+1)) return true;
    interp[var_index] = 0;
    return false;
}

/* --- Top-level utilities for user commands --- */

/* mode CNF: parse -> NNF -> to_cnf -> print */
void run_cnf(const char *s) {
    varcount=0;
    Node *ast = parse_formula(s);
    Node *nnf = to_nnf(ast);
    Node *cnf = to_cnf(nnf);
    print_node(cnf); printf("\n");
    freetree(ast); freetree(nnf); freetree(cnf);
}

/* mode DNF */
void run_dnf(const char *s) {
    varcount=0;
    Node *ast = parse_formula(s);
    Node *nnf = to_nnf(ast);
    Node *dnf = to_dnf(nnf);
    print_node(dnf); printf("\n");
    freetree(ast); freetree(nnf); freetree(dnf);
}

/* mode SAT: expects CNF input in usual DIMACS-like? We'll accept an arbitrary formula,
   convert to CNF and run solver. */
void run_sat(const char *s) {
    varcount=0;
    Node *ast = parse_formula(s);
    Node *nnf = to_nnf(ast);
    Node *cnf = to_cnf(nnf);
    FormulaMat *F = cnf_to_matrix(cnf);
    int interp[MAXVARS]; for(int i=0;i<MAXVARS;i++) interp[i]=0;
    bool res = sat_backtrack(F, interp, 0);
    if(res) {
        printf("SATISFIABLE\n");
        for(int i=0;i<varcount;i++) if(interp[i]!=0) printf("%s: %d ", var_name(i), interp[i]);
        printf("\n");
    } else {
        printf("UNSATISFIABLE\n");
    }
    free_formula(F);
    freetree(ast); freetree(nnf); freetree(cnf);
}

/* mode EQ: check equivalence of two formulas A and B.
   Build formula NOT(EQUIV(A,B)) => convert to CNF => if unsat then equivalent.
*/
void run_eq(const char *A, const char *B) {
    varcount=0;
    Node *astA = parse_formula(A);
    Node *astB = parse_formula(B);
    // Build (A <-> B) as (A->B) & (B->A) => already handled earlier but let's construct:
    // ( (~A | B) & (~B | A) )
    Node *notA = mkun(T_NOT, clone(astA));
    Node *notB = mkun(T_NOT, clone(astB));
    Node *imp1 = mkbin(T_OR, notA, clone(astB));
    Node *imp2 = mkbin(T_OR, notB, clone(astA));
    Node *equiv = mkbin(T_AND, imp1, imp2);
    Node *neg_equiv = mkun(T_NOT, equiv);
    Node *nnf = to_nnf(neg_equiv);
    Node *cnf = to_cnf(nnf);
    FormulaMat *F = cnf_to_matrix(cnf);
    int interp[MAXVARS]; for(int i=0;i<MAXVARS;i++) interp[i]=0;
    bool is_sat = sat_backtrack(F, interp, 0);
    if(!is_sat) {
        printf("EQUIVALENT\n");
    } else {
        printf("NOT EQUIVALENT (counterexample assignment):\n");
        for(int i=0;i<varcount;i++) if(interp[i]!=0) printf("%s: %d ", var_name(i), interp[i]);
        printf("\n");
    }
    free_formula(F);
    freetree(astA); freetree(astB); freetree(equiv); freetree(neg_equiv); freetree(nnf); freetree(cnf);
}

/* --- main: CLI --- */
void usage(const char *p){
    printf("Usage:\n");
    printf("  %s cnf \"formula\"\n", p);
    printf("  %s dnf \"formula\"\n", p);
    printf("  %s sat \"formula\"      # checks satisfiability by converting to CNF\n", p);
    printf("  %s eq \"formulaA\" \"formulaB\"  # checks equivalence (algebra + SAT)\n", p);
    printf("\nOperators: ~ (not), & (and), | (or), > (implies), = (biconditional)\n");
    printf("Example: %s cnf \"(p & (q | r))\"\n", p);
}

int main(int argc, char **argv) {
    if(argc < 3) { usage(argv[0]); return 1; }
    if(strcmp(argv[1],"cnf")==0 && argc==3) { run_cnf(argv[2]); return 0; }
    if(strcmp(argv[1],"dnf")==0 && argc==3) { run_dnf(argv[2]); return 0; }
    if(strcmp(argv[1],"sat")==0 && argc==3) { run_sat(argv[2]); return 0; }
    if(strcmp(argv[1],"eq")==0 && argc==4) { run_eq(argv[2], argv[3]); return 0; }
    usage(argv[0]); return 1;
}
