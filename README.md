# 🧠 LogicTools — Manipulação e Análise de Lógica Proposicional em C

Aceita:

| Função | Operador(s) aceitos |
|--------|----------------------|
| Negação | `~` |
| Conjunção | `&` |
| Disjunção | `|` |
| Implicação | `->` ou `>` |
| Bicondicional | `<->` ou `=` |
| Agrupamento | `(` `)` |
| Variáveis | `p`, `q`, `A1`, `var_x`, etc |

---

## 📦 Como compilar e executar

Compile usando GCC:

```bash
gcc -O2 logic_tools.c -o logic_tools -lm
```

Execute usando:

Utilize ./logic_tools cnf "Exemplo" para rodar no modo conversão para CNF:
```bash
./logic_tools cnf "(p -> q) & (r | ~s)" 

Saída:
((~p | q) & (r | ~s))
```

Utilize ./logic_tools dnf "Exemplo" para rodar no modo conversão para DNF.
```bash
./logic_tools dnf "~(p & q) | r" 

Saída:
((~p | ~q) | r)
```

Utilize ./logic_tools sat "Exemplo" para rodar no modo Sat Solver.
```bash
./logic_tools sat "(p | q) & (~p | q) & (~q | p)" 

Saída:
SATISFIABLE
p: 1 q: 1 
```

Utilize ./logic_tools eq "Exemplo1" "Exemplo2" para rodar no modo Equivalência.
```bash
./logic_tools eq "p -> q" "~p | q"

Saída:
EQUIVALENT
```
