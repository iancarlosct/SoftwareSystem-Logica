# 🧠 LogicTools — Manipulação e Análise de Lógica Proposicional em C

**LogicTools** é um programa em C capaz de:

- Verificar **equivalência lógica** entre duas sentenças (`eq`)
- Converter uma sentença para **Forma Normal Conjuntiva (FNC)** (`cnf`)
- Converter para FND (*se implementado*)
- Remover implicações e bicondicionais
- Aplicar De Morgan e empurrar negações
- Distribuir disjunções sobre conjunções para gerar FNC
- Analisar e montar árvores sintáticas (AST)

O algoritmo é rápido, determinístico e utiliza análise sintática formal + reescrita algébrica de expressões proposicionais.

---

## ✨ Funcionalidades

### ✔️ Equivalência entre expressões (`eq`)
Verifica se duas fórmulas proposicionais são logicamente equivalentes.

### ✔️ Conversão para FNC (`cnf`)
Transforma qualquer sentença proposicional em uma versão equivalente na Forma Normal Conjuntiva.

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

## 📦 Como compilar

Compile usando GCC:

```bash
gcc -O2 logic_tools.c -o logic_tools -lm
