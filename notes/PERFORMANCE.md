# Performance Guide

This documents performance issues we have encountered during development and their mitigations.

## Avoid using well-founded recursion

[Well-founded recursion] allows one to write recursive functions that are not structurally
recursive by proving that they are decreasing on some well-founded relation. Lean has special
support for automatically doing these proofs via the equation compiler. However, the resulting
equations are not definitional which precludes using `#reduce` or proofs by reflexivity. See [1]
and [2] for discussions on this topic from the Lean community Zulip chat.

There does not seem to be a general way of disabling well-founded recursion in the equation
compiler. Instead, one must either take care to avoid using it, or explicitly write out the
definition using [`well_founded.Fix`].

### Example 1

Suppose we write the following function in Lean. The author may have intended for it to be defined
via structural recursion on ℕ, but in fact is using well-founded recursion on the length of the
vector argument.

```lean
def bad : ∀ {n : ℕ}, vector bool n → bool
| 0       _ := ff
| (n + 1) v := bad (vector.tail v)
```

One can confirm this with `#print bad._main._pack`, showing the following:

```
def bad._main._pack : Π (_x : Σ' {n : ℕ}, vector bool n), (λ (_x : Σ' {n : ℕ}, vector bool n), bool) _x :=
λ (_x : Σ' {n : ℕ}, vector bool n),
  has_well_founded.wf.fix ... _x
```

A fixed version makes the argument `n` explicit in the recursive call:

```lean
def good : ∀ {n : ℕ}, vector bool n → bool
| 0       v := ff
| (n + 1) v := @good n (vector.tail v)
```

`#print good._main` shows the new definition uses structural recursion (`n.brec_on`):

```
def good._main : Π {n : ℕ}, vector bool n → bool :=
λ {n : ℕ} (ᾰ : vector bool n),
  n.brec_on ᾰ
```

### Example 2

To convert `x` of type `num` to `nat`, we may use:
- coercion `x : nat`, or
- `num.of_nat' x`.

The latter is defined using `nat.binary_rec`, causing performance issues for in-kernel computation.

## Avoid nested inductive types

We tried to use lists in CBC nodes (e.g., AND gates, each of which consists of a list of subnodes, similar to [3]).
Lean produces poor code for nested recursion, which is not suitable for in-kernel comptuation.

[Well-founded recursion]: https://leanprover-community.github.io/extras/well_founded_recursion.html
[1]: https://leanprover-community.github.io/archive/stream/113488-general/topic/semantics.20of.20description.20logics.3A.20binary.20representation.20of.2E.2E.2E.html
[2]: https://leanprover-community.github.io/archive/stream/113489-new-members/topic/defining.20a.20list.20merge.20function.html
[`well_founded.fix`]: https://leanprover-community.github.io/mathlib_docs/init/wf.html#well_founded.fix
[3]: https://leanprover.github.io/theorem_proving_in_lean/inductive_types.html#mutual-and-nested-inductive-types
