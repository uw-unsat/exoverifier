/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import logic.relation
import data.num.basic
import misc.semidecision

namespace compiler

-- Trees are either and of two trees or leaf. All nodes have a pos_num label.
@[derive [decidable_eq, inhabited]]
inductive tree : Type
| leaf : pos_num → tree
| and : pos_num → tree → tree → tree

-- Get label of the root node of a tree.
def label : tree → pos_num
| (tree.leaf l) := l
| (tree.and l _ _) := l

-- Reflexive-transitive closure of child relationship between trees.
inductive child : tree → tree → Prop
| and_l : ∀ p x l r, child x l → child x (tree.and p l r)
| and_r : ∀ p x l r, child x r → child x (tree.and p l r)
| refl : ∀ l, child l l

-- A child of a leaf must be the leaf itself.
lemma child_of_leaf (x : tree) (l : pos_num) (h : child x (tree.leaf l)) :
  x = tree.leaf l :=
begin
  generalize e : (tree.leaf l) = z,
  rw e at h,
  induction h,
  contradiction,
  contradiction,
  refl,
end

-- x is unique in y iff all children of y with the same label of x are structurally equal to x.
def unique (x : tree) : tree → Prop :=
  λ (y : tree),
    ∀ (z : tree),
      child z y →
      label x = label z →
      x = z

-- Given that tree x is unique in trees l and r, x is also unique in (and p l r)
-- if either the label of x is distinct from p, or x is structurally eq to (and p l r)
lemma unique_of_unique_children (x l r : tree) (p : pos_num) :
  unique x l →
  unique x r →
  (p ≠ label x ∨ x = tree.and p l r) →
  unique x (tree.and p l r) :=
begin
  intros hl hr heq z ch,
  generalize we : (tree.and p l r) = w,
  rw we at ch,
  revert we heq hl hr p x l r,
  induction ch with _ _ _ _ ch ih1 ih2; intros _ _ _ _ _ _ _ _ leq,
  { cases we, clear we,
    apply hl,
    assumption, assumption,
  },
  { cases we, clear we,
    apply hr,
    assumption, assumption,
  },
  { cases heq,
    swap, cc,
    subst we,
    simp only [label] at leq,
    subst leq, contradiction,
  },
end

-- unique x y is semidecision, by comparing x against each node in y.
def dec_unique (x : tree) : ∀ (y : tree), semidecision (unique x y)
| (tree.leaf l) :=
  if h : (l ≠ label x) ∨ (x = tree.leaf l)
  then semidecision.is_true (by {
    intros z ch h2,
    have : z = tree.leaf l, by apply child_of_leaf; assumption,
    subst this,
    simp only [label] at *,
    subst h2,
    cases h,
    contradiction,
    from h,
  })
  else semidecision.unknown
| (tree.and p l r) :=
  match dec_unique l, dec_unique r with
  | semidecision.is_true h1, semidecision.is_true h2 :=
    if h : (p ≠ label x) ∨ (x = (tree.and p l r))
    then semidecision.is_true (by {
      apply unique_of_unique_children; assumption,
    })
    else semidecision.unknown
  | _, _ := semidecision.unknown
  end

-- all_unique x y means all of x's children are unique in y.
def all_unique (x y : tree) : Prop :=
  ∀ (z : tree),
    child z x →
    unique z y

-- all_unique x y is semidecision by checking if each child of x is unique in y,
-- using semidecidability of unique.
def dec_all_unique (y : tree) : ∀ (x : tree), semidecision (all_unique x y)
| (tree.leaf p) :=
  match dec_unique (tree.leaf p) y with
  | semidecision.is_true h := semidecision.is_true (by {
      intros z ch1 w ch2 leq,
      rw child_of_leaf _ _ ch1 at *,
      apply h, assumption, assumption,
    })
  | _ := semidecision.unknown
  end
| (tree.and p l r) :=
  match dec_unique (tree.and p l r) y, dec_all_unique l, dec_all_unique r with
  | semidecision.is_true h1, semidecision.is_true h2, semidecision.is_true h3 := semidecision.is_true (by {
      intros z ch,
      cases ch,
      apply h2,
      assumption,
      apply h3,
      assumption,
      assumption,
    })
  | _, _, _ := semidecision.unknown
  end

-- A tree is wellformed iff all of its subchildren are unique in itself.
def wf (t : tree) := all_unique t t

-- wf is semidecision by the fact that all_unique is.
def dec_wf (t : tree) : semidecision (wf t) := dec_all_unique t t

section example_

-- construct a simple tree
def x : tree := (tree.and 1 (tree.leaf 2) (tree.leaf 3))

-- construct another tree reusing x
def y : tree := (tree.and 4 x x)

-- dec_wf says y is well-formed
-- #eval (dec_wf y).to_bool

-- Here's hwo to turn dec_wf y into an actual proof of wf y
example : wf y := semidec_trivial (dec_wf _)

-- bad x reuses label 1 without being structurally equal
def bad_x : tree := (tree.and 1 (tree.leaf 4) (tree.leaf 5))

-- bad y uses bad_x and x
def bad_y : tree := (tree.and 6 bad_x x)

-- says unknown (since it's not well-formed)
-- #eval (dec_wf bad_y).to_bool

end example_


-- Axiom for faster equality checking. Cannot use them yet
-- since there's no computation backing it.
--
-- constant physEq :
--   ∀ {α : Type} {β : α → α → Type}
--     (eq : ∀ (x y : α), x = y → β x y)
--     (neq : ∀ (x y : α), β x y)
--     (H : ∀ x y (h : x = y), eq x y h = neq x y) (x y : α),
--     β x y

-- noncomputable def physEqInstance (α : Type) [h : decidable_eq α] : decidable_eq α :=
--   @physEq α (λ a b, decidable (a = b))
--   (λ x y, decidable.is_true)
--   h
--   (by {
--     intros x y h, subst h, simp only,
--     cases (h x x),
--     contradiction,
--     refl,
--   })

-- Spec algorithm: brute force recursion of compiling a tree to string.
def spec : tree → string
| (tree.leaf p) := repr p
| (tree.and p x y) := "(and " ++ repr p ++ " " ++ spec x ++ " " ++ spec y ++ ")"

-- Optimized implementation will use a cache from id to string result.
def cache : Type := pos_num → option string

-- Add cache entry p -> s
def add (p : pos_num) (s : string) : state cache unit :=
  do  h ← get,
      put $ λ x, if x = p then some s else (h x)

-- Try to get the cache result associated with id p.
def try_get (p : pos_num) : state cache (option string) :=
  do  h ← get,
      match (h p) with
      | none := pure none
      | (some x) := pure x
      end

-- Smarter implementation: caches results to avoid duplicating work.
def impl : tree → state cache string
| (tree.leaf p) := pure $ repr p
| (tree.and p x y) :=
  do cached ← try_get p,
     match cached with
     | (some x) := pure x
     | none :=
       do l ← impl x,
          r ← impl y,
          let result := "(and " ++ repr p ++ " " ++ l ++ " " ++ r ++ ")"
          in do add p result,
                pure result
     end

-- For all children of t, cache is correct for t
def invariant (s : cache) (t : tree) : Prop :=
  ∀ (z : tree) (cached_result : string),
    child z t →
    s (label z) = some cached_result →
    spec z = cached_result

def child_of_and_left (p : pos_num) (l r o : tree) :
  child (tree.and p l r) o →
  child l o :=
begin
  intro h,
  generalize heq : (tree.and p l r) = z,
  rw heq at h,
  revert heq,
  induction h; intros; subst heq,
  apply child.and_l,
  apply h_ih, refl,
  apply child.and_r,
  apply h_ih, refl,
  constructor,
  constructor,
end

def child_of_and_right (p : pos_num) (l r o : tree) :
  child (tree.and p l r) o →
  child r o :=
begin
  intro h,
  generalize heq : (tree.and p l r) = z,
  rw heq at h,
  revert heq,
  induction h; intros; subst heq,
  apply child.and_l,
  apply h_ih, refl,
  apply child.and_r,
  apply h_ih, refl,
  apply child.and_r,
  apply child.refl,
end

-- Given some outer tree o and current tree t, if o is well-formed
-- and t is a child of o and the invariant holds for o,
-- then running the smart impl for t yields a cache that still
-- maintains the invariant and produces a correct result w.r.t. the spec.
lemma impl_correct' :
  ∀ (t o : tree) (res : string) (s s' : cache),
    wf o →
    child t o →
    invariant s o →
    (impl t).run s = (res, s') →
    invariant s' o ∧ spec t = res :=
begin
  intros t,
  induction t with p p l r ih1 ih2; intros o res s s' wf_o child_t_o inv_s_o imp,
  { simp only [impl] at imp,
    injection imp,
    subst_vars,
    split, assumption,
    refl,
  },
  { simp only [impl, try_get, get, state_t.run_bind, monad_state.lift, state_t.get, id.pure_eq, id.bind_eq] at imp,
    cases hit : (s p),
    { rw hit at imp,
      simp only [try_get._match_1, impl._match_1, id.pure_eq, state_t.run_pure, state_t.run_bind] at imp,
      cases impl_l : (impl l).run s with res_l s_l,
      rw impl_l at imp,
      simp only [id.bind_eq] at imp,
      cases impl_r : (impl r).run s_l with res_r s_r,
      rw impl_r at imp,
      injection imp,
      clear imp,
      specialize (ih1 o _ _ _ wf_o _ inv_s_o impl_l),
      { apply child_of_and_left; assumption },
      cases ih1 with ih1l ih1r,
      subst ih1r,
      specialize (ih2 o _ _ _ wf_o _ ih1l impl_r),
      { apply child_of_and_right; assumption },
      cases ih2 with ih2l ih2r,
      subst ih2r,
      split, swap,
      subst h_1,
      refl,
      simp [add] at h_2,
      cases h_2,
      clear h_2,
      clear h_1,
      { intros z cached_result ch_z_o cache_eq,
        simp at cache_eq,
        split_ifs at cache_eq,
        subst cache_eq,
        suffices : (tree.and p l r) = z,
        subst this,
        refl,
        apply wf_o,
        from child_t_o,
        from ch_z_o,
        rw ← h, refl,
        apply ih2l,
        from ch_z_o,
        from cache_eq,
      },
    },
    { rw hit at imp,
      simp [try_get._match_1] at imp,
      injection imp, subst_vars,
      split,
      assumption,
      apply inv_s_o,
      exact child_t_o,
      exact hit,
    },
  },
end

-- specialize impl_correct' for the initial state.
theorem impl_correct (t : tree) (res : string) {s : cache} :
  wf t →
  (impl t).run (λ _, none) = (res, s) →
  spec t = res :=
begin
  intros w h,
  cases (impl_correct' t t res (λ _, none) s _ _ _ _),
  from right,
  from w,
  constructor,
  intros a b c d,
  contradiction,
  assumption,
end

namespace example_

def mytree : tree := tree.and 1 (tree.and 2 (tree.leaf 3) (tree.leaf 4)) (tree.and 2 (tree.leaf 3) (tree.leaf 4))

def fast_result : string := ((impl mytree).run (λ _, none)).1

-- could use refl here: but that will invoke spec and be slow (in theory)
example : spec mytree = fast_result := impl_correct mytree fast_result (semidec_trivial (dec_wf _)) (by refl)

end example_

end compiler
