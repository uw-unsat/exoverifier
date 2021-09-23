import data.unordered_map.basic
import data.unordered_map.trie

open unordered_map

namespace map_test
variables {α : Type} [decidable_eq α] {σ : Type → Type} [d : generic_map α σ]
include d

/- Example functions defined over generic maps. -/

/-- Map nats to strings .-/
def map_nat_to_string (map : σ ℕ) : σ string :=
(λ (x : ℕ), to_string x) <$> map

meta def print_all (map : σ string) : io unit :=
traverse io.print_ln map >> pure ()

/-- Insert four into a map. -/
def insert_four (x : σ ℕ) (k : α) : σ ℕ :=
kinsert k 4 x

/-- Union two maps, using a function `f` to send their values to a common type. -/
def union_with {a b c : Type} [decidable_eq c] (f : (a ⊕ b) → c) (l : σ a) (r : σ b) : option (σ c) :=
let l' : σ c := (λ x, f (sum.inl x)) <$> l,
    r' : σ c := (λ x, f (sum.inr x)) <$> r in
  union₂ l' r'

end map_test

section

def tree1 : trie ℕ :=
kinsert 1 2 $
kinsert 2 3 $
kinsert 3 4 $ empty

def tree2 : trie string :=
kinsert 4 "five" $
kinsert 5 "six" $
kinsert 6 "seven" empty

def f : (ℕ ⊕ string) → string
| (sum.inl x) := to_string x
| (sum.inr x) := x

end
