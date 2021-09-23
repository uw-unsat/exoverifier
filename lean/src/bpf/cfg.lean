/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic
import data.unordered_map.basic
import data.unordered_map.alist
import data.unordered_map.trie
import data.list.sort

/-!
# Control-flow graphs of BPF programs

This file contains a representation of BPF programs that is more amenable to automated reasoning.
Rather than raw BPF which is a "flat" list of instructions, this representation treats the program
as a map from (abstract) labels to instructions, and arithmetic jump offsets etc. have been
replaced by the label of the jump target.
-/

namespace bpf
namespace cfg

section syntax

/-- An abstraction of BPF instructions where instructions contain the label of the next instruction to execute. -/
@[derive [decidable_eq, inhabited, has_reflect]]
inductive instr (α : Type*)
| ALU64_X : ALU → reg → reg → α → instr
| ALU64_K : ALU → reg → lsbvector 64 → α → instr
| JMP_X   : JMP → reg → reg → α → α → instr
| JMP_K   : JMP → reg → lsbvector 64 → α → α → instr
| Exit    : instr

namespace instr
variable {α : Type*}

private def repr' [has_repr α] : instr α → string
| (ALU64_X op dst src next)          := "ALU64_X(" ++ repr op ++ ", " ++ repr dst ++ ", " ++ repr src ++ ", " ++ repr next ++ ")"
| (ALU64_K op dst imm next)          := "ALU64_K(" ++ repr op ++ ", " ++ repr dst ++ ", " ++ repr imm ++ ", " ++ repr next ++ ")"
| (JMP_X op r1 r2 if_true if_false)  := "JMP_X(" ++ repr op ++ ", " ++ repr r1 ++ ", " ++ repr r2 ++ ", " ++ repr if_true ++ ", " ++ repr if_false ++ ")"
| (JMP_K op r1 imm if_true if_false) := "JMP_K(" ++ repr op ++ ", " ++ repr r1 ++ ", " ++ repr imm ++ ", " ++ repr if_true ++ ", " ++ repr if_false ++ ")"
| Exit                               := "Exit()"

instance [has_repr α] : has_repr (instr α) := ⟨repr'⟩

end instr

/-- A CFG is an abstraction of a program which maps addresses to (optional) instructions. -/
@[derive [has_reflect, inhabited]]
structure CFG (χ α : Type*) [unordered_map α (instr α) χ] :=
(entry : α)
(code  : χ)

instance (χ : Type*) [unordered_map pos_num (instr pos_num) χ] :
  has_repr (CFG χ pos_num) :=
⟨λ x,
  let l : list (Σ (_ : pos_num), instr pos_num) := unordered_map.to_list x.code,
      l' := list.merge_sort (λ (x y : Σ (_ : pos_num), instr pos_num), x.1 ≤ y.1) l in
    repr (x.entry, l') ⟩

/-- An implementation of CFG using pos_num as label and trie as map. -/
abbreviation trie_program : Type := CFG (trie (instr pos_num)) pos_num

namespace trie_program

private def of_list_aux : trie (instr pos_num) → pos_num → list (instr pos_num) → trie (instr pos_num)
| tr _ []         := tr
| tr n (hd :: tl) := of_list_aux (tr.kinsert n hd) n.succ tl

/-- Turn a list into a trie_program -/
def of_list (l : list (instr pos_num)) : trie_program :=
⟨1, of_list_aux trie.nil 1 l⟩

private def vector_to_num {n : ℕ} (v : vector bool n) : num :=
v.1.foldl (λ acc x, if x then acc.bit1 else acc.bit0) 0

/-- Vector to signed integer. Assume MSB at index 0. -/
private def vector_to_znum {n : ℕ} (v : vector bool (n + 1)) : znum :=
let x : znum := ↑(vector_to_num v.tail) in
if v.head then (x - 2^n) else x

/--
Convert a bitvector jump offset to an absolute `num` target.
First, convert `off` into signed `znum` representing the offset.
Then, add 1 since jump offsets in BPF are relative to the instruction following the jump.
Then, add the index of the current instruction. Because the actual program counter is a 32-bit
int (not an unbounded `num`), take the value mod 2^32 and use `abs` to convert `znum` → `num`.

TODO: write a semantics for the lower-level BPF instructions so that this function no longer
need be trusted.
-/
private def jump_off_to_jump_target (cur : num) (off : msbvector 16) : num :=
((vector_to_znum off + 1 + ↑cur) % (2^32 : znum)).abs

/--
Decode the immediate in the low-level BPF format into the high-level format.
Takes as input a 32-bit immediate encoded MSB first, sign extends it to 64-bits, and reverses
the result to obtain an LSB first representation.
-/
private def msb_imm32_sext_to_lsb_imm64 (v : msbvector 32) : lsbvector 64 :=
vector.append v.reverse (vector.repeat v.head 32)

/--
Insert a low-level instruction at index `cur` into the trie representing the BPF program's CFG.
Sign-extends immediates and converts to LSB-first form, rewrites relative jump targets into
absolute jump targets. Because jump target arithmetic uses `num`, and trie uses `pos_num` as keys,
use the injective function `num.succ'` everywhere that we need a key to the trie.
-/
private def decode_flat_instr (cur : num) (pr : trie (instr pos_num)) : bpf.instr → trie (cfg.instr pos_num)
| (bpf.instr.ALU64_X op dst src) :=
  pr.kinsert cur.succ' (instr.ALU64_X op dst src (cur + 1).succ')
| (bpf.instr.ALU64_K op dst imm) :=
  let imm64 := msb_imm32_sext_to_lsb_imm64 imm in
  pr.kinsert cur.succ' (instr.ALU64_K op dst imm64 (cur + 1).succ')
| (bpf.instr.JMP_X op dst src off) :=
  let target : num := jump_off_to_jump_target cur off in
  pr.kinsert cur.succ' (instr.JMP_X op dst src target.succ' (cur + 1).succ')
| (bpf.instr.JMP_K op dst imm off) :=
  let target : num := jump_off_to_jump_target cur off,
      imm64 := msb_imm32_sext_to_lsb_imm64 imm in
    pr.kinsert cur.succ' (instr.JMP_K op dst imm64 target.succ' (cur + 1).succ')
| (bpf.instr.Exit) := pr.kinsert cur.succ' instr.Exit

private def decode_from_flat_aux : list bpf.instr → num → trie (instr pos_num) → trie (cfg.instr pos_num)
| []         cur pr := pr
| (hd :: tl) cur pr := decode_from_flat_aux tl cur.succ $ decode_flat_instr cur pr hd

def decode_from_flat (l : list bpf.instr) : trie_program :=
⟨1, decode_from_flat_aux l 0 trie.nil⟩

end trie_program
end syntax

section semantics
variables {α χ : Type*} [unordered_map α (instr α) χ]

@[derive [decidable_eq]]
inductive state (α : Type*)
| running : Π (pc : α) (regs : reg → i64), state
| exited  : Π (return : i64), state

instance : inhabited (state α) := ⟨state.exited 0⟩

open unordered_map
variable [decidable_eq α]

@[mk_iff]
inductive step (cfg : CFG χ α) : state α → state α → Prop
| ALU64_X :
  ∀ {pc : α} {regs : reg → i64} {op : ALU} {dst src : reg} {v : i64} {next : α},
    lookup pc cfg.code = some (instr.ALU64_X op dst src next) →
    ALU.ALU_check op (regs dst) (regs src) = tt →
    ALU.doALU op (regs dst) (regs src) = v →
    step (state.running pc regs) (state.running next (function.update regs dst v))
| ALU64_K :
  ∀ {pc : α} {regs : reg → i64} {op : ALU} {dst : reg} {imm : lsbvector 64} {v : i64} {next : α},
    lookup pc cfg.code = some (instr.ALU64_K op dst imm next) →
    ALU.ALU_check op (regs dst) imm.nth = tt →
    ALU.doALU op (regs dst) imm.nth = v →
    step (state.running pc regs) (state.running next (function.update regs dst v))
| JMP_X :
  ∀ {pc : α} {regs : reg → i64} {op : JMP} {r₁ r₂ : reg} {c : bool} {if_true if_false : α},
    lookup pc cfg.code = some (instr.JMP_X op r₁ r₂ if_true if_false) →
    c = JMP.doJMP op (regs r₁) (regs r₂) →
    step (state.running pc regs) (state.running (if c then if_true else if_false) regs)
| JMP_K :
  ∀ {pc : α} {regs : reg → i64} {op : JMP} {r₁ : reg} {imm : lsbvector 64} {c : bool} {if_true if_false : α},
    lookup pc cfg.code = some (instr.JMP_K op r₁ imm if_true if_false) →
    c = JMP.doJMP op (regs r₁) imm.nth →
    step (state.running pc regs) (state.running (if c then if_true else if_false) regs)
| Exit :
  ∀ {pc : α} {regs : reg → i64},
    lookup pc cfg.code = some instr.Exit →
    step (state.running pc regs) (state.exited $ regs reg.R0)

theorem do_step_alu64_x {cfg : CFG χ α} :
  ∀ {pc regs op dst src next},
    lookup pc cfg.code = some (instr.ALU64_X op dst src next) →
    ∀ {s : state α},
      step cfg (state.running pc regs) s →
      s = state.running next (function.update regs dst (ALU.doALU op (regs dst) (regs src))) :=
begin
  intros _ _ _ _ _ _ fetch _ step₁,
  cases step₁,
  case ALU64_X : _ _ _ _ _ _ _ fetch' {
    rw [fetch] at fetch',
    cases fetch',
    subst_vars },
  case ALU64_K : _ _ _ _ _ _ _ fetch' {
    rw [fetch] at fetch',
    cases fetch' },
  case JMP_X : _ _ _ _ _ _ _ _ fetch' {
    rw [fetch] at fetch',
    cases fetch' },
  case JMP_K : _ _ _ _ _ _ _ _ fetch' {
    rw [fetch] at fetch',
    cases fetch' },
  case Exit : _ _ fetch' {
    rw [fetch] at fetch',
    cases fetch' },
end

theorem step_alu64_x_det {cfg : CFG χ α} :
  ∀ {pc regs op dst src next},
    lookup pc cfg.code = some (instr.ALU64_X op dst src next) →
    set.subsingleton (step cfg (state.running pc regs)) :=
begin
  intros _ _ _ _ _ _ fetch s₁ step₁ s₂ step₂,
  rw [do_step_alu64_x fetch step₁, do_step_alu64_x fetch step₂]
end

theorem do_step_alu64_k {cfg : CFG χ α} :
  ∀ {pc regs op dst imm next},
    lookup pc cfg.code = some (instr.ALU64_K op dst imm next) →
    ∀ {s : state α},
      step cfg (state.running pc regs) s →
      s = state.running next (function.update regs dst (ALU.doALU op (regs dst) imm.nth)) :=
begin
  intros _ _ _ _ _ _ fetch _ step₁,
  cases step₁,
  case ALU64_X : _ _ _ _ _ _ _ fetch' {
    rw [fetch] at fetch',
    cases fetch' },
  case ALU64_K : _ _ _ _ _ _ _ fetch' {
    rw [fetch] at fetch',
    cases fetch',
    subst_vars },
  case JMP_X : _ _ _ _ _ _ _ _ fetch' {
    rw [fetch] at fetch',
    cases fetch' },
  case JMP_K : _ _ _ _ _ _ _ _ fetch' {
    rw [fetch] at fetch',
    cases fetch' },
  case Exit : _ _ fetch' {
    rw [fetch] at fetch',
    cases fetch' },
end

theorem step_alu64_k_det {cfg : CFG χ α} :
  ∀ {pc regs op dst imm next},
    lookup pc cfg.code = some (instr.ALU64_K op dst imm next) →
    set.subsingleton (step cfg (state.running pc regs)) :=
begin
  intros _ _ _ _ _ _ fetch s₁ step₁ s₂ step₂,
  rw [do_step_alu64_k fetch step₁, do_step_alu64_k fetch step₂]
end

theorem do_step_jmp_x {cfg : CFG χ α} :
  ∀ {pc regs op r₁ r₂ if_true if_false},
    lookup pc cfg.code = some (instr.JMP_X op r₁ r₂ if_true if_false) →
    ∀ {s : state α},
      step cfg (state.running pc regs) s →
      s = state.running (if JMP.doJMP op (regs r₁) (regs r₂) then if_true else if_false) regs :=
begin
  intros _ _ _ _ _ _ _ fetch _ step₁,
  cases step₁,
  case ALU64_X : _ _ _ _ _ _ _ fetch' {
    rw [fetch] at fetch',
    cases fetch' },
  case ALU64_K : _ _ _ _ _ _ _ fetch' {
    rw [fetch] at fetch',
    cases fetch' },
  case JMP_X : _ _ _ _ _ _ _ _ fetch' {
    rw [fetch] at fetch',
    cases fetch',
    subst_vars },
  case JMP_K : _ _ _ _ _ _ _ _ fetch' {
    rw [fetch] at fetch',
    cases fetch' },
  case Exit : _ _ fetch' {
    rw [fetch] at fetch',
    cases fetch' },
end

theorem step_jmp_x_det {cfg : CFG χ α} :
  ∀ {pc regs op r₁ r₂ if_true if_false},
    lookup pc cfg.code = some (instr.JMP_X op r₁ r₂ if_true if_false) →
    set.subsingleton (step cfg (state.running pc regs)) :=
begin
  intros _ _ _ _ _ _ _ fetch s₁ step₁ s₂ step₂,
  rw [do_step_jmp_x fetch step₁, do_step_jmp_x fetch step₂]
end

theorem do_step_jmp_k {cfg : CFG χ α} :
  ∀ {pc regs op r₁ imm if_true if_false},
    lookup pc cfg.code = some (instr.JMP_K op r₁ imm if_true if_false) →
    ∀ {s : state α},
      step cfg (state.running pc regs) s →
      s = state.running (if JMP.doJMP op (regs r₁) imm.nth then if_true else if_false) regs :=
begin
  intros _ _ _ _ _ _ _ fetch _ step₁,
  cases step₁,
  case ALU64_X : _ _ _ _ _ _ _ fetch' {
    rw [fetch] at fetch',
    cases fetch' },
  case ALU64_K : _ _ _ _ _ _ _ fetch' {
    rw [fetch] at fetch',
    cases fetch' },
  case JMP_X : _ _ _ _ _ _ _ _ fetch' {
    rw [fetch] at fetch',
    cases fetch' },
  case JMP_K : _ _ _ _ _ _ _ _ fetch' {
    rw [fetch] at fetch',
    cases fetch',
    subst_vars },
  case Exit : _ _ fetch' {
    rw [fetch] at fetch',
    cases fetch' },
end

theorem step_jmp_k_det {cfg : CFG χ α} :
  ∀ {pc regs op r₁ imm if_true if_false},
    lookup pc cfg.code = some (instr.JMP_K op r₁ imm if_true if_false) →
    set.subsingleton (step cfg (state.running pc regs)) :=
begin
  intros _ _ _ _ _ _ _ fetch s₁ step₁ s₂ step₂,
  rw [do_step_jmp_k fetch step₁, do_step_jmp_k fetch step₂]
end

theorem do_step_exit {cfg : CFG χ α} :
  ∀ {pc regs},
    lookup pc cfg.code = some instr.Exit →
    ∀ {s : state α},
      step cfg (state.running pc regs) s →
      s = state.exited (regs reg.R0) :=
begin
  intros _ _ fetch _ step₁,
  cases step₁,
  case ALU64_X : _ _ _ _ _ _ _ fetch' {
    rw [fetch] at fetch',
    cases fetch' },
  case ALU64_K : _ _ _ _ _ _ _ fetch' {
    rw [fetch] at fetch',
    cases fetch' },
  case JMP_X : _ _ _ _ _ _ _ _ fetch' {
    rw [fetch] at fetch',
    cases fetch' },
  case JMP_K : _ _ _ _ _ _ _ _ fetch' {
    rw [fetch] at fetch',
    cases fetch' },
  case Exit : _ _ fetch' {
    rw [fetch] at fetch' },
end

theorem step_exit_det {cfg : CFG χ α} :
  ∀ {pc regs},
    lookup pc cfg.code = some instr.Exit →
    set.subsingleton (step cfg (state.running pc regs)) :=
begin
  intros _ _ fetch s₁ step₁ s₂ step₂,
  rw [do_step_exit fetch step₁, do_step_exit fetch step₂]
end

theorem running_backwards (cfg : CFG χ α) (s : state α) :
  ∀ pc regs,
  step cfg s (state.running pc regs) →
  ∃ pc' regs',
    s = state.running pc' regs' :=
begin
  intros _ _ step,
  cases step; tauto
end

inductive initial_state (cfg : CFG χ α) : state α → Prop
| intro :
  ∀ (regs : reg → i64),
    initial_state (state.running (CFG.entry cfg) regs)

@[reducible]
def star (cfg : CFG χ α) : state α → state α → Prop :=
relation.refl_trans_gen (step cfg)

/-- A Safe state either can take an additional step or has exited. -/
def safe_state (cfg : CFG χ α) (s : state α) : Prop :=
(∃ s', step cfg s s') ∨
(∃ r, s = state.exited r)

/--
A cfg is safe from some state `s` iff all states reachable from `s` are safe states.
-/
def safe_from_state (cfg : CFG χ α) (s : state α) : Prop :=
∀ s',
  star cfg s s' →
  safe_state cfg s'

def safe_with_regs (cfg : CFG χ α) (regs : reg → i64) : Prop :=
safe_from_state cfg (state.running cfg.entry regs)

/-- A cfg being safe is defined as all states reachable from all initial states being safe. -/
def safe (cfg : CFG χ α) : Prop :=
∀ (s : state α),
  initial_state cfg s →
  safe_from_state cfg s

/-- A program is safe iff it is safe with all initial registers. -/
theorem safe_iff_safe_with_all_regs {cfg : CFG χ α} :
  safe cfg ↔ (∀ r, safe_with_regs cfg r) :=
begin
  split,
  { intros s r,
    specialize s (state.running cfg.entry r) _,
    constructor,
    apply s },
  { intros h₁ s s_init,
    cases s_init,
    apply h₁ },
end

/--
All states reachable from an exited state are safe.
-/
theorem safe_from_exited {cfg : CFG χ α} {r : i64} :
  safe_from_state cfg (state.exited r) :=
begin
  generalize exited : state.exited r = s',
  intros s' star₁,
  induction star₁ using relation.refl_trans_gen.head_induction_on,
  { right,
    tauto },
  { subst exited,
    cases star₁_h' }
end

/--
If s is a safe state, and, for all states reachable in one step from s,
all states reachable from those states are safe, then all states reachable
from s are safe as well.
-/
theorem safe_from_state_of_all_steps_safe {cfg : CFG χ α} {s : state α} :
  safe_state cfg s →
  (∀ (s' : state α), step cfg s s' → safe_from_state cfg s') →
  safe_from_state cfg s :=
begin
  intros safe₁ safe₂,
  rcases safe₁ with ⟨s', step₁⟩ | ⟨r, exited⟩,
  { intros s'' star₁,
    rcases relation.refl_trans_gen.cases_head star₁ with ⟨⟨⟩⟩ | ⟨s''', step₂, star₂⟩,
    { left,
      tauto },
    { exact safe₂ _ step₂ _ star₂ } },
  { subst exited,
    apply safe_from_exited }
end

/--
If s => s' and all states reachable from s' are safe, and the step
from s is deterministic, then all states reachable from s are safe.
-/
theorem safe_from_state_of_det_step {cfg : CFG χ α} {s s' : state α} :
  safe_from_state cfg s' →
  step cfg s s' →
  set.subsingleton (step cfg s) →
  safe_from_state cfg s :=
begin
  intros h₁ h₂ h₃,
  apply safe_from_state_of_all_steps_safe,
  left,
  { exact ⟨_, h₂⟩ },
  { intros s'' h₄,
    specialize h₃ h₄ h₂,
    subst h₃,
    exact h₁ }
end

/- Mark `state` as protected to avoid conflicts with `init.control.state`. -/
attribute [protected] state

end semantics
end cfg
end bpf
