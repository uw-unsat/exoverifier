/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .basic

/-!
# Injectivity and related theorems for btor.node.
-/

namespace btor
namespace node
universe u
variables {α : Type u}

theorem sat_var_iff {g : graph α} {n_id : α} {n : ℕ} {v₁ : erased (fin n → bool)} {r₁ : Σ n, fin n → bool} :
  g n_id = some (node.var v₁) →
  (node.sat g n_id r₁ ↔ r₁ = ⟨n, v₁.out⟩) :=
begin
  intros h,
  rw [sat_iff],
  simp only [h, false_and, exists_false, false_or, or_false],
  cases r₁,
  split,
  { rintros ⟨n, m, ⟨⟨⟩, ⟨⟩⟩, ⟨⟩⟩, refl },
  { tauto }
end

theorem sat_const_iff {g : graph α} {n_id : α} {n : ℕ} {v₁ : lsbvector n} {r₁ : Σ n, fin n → bool} :
  g n_id = some (node.const v₁) →
  (node.sat g n_id r₁ ↔ r₁ = ⟨n, v₁.nth⟩) :=
begin
  intros h,
  rw [sat_iff],
  simp only [h, false_and, exists_false, false_or, or_false],
  cases r₁,
  split,
  { rintros ⟨n, m, ⟨⟨⟩, ⟨⟩⟩, ⟨⟩⟩, refl },
  { tauto }
end

theorem sat_not_iff {g : graph α} {n_id : α} {v₁ : α} {r₂ : Σ n, fin n → bool} :
  g n_id = some (node.not v₁) →
  (node.sat g n_id r₂ ↔ (∃ (n : ℕ) (r₁ : fin n → bool), node.sat g v₁ ⟨n, r₁⟩ ∧ r₂ = ⟨n, bv.not r₁⟩)) :=
begin
  intros h,
  rw [sat_iff],
  simp only [h, false_and, exists_false, false_or, or_false],
  cases r₂,
  split,
  { rintros ⟨n, m, v, ⟨⟩, h, ⟨⟩⟩,
    tauto },
  { tauto }
end

theorem sat_add_iff {g : graph α} {n_id : α} {v₁ v₂ : α} {r₃ : Σ n, fin n → bool} :
  g n_id = some (node.add v₁ v₂) →
  (node.sat g n_id r₃ ↔ (∃ (n : ℕ) (r₁ r₂ : fin n → bool), node.sat g v₁ ⟨n, r₁⟩ ∧ node.sat g v₂ ⟨n, r₂⟩ ∧ r₃ = ⟨n, bv.add r₁ r₂⟩)) :=
begin
  intros h,
  rw [sat_iff],
  simp only [h, false_and, exists_false, false_or, or_false],
  cases r₃,
  split,
  { rintros ⟨_, _, _, _, _, ⟨⟨⟩, ⟨⟩⟩, _, _, ⟨⟩⟩,
    tauto },
  { tauto }
end

theorem sat_mul_iff {g : graph α} {n_id : α} {v₁ v₂ : α} {r₃ : Σ n, fin n → bool} :
  g n_id = some (node.mul v₁ v₂) →
  (node.sat g n_id r₃ ↔ (∃ (n : ℕ) (r₁ r₂ : fin n → bool), node.sat g v₁ ⟨n, r₁⟩ ∧ node.sat g v₂ ⟨n, r₂⟩ ∧ r₃ = ⟨n, bv.mul r₁ r₂⟩)) :=
begin
  intros h,
  rw [sat_iff],
  simp only [h, false_and, exists_false, false_or, or_false],
  cases r₃,
  split,
  { rintros ⟨_, _, _, _, _, ⟨⟨⟩, ⟨⟩⟩, _, _, ⟨⟩⟩,
    tauto },
  { tauto }
end

theorem sat_udiv_iff {g : graph α} {n_id : α} {v₁ v₂ : α} {r₃ : Σ n, fin n → bool} :
  g n_id = some (node.udiv v₁ v₂) →
  (node.sat g n_id r₃ ↔ (∃ (n : ℕ) (r₁ r₂ : fin n → bool), node.sat g v₁ ⟨n, r₁⟩ ∧ node.sat g v₂ ⟨n, r₂⟩ ∧ r₃ = ⟨n, bv.udiv r₁ r₂⟩)) :=
begin
  intros h,
  rw [sat_iff],
  simp only [h, false_and, exists_false, false_or, or_false],
  cases r₃,
  split,
  { rintros ⟨_, _, _, _, _, ⟨⟨⟩, ⟨⟩⟩, _, _, ⟨⟩⟩,
    tauto },
  { tauto }
end

theorem sat_urem_iff {g : graph α} {n_id : α} {v₁ v₂ : α} {r₃ : Σ n, fin n → bool} :
  g n_id = some (node.urem v₁ v₂) →
  (node.sat g n_id r₃ ↔ (∃ (n : ℕ) (r₁ r₂ : fin n → bool), node.sat g v₁ ⟨n, r₁⟩ ∧ node.sat g v₂ ⟨n, r₂⟩ ∧ r₃ = ⟨n, bv.urem r₁ r₂⟩)) :=
begin
  intros h,
  rw [sat_iff],
  simp only [h, false_and, exists_false, false_or, or_false],
  cases r₃,
  split,
  { rintros ⟨_, _, _, _, _, ⟨⟨⟩, ⟨⟩⟩, _, _, ⟨⟩⟩,
    tauto },
  { tauto }
end

theorem sat_and_iff {g : graph α} {n_id : α} {v₁ v₂ : α} {r₃ : Σ n, fin n → bool} :
  g n_id = some (node.and v₁ v₂) →
  (node.sat g n_id r₃ ↔ (∃ (n : ℕ) (r₁ r₂ : fin n → bool), node.sat g v₁ ⟨n, r₁⟩ ∧ node.sat g v₂ ⟨n, r₂⟩ ∧ r₃ = ⟨n, bv.and r₁ r₂⟩)) :=
begin
  intros h,
  rw [sat_iff],
  simp only [h, false_and, exists_false, false_or, or_false],
  cases r₃,
  split,
  { rintros ⟨_, _, _, _, _, ⟨⟨⟩, ⟨⟩⟩, _, _, ⟨⟩⟩,
    tauto },
  { tauto }
end

theorem sat_eq_iff {g : graph α} {n_id : α} {v₁ v₂ : α} {r₃ : Σ n, fin n → bool} :
  g n_id = some (node.eq v₁ v₂) →
  (node.sat g n_id r₃ ↔ (∃ (n : ℕ) (r₁ r₂ : fin n → bool), node.sat g v₁ ⟨n, r₁⟩ ∧ node.sat g v₂ ⟨n, r₂⟩ ∧ r₃ = ⟨1, λ _, r₁ = r₂⟩)) :=
begin
  intros h,
  rw [sat_iff],
  simp only [h, false_and, exists_false, false_or, or_false],
  cases r₃,
  split,
  { rintros ⟨_, _, _, _, _, ⟨⟨⟩, ⟨⟩⟩, _, _, ⟨⟩⟩,
    tauto },
  { tauto }
end

theorem sat_ult_iff {g : graph α} {n_id : α} {v₁ v₂ : α} {r₃ : Σ n, fin n → bool} :
  g n_id = some (node.ult v₁ v₂) →
  (node.sat g n_id r₃ ↔ (∃ (n : ℕ) (r₁ r₂ : fin n → bool), node.sat g v₁ ⟨n, r₁⟩ ∧ node.sat g v₂ ⟨n, r₂⟩ ∧ r₃ = ⟨1, λ _, r₁ < r₂⟩)) :=
begin
  intros h,
  rw [sat_iff],
  simp only [h, false_and, exists_false, false_or, or_false],
  cases r₃,
  split,
  { rintros ⟨_, _, _, _, _, ⟨⟨⟩, ⟨⟩⟩, _, _, ⟨⟩⟩,
    tauto },
  { tauto }
end

theorem sat_shl_iff {g : graph α} {n_id : α} {v₁ v₂ : α} {r₃ : Σ n, fin n → bool} :
  g n_id = some (node.shl v₁ v₂) →
  (node.sat g n_id r₃ ↔ (∃ (n₁ n₂ : ℕ) (r₁ : fin n₁ → bool) (r₂ : fin n₂ → bool),
                          node.sat g v₁ ⟨n₁, r₁⟩ ∧ node.sat g v₂ ⟨n₂, r₂⟩ ∧ r₃ = ⟨n₁, bv.shl r₁ r₂⟩)) :=
begin
  intros h,
  rw [sat_iff],
  simp only [h, false_and, exists_false, false_or, or_false],
  cases r₃,
  split,
  { rintros ⟨_, _, _, _, _, _, ⟨⟨⟩, ⟨⟩⟩, _, _, ⟨⟩⟩,
    tauto },
  { tauto }
end

theorem sat_lshr_iff {g : graph α} {n_id : α} {v₁ v₂ : α} {r₃ : Σ n, fin n → bool} :
  g n_id = some (node.lshr v₁ v₂) →
  (node.sat g n_id r₃ ↔ (∃ (n₁ n₂ : ℕ) (r₁ : fin n₁ → bool) (r₂ : fin n₂ → bool),
                          node.sat g v₁ ⟨n₁, r₁⟩ ∧ node.sat g v₂ ⟨n₂, r₂⟩ ∧ r₃ = ⟨n₁, bv.lshr r₁ r₂⟩)) :=
begin
  intros h,
  rw [sat_iff],
  simp only [h, false_and, exists_false, false_or, or_false],
  cases r₃,
  split,
  { rintros ⟨_, _, _, _, _, _, ⟨⟨⟩, ⟨⟩⟩, _, _, ⟨⟩⟩,
    tauto },
  { tauto }
end

theorem sat_concat_iff {g : graph α} {n_id : α} {v₁ v₂ : α} {r₃ : Σ n, fin n → bool} :
  g n_id = some (node.concat v₁ v₂) →
  (node.sat g n_id r₃ ↔ (∃ (n₁ n₂ : ℕ) (r₁ : fin n₁ → bool) (r₂ : fin n₂ → bool),
                          node.sat g v₁ ⟨n₁, r₁⟩ ∧ node.sat g v₂ ⟨n₂, r₂⟩ ∧ r₃ = ⟨n₁ + n₂, bv.concat r₁ r₂⟩)) :=
begin
  intros h,
  rw [sat_iff],
  simp only [h, false_and, exists_false, false_or, or_false],
  cases r₃,
  split,
  { rintros ⟨_, _, _, _, _, _, ⟨⟨⟩, ⟨⟩⟩, _, _, ⟨⟩⟩,
    tauto },
  { tauto }
end

theorem sat_extract_iff {g : graph α} {n_id : α} {upper lower : ℕ} {v₁ : α} {r₃ : Σ n, fin n → bool} :
  g n_id = some (node.extract upper lower v₁) →
  (node.sat g n_id r₃ ↔ (∃ (n : ℕ) (r : fin n → bool) (h₁ : upper < n) (h₂ : lower ≤ upper),
                          node.sat g v₁ ⟨n, r⟩ ∧ r₃ = ⟨upper - lower + 1, bv.extract upper lower h₁ h₂ r⟩)) :=
begin
  intros h,
  rw [sat_iff],
  simp only [h, false_and, exists_false, false_or, or_false],
  cases r₃,
  split,
  { rintros ⟨_, _, _, _, _, _, _, ⟨⟨⟩, ⟨⟩, ⟨⟩⟩, _, _, ⟨⟩⟩,
    tauto },
  { tauto }
end

theorem sat_ite_iff {g : graph α} {n_id : α} {v₁ v₂ v₃ : α} {r₄ : Σ n, fin n → bool} :
  g n_id = some (node.ite v₁ v₂ v₃) →
  (node.sat g n_id r₄ ↔ (∃ (n : ℕ) (r₁ : fin 1 → bool) (r₂ r₃ : fin n → bool),
                          node.sat g v₁ ⟨1, r₁⟩ ∧ node.sat g v₂ ⟨n, r₂⟩ ∧ node.sat g v₃ ⟨n, r₃⟩ ∧ r₄ = ⟨n, bv.ite r₁ r₂ r₃⟩)) :=
begin
  intros h,
  rw [sat_iff],
  simp only [h, false_and, exists_false, false_or, or_false],
  cases r₄,
  split,
  { rintros ⟨_, _, _, _, _, _, _, ⟨⟨⟩, ⟨⟩, ⟨⟩⟩, _, _, ⟨⟩⟩,
    tauto },
  { tauto }
end

theorem sat_inj {g : graph α} {x : α} {b₁ b₂ : Σ n, fin n → bool} :
  sat g x b₁ →
  sat g x b₂ →
  b₁ = b₂ :=
begin
  intro h₁, revert b₂,
  induction h₁; intros b₂ h₂,
  case var : _ _ _ lookup {
    rw [sat_var_iff lookup] at h₂,
    symmetry, from h₂ },
  case const : _ _ _ lookup {
    rw [sat_const_iff lookup] at h₂,
    symmetry, from h₂ },
  case not : _ _ _ _ lookup i ih₁ {
    cases b₂ with n b₂,
    rw [sat_not_iff lookup] at h₂,
    rcases h₂ with ⟨n, r₁, sat₁, h₂⟩,
    specialize ih₁ sat₁, cases ih₁,
    simp only at h₂,
    obtain ⟨l, r⟩ := h₂,
    subst l,
    congr,
    rw [heq_iff_eq] at r, cases r, refl },
  case add : _ _ _ _ _ _ lookup h i ih₁ ih₂ {
    cases b₂ with n b₂,
    rw [sat_add_iff lookup] at h₂,
    rcases h₂ with ⟨n, r₁, r₂, sat₁, sat₂, h₂⟩,
    specialize ih₁ sat₁, cases ih₁,
    specialize ih₂ sat₂, cases ih₂,
    simp only at h₂,
    obtain ⟨l, r⟩ := h₂,
    subst l,
    congr,
    rw [heq_iff_eq] at r, cases r, refl },
  case mul : _ _ _ _ _ _ lookup h i ih₁ ih₂ {
    cases b₂ with n b₂,
    rw [sat_mul_iff lookup] at h₂,
    rcases h₂ with ⟨n, r₁, r₂, sat₁, sat₂, h₂⟩,
    specialize ih₁ sat₁, cases ih₁,
    specialize ih₂ sat₂, cases ih₂,
    simp only at h₂,
    obtain ⟨l, r⟩ := h₂,
    subst l,
    congr,
    rw [heq_iff_eq] at r, cases r, refl },
  case udiv : _ _ _ _ _ _ lookup h i ih₁ ih₂ {
    cases b₂ with n b₂,
    rw [sat_udiv_iff lookup] at h₂,
    rcases h₂ with ⟨n, r₁, r₂, sat₁, sat₂, h₂⟩,
    specialize ih₁ sat₁, cases ih₁,
    specialize ih₂ sat₂, cases ih₂,
    simp only at h₂,
    obtain ⟨l, r⟩ := h₂,
    subst l,
    congr,
    rw [heq_iff_eq] at r, cases r, refl },
  case urem : _ _ _ _ _ _ lookup h i ih₁ ih₂ {
    cases b₂ with n b₂,
    rw [sat_urem_iff lookup] at h₂,
    rcases h₂ with ⟨n, r₁, r₂, sat₁, sat₂, h₂⟩,
    specialize ih₁ sat₁, cases ih₁,
    specialize ih₂ sat₂, cases ih₂,
    simp only at h₂,
    obtain ⟨l, r⟩ := h₂,
    subst l,
    congr,
    rw [heq_iff_eq] at r, cases r, refl },
  case and : _ _ _ _ _ _ lookup h i ih₁ ih₂ {
    cases b₂ with n b₂,
    rw [sat_and_iff lookup] at h₂,
    rcases h₂ with ⟨n, r₁, r₂, sat₁, sat₂, h₂⟩,
    specialize ih₁ sat₁, cases ih₁,
    specialize ih₂ sat₂, cases ih₂,
    simp only at h₂,
    obtain ⟨l, r⟩ := h₂,
    subst l,
    congr,
    rw [heq_iff_eq] at r, cases r, refl },
  case eq : _ _ _ _ _ _ lookup h i ih₁ ih₂ {
    cases b₂ with n b₂,
    rw [sat_eq_iff lookup] at h₂,
    rcases h₂ with ⟨n, r₁, r₂, sat₁, sat₂, h₂⟩,
    specialize ih₁ sat₁, cases ih₁,
    specialize ih₂ sat₂, cases ih₂,
    simp only at h₂,
    obtain ⟨l, r⟩ := h₂,
    subst l,
    congr,
    rw [heq_iff_eq] at r, cases r, refl },
  case ult : _ _ _ _ _ _ lookup h i ih₁ ih₂ {
    cases b₂ with n b₂,
    rw [sat_ult_iff lookup] at h₂,
    rcases h₂ with ⟨n, r₁, r₂, sat₁, sat₂, h₂⟩,
    specialize ih₁ sat₁, cases ih₁,
    specialize ih₂ sat₂, cases ih₂,
    simp only at h₂,
    obtain ⟨l, r⟩ := h₂,
    subst l,
    congr,
    rw [heq_iff_eq] at r, cases r, refl },
  case shl : _ _ _ _ _ _ _ lookup h i ih₁ ih₂ {
    cases b₂ with n b₂,
    rw [sat_shl_iff lookup] at h₂,
    rcases h₂ with ⟨n₁, n₂, r₁, r₂, sat₁, sat₂, h₂⟩,
    specialize ih₁ sat₁, cases ih₁,
    specialize ih₂ sat₂, cases ih₂,
    simp only at h₂,
    obtain ⟨l, r⟩ := h₂,
    subst l,
    congr,
    rw [heq_iff_eq] at r, cases r, refl },
  case lshr : _ _ _ _ _ _ _ lookup h i ih₁ ih₂ {
    cases b₂ with n b₂,
    rw [sat_lshr_iff lookup] at h₂,
    rcases h₂ with ⟨n₁, n₂, r₁, r₂, sat₁, sat₂, h₂⟩,
    specialize ih₁ sat₁, cases ih₁,
    specialize ih₂ sat₂, cases ih₂,
    simp only at h₂,
    obtain ⟨l, r⟩ := h₂,
    subst l,
    congr,
    rw [heq_iff_eq] at r, cases r, refl },
  case concat : _ _ _ _ _ _ _ lookup h i ih₁ ih₂ {
    cases b₂ with n b₂,
    rw [sat_concat_iff lookup] at h₂,
    rcases h₂ with ⟨n₁, n₂, r₁, r₂, sat₁, sat₂, h₂⟩,
    specialize ih₁ sat₁, cases ih₁,
    specialize ih₂ sat₂, cases ih₂,
    simp only at h₂,
    obtain ⟨l, r⟩ := h₂,
    subst l,
    congr,
    rw [heq_iff_eq] at r, cases r, refl },
  case extract : _ _ upper lower n h₁ h₂ _ lookup sat₂ ih₁ {
    cases b₂ with n b₂,
    rw [sat_extract_iff lookup] at h₂,
    rcases h₂ with ⟨n₁, r₁, h'₁, h'₂, sat₁, h₂⟩,
    specialize ih₁ sat₁, cases ih₁,
    simp only at h₂,
    obtain ⟨l, r⟩ := h₂,
    subst l,
    congr,
    rw [heq_iff_eq] at r, cases r, refl },
  case ite : _ _ _ _ _ _ _ _ lookup h i _ ih₁ ih₂ ih₃ {
    cases b₂ with n b₂,
    rw [sat_ite_iff lookup] at h₂,
    rcases h₂ with ⟨n, r₁, r₂, r₃, sat₁, sat₂, sat₃, h₂⟩,
    specialize ih₁ sat₁, cases ih₁,
    specialize ih₂ sat₂, cases ih₂,
    specialize ih₃ sat₃, cases ih₃,
    simp only at h₂,
    obtain ⟨l, r⟩ := h₂,
    subst l,
    congr,
    rw [heq_iff_eq] at r, cases r, refl }
end

end node
end btor
