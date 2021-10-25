import misc.with_top
import sat.factory

/-- Ternary digits. -/
@[reducible]
def trit := with_top (id bool)

/-- `trit` with a concrete interpretation. -/
abbreviation btrit : Type* := trit × erased bool

namespace trit

protected def sat : trit → bool → Prop
| (some ff) tt := false
| (some tt) ff := false
| _         _  := true

protected def and : trit → trit → trit
| (some ff) _         := some ff
| _         (some ff) := some ff
| (some tt) (some tt) := some tt
| _          _        := none

theorem sat_mk_and (r₁ r₂ : trit) {b₁ b₂ : bool} :
  r₁.sat b₁ →
  r₂.sat b₂ →
  (trit.and r₁ r₂).sat (b₁ && b₂) :=
begin
  cases r₁; cases r₂,
  { simp [trit.sat, trit.and] },
  { cases r₂; cases b₂;
    simp [trit.sat, trit.and] },
  { cases r₁; cases b₁;
    simp [trit.sat, trit.and] },
  { cases r₁; cases r₂; cases b₁; cases b₂;
    simp [trit.sat, trit.and] }
end

protected def or : trit → trit → trit
| (some tt) _         := some tt
| _         (some tt) := some tt
| (some ff) (some ff) := some ff
| _          _        := none

theorem sat_mk_or (r₁ r₂ : trit) {b₁ b₂ : bool} :
  r₁.sat b₁ →
  r₂.sat b₂ →
  (trit.or r₁ r₂).sat (b₁ || b₂) :=
begin
  cases r₁; cases r₂,
  { simp [trit.sat, trit.or] },
  { cases r₂; cases b₂;
    simp [trit.sat, trit.or] },
  { cases r₁; cases b₁;
    simp [trit.sat, trit.or] },
  { cases r₁; cases r₂; cases b₁; cases b₂;
    simp [trit.sat, trit.or] }
end

protected def not : trit → trit
| (some ff) := some tt
| (some tt) := some ff
| none      := none

theorem sat_mk_not (r₁ : trit) {b₁ : bool} :
  r₁.sat b₁ →
  (trit.not r₁).sat (!b₁) :=
begin
  cases r₁,
  { simp [trit.sat, trit.not] },
  { cases r₁; cases b₁;
    simp [trit.sat, trit.not] }
end

instance : sat.factory btrit unit :=
{ sat          := λ g x b, trit.sat x.1 b ∧ erased.mk b = x.2,
  default      := infer_instance,
  init_f       := (),
  denote       := λ x, x.2,
  denote_sound := λ _ _ _ ⟨h₁, h₂⟩, by rw [← h₂],
  sat_of_le    := λ _ _ _ _ _ sat, sat }

@[reducible]
private def lift2 (f : bool → bool → bool) : erased bool → erased bool → erased bool :=
λ x y, x.bind $ λ x', y.bind $ λ y', erased.mk $ f x' y'

instance : sat.const_factory btrit unit :=
{ mk_const     := λ _ b, (some b, erased.mk b),
  sat_mk_const := by {
    intros _ b,
    cases b; simp [factory.sat, trit.sat] } }

instance : sat.and_factory btrit unit :=
{ mk_and       := λ r₁ r₂, pure (trit.and r₁.1 r₂.1, lift2 band r₁.2 r₂.2),
  le_mk_and    := by simp,
  sat_mk_and   := by {
    intros _ _ _ _ _ _ _ mk sat₁ sat₂,
    cases sat₁ with sat₁ h₁,
    cases sat₂ with sat₂ h₂,
    simp at mk,
    cases mk,
    split,
    { exact sat_mk_and _ _ sat₁ sat₂ },
    { simp only [← h₁, ← h₂, lift2, erased.bind_eq_out, erased.out_mk] } } }

instance : sat.or_factory btrit unit :=
{ mk_or       := λ r₁ r₂, pure (trit.or r₁.1 r₂.1, lift2 bor r₁.2 r₂.2),
  le_mk_or    := by simp,
  sat_mk_or   := by {
    intros _ _ _ _ _ _ _ mk sat₁ sat₂,
    cases sat₁ with sat₁ h₁,
    cases sat₂ with sat₂ h₂,
    simp at mk,
    cases mk,
    split,
    { exact sat_mk_or _ _ sat₁ sat₂ },
    { simp only [← h₁, ← h₂, lift2, erased.bind_eq_out, erased.out_mk] } } }

instance : sat.not_factory btrit unit :=
{ mk_not       := λ r₁, pure (trit.not r₁.1, bnot <$> r₁.2),
  le_mk_not    := by simp,
  sat_mk_not   := by {
    intros _ _ _ _ _ mk sat₁,
    cases sat₁ with sat₁ h₁,
    simp at mk,
    cases mk,
    split,
    { exact sat_mk_not _ sat₁ },
    { simp only [← h₁, erased.bind_eq_out, erased.out_mk, erased.map] } } }

end trit
