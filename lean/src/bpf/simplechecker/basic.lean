import ..cfg
import ..basic

axiom bogus : false

namespace bpf
namespace simplechecker

section
parameters {α : Type} [decidable_eq α] {map : Type → Type} [generic_map α map]
open unordered_map

abbreviation program : Type := bpf.cfg.CFG (map (bpf.cfg.instr α)) α

def check_from (p : program) : α → ℕ → bool
| pc 0       := ff
| pc (n + 1) :=
  match lookup pc p.code with
  | none := ff
  | some (bpf.cfg.instr.ALU64_X ALU.ADD _ _ next) := check_from next n
  | some bpf.cfg.instr.Exit := tt
  | _ := ff
  end

/- A very simple checker for BPF programs. -/
def check (p : program) (fuel : ℕ) : bool := check_from p p.entry fuel

theorem check_sound {p : program} (fuel : ℕ) :
  check p fuel = tt →
  bpf.cfg.safe p := bogus.elim

end
end simplechecker
end bpf
