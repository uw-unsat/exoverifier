/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import .factory
import misc.semidecision
import sat.cnf
import sat.proof
import sat.tactic

/-!
# AIG-to-CNF

The file provides support for translating an AIG to CNF using the Tseitin transformation.

The main theorem `bnot_of_unsat_to_cnf` says that an AIG is false if the translated CNF
is unsatisfiable.

## Implementation notes

A purely functional representation of a graph is known to be tricky. For instance, traversing
each node once would require recording "visited" status, using complex data structures, or even
changing the theorem prover (see references below).

We avoid this issue by explicitly assigning an ID to each AIG node and using cheaper ID equality
for tesing node equality. An AIG factory maintains that any node "owned" by a factory has the
property that any subnodes with equal IDs are equal.

An earlier version of the factory maintains a stronger invariant, that _every_ node in the
factory's list of nodes has the property that equal IDs imply equality. This enables a simpler
implementation that avoids traversing an AIG and ID equality checking altogether, by simply
translating every node in the factory's list to CNF, regardless of the given AIG. The catches are:
1) it complicates the factory interface as maintaining the invariant requires to pass a witness of
ownership to `mk_*` functions; and 2) it may emit superfluous clauses. We therefore switch to the
current design.

## References

* <https://en.wikipedia.org/wiki/Tseytin_transformation>

* Thomas Braibant, Jacques-Henri Jourdan, and David Monniaux.
  *Implementing and reasoning about hash-consed data structures in Coq*.
  <https://arxiv.org/pdf/1311.2959.pdf>

* Jacques-Henri Jourdan. *Data Structures with Sharing in Coq*, Chapter 9 of
  *Verasco: a Formally Verified C Static Analyzer*.
  <https://hal.archives-ouvertes.fr/tel-01327023>

* Robert S. Boyer and Warren A. Hunt, Jr.
  *Function Memoization and Unique Object Representation for ACL2 Functions*.
  <https://www.cs.utexas.edu/users/boyer/memo.pdf>

* Martin Erwig. *Inductive Graphs and Functional Graph Algorithms*.
  <https://web.engr.oregonstate.edu/~erwig/papers/InductiveGraphs_JFP01.pdf>
-/

namespace aig

open sat.cnf

namespace node
variables {?? ?? : Type*} [clause ?? ??] [counter ??]

/-- Emit a subformula of the equivalence between the circuit of an AIG node and its ID. -/
def to_subformula : ?? ??? node ?? ??? list ??
| _ (var _)           := []
| a (and n??? b??? n??? b???) :=
  [ clause.of_list [literal.mk_neg a, literal.mk n??? b???],
    clause.of_list [literal.mk_neg a, literal.mk n??? b???],
    clause.of_list [literal.mk_pos a, literal.mk n??? (!b???), literal.mk n??? (!b???)] ]

/-- An (ID, node) is valid iff the IDs of children of the node are strictly less than itself,
    and not equal to each other. It additionally assumes that the ID of the left child is no
    smaller than that of the right child, which is maintained by both AIGER and the factory. -/
def valid (a : ??) : node ?? ??? bool
| (node.var _)         := tt
| (node.and a??? _ a??? _) := a??? < a ??? a??? < a???

/-- Emit subformulas for a list of (id, node) pairs. -/
def list_to_subformulas : list (?? (_ : ??), node ??) ??? option (list ??)
| []              := some []
| (???id, n??? :: xs) :=
  if valid id n
  then let f : list ?? := node.to_subformula id n in
    option.map (?? fs, f ++ fs) $ list_to_subformulas xs
  else none

end node

namespace ref
variables {?? ?? ?? ?? : Type*} [clause ?? ??] [formula ?? ?? ??]
          [decidable_eq ??] [has_one ??] [has_add ??]
          {?? : Type*} [unordered_map ?? (node ??) ??] [counter ??]

include ?? ??

open unordered_map

/-- Compile AIG to CNF by emitting the ID with all subformulas. -/
def to_cnf (g : ??) : ref ?? ??? option ??
| ref.top        := some empty
| ref.bot        := some $ formula.of_list [empty]
| (ref.root a b) :=
  option.map (?? (fs : list ??), formula.of_list $ clause.of_list [literal.mk a b] :: fs)
             (node.list_to_subformulas (to_list g))

end ref

namespace compile
variable {?? : Type*}

/-- Complete an AIG by filling in missing ids with variables. -/
def complete (g : graph ??) : graph ?? :=
?? x, if (g x).is_some then g x else some (node.var $ erased.mk ff)

section
open classical
local attribute [instance] prop_decidable

/-- Construct an interpretation by matching the satisfiability of an AIG node and that of its ID.

Each variable is assigned the boolean value of the corresponding AIG node, if one exists;
otherwise it's assigned false (true would also work since the actual value doesn't matter).

While it's possible to do so computationally, this uses classical axioms to simplify the proof.
-/
noncomputable def interpret (g : graph ??) : ?? ??? bool :=
?? (a : ??), to_bool (node.sat (complete g) a tt)

end

lemma subset_complete {g : graph ??} :
  g ??? (complete g) :=
begin
  intros x n h,
  simp only [complete],
  rw [if_pos],
  { assumption },
  { rw [h],
    apply option.is_some_some }
end

lemma sat_of_sat_complete {g : graph ??} {n : ??} {b??? b??? : bool} :
  node.sat g n b??? ???
  node.sat (complete g) n b??? ???
  node.sat g n b??? :=
begin
  intros sat???,
  revert b???,
  induction sat???,
  case var : _ _ lookup {
    intros _ sat???,
    rw [??? erased.out_mk b???],
    apply node.sat.var,
    cases sat???,
    case var {
      have := subset_complete (option.mem_def.2 lookup),
      simp only [erased.mk_out],
      cc },
    case and {
      have := subset_complete (option.mem_def.2 lookup),
      cc } },
  case and : _ _ _ _ _ _ _ lookup sat??? sat??? ih??? ih??? {
    intros b??? sat???,
    rw [node.sat_and_iff] at sat???,
    swap,
    { rw [??? option.mem_def],
      apply subset_complete,
      exact lookup },
    rw [node.sat_and_iff lookup],
    rcases sat??? with ???r???, r???, sat??????, sat??????, bxor_eq???,
    existsi [r???, r???],
    exact ???ih??? sat??????, ???ih??? sat??????, bxor_eq?????? }
end

/-- A list of nodes is total iff all nodes in it have an interpretation
    in the completed version of the graph. -/
def total [decidable_eq ??] (l : list (?? (_ : ??), node ??)) : Prop :=
??? n, n ??? l ??? ??? b, node.sat (complete (?? x, @list.lookup _ _ _ x l)) n.1 b

end compile

section
variables {?? ?? ?? ?? : Type*} [clause ?? ??] [formula ?? ?? ??]
          [decidable_eq ??] [has_one ??] [has_add ??]
          {?? : Type*} [unordered_map ?? (node ??) ??] [counter ??]

open compile
open unordered_map

theorem sat_complete_ff_of_lookup_none
  {ns : list (?? (_ : ??), node ??)}
  {n : ??}
  (h : list.lookup n ns = none) :
  node.sat (complete (?? x, @list.lookup _ _ _ x ns)) n ff :=
begin
  rw [??? erased.out_mk ff],
  apply node.sat.var,
  simp only [complete, h, if_neg, option.is_some_none, not_false_iff, coe_sort_ff]
end

private lemma option_map_is_some {a b : Type*} {f : a ??? b} {o : option a} :
  ((option.map f o).is_some : Prop) ???
  (o.is_some : Prop) :=
begin
  intro h,
  cases o,
  { cases h },
  { simp only [coe_sort_tt, option.is_some_some] }
end

theorem all_valid_of_to_subformula_eq_some
    {ns : list (?? (_ : ??), node ??)}
    (mk : (node.list_to_subformulas ns : option (list ??)).is_some) :
  ns.all (?? p, node.valid p.1 p.2) :=
begin
  revert mk,
  induction ns; intros,
  { cases mk,
    simp only [coe_sort_tt, list.all_nil] },
  { simp only [band_coe_iff, list.all_cons],
    cases ns_hd with i n,
    simp only [node.list_to_subformulas] at mk,
    split_ifs at mk with h,
    { exact ???h, ns_ih (option_map_is_some mk)??? },
    { cases mk } }
end

theorem exists_sat_of_all_valid
    {ns : list (?? (_ : ??), node ??)}
    (nodup : ns.nodupkeys)
    (all_valid : ns.all (?? p, node.valid p.1 p.2)) :
  ??? (n_id : ??) (n : node ??),
    ns.lookup n_id = some n ???
    ??? b, node.sat (complete (?? x, @list.lookup _ _ _ x ns)) n_id b :=
begin
  intros n_id,
  apply counter.strong_induction_on n_id,
  intros i ih n lookup,
  have n_valid : (node.valid i n : Prop),
  { rw [list.all_iff_forall] at all_valid,
    apply all_valid ???i, n???,
    rw [??? list.mem_lookup_iff nodup, option.mem_def],
    exact lookup },
  cases n,
  case var {
    existsi n.out,
    apply node.sat.var,
    apply subset_complete,
    exact lookup },
  case and : n??? b??? n??? b??? {
    simp only [node.valid, bool.to_bool_not, bool.of_to_bool_iff, bool.to_bool_and, band_coe_iff] at n_valid,
    rcases n_valid with ???lt???, lt??????,
    have ih_n??? := ih n??? lt???,
    have ih_n??? := ih n??? (lt_trans lt??? lt???),
    clear lt??? lt??? ih,
    cases lookup_n??? : list.lookup n??? ns with n???_val;
      cases lookup_n??? : list.lookup n??? ns with n???_val,
    case none none {
      have sat??? := sat_complete_ff_of_lookup_none lookup_n???,
      have sat??? := sat_complete_ff_of_lookup_none lookup_n???,
      existsi (bxor b??? ff) && (bxor b??? ff),
      exact node.sat.and (subset_complete lookup) sat??? sat??? },
    case none some {
      have sat??? := sat_complete_ff_of_lookup_none lookup_n???,
      rcases ih_n??? _ lookup_n??? with ???r???, sat??????,
      existsi (bxor b??? ff) && (bxor b??? r???),
      exact node.sat.and (subset_complete lookup) sat??? sat??? },
    case some none {
      have sat??? := sat_complete_ff_of_lookup_none lookup_n???,
      rcases ih_n??? _ lookup_n??? with ???r???, sat??????,
      existsi (bxor b??? r???) && (bxor b??? ff),
      exact node.sat.and (subset_complete lookup) sat??? sat??? },
    case some some {
      rcases ih_n??? _ lookup_n??? with ???r???, sat??????,
      rcases ih_n??? _ lookup_n??? with ???r???, sat??????,
      existsi (bxor b??? r???) && (bxor b??? r???),
      exact node.sat.and (subset_complete lookup) sat??? sat??? } }
end

lemma total_of_all_valid
    {ns : list (?? (_ : ??), node ??)}
    (nodup : ns.nodupkeys)
    (all_valid : ns.all (?? p, node.valid p.1 p.2)) :
  total ns :=
begin
  intros n n_in_ns,
  cases n with n_id n,
  refine exists_sat_of_all_valid nodup all_valid n_id n _,
  rw [??? list.mem_lookup_iff nodup] at n_in_ns,
  exact n_in_ns
end

lemma id_neq_child_ids_of_valid_node {b??? b??? : bool} {n_id n??? n??? : ??} :
  (node.valid n_id (node.and n??? b??? n??? b???) : Prop) ???
  n_id ??? n??? ??? n_id ??? n??? ??? n??? ??? n??? :=
begin
  intro h,
  simp only [node.valid, bool.of_to_bool_iff] at h,
  rcases h with ???h???, h??????,
  rw [counter.lt_to_nat] at h??? h???,
  refine ???_, ???_, _??????,
  { contrapose! h???, subst_vars },
  { contrapose! h???, subst_vars, apply le_of_lt h??? },
  { contrapose! h???, subst_vars }
end

theorem interpret_sat_and_tt
    {nodes : list (?? (_ : ??), node ??)}
    (nodup : nodes.nodupkeys)
    {n_id n??? n??? : ??}
    {b??? b??? : bool}
    (n_h : (???n_id, node.and n??? b??? n??? b?????? : ?? (_ : ??), node ??) ??? nodes)
    (i : interpret (?? x, @list.lookup _ _ _ x nodes) n_id = tt) :
  (interpret (?? x, @list.lookup _ _ _ x nodes) n??? = !b???) ???
  (interpret (?? x, @list.lookup _ _ _ x nodes) n??? = !b???) :=
begin
  simp only [interpret, to_bool_iff] at i,
  rw [node.sat_and_tt_iff n??? b??? n??? b???] at i,
  { simp only [interpret],
    cases i with i??? i???,
    cases b???; cases b???; change !ff with tt at i??? i???; change !tt with ff at i??? i???,
    { rw [(iff_true _).2 i???, (iff_true _).2 i???],
      simp only [to_bool_true_eq_tt, bool.bnot_false, and_self] },
    { replace i??? := not_sat_tt_of_sat_ff (node.sat_right_unique _) i???,
      rw [(iff_true _).2 i???, (iff_false _).2 i???],
      simp only [to_bool_false_eq_ff, to_bool_true_eq_tt, eq_self_iff_true, bool.bnot_false, and_self, bool.bnot_true] },
    { replace i??? := not_sat_tt_of_sat_ff (node.sat_right_unique _) i???,
      rw [(iff_true _).2 i???, (iff_false _).2 i???],
      simp only [to_bool_false_eq_ff, to_bool_true_eq_tt, eq_self_iff_true, bool.bnot_false, and_self, bool.bnot_true] },
    { replace i??? := not_sat_tt_of_sat_ff (node.sat_right_unique _) i???,
      replace i??? := not_sat_tt_of_sat_ff (node.sat_right_unique _) i???,
      rw [(iff_false _).2 i???, (iff_false _).2 i???],
      simp only [to_bool_false_eq_ff, and_self, bool.bnot_true] } },
  { apply subset_complete,
    exact list.mem_lookup nodup n_h }
end

theorem interpret_sat_and_ff
    {nodes : list (?? (_ : ??), node ??)}
    (nodes_total : total nodes)
    (nodup : nodes.nodupkeys)
    {n_id n??? n??? : ??}
    {b??? b??? : bool}
    (n_h : (???n_id, node.and n??? b??? n??? b?????? : ?? (_ : ??), node ??) ??? nodes)
    (i : interpret (?? x, @list.lookup _ _ _ x nodes) n_id = ff) :
  (interpret (?? x, @list.lookup _ _ _ x nodes) n??? = b???) ???
  (interpret (?? x, @list.lookup _ _ _ x nodes) n??? = b???) :=
begin
  simp only [aig.compile.total] at nodes_total,
  simp only [interpret, to_bool_ff_iff] at i,
  specialize nodes_total _ n_h,
  rcases nodes_total with ???b, sat??????,
  have tot := sat???,
  rw [node.sat_and_iff] at tot,
  rcases tot with ???r???, r???, sat???, sat???, xor_eq???,
  swap 2,
  { rw [??? option.mem_def],
    apply subset_complete,
    apply list.mem_lookup; assumption },
  subst xor_eq,
  cases br??? : (bxor b??? r???),
  case ff {
    left,
    simp only [interpret],
    rw [node.bxor_eq_ff_iff] at br???,
    subst br???,
    cases b???,
    { rw [to_bool_ff],
      exact not_sat_tt_of_sat_ff (node.sat_right_unique _) sat??? },
    { rw [to_bool_tt],
      exact sat??? } },
  case tt {
    rw [br???] at sat???,
    cases br??? : (bxor b??? r???),
    case ff {
      right,
      simp only [interpret],
      rw [node.bxor_eq_ff_iff] at br???,
      subst br???,
      cases b???,
      case ff {
        rw [to_bool_ff],
        exact not_sat_tt_of_sat_ff (node.sat_right_unique _) sat??? },
      case tt {
        rw [to_bool_tt],
        exact sat??? } },
    case tt {
      contrapose! i,
      rw [br???] at sat???,
      exact sat??? } }
end

private theorem interpret_sat_node_to_subformula
    {nodes : list (?? (_ : ??), node ??)}
    (nodes_total : total nodes)
    {n_id : ??}
    {n : node ??}
    {f : ??}
    (nodup : nodes.nodupkeys)
    (n_h : (???n_id, n??? : ?? (_ : ??), node ??) ??? nodes)
    (f_h : f ??? (node.to_subformula n_id n : list ??))
    (n_valid : (node.valid n_id n : Prop)) :
  interpret (?? (x : ??), @list.lookup _ _ _ x nodes) ??? f :=
begin
  cases n,
  case var {
    cases f_h },
  case and : n??? b??? n??? b??? {
    obtain ???neq???, neq???, neq?????? := id_neq_child_ids_of_valid_node n_valid,
    simp only [node.to_subformula, literal.mk_neg, list.mem_cons_iff, literal.mk_pos, literal.mk,
               list.mem_singleton] at f_h,
    rcases f_h with _ | _ | _; subst_vars,
    { rw [clause.sat_of_list_of_nodupkeys], swap,
      by simpa,
      simp only [bor_ff, bor_coe_iff, bool.of_to_bool_iff, list.any_nil, list.any_cons],
      cases interpretation : interpret (?? (x : ??), @list.lookup _ _ _ x nodes) n_id,
      { left,
        simp only [has_sat.sat, interpretation],
        tauto },
      { right,
        obtain ???h, _??? := interpret_sat_and_tt nodup n_h interpretation,
        simp only [has_sat.sat, h, coe_sort_tt, bool.bxor_bnot_left]} },
    { rw [clause.sat_of_list_of_nodupkeys], swap,
      by simpa,
      simp only [bor_ff, bor_coe_iff, bool.of_to_bool_iff, list.any_nil, list.any_cons],
      cases interpretation : interpret (?? (x : ??), @list.lookup _ _ _ x nodes) n_id,
      { left,
        simp only [has_sat.sat, interpretation],
        tauto },
      { right,
        obtain ???_, h??? := interpret_sat_and_tt nodup n_h interpretation,
        simp only [has_sat.sat, h, coe_sort_tt, bool.bxor_bnot_left] } },
    { rw [clause.sat_of_list_of_nodupkeys], swap,
      { simp, push_neg, tauto },
      simp only [bor_ff, bor_coe_iff, bool.of_to_bool_iff, list.any_nil, list.any_cons],
      cases interpretation : interpret (?? (x : ??), @list.lookup _ _ _ x nodes) n_id,
      case tt {
        left,
        simp only [has_sat.sat, interpretation],
        tauto },
      case ff {
        right,
        obtain h | h := interpret_sat_and_ff nodes_total nodup n_h interpretation,
        { left,
          simp only [has_sat.sat, h, coe_sort_tt, bool.bxor_bnot_right] },
        { right,
          simp only [has_sat.sat, h, coe_sort_tt, bool.bxor_bnot_right] } } } }
end

private theorem interpret_sat_list_to_subformulas
    {nodes : list (?? (_ : ??), node ??)}
    {ns : list (?? (_ : ??), node ??)}
    (nodes_total : total nodes)
    (sub : ns ??? nodes)
    (nodup : nodes.nodupkeys) {fs : list ??} :
  node.list_to_subformulas ns = some fs ???
  ??? (f : ??),
    f ??? fs ???
    interpret (?? (x : ??), nodes.lookup x) ??? f :=
begin
  revert fs nodes_total nodup sub nodes,
  induction ns,
  case nil {
    intros nodes _ sub nodup fs to_subformulas_eq f f_in_fs,
    cases to_subformulas_eq,
    cases f_in_fs },
  case cons : n ns {
    intros nodes nodes_total sub nodup fs to_subformulas_eq f f_in_fs,
    cases n with n_id n,
    simp only [node.list_to_subformulas] at to_subformulas_eq,
    split_ifs at to_subformulas_eq with h, swap, contradiction,
    simp only [option.map_eq_some'] at to_subformulas_eq,
    rcases to_subformulas_eq with ???fs', fs'_h, fs_fs'???,
    subst fs_fs',
    rw [list.mem_append] at f_in_fs,
    rw [list.cons_subset] at sub,
    cases sub with sub??? sub???,
    cases f_in_fs,
    case inr {
      exact ns_ih nodes_total sub??? nodup fs'_h f f_in_fs },
    case inl {
      exact interpret_sat_node_to_subformula nodes_total nodup sub??? f_in_fs h } }
end

private lemma map_lookup_eq_to_list_lookup {g : ??} {x : ??} :
  lookup x g = list.lookup x (to_list g) :=
begin
  apply option.ext,
  intros a,
  rw [mem_lookup_iff, ??? list.mem_lookup_iff],
  apply nodupkeys
end

include ?? ??

theorem sat_eq_ff_of_unsat_to_cnf {nodes : ??} {r : ref ??} {b : bool} {cnf : ??} :
  ref.sat (node.interpret nodes) r b ???
  r.to_cnf nodes = some cnf ???
  unsatisfiable cnf ???
  b = ff :=
begin
  intros sat cnf_ex unsat,
  suffices h : b = tt ??? (??? (p : ?? ??? bool), p ??? cnf),
  { cases b, refl,
    exfalso,
    cases h rfl with p h,
    apply unsat, assumption },
  intros; subst_vars,
  cases r,
  case top {
    cases cnf_ex,
    simp only [formula.sat_empty, exists_const] },
  case bot {
    cases sat },
  case root : a b {
    existsi interpret (node.interpret nodes),
    simp only [ref.to_cnf, option.map_eq_some'] at cnf_ex,
    rcases cnf_ex with ???fs, fs_h, cnf_h???,
    simp only [formula.sat_iff_forall],
    intros k c hmem,
    subst cnf_h,
    replace hmem := formula.mem_to_of_list_of_mem hmem,
    simp only [list.mem_cons_iff] at hmem,
    cases hmem,
    case inl {
      subst hmem,
      simp [clause.sat_of_list_of_nodupkeys, interpret], -- Why doesn't squeeze_simp work?
      simp only [has_sat.sat],
      rw [ref.sat_root_iff] at sat,
      cases b,
      case ff {
        simp only [bool.of_to_bool_iff, bool.bxor_ff_right],
        apply node.sat_of_subset sat,
        apply subset_complete },
      case tt {
        simp only [bool.bnot_true, tt_bxor] at sat,
        have sat' := node.sat_of_subset sat (by apply subset_complete),
        have not_sat_tt := not_sat_tt_of_sat_ff (node.sat_right_unique _) sat',
        rw [(iff_false _).2 not_sat_tt],
        simp only [to_bool_false_eq_ff, bxor, coe_sort_tt] } },
    case inr {
      have to_list_nodupkeys : (to_list nodes).nodupkeys := unordered_map.nodupkeys nodes,
      have to_list_total : total (to_list nodes : list (?? (_ : ??), node ??)),
      { apply total_of_all_valid,
        by from to_list_nodupkeys,
        apply all_valid_of_to_subformula_eq_some _,
        swap 3,
        rw [option.is_some_iff_exists],
        exact ???fs, fs_h??? },
      have sat_formulas := interpret_sat_list_to_subformulas to_list_total (list.subset.refl _) to_list_nodupkeys fs_h c hmem,
      simp only [node.interpret],
      suffices feq : (?? x, list.lookup x (to_list nodes)) = (?? x, lookup x nodes),
        by rw [feq] at sat_formulas; assumption,
      ext i,
      simp only [map_lookup_eq_to_list_lookup] } }
end

theorem sat_eq_tt_of_unsat_to_cnf {nodes : ??} {r : ref ??} {b : bool} {cnf : ??} :
  ref.sat (node.interpret nodes) r b ???
  (-r).to_cnf nodes = some cnf ???
  unsatisfiable cnf ???
  b = tt :=
begin
  intros sat to_cnf unsat,
  have h : b = !!b, by simp only [bnot_bnot],
  rw [h, ??? ref.sat_neg_iff] at sat,
  have h := sat_eq_ff_of_unsat_to_cnf sat to_cnf unsat,
  simp only [bnot_eq_ff_eq_eq_tt] at h,
  tauto
end

open semidecision

/-- semidecidability of `ref.sat` via reduction to CNF given a proof of unsatisfiability. -/
def semidecision_ref_sat (nodes : ??) (r : ref ??) (b??? : bool) (proof : sat.proof.proof ?? ?? ?? ??) :
  semidecision (??? {b???}, ref.sat (node.interpret nodes) r b??? ??? b??? = b???) :=
begin
  refine semidecision.bind_true (semidecision.of_decidable ((cond b??? (-r) r).to_cnf nodes : option ??).is_some) (?? h, _),
  refine (sat.proof.decide_unsat_via_rup_check (option.get h) proof).modus_ponens _,
  intros unsat b??? sat???,
  cases b???,
  case tt {
    exact sat_eq_tt_of_unsat_to_cnf sat??? (option.some_get h).symm unsat },
  case ff {
    exact sat_eq_ff_of_unsat_to_cnf sat??? (option.some_get h).symm unsat }
end

end

section
universe u
variables {?? ?? : Type u} {?? ?? ?? : Type*} [clause ?? ??] [formula ?? ?? ??]
          [decidable_eq ??] [has_one ??] [has_add ??]
          [unordered_map ?? (node ??) ??] [counter ??] [perfect_hashable ??]

def decide_via_to_cnf : factory.decision_procedure bool (bref ??) (factory ?? ??) (sat.proof.proof ?? ?? ?? ??) :=
semidecision.procedure.sequence decide_via_trivial $ by {
  rintros ???g, ??????e, b???, v????????? w,
  refine (semidecision_ref_sat g.nodes e v??? w).modus_ponens _,
  simp only [factory.sat], tauto }

end

meta def to_cnf_oracle :
  sat.oracle (bref pos_num) (factory pos_num (trie (node pos_num))) sat.proof.default.proof :=
?? ???g, ???r, b??????,
  match ((cond b (-(r.1)) r.1).to_cnf g.nodes : option default.formula) with
  | some formula := sat.proof.sat_oracle formula
  | none         := tactic.fail "Failed to compile formula to cnf."
  end

end aig
