-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/StoredGlue.lean: the stored tables' openings as one list, and what is asked of them.

The library keeps the stored tables' openings of a chain in one list (`storedB`). This file shows,
from what the strict reader has checked (`StoredFact`): which table each opening belongs to; that
the listed places are no more than the draws given to the tables; and that they are the places that
the draws ask for.

Main definitions: `stoOf`, `pick`.
Main theorems: `sto_keys`, `sto_count`, `xWanted_asked`.
It claims nothing on what a chain proves.
-/
import Run.PageIsProofs
import Run.PlanQXRun
import OnBytes.Tie.StoredLists
import OnBytes.Tie.StoredExt
import Run.CostFmtProofs

set_option autoImplicit false

namespace OnBytes.Tie
open Rom Iop Compile Compile.Batch Run Run.PQ Run.Twin Run.Thin

/-- The stored tables' openings round by round, as `storedB_eq` gives them. -/
abbrev stoOf (tss : List (List Fmt.Stored)) (rc : List Cut) : List (Bool × ℕ × OpenB) :=
  (tss.zip rc).flatMap fun y => (y.1.zip y.2.2).map fun z => (z.1.item == 1, z.2.1.W, obOf z.2)

/-- The openings belong to the tables in the description's order. -/
theorem stoOf_keys : ∀ (tss : List (List Fmt.Stored)) (rc : List Cut), SameLengths tss rc →
    (stoOf tss rc).map (·.1) = tss.flatten.map (·.item == 1)
  | _, _, .nil => rfl
  | ts :: tss, p :: rc, .cons h t => by
    have ih := stoOf_keys tss rc t
    unfold stoOf at ih ⊢
    rw [List.zip_cons_cons, List.flatMap_cons, List.map_append, ih, List.flatten_cons,
      List.map_append]
    congr 1
    show ((ts.zip p.2).map _).map _ = _
    rw [List.map_map]
    conv_rhs => rw [← List.map_fst_zip (l₁ := ts) (l₂ := p.2) (Nat.le_of_eq h)]
    rw [List.map_map]
    rfl

/-- The numbers of draws in the library's list are those of the description's lists. -/
theorem count_from : ∀ (tss : List (List Fmt.Stored)) (k : ℕ),
    (((tss.zipIdx k).flatMap fun t => t.1.map fun s =>
      (⟨t.2, s.item == 1, s.lo, s.count⟩ : XO)).map (·.count)) = tss.flatten.map (·.count)
  | [], _ => rfl
  | ts :: tss, k => by
    rw [List.zipIdx_cons, List.flatMap_cons, List.map_append, count_from tss (k + 1),
      List.flatten_cons, List.map_append, List.map_map]
    rfl

/-- One round: the listed places are no more than the draws given to the tables. -/
theorem count_round (h : HId) (cfg statement : ByteArray) (poss : List ℕ) :
    ∀ {ts : List Fmt.Stored} {zs : List (Fmt.Shape × List ℕ × Fmt.OpenOut)},
    List.Forall₂ (StoredFact h cfg statement poss) ts zs →
    (((ts.zip zs).map fun z => ((z.1.item == 1, z.2.1.W, obOf z.2) : Bool × ℕ × OpenB)).map
      (·.2.2.idx.length)).sum ≤ (ts.map (·.count)).sum
  | _, _, .nil => Nat.le_refl _
  | t :: ts, z :: zs, .cons f r => by
    have ih := count_round h cfg statement poss r
    rw [List.zip_cons_cons, List.map_cons, List.map_cons, List.sum_cons, List.map_cons,
      List.sum_cons]
    refine Nat.add_le_add ?_ ih
    show z.2.1.length ≤ t.count
    rw [f.xs]
    refine Nat.le_trans (CostP.listOf_len _) ?_
    rw [List.length_map]
    unfold Fmt.partOf
    rw [List.length_take]
    exact Nat.min_le_left _ _

/-- All rounds: the listed places are no more than the draws given to the tables. -/
theorem count_all (h : HId) (cfg statement : ByteArray) :
    ∀ {tss : List (List Fmt.Stored)} {rc : List Cut},
    List.Forall₂ (fun (ts : List Fmt.Stored) (p : Cut) =>
      List.Forall₂ (StoredFact h cfg statement p.1.drawn.poss) ts p.2) tss rc →
    ((stoOf tss rc).map (·.2.2.idx.length)).sum ≤ (tss.flatten.map (·.count)).sum
  | _, _, .nil => Nat.le_refl _
  | ts :: tss, p :: rc, .cons f r => by
    have ih := count_all h cfg statement r
    unfold stoOf at ih ⊢
    rw [List.zip_cons_cons, List.flatMap_cons, List.map_append, List.sum_append,
      List.flatten_cons, List.map_append, List.sum_append]
    exact Nat.add_le_add (count_round h _ _ _ f) ih

/-- Which of the two tables a key of a view's opened columns names, if any: the filter of the
library's `xWanted`. -/
def pick (kx : ℕ × ℕ) : Option (Bool × ℕ) :=
  if kx.1 = PQ.storedKey false then some (false, kx.2)
  else if kx.1 = PQ.storedKey true then some (true, kx.2) else none

/-- A stored table's key names its table. -/
theorem pick_stored (b : Bool) (x : ℕ) : pick (PQ.storedKey b, x) = some (b, x) := by
  cases b
  · exact if_pos rfl
  · unfold pick
    have h0 : ¬ (PQ.storedKey true, x).1 = PQ.storedKey false := by
      show ¬ 2 ^ 16 + 1 = 2 ^ 16 + 0
      omega
    rw [if_neg h0, if_pos rfl]

/-- A key below 2 ^ 16 names none. -/
theorem pick_small (k x : ℕ) (h : k < 2 ^ 16) : pick (k, x) = none := by
  have h0 : ¬ (k, x).1 = PQ.storedKey false := by
    show ¬ k = 2 ^ 16 + 0
    omega
  have h1 : ¬ (k, x).1 = PQ.storedKey true := by
    show ¬ k = 2 ^ 16 + 1
    omega
  unfold pick
  rw [if_neg h0, if_neg h1]

/-- Under one stored table's key `pick` keeps every place, with its table. -/
theorem filterMap_key (b : Bool) : ∀ L : List ℕ,
    (L.map fun x => (PQ.storedKey b, x)).filterMap pick = L.map fun x => (b, x)
  | [] => rfl
  | x :: L => by
    rw [List.map_cons, List.filterMap_cons_some (pick_stored b x), filterMap_key b L,
      List.map_cons]

/-- `pick` drops the chain's own trees, whose numbers are below 2 ^ 16. -/
theorem filterMap_own (first : ℕ) (ys : List (Fmt.Shape × List ℕ × Fmt.OpenOut))
    (h : ∀ x ∈ ys, x.1.tree < 2 ^ 16) :
    (ys.flatMap fun x => x.2.1.map fun z => (x.1.tree - first, z)).filterMap pick = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro kx hk
  obtain ⟨x, hx, hk⟩ := List.mem_flatMap.1 hk
  obtain ⟨z, _, rfl⟩ := List.mem_map.1 hk
  exact pick_small _ _ (by have := h x hx; omega)

/-- One round: what the draws ask of the tables is what the openings list. -/
theorem asked_round (h : HId) (cfg statement : ByteArray) (poss : List ℕ) (a : ℕ) :
    ∀ {ts : List Fmt.Stored} {zs : List (Fmt.Shape × List ℕ × Fmt.OpenOut)},
    List.Forall₂ (StoredFact h cfg statement poss) ts zs → (∀ t ∈ ts, t.sh.a = a) →
    (ts.flatMap fun t => (Fmt.listOf ((Fmt.partOf t poss).map (· % 2 ^ a))).map fun x =>
        (PQ.storedKey (t.item == 1), x)).filterMap pick =
      askedOf ((ts.zip zs).map fun z => (z.1.item == 1, z.2.1.W, obOf z.2))
  | _, _, .nil, _ => rfl
  | t :: ts, z :: zs, .cons f r, ha => by
    have ih := asked_round h cfg statement poss a r fun t' ht' =>
      ha t' (List.mem_cons_of_mem _ ht')
    unfold askedOf at ih ⊢
    rw [List.flatMap_cons, List.filterMap_append, filterMap_key, ih, List.zip_cons_cons,
      List.map_cons, List.flatMap_cons]
    congr 1
    show _ = z.2.1.map fun x => (t.item == 1, x)
    rw [f.xs, ha t List.mem_cons_self]

/-- All rounds: what the draws ask of the tables is what the openings list. -/
theorem asked_all (h : HId) (cfg statement : ByteArray) (a first : ℕ) :
    ∀ {tss : List (List Fmt.Stored)} {rc : List Cut},
    List.Forall₂ (fun (ts : List Fmt.Stored) (p : Cut) =>
      List.Forall₂ (StoredFact h cfg statement p.1.drawn.poss) ts p.2) tss rc →
    (∀ t ∈ tss.flatten, t.sh.a = a) →
    (∀ p ∈ rc, ∀ x ∈ (stripR p.1).opens, x.1.tree < 2 ^ 16) →
    ((tss.zip (rc.map fun p => stripR p.1)).flatMap fun y =>
        (y.1.flatMap fun t =>
          (Fmt.listOf ((Fmt.partOf t y.2.drawn.poss).map (· % 2 ^ a))).map fun x =>
            (PQ.storedKey (t.item == 1), x)) ++
        y.2.opens.flatMap fun x => x.2.1.map fun z => (x.1.tree - first, z)).filterMap pick =
      askedOf (stoOf tss rc)
  | _, _, .nil, _, _ => rfl
  | ts :: tss, p :: rc, .cons f r, ha, hs => by
    have ih := asked_all h cfg statement a first r
      (fun t ht => ha t (by rw [List.flatten_cons]; exact List.mem_append_right _ ht))
      (fun p' hp' => hs p' (List.mem_cons_of_mem _ hp'))
    have e1 := asked_round h cfg statement p.1.drawn.poss a f
      (fun t ht => ha t (by rw [List.flatten_cons]; exact List.mem_append_left _ ht))
    have e2 := filterMap_own first (stripR p.1).opens (hs p List.mem_cons_self)
    unfold stoOf askedOf at ih e1 ⊢
    rw [List.map_cons, List.zip_cons_cons, List.flatMap_cons, List.filterMap_append,
      List.filterMap_append, ih, List.zip_cons_cons, List.flatMap_cons, List.flatMap_append]
    congr 1
    rw [e2, List.append_nil]
    exact e1

/-- Each member of the second of two lists that are related member by member has its partner. -/
theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β},
    List.Forall₂ R l₁ l₂ → ∀ b ∈ l₂, ∃ a ∈ l₁, R a b
  | _, _, .nil, _, hb => by cases hb
  | a :: l₁, b' :: l₂, .cons h t, b, hb => by
    rcases List.mem_cons.1 hb with e | hb'
    · subst e
      exact ⟨a, List.mem_cons_self, h⟩
    · obtain ⟨a', ha', hr⟩ := forall₂_mem_right t b hb'
      exact ⟨a', List.mem_cons_of_mem _ ha', hr⟩

/-- The trees that were opened have the numbers of the description's trees, below 2 ^ 16. -/
theorem tab_small : ∀ (rs : List Fmt.Round) (ros : List Fmt.RoundOut) (acc : List ByteArray),
    TabTR rs ros acc → (∀ r ∈ rs, ∀ x ∈ r.opens, x.1.tree < 2 ^ 16) →
    ∀ ro ∈ ros, ∀ y ∈ ro.opens, y.1.tree < 2 ^ 16
  | [], [], _, _, _, _, hro, _, _ => by cases hro
  | [], _ :: _, _, t, _, _, _, _, _ => t.elim
  | _ :: _, [], _, t, _, _, _, _, _ => t.elim
  | r :: rs, ro' :: ros, acc, t, hs, ro, hro, y, hy => by
    rcases List.mem_cons.1 hro with e | hro'
    · subst e
      obtain ⟨x, hx, hxy⟩ := forall₂_mem_right t.1 y hy
      rw [hxy.1]
      exact hs r List.mem_cons_self x hx
    · exact tab_small rs ros _ t.2 (fun r' hr' => hs r' (List.mem_cons_of_mem _ hr')) ro hro' y hy

/-- The library's limits imply the strict reader's conditions on a description. -/
theorem base_ok (S : Fmt.Spec) (h : PQ.ok S = true) : S.ok = true := by
  simp only [PQ.ok, Bool.and_eq_true] at h
  exact h.1.1.1.1

section
variable (h : HId) (D : XD) (o : Fmt.ChainOut)
  (rc : List (Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)))
  (ho : o.rounds.toList = rc.map roundWithStoredOpenings)
  (hS : List.Forall₂ (fun (ts : List Fmt.Stored)
      (p : Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)) =>
    List.Forall₂ (StoredFact h D.base.cfg D.base.statement p.1.drawn.poss) ts p.2) D.stored rc)

include ho hS in
/-- The library's list `storedB` is `stoOf`: the openings round by round. -/
theorem sto_eq : storedB D.xs o = stoOf D.stored rc :=
  storedB_eq D.stored o rc ho (hS.imp fun _ _ f => f.length_eq)

include ho hS in
/-- The openings belong to the tables in the description's order, under the section's two
hypotheses: o is rc with the stored openings joined in, and each has `StoredFact`. -/
theorem sto_keys : (storedB D.xs o).map (·.1) = D.stored.flatten.map (·.item == 1) := by
  rw [sto_eq h D o rc ho hS]
  exact stoOf_keys D.stored rc (hS.imp fun _ _ f => f.length_eq)

include ho hS in
/-- The listed places are no more than the draws that the description gives to the tables, under
the same two hypotheses. -/
theorem sto_count : ((storedB D.xs o).map (·.2.2.idx.length)).sum ≤ (D.xs.map (·.count)).sum := by
  rw [sto_eq h D o rc ho hS]
  have e : D.xs.map (·.count) = D.stored.flatten.map (·.count) := count_from D.stored 0
  rw [e]
  exact count_all h _ _ hS

include ho hS in
/-- What the drawn positions ask of the two tables is what the openings list, under the same two
hypotheses, if the own part is within the library's limits, oo has `LaxFacts`, and all tables have
the depth `D.a`. `oo` is the chain as read without the stored tables' openings. -/
theorem xWanted_asked (hok : PQ.ok D.base = true) (oo : Fmt.ChainOut)
    (hL : LaxFacts h D.base oo) (hoo : oo.rounds.toList = rc.map fun p => stripR p.1)
    (hD : ∀ s ∈ D.stored.flatten, s.sh.a = D.a) :
    xWanted D.a D.ds D.xs (oo.rounds.toList.map (·.drawn)) = askedOf (storedB D.xs o) := by
  have ht : TabTR D.base.rounds oo.rounds.toList [] := tab_tr h _ _ _ _ _ hL.trace
  have hlen : D.stored.length = oo.rounds.toList.length := by
    rw [hoo, List.length_map]
    exact hS.length_eq
  have ht16 : ∀ r ∈ D.base.rounds, ∀ x ∈ r.opens, x.1.tree < 2 ^ 16 := by
    have e := Fmt.ok_trees (base_ok D.base hok)
    simp only [List.all_eq_true, decide_eq_true_eq] at e
    exact e
  have hsm := tab_small _ _ _ ht ht16
  have hw := wantedX_eq D.base D.a D.stored oo.rounds.toList hlen ht
    fun r hr x hx => tab_good D.base (tab_limits D.base hok) r hr x hx
  show (wantedX D.a (rds D.base) (xsOf D.stored) (oo.rounds.toList.map (·.drawn))).filterMap pick
    = _
  rw [hw, sto_eq h D o rc ho hS, hoo]
  refine asked_all h _ _ D.a D.base.firstTree hS hD fun p hp x hx => ?_
  exact hsm (stripR p.1) (by rw [hoo]; exact List.mem_map_of_mem hp) x hx

end

end OnBytes.Tie

#print axioms OnBytes.Tie.sto_keys
#print axioms OnBytes.Tie.sto_count
#print axioms OnBytes.Tie.xWanted_asked
