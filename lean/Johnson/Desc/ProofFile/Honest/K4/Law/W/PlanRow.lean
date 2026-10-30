-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/PlanRow.lean: CONDITIONAL. THE PARTS INTO WHICH THE BOOK's
MAKER CUTS THE SUB-PROTOCOL OF THE LAYERS' OWN ROUNDS (kind K4), WRITTEN OUT, AT EVERY PLAN.

What is here. PUBLIC DATA ALONE: names of rounds and counts of scalars. The book's maker cuts a
sub-protocol's rounds into parts by their names (`planParts`, Honest/BookEntries.lean; `unitLen`,
Honest/BookOf.lean). It reads of the sub-protocol its place, each round's name and each round's
number of scalars. Where the sub-protocol declares the entries of K4's own table of rounds
(`rounds`, OnBytes/Desc/First/K4/Rounds.lean), these are the table's names and its counts of sent
elements; the table is a written list: single rounds and seven masked sumchecks. Definitions,
statements and proofs.

  `maskedP`, `k4TailUnits`, `k4Units`, `k4PlanRow`: a masked sumcheck's rounds as names and
      counts; K4's row unit by unit: 17 units, 19 in the first group of layers; the row as the
      maker's parts.
  `k4_table_rows`: the table's names and counts are these units, one behind the other. No
      hypothesis.
  `unitLen_masked`, `unitLen_plain`, `unitsOf_good`, `stretchesBy_flatten`, `cutOfNames_K4`: the
      maker's cut takes a masked sumcheck as one unit and a round under one of K4's four other names
      as a unit by itself.
  `k4_partsCut`, `k4_planParts`: **the maker's cut and its parts at such a sub-protocol are the
      written ones.**

Not shown here. hpl, that the sub-protocol stands at K4's place, and hr, that it declares the
entries of K4's table at the plan, are hypotheses. Law/MemberAt.lean's `k4_member_rounds` has hr AT
THE FULL SIZE ALONE, under eight hypotheses, of which the place is one. Law/W/LockAtMember.lean's
`k4_member_there` has both, in the goals' scope, at a member that the library hands. `k4Units` IS A
THIRD WRITING OF ONE ROW, beside the sealed table and `k4Rows` (Law/ExactFresh/AtSide.lean):
`k4_table_rows` ties the units, laid one behind the other, to the table; that the units' borders are
those of `k4Rows`, and so of our own cut, is shown in Law/W/CutIsOurs.lean, not here. Nothing on a
book, on coins, or on what a part sends. Nothing holds the maker's reading of names against the
format.
No property is claimed.
A LAW, NOT A PART: no file that defines a part of the proof file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SlotsTrue
import Johnson.Desc.ProofFile.Honest.BookEntries

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.W
open OnBytes.Model (ledNS ledNP ledNO)
open OnBytes.Model.Layer (nEndT)
open OnBytes.Desc.First.K4 (rounds masked layerRds pointRd batchRd entries entryOf Rd)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block Place KindName)

variable {S Cl : Type}

/-! ## 1 The row, written out -/

/-- A masked sumcheck's rounds as names and counts. -/
def maskedP (k first y ends : Nat) : List (String × Nat) :=
  ("PSC epsilon", first) ::
    (List.replicate k ("PSC round", 2) ++ [("PSC Y", y), ("PSC values", ends)])

/-- K4's row behind the points in front, unit by unit. -/
def k4TailUnits (Q : K4Pub) : List (List (String × Nat)) :=
  [[("BAT-sigma", ledNS Q.P.y.h.xl * Q.P.y.NI)], [("JOIN", 0)], maskedP Q.P.rd.muV 1 2 2,
   [("LINE", 0)], [("BAT-sigma", ledNP Q.P.y.h.xl * Q.P.y.NI)],
   maskedP Q.P.y.h.lt 2 2 (ledNO Q.P.y.h.xl * Q.P.y.NI), maskedP Q.P.y.h.lt 2 1 (nEndT Q.P.y),
   [("BAT-sigma", 0)], maskedP Q.hp.lamS 1 2 (nStack Q.P Q.hp Q.g), maskedP Q.P.rd.muH 1 2 2,
   [("LINE", 0)], [("JOIN", 0)], maskedP Q.P.rd.muH2 1 2 2, [("LINE", 0)],
   [("BAT-sigma", if Q.g == 0 then 1 else 0)], maskedP Q.P.wsLay.lk 1 1 1]

/-- **K4's row, unit by unit**: three points in front in the first group of layers, else one. -/
def k4Units (Q : K4Pub) : List (List (String × Nat)) :=
  (if Q.g == 0 then [[("ZERO", 0)], [("ZERO", 0)], [("ZERO", 0)]] else [[("ZERO", 0)]]) ++
    k4TailUnits Q

/-- **The row as the maker's parts.** -/
def k4PlanRow (Q : K4Pub) : List PartAt :=
  (k4Units Q).zipIdx.map fun x => ⟨k4Addr Q x.2, x.1⟩

/-- The table's names and counts are these units, one behind the other. -/
theorem k4_table_rows (Q : K4Pub) :
    (rounds Q.P Q.hp Q.g).map (fun d => (d.name.name, d.sent)) = (k4Units Q).flatten := by
  cases hg : (Q.g == 0) <;>
    simp [rounds, k4Units, k4TailUnits, maskedP, layerRds, masked, pointRd, batchRd, nStack, hg,
      OnBytes.Model.RoundName.name]

/-! ## 2 The maker's cut -/

/-- The run of "PSC round" in front of a "PSC Y". -/
theorem headRun_rounds : ∀ (k : Nat) (l : List String),
    headRun "PSC round" (List.replicate k "PSC round" ++ "PSC Y" :: l) = k
  | 0, l => by simp [headRun]
  | k + 1, l => by
    have h := headRun_rounds k l
    unfold headRun at h ⊢
    rw [List.replicate_succ, List.cons_append, List.takeWhile_cons_of_pos (by simp),
      List.length_cons, h]

/-- A masked sumcheck is one unit. -/
theorem unitLen_masked (k : Nat) (l : List String) :
    unitLen ("PSC epsilon" :: (List.replicate k "PSC round" ++ "PSC Y" :: "PSC values" :: l)) =
      k + 3 := by
  have d1 : (List.replicate k "PSC round" ++ "PSC Y" :: "PSC values" :: l).drop k =
      "PSC Y" :: "PSC values" :: l := List.drop_left' List.length_replicate
  have d2 : (List.replicate k "PSC round" ++ "PSC Y" :: "PSC values" :: l).drop (k + 1) =
      "PSC values" :: l := by
    have e : List.replicate k "PSC round" ++ "PSC Y" :: "PSC values" :: l =
        (List.replicate k "PSC round" ++ ["PSC Y"]) ++ "PSC values" :: l := by simp
    rw [e]
    exact List.drop_left' (by simp)
  have a : headRun "PSC round" (List.replicate k "PSC round" ++ "PSC Y" :: "PSC values" :: l) = k :=
    headRun_rounds k _
  have b : headOne "PSC Y"
      ((List.replicate k "PSC round" ++ "PSC Y" :: "PSC values" :: l).drop k) = 1 := by
    rw [d1]
    simp [headOne]
  have c : headOne "PSC values"
      ((List.replicate k "PSC round" ++ "PSC Y" :: "PSC values" :: l).drop (k + 1)) = 1 := by
    rw [d2]
    simp [headOne]
  have u : unitLen ("PSC epsilon" ::
      (List.replicate k "PSC round" ++ "PSC Y" :: "PSC values" :: l)) =
      1 + sumTail (List.replicate k "PSC round" ++ "PSC Y" :: "PSC values" :: l) := by
    simp [unitLen]
  rw [u]
  unfold sumTail
  simp only [a, b, c]
  omega

/-- K4's four other names. -/
def plainNames : List String := ["ZERO", "BAT-sigma", "JOIN", "LINE"]

/-- A round under one of these is a unit by itself. -/
theorem unitLen_plain {n : String} (h : n ∈ plainNames) (l : List String) :
    unitLen (n :: l) = 1 := by
  simp only [plainNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> simp [unitLen]

/-- A unit of K4's row: one round under one of the four names, or a masked sumcheck. -/
def GoodUnit (u : List (String × Nat)) : Prop :=
  (∃ n c, n ∈ plainNames ∧ u = [(n, c)]) ∨ ∃ k a y e, u = maskedP k a y e

theorem GoodUnit.ne_nil {u : List (String × Nat)} (h : GoodUnit u) : u ≠ [] := by
  rcases h with ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩
  · exact List.cons_ne_nil _ _
  · exact List.cons_ne_nil _ _

/-- The maker's unit at the head of such a unit's names is that unit. -/
theorem unitLen_good {u : List (String × Nat)} (h : GoodUnit u) (l : List String) :
    unitLen (u.map (·.1) ++ l) = u.length := by
  rcases h with ⟨n, c, hn, rfl⟩ | ⟨k, a, y, e, rfl⟩
  · exact unitLen_plain hn l
  · have e1 : (maskedP k a y e).map (·.1) ++ l =
        "PSC epsilon" :: (List.replicate k "PSC round" ++ "PSC Y" :: "PSC values" :: l) := by
      simp [maskedP]
    rw [e1, unitLen_masked]
    simp [maskedP]

theorem unitsOf_succ {k : Nat} {ns : List String} (h : ns ≠ []) :
    unitsOf (k + 1) ns = unitLen ns :: unitsOf k (ns.drop (unitLen ns)) := by
  cases ns with
  | nil => exact absurd rfl h
  | cons x t => rfl

/-- **The maker's units of a list of such units' names are these units' lengths.** -/
theorem unitsOf_good : ∀ (us : List (List (String × Nat))) (fuel : Nat),
    (∀ u ∈ us, GoodUnit u) → us.length ≤ fuel →
      unitsOf fuel (us.flatten.map (·.1)) = us.map (·.length)
  | [], fuel, _, _ => by cases fuel <;> rfl
  | u :: us, 0, _, h => absurd h (by simp)
  | u :: us, fuel + 1, hg, h => by
    have gu := hg u List.mem_cons_self
    have e : (u :: us).flatten.map (·.1) = u.map (·.1) ++ us.flatten.map (·.1) := by
      rw [List.flatten_cons, List.map_append]
    have hne : u.map (·.1) ++ us.flatten.map (·.1) ≠ [] := by
      intro h0
      exact gu.ne_nil (List.map_eq_nil_iff.1 (List.append_eq_nil_iff.1 h0).1)
    rw [e, unitsOf_succ hne, unitLen_good gu, List.drop_left' (List.length_map _),
      unitsOf_good us fuel (fun v hv => hg v (List.mem_cons_of_mem _ hv))
        (Nat.le_of_succ_le_succ h)]
    rfl

/-- A list of lists, laid one behind the other and cut by their lengths, is that list. -/
theorem stretchesBy_flatten {α : Type} : ∀ us : List (List α),
    stretchesBy us.flatten (us.map (·.length)) = us
  | [] => rfl
  | u :: us => by
    rw [List.flatten_cons, List.map_cons]
    show (u ++ us.flatten).take u.length ::
      stretchesBy ((u ++ us.flatten).drop u.length) (us.map (·.length)) = _
    rw [List.take_left' rfl, List.drop_left' rfl, stretchesBy_flatten us]

/-- At the kind K4 the cut is the units'. -/
theorem cutOfNames_K4 (ns : List String) : cutOfNames KindName.K4 ns = unitsOf ns.length ns := by
  unfold cutOfNames
  cases unitsOf ns.length ns <;> rfl

theorem length_le_flatten {α : Type} : ∀ us : List (List α), (∀ u ∈ us, u ≠ []) →
    us.length ≤ us.flatten.length
  | [], _ => Nat.le_refl _
  | u :: us, h => by
    have h1 : 1 ≤ u.length := List.length_pos_iff.2 (h u List.mem_cons_self)
    have h2 := length_le_flatten us fun v hv => h v (List.mem_cons_of_mem _ hv)
    rw [List.flatten_cons, List.length_append, List.length_cons]
    omega

/-! ## 3 At K4's row -/

/-- Each unit of K4's row is of one of the two sorts. -/
theorem k4Units_good (Q : K4Pub) : ∀ u ∈ k4Units Q, GoodUnit u := by
  intro u hu
  unfold k4Units k4TailUnits at hu
  split at hu <;>
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hu <;>
    casesm* _ ∨ _ <;> subst_vars <;>
    first
      | exact Or.inr ⟨_, _, _, _, rfl⟩
      | exact Or.inl ⟨_, _, by simp [plainNames], rfl⟩

/-- A declared round of K4's table holds as many scalars as the table's row sends. -/
theorem scalarsIn_entryOf (d : Rd) :
    scalarsIn ({ entry := entryOf d } : Fmt.DeclaredRound) = d.sent := by
  show (24 * d.sent - 32 * 0 - 24 * 0) / 24 = d.sent
  omega

variable {b : Block S Cl} {Q : K4Pub}

/-- CONDITIONAL: on hr. The sub-protocol's rounds as names and counts. -/
theorem k4_rounds_rows
    (hr : b.rounds = (entries Q.P Q.hp Q.g).map fun e => ({ entry := e } : Fmt.DeclaredRound)) :
    b.rounds.map (fun r => (r.entry.name, scalarsIn r)) = (k4Units Q).flatten := by
  rw [hr, ← k4_table_rows]
  unfold entries
  rw [List.map_map, List.map_map]
  refine List.map_congr_left fun d _ => ?_
  exact Prod.ext rfl (scalarsIn_entryOf d)

/-- CONDITIONAL: on hpl and hr. **THE MAKER's CUT IS THE WRITTEN ROW's.** -/
theorem k4_partsCut (hpl : b.place = k4Place Q)
    (hr : b.rounds = (entries Q.P Q.hp Q.g).map fun e => ({ entry := e } : Fmt.DeclaredRound)) :
    partsCut b = (k4Units Q).map (·.length) := by
  have h2 : b.rounds.map (·.entry.name) = (k4Units Q).flatten.map (·.1) := by
    rw [← k4_rounds_rows hr, List.map_map]
    rfl
  unfold partsCut
  rw [h2, hpl]
  show cutOfNames KindName.K4 _ = _
  rw [cutOfNames_K4]
  refine unitsOf_good _ _ (k4Units_good Q) ?_
  rw [List.length_map]
  exact length_le_flatten _ fun u hu => (k4Units_good Q u hu).ne_nil

/-- CONDITIONAL: on hpl and hr. **THE MAKER's PARTS ARE THE WRITTEN ROW.** -/
theorem k4_planParts (hpl : b.place = k4Place Q)
    (hr : b.rounds = (entries Q.P Q.hp Q.g).map fun e => ({ entry := e } : Fmt.DeclaredRound)) :
    planParts b = k4PlanRow Q := by
  unfold planParts
  rw [k4_rounds_rows hr, k4_partsCut hpl hr, stretchesBy_flatten, hpl]
  rfl

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4_table_rows
#print axioms ProofFile.Honest.K4.W.headRun_rounds
#print axioms ProofFile.Honest.K4.W.unitLen_masked
#print axioms ProofFile.Honest.K4.W.unitLen_plain
#print axioms ProofFile.Honest.K4.W.GoodUnit.ne_nil
#print axioms ProofFile.Honest.K4.W.unitLen_good
#print axioms ProofFile.Honest.K4.W.unitsOf_succ
#print axioms ProofFile.Honest.K4.W.unitsOf_good
#print axioms ProofFile.Honest.K4.W.stretchesBy_flatten
#print axioms ProofFile.Honest.K4.W.cutOfNames_K4
#print axioms ProofFile.Honest.K4.W.length_le_flatten
#print axioms ProofFile.Honest.K4.W.k4Units_good
#print axioms ProofFile.Honest.K4.W.scalarsIn_entryOf
#print axioms ProofFile.Honest.K4.W.k4_rounds_rows
#print axioms ProofFile.Honest.K4.W.k4_partsCut
#print axioms ProofFile.Honest.K4.W.k4_planParts
