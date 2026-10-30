-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/G4/RunRows.lean: what a sumcheck of the lookup hands on, field by field, on plain data that
fit.

OnBytes/G4/RunValues.lean names what a sumcheck hands on as "what Psc.run gives" (`pscOut`). Psc.run
gives
something only where sizes fit. This file writes out the record that it then gives (`runValue`),
shows
that on rounds that fit the plan's entries it does give it (`run_eq`, `heardOf_sizes`, `pscOut_eq`),
and
reads off the row's coefficients on the kept maps, which the laws on rows in RunValues.lean take as
a
premise (`pscOut_rowMaps_nil`, `pscOut_rowMaps_leaves`).

Main definitions: runValue, placed.
Main theorems: run_eq, heardOf_sizes, pscOut_eq, pscOut_rowMaps_nil, pscOut_rowMaps_leaves.
Not claimed: as in OnBytes/G4/RunLaws.lean.
-/
import OnBytes.G4.RunValues

set_option autoImplicit false

namespace OnBytes.G4

open Blk

/-- The record that Psc.run gives where it gives one. -/
def runValue (c : Psc.Claim) (Sm : Psc.Summand) (fresh : List Slot) (h : Psc.Heard) : Psc.Out :=
  let vars := Psc.varsOf c Sm
  let challenges := h.rounds.map (·.2)
  let point := challenges.take c.vars.length
  let a := Sm.coeffs point h.values
  let hw := Psc.hidingWalk (vars.zip challenges)
  let last := Psc.claimAfter vars h.rounds (addE h.mu (mulE h.eps c.target))
  let beta := if Sm.shown == 0 then none else challenges.getLast?
  { point := point
    rowMasks := fresh.zip hw.1 ++ Psc.scaleForm (mulE h.eps hw.2) c.masks
    rowMaps := (a.drop 1).map fun x => mulE h.eps x
    rowTarget := subE last (mulE h.eps (a.headD zeroE))
    ends := ((fresh.drop hw.1.length).zip h.values).map fun p =>
      ⟨point, [(p.1, beta.getD zeroE)], p.2⟩
    eps := h.eps
    beta := beta }

/-- Where the sizes fit, Psc.run gives that record. -/
theorem run_eq (c : Psc.Claim) (Sm : Psc.Summand) (fr : List Slot) (h : Psc.Heard)
    (hform : Psc.formOK c Sm = true) (hfr : fr.length = Psc.masksOf c Sm)
    (hl : h.rounds.map (fun p => p.1.length) = (Psc.varsOf c Sm).map (fun w => w.d - 1))
    (hv : h.values.length = Sm.shown) (ha : ∀ p y, (Sm.coeffs p y).length = 1 + Sm.kept)
    (hd : ∀ w ∈ Psc.varsOf c Sm, 1 ≤ w.d) :
    Psc.run c Sm fr h = some (runValue c Sm fr h) := by
  have hlen : h.rounds.length = (Psc.varsOf c Sm).length := by
    simpa using congrArg List.length hl
  have cond : (Psc.formOK c Sm && fr.length == Psc.masksOf c Sm &&
      h.rounds.length == (Psc.varsOf c Sm).length && h.values.length == Sm.shown &&
      (Sm.coeffs ((h.rounds.map (·.2)).take c.vars.length) h.values).length == 1 + Sm.kept &&
      (((Psc.varsOf c Sm).zip h.rounds).all fun p => p.2.1.length + 1 == p.1.d)) = true := by
    simp [hform, hfr, hlen, hv, ha, sizes_fit _ _ hl hd]
  unfold Psc.run
  simp only []
  rw [if_pos cond]
  rfl

/-- The sizes of what a sumcheck reads of rounds that fit its entries. -/
theorem heardOf_sizes (work : Nat) (x : Psc.Size) (es' : List Fmt.Entry) (rs : List FlatRound)
    (h : FitsAll rs (pscEntries work x ++ es')) :
    (heardOf x rs).rounds.map (fun p => p.1.length) =
        x.degree.map (· - 1) ++ (if x.withY then [x.degreeY] else []) ∧
      (heardOf x rs).values.length = (if x.withY then x.values else 0) := by
  -- both laws on Psc.hear speak of one call, at any public inputs
  have hq : NoRows none := by intro e he; cases he
  obtain ⟨_, _, _, hval⟩ := hear_val default work 0 #[] x es' rs none hq h
  obtain ⟨hd', _, _, _, _, hat, hlens, hvals⟩ := hear_at default work 0 #[] x es' rs none hq h
  have hsame : hd' = heardOf x rs := by
    rw [hval] at hat
    exact (congrArg Prod.fst (Except.ok.inj hat)).symm
  subst hsame
  exact ⟨hlens, hvals⟩

/-- A sumcheck's record with the coordinates of its points put back at their variables' places. -/
def placed (place : List E → List E) (o : Psc.Out) : Psc.Out :=
  { o with
    point := place o.point
    ends := o.ends.map fun x => { x with point := place x.point } }

/-- On rounds that fit, what a sumcheck of the lookup hands on, field by field. -/
theorem pscOut_eq (work : Nat) (c : Psc.Claim) (Sm : Psc.Summand) (place : List E → List E)
    (k : Nat)
    (es' : List Fmt.Entry) (rs : List FlatRound)
    (hfit : FitsAll rs (pscEntries work (Psc.sizeOf c Sm) ++ es'))
    (hform : Psc.formOK c Sm = true) (ha : ∀ p y, (Sm.coeffs p y).length = 1 + Sm.kept)
    (hd : ∀ w ∈ Psc.varsOf c Sm, 1 ≤ w.d) :
    pscOut c Sm place k rs =
      placed place (runValue c Sm (slotsFrom k (Psc.masksOf c Sm))
          (heardOf (Psc.sizeOf c Sm) rs)) := by
  obtain ⟨hlens, hvals⟩ := heardOf_sizes work (Psc.sizeOf c Sm) es' rs hfit
  rw [lens_eq] at hlens
  have hv : (heardOf (Psc.sizeOf c Sm) rs).values.length = Sm.shown := by
    rw [hvals]
    unfold Psc.sizeOf
    by_cases h : Sm.shown = 0 <;> simp [h, Nat.pos_of_ne_zero]
  have ho := run_eq c Sm (slotsFrom k (Psc.masksOf c Sm)) (heardOf (Psc.sizeOf c Sm) rs) hform
    (slotsFrom_length _ _) hlens hv ha hd
  simp [pscOut, placed, ho]

/-- A sumcheck without a kept map has no coefficient on a kept map, whatever the data. -/
theorem pscOut_rowMaps_nil (c : Psc.Claim) (Sm : Psc.Summand) (place : List E → List E) (k : Nat)
    (rs : List FlatRound) (hk : Sm.kept = 0) : (pscOut c Sm place k rs).rowMaps = [] := by
  show ((Psc.run c Sm (slotsFrom k (Psc.masksOf c Sm))
    (heardOf (Psc.sizeOf c Sm) rs)).getD default).rowMaps = []
  cases ho : Psc.run c Sm (slotsFrom k (Psc.masksOf c Sm)) (heardOf (Psc.sizeOf c Sm) rs) with
  | none => rfl
  | some o =>
    unfold Psc.run at ho
    simp only [] at ho
    split at ho
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      have hlen := hc.1.2
      injection ho with ho
      subst ho
      simp only [Option.getD_some]
      apply List.length_eq_zero_iff.1
      simp [hlen, hk]
    · cases ho

/-- The sumcheck on the leaves of the table's tree has one coefficient on a kept map: the element
that
joins the first polynomial to the claim, times the leaves' factor at the point. -/
theorem pscOut_rowMaps_leaves (S : Lkp.Public) (theta alpha : E) (order : List Nat) (work : Nat)
    (c : Psc.Claim) (place : List E → List E) (k : Nat) (es' : List Fmt.Entry) (rs : List FlatRound)
    (hfit : FitsAll rs
      (pscEntries work (Psc.sizeOf c (Lkp.summandLeaves S theta alpha order)) ++ es'))
    (hform : Psc.formOK c (Lkp.summandLeaves S theta alpha order) = true)
    (hd : ∀ w ∈ Psc.varsOf c (Lkp.summandLeaves S theta alpha order), 1 ≤ w.d) :
    (pscOut c (Lkp.summandLeaves S theta alpha order) place k rs).rowMaps =
      [mulE (heardOf (Psc.sizeOf c (Lkp.summandLeaves S theta alpha order)) rs).eps
        (Lkp.leavesFactor S theta alpha (Lkp.byVariable
          (((heardOf (Psc.sizeOf c (Lkp.summandLeaves S theta alpha order)) rs).rounds.map
            (·.2)).take c.vars.length) order))] := by
  rw [pscOut_eq work c _ place k es' rs hfit hform (fun _ _ => rfl) hd]
  rfl

end OnBytes.G4

#print axioms OnBytes.G4.run_eq
#print axioms OnBytes.G4.heardOf_sizes
#print axioms OnBytes.G4.pscOut_eq
#print axioms OnBytes.G4.pscOut_rowMaps_nil
#print axioms OnBytes.G4.pscOut_rowMaps_leaves
