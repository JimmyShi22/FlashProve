-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/PlanSevenAt.lean: THE SEVEN PREMISES ON THE PLAN THAT THE
CLOSING KIND K10's LAW TAKES (`k10_two_cs`, Johnson/Desc/First/Close/Law/LawTwoCs.lean: hSit · hAl ·
hHit · hAlM · hGrp · hi1 · hi2), AT THE COMPOSED MEANING's OWN LETTERS, IN THE GOALS' SCOPE, WHERE
THE VERIFIER's OWN VALUE IS LAID AND THE ROWS' MAKER RETURNS: ONE BUNDLE A LINK. A joining: other
files have all seven at the written values, by Lean's kernel; joints in three other sets of files
carry the written values to the letters. A structure, one closed test, theorems. A law file; no
running text imports it.
  `PlanSeven Nu ms arr links ps k p lo seat`   THE SEVEN, TO THE LETTER, as one structure.
  `pinsLowB`, `pinsLow_full`, `pinsLow_bent`, `pin_low`   a closed test on the table, BY THE KERNEL:
                    at a place of the kind K10 every pin that the row closes or reads has a moment
                    below 3; the control: below 2 it fails.
  `arr_at_laid`       the letters' numbering of the witness's messages is the written one.
  `plan_seven_at`     at a place p of the kind K10 of At.ps whose link's number lies below 25:
                    PlanSeven (At.N Zp cF) (At.ms Zp Z.lay) (At.arr Zp) fullLinks At.ps k p lo
                    (seatK10 lo (At.pseats Zp) l), l := p.link.getD 0, lo := the l-th written list.
                    AT l = 0 TOO (there lo is the six-list).
  `plan_seven_of`     the tool: the seven from six sentences at the written values, general in the
                    list and the seats: PlanSevenFive.lean beside this file spends it at link 0's
                    five-list.

Limits. PREMISES: the scope · the value is laid, at OnBytes.secondHashFunction · P5J.rowsRead Z (the rows' maker
returns: the one named condition). The full size alone. Nothing on the verifier's state. "The value
is laid" is spent here also for the entry test madeRow (Johnson/Desc/Laid/ProofAsks.lean: what the
planner has made is the written): by P5J.pins_of_laid's first half and LaidAt.seats. Nothing on
soundness or on hiding.
-/
import Johnson.Desc.First.Close.Law.AlikeInScope
import Johnson.Desc.First.Close.Law.MainAtFull
import Johnson.Desc.First.Close.Law.SeatsApart
import Johnson.Desc.Sound.BordersFill
import Johnson.P5J.K10Lays
import Johnson.Goal.Skeleton.RowsRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes
open OnBytes.Maker (WholeD)
open Johnson.G (linksFullLit memMain)
open VerifiableInference.Desc (Chain Place KindName)
open VerifiableInference.Desc.Sound (Mem SitsAt Alike seatOf mineAt insQ rowQ msOf)
open VerifiableInference.Desc.First (Numbers ModelPart Item laysSeats)
open VerifiableInference.Desc.First.Close

/-- **THE SEVEN PREMISES ON THE PLAN**, to the letter. -/
structure PlanSeven (Nu : Numbers) (ms : List Mem) (arr : ℕ → ℕ → ℕ) (links : List ModelPart)
    (ps : List Place) (k : ℕ) (p : Place) (lo : List (OracleShape × ℕ))
    (seat : Fin lo.length → ℕ × ℕ) : Prop where
  hSit : ∀ t, insQ links ps k (Item.pin (p.link.getD 0) t) →
    ∀ s ∈ Nu.sent (p.link.getD 0) t, ∃ y ∈ ms, SitsAt y s.1 s.2
  hAl : ∀ t, insQ links ps k (Item.pin (p.link.getD 0) t) →
    ∀ s ∈ Nu.sent (p.link.getD 0) t, ∀ y ∈ ms, SitsAt y s.1 s.2 →
      ∃ i : Fin lo.length, memMain lo i ∧ Alike y ⟨⟨lo, seat⟩, i⟩
  hHit : ∀ i, memMain lo i → ∃ y ∈ ms, Alike y ⟨⟨lo, seat⟩, i⟩
  hAlM : ∀ y ∈ mineAt ms Nu links p, ∃ i : Fin lo.length, Alike y ⟨⟨lo, seat⟩, i⟩
  hGrp : ∀ i, memMain lo i →
    seat i ∈ laysSeats Nu links p ∨ seat i ∈ Nu.keptOf (p.link.getD 0)
  hi1 : ∀ i i' : Fin lo.length,
    arr (seat i).1 (seat i).2 = arr (seat i').1 (seat i').2 → i = i'
  hi2 : Function.Injective seat

/-- A closed test on the table: at the places of the kind K10 every pin among what the row closes
or reads has a moment below n. -/
def pinsLowB (n : ℕ) : Bool :=
  (List.range P5J.At.ps.length).all fun k =>
    (P5J.At.ps[k]?).all fun p => !(p.kind == KindName.K10) ||
      ((rowQ P5J.fullLinks P5J.At.ps k).ins ++ (rowQ P5J.fullLinks P5J.At.ps k).ctx ++
        [Item.unmarked]).all fun i =>
          match i with
          | .pin _ t => decide (t < n)
          | _ => true

set_option maxRecDepth 1000000 in
theorem pinsLow_full : pinsLowB 3 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The control. -/
theorem pinsLow_bent : pinsLowB 2 = false := by decide +kernel

/-- So a pin of such a row has a moment below 3. -/
theorem pin_low {k : ℕ} {p : Place} (hp : P5J.At.ps[k]? = some p) (hK : p.kind = KindName.K10)
    {m t : ℕ} (h : insQ P5J.fullLinks P5J.At.ps k (Item.pin m t)) : t < 3 := by
  have hk : k < P5J.At.ps.length := (List.getElem?_eq_some_iff.1 hp).1
  have a := List.all_eq_true.1 pinsLow_full k (List.mem_range.2 hk)
  rw [hp] at a
  simp only [Option.all_some, hK, beq_self_eq_true, Bool.not_true, Bool.false_or] at a
  exact of_decide_eq_true (List.all_eq_true.1 a _ h)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl}

/-- The letters' numbering is the written one. -/
theorem arr_at_laid (hW : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) : P5J.At.arr Zp = arrFull := by
  unfold P5J.At.arr P5J.At.pseatsAll
  rw [(P5T.seats_in_scope hW L.pub (P5J.pins_of_laid hW L).1 L.laidPOf).2.1]

/-- A tenant of one of the three moments lies in the group. -/
theorem sent_in_group (Nu : Numbers) (l : ℕ) {t : ℕ} (ht : t < 3) {s : ℕ × ℕ}
    (hs : s ∈ Nu.sent l t) : s ∈ Nu.group l := by
  unfold Numbers.group
  simp only [List.mem_append]
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl
  · exact Or.inl (Or.inl hs)
  · exact Or.inl (Or.inr hs)
  · exact Or.inr hs

/-- What a row of the kind K10 lays lies in the group. -/
theorem lays_in_group (Nu : Numbers) (links : List ModelPart) {p : Place} (hK : p.kind = KindName.K10)
    {s : ℕ × ℕ} (hs : s ∈ laysSeats Nu links p) : s ∈ Nu.group (p.link.getD 0) := by
  unfold laysSeats at hs
  split at hs
  · exact absurd hs List.not_mem_nil
  · rw [hK] at hs
    exact (List.mem_filter.1 hs).1

/-- The seven from six sentences at the written values: general in the list and the seats. -/
theorem plan_seven_of (hW : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) (hrr : P5J.rowsRead Z) {k : ℕ}
    {p : Place} (hp : P5J.At.ps[k]? = some p) (hK : p.kind = KindName.K10)
    (hl : p.link.getD 0 < 26) {lo : List (OracleShape × ℕ)} {seat : Fin lo.length → ℕ × ℕ}
    (a1 : ∀ x ∈ msOf mlFull, seatOf x ∈ P5T.N0Full.group (p.link.getD 0) →
      ∃ i : Fin lo.length, Alike x ⟨⟨lo, seat⟩, i⟩)
    (a2 : ∀ i : Fin lo.length, ∃ x ∈ msOf mlFull, Alike x ⟨⟨lo, seat⟩, i⟩)
    (a3 : ∀ x ∈ msOf mlFull, seatOf x ∈ P5T.N0Full.group (p.link.getD 0) →
      ∃ i : Fin lo.length, memMain lo i ∧ Alike x ⟨⟨lo, seat⟩, i⟩)
    (a4 : ∀ i : Fin lo.length, memMain lo i → seat i ∈ P5T.N0Full.group (p.link.getD 0))
    (a5 : ∀ i i' : Fin lo.length,
      arrFull (seat i).1 (seat i).2 = arrFull (seat i').1 (seat i').2 → i = i')
    (a6 : Function.Injective seat) :
    PlanSeven (P5J.At.N Zp cF) (P5J.At.ms Zp Z.lay) (P5J.At.arr Zp) P5J.fullLinks P5J.At.ps k p lo
      seat := by
  obtain ⟨R, hr⟩ := hrr.rows
  have ems := ms_at_laid hW L hr
  have egr := group_at_laid (cF := cF) hW L (p.link.getD 0)
  refine ⟨fun t hin s hs => ?_, fun t hin s hs y hy hsit => ?_, fun i _ => ?_, fun y hy => ?_,
    fun i hi => ?_, ?_, a6⟩
  · rw [ems]
    exact sit_full _ hl s (egr ▸ sent_in_group _ _ (pin_low hp hK hin) hs)
  · rw [ems] at hy
    have e : seatOf y = s := hsit
    exact a3 y hy (by rw [e]; exact egr ▸ sent_in_group _ _ (pin_low hp hK hin) hs)
  · rw [ems]
    exact a2 i
  · obtain ⟨hy1, hy2⟩ := List.mem_filter.1 hy
    rw [ems] at hy1
    have h2 : seatOf y ∈ laysSeats (P5J.At.N Zp cF) P5J.fullLinks p := by simpa using hy2
    exact a1 y hy1 (egr ▸ lays_in_group _ _ hK h2)
  · exact P5J.k10_grp_at _ k p hp hK _ (egr.symm ▸ a4 i hi)
  · rw [arr_at_laid hW L]
    exact a5

/-- **The seven at the written list.** -/
theorem plan_seven_at (hW : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) (hrr : P5J.rowsRead Z) {k : ℕ}
    {p : Place} (hp : P5J.At.ps[k]? = some p) (hK : p.kind = KindName.K10)
    (hl : p.link.getD 0 < 25) :
    PlanSeven (P5J.At.N Zp cF) (P5J.At.ms Zp Z.lay) (P5J.At.arr Zp) P5J.fullLinks P5J.At.ps k p
      (linksFullLit.getD (p.link.getD 0) [])
      (seatK10 (linksFullLit.getD (p.link.getD 0) []) (P5J.At.pseats Zp) (p.link.getD 0)) := by
  have e1 : P5J.At.pseats Zp = P5T.psFull := L.seats hW
  have h26 : p.link.getD 0 < 26 := by omega
  rw [e1]
  exact plan_seven_of hW L hrr hp hK h26 (alike_full _ h26) (hit_full _ h26)
    (alikeMain_full _ h26) (grp_full _ h26) (num_inj_full _ h26) (seat_inj_full _ h26)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.pinsLow_full
#print axioms VerifiableInference.Desc.LinkJoin.pinsLow_bent
#print axioms VerifiableInference.Desc.LinkJoin.pin_low
#print axioms VerifiableInference.Desc.LinkJoin.arr_at_laid
#print axioms VerifiableInference.Desc.LinkJoin.plan_seven_of
#print axioms VerifiableInference.Desc.LinkJoin.plan_seven_at
