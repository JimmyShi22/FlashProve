-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/RadiiAtAll.lean: THE RADII OF THE SAMPLED ORACLE MESSAGES AT THE
CLOSED CONSTANT (`hA.𝔇`, Johnson/P5J/MgAtAll.lean), AND WITH THEM THE PREMISE hPlanR OF THE LAW ON
THE SUB-PROTOCOL K1 AT ITS FIFTY LATER PLACES, in the premise's own type. Statements with their
proofs; one small closed fact by Lean's kernel.

THE PREMISES: hA, O, hP1, hP2: as in TestsAtAll.lean (this folder); and
  hRad   where the maker of the sendings' rows returns R at the public files, the first proof
         chain's rows have the written radii: `(P5T.firstRows R).map (·.sampled) =
         Johnson.G.radsFull`: the END of `radii_in_scope`
         (Johnson/HB/LLHARD/RadiiInScope.lean), whose other premises are the scope, the public part
         and hP1. It stands as a premise here: that file is not imported here;
         RadiiAtAllPaid.lean (this folder) calls it.

  `rows_bite`      BY LEAN's KERNEL: the written list has a sending, and its sending number 0 has a
                   seat with an out-of-domain (OOD) sample
  `rows_atAll`     AN IMPLICATION, FOR THE CALL AT THE HEAD; NO PAYMENT: under the head the maker of
                   the rows returns, and the constant's radii are read off what it returns: off the
                   head's own field `plan.radii` (the test `P5T.radIsB`: at every seat with an OOD
                   sample the rows have a radius): with no rows that test rejects. IN THE ASSEMBLY
                   THAT FIELD IS ITSELF PAID FROM "the rows' maker returns" (rowsRead): so this is
                   no payment of rowsRead, which stays owed by name
  `base_atAll`     the piece's base at the place (l, d) is 3 l + moment + 1
  `radAt_atAll`    `RadAt` (Johnson/Desc/AtSeats/MemsAtPlan.lean) at each of the fifty, at the
                   constant's own letters: a call of `radAt_of_rows`
                   (Johnson/Desc/AtSeats/RadAtRows.lean)
  `hPlanR_atAll`   **hPlanR**: a call of `rest_at` (Johnson/Desc/AtSeats/PlanRestAtCut.lean) and
                   `fits_of_cut` (Johnson/Desc/AtSeats/FromTheCut.lean)

What is not claimed. That the rows' maker returns at any files. That hP1 or hP2 accept at any
files. No member of the head hA. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.TiesAtAll
import Johnson.Desc.K1.Law.PlanParts
import Johnson.Desc.AtSeats.RadAtRows
import Johnson.Desc.AtSeats.FromTheCut
import Johnson.Desc.ProofFile.Law.CarryAtLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Params Johnson.G
open OnBytes.Maker (WholeD)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.Sound (linksFull msOf)
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.PlanWritten (madePinnedAt cutIs cutIs_eq)
open _root_.Desc.K14.Law (seatZ secondAt)
open P5T (N0Full psFull)
open ProofFile (Cl)
open IM (Open)

set_option maxRecDepth 1000000 in
theorem rows_bite : 0 < proofSendsFull.1.sends.length ∧ 0 < (P5T.mineAt psFull 0).length := by
  decide +kernel

section
variable {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : First.Look.Place} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)}
  (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
  (O : Open OnBytes.secondHashFunction Zl.pol Zl.lay Zl.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
    (seatZ Zp Np) (secondAt Zp Np))
  (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
include hA O hP1

/-- An implication, no payment: under the head the maker of the rows returns, and the constant's
radii are read off what it returns. Off the head's field `plan.radii`, which in the assembly is
itself paid from "the rows' maker returns": no payment of that condition. -/
theorem rows_atAll : ∃ R, sendRowsOf Zl.pol Zl.lay Zl.KL = .ok R ∧
    P5J.At.rad Zp Zl.lay = P5T.radOf R := by
  have hf := ProofFile.Law.pub_files hA.laid.pub
  have hr : P5T.radIsB ((P5T.rowsAt? Zp.pol Zl.lay Zp.KL).getD []) Zp.made.proof.1.sends.length
      (P5J.At.rad Zp Zl.lay) (P5T.planSeats Zp Zp.D.1) = true := hA.plan.radii
  have eS := PlanWritten.Joined.sends_in_scope hA.scope hA.laid.pub hP1
  have eP := (P5T.seats_in_scope hA.scope hA.laid.pub hP1 (laidP_atAll hA)).1
  cases e : sendRowsOf Zp.pol Zl.lay Zp.KL with
  | error w =>
    exfalso
    have e0 : (P5T.rowsAt? Zp.pol Zl.lay Zp.KL).getD [] = [] := by
      unfold P5T.rowsAt?
      rw [e]
      rfl
    rw [e0, eS, eP] at hr
    unfold P5T.radIsB at hr
    have h1 := List.all_eq_true.1 (List.all_eq_true.1 hr 0 (List.mem_range.2 rows_bite.1)) 0
      (List.mem_range.2 rows_bite.2)
    have h2 : ((none : Option ℕ) == some (P5J.At.rad Zp Zl.lay 0 0)) = true := h1
    cases h2
  | ok R =>
    refine ⟨R, by rw [← hf.1, ← hf.2]; exact e, ?_⟩
    unfold P5J.At.rad P5T.rowsAt?
    rw [e]
    rfl

variable (hP2 : cutIs (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true)
include hP2

/-- The piece's base at the place (l, d). -/
theorem base_atAll (l : ℕ) (hl : l < 25) (d : Bool) :
    baseD (D.at frS.P.T.a) cF l d = baseL3 l d := by
  refine (baseK_atAll hA O (noL l d) (noL_lt l hl d)).trans ?_
  rw [(atAll_letters hA O hP1).1,
    atBlocks_written N0Full _ _ cF.blocksInOrder (LPFK9.blockPlaces_full hA.scope hA.reads O)]
  exact trees_of_cut (bs := cF.blocksInOrder) (cutIs_eq hP2).1 _ l hl d

variable (hRad : ∀ R, sendRowsOf Zl.pol Zl.lay Zl.KL = .ok R →
    (P5T.firstRows R).map (·.sampled) = radsFull)
include hRad

/-- **RadAt at each of the fifty, at the constant's own letters.** -/
theorem radAt_atAll (l : ℕ) (hl : l < 25) (d : Bool) :
    RadAt Zp.made.proof.1.sends.length (P5J.At.rad Zp Zl.lay) (P5T.planSeats Zp Zp.D.1)
      (parL Zp Bs.G₀ l d) (radRec (recL l d) (parL Zp Bs.G₀ l d))
      (baseD (D.at frS.P.T.a) cF l d) := by
  obtain ⟨R, hR, eR⟩ := rows_atAll hA O hP1
  have eL : recL l d = 3 * l + cond d 2 1 := by cases d <;> rfl
  rw [PlanWritten.Joined.sends_in_scope hA.scope hA.laid.pub hP1,
    (P5T.seats_in_scope hA.scope hA.laid.pub hP1 (laidP_atAll hA)).1, eR,
    parL_place (hc_atAll hA O hP1) (hs_atAll hA O hP1)
      (K13.Law.gpOf_in_scope hA.scope hA.laid.pub hP1) l d,
    base_atAll hA O hP1 hP2 l hl d, eL]
  exact radAt_of_rows (hRad R hR) l hl d

/-- **hPlanR.** -/
theorem hPlanR_atAll : ∀ l, l < 25 → ∀ d : Bool,
    PlanRest hA.𝔇.pubD.cs hA.𝔇.G hA.𝔇.ms (parL Zp Bs.G₀ l d)
      (radRec (recL l d) (parL Zp Bs.G₀ l d)) (baseD (D.at frS.P.T.a) cF l d)
      (hA.𝔇.N.sent l (momL d)) := by
  intro l hl d
  obtain ⟨R, hR, eR⟩ := rows_atAll hA O hP1
  have eS := PlanWritten.Joined.sends_in_scope hA.scope hA.laid.pub hP1
  have eP := (P5T.seats_in_scope hA.scope hA.laid.pub hP1 (laidP_atAll hA)).1
  have eL : recL l d = 3 * l + cond d 2 1 := by cases d <;> rfl
  have eM : hA.𝔇.ms =
      msOf (P5T.memberListsR proofSendsFull.1.sends.length (P5T.radOf R) psFull) := by
    show P5T.msAtR Zp (P5J.At.rad Zp Zl.lay) = _
    unfold P5T.msAtR
    rw [eS, eP, eR]
  have eN : hA.𝔇.N.sent l (momL d) = N0Full.sent l (cond d 2 1) := by
    have e : hA.𝔇.N.sent = N0Full.sent := congrArg (·.sent) (atAll_letters hA O hP1).1
    rw [e]
    cases d <;> rfl
  have eC : hA.𝔇.pubD.cs = codesFull2 :=
    (K13.Law.likeFull_in_scope hA.scope hA.laid.pub hP1).codes
  have hn : ∀ p ∈ psFull, p.smpd = true → p.send < proofSendsFull.1.sends.length := by
    intro p hp _
    have h := P5T.planSeats_send_lt Zp Zp.D.1 p (by rw [eP]; exact hp)
    rw [eS] at h
    exact h
  rw [eM, eN, eC, parL_place (hc_atAll hA O hP1) (hs_atAll hA O hP1)
      (K13.Law.gpOf_in_scope hA.scope hA.laid.pub hP1) l d,
    base_atAll hA O hP1 hP2 l hl d, eL]
  obtain ⟨h1, h2, h3, h4⟩ := rest_at hA.𝔇.G l hl d (cs := codesFull2) rfl
    (radAt_of_rows (hRad R hR) l hl d)
    (fits_of_cut hA.𝔇.G (P5T.radOf R) hn (cutIs_eq hP2).1)
  exact ⟨h1, h2, h3.one, h3.pad, h3.row, h4⟩

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.rows_bite
#print axioms VerifiableInference.Desc.K1.rows_atAll
#print axioms VerifiableInference.Desc.K1.base_atAll
#print axioms VerifiableInference.Desc.K1.radAt_atAll
#print axioms VerifiableInference.Desc.K1.hPlanR_atAll
