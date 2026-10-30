-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/CellsAt.lean

Limits. CONDITIONAL. THAT THE TIE `K4CellsTieAt` (Law/ScriptAt.lean) HOLDS ANYWHERE is not shown:
it is a hypothesis on the thread's parameters: what the witness's tables hold at the seats own.
That the reader M of the matrices is the library's `matsOfData` at the plan's list tl and the
arrays' names is a hypothesis (hM), as the head of Law/Table.lean means M. Two public equations on
the plan's list are hypotheses too: hm (the honest side's sizes of the matrices are tl's) and hNM
(tl counts its own list): `K4Plan` (Johnson/Road/K4/W/GroundOfHear.lean) has both among its fields
(tails with mats; NM), and Law/W/FootAtStand.lean takes them from there. No example is known.
Nothing on soundness, on completeness or on any other property.
No property is claimed.
WHAT THIS FILE's IMPORTS REACH: as Law/RowBatch.lean's.

What is here. `CellsAre` (Johnson/Road/K4/C/Cells.lean: the matrices that the item's sentence
reads hold the honest input's cells, off the matrix of the lookup's planes) at every state behind
the step of the member of the layers' own rounds (kind K4), from that tie at the stand in front.
Statements with their proofs.

  `sizes_at`: where a row and a column lie below the honest side's sizes of matrix i, i stands in
      tl's list and they lie below that entry's numbers.
  `cellsAre_at`: CellsAre Q w Mm at w := the row's small input at the stand's input and Mm := M at
      the state behind and at what the item's sentence reads of the witness there, at every
      continuation of the challenges.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.RowBatch
import Johnson.Desc.ProofFile.Honest.K4.Law.ScriptAt
import Johnson.Road.K4.C.Cells

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes.Model (HTailF2)
open OnBytes.Model.Layer (Own)
open OnBytes.Road.K4.C (CellsAre CellsOn)
open OnBytes.Desc.First.K4 (Par seatS)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block Claim First.S)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ dataQ matsOfData)

/-- Below the honest side's sizes of matrix i: i stands in tl's list, and below its numbers. -/
theorem sizes_at {Q : K4Pub} {tl : HTailF2} (hm : matsOf Q = tl.mats.map fun M => (M.m, M.k))
    {i r c : Nat} (hr : r < ((matsOf Q).getD i (0, 0)).1) (hc : c < ((matsOf Q).getD i (0, 0)).2) :
    i < tl.mats.size ∧ r < (tl.mats.getD i {}).m ∧ c < (tl.mats.getD i {}).k := by
  rw [hm, Array.getD_eq_getD_getElem?, Array.getElem?_map] at hr hc
  rw [Array.getD_eq_getD_getElem?]
  cases hi : tl.mats[i]? with
  | none =>
    rw [hi] at hr
    exact absurd hr (Nat.not_lt_zero r)
  | some Mi =>
    rw [hi] at hr hc
    refine ⟨?_, hr, hc⟩
    by_contra hlt
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt hlt)] at hi
    cases hi

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}

/-- **`CellsAre` BEHIND THE MEMBER's STEP.** CONDITIONAL: on the seat, the tie at the stand in
front, the reader M, and two public equations. -/
theorem cellsAre_at {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {b : Nat} {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
    {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Q : K4Pub} {p : Par}
    {blk : Block First.S Claim} (Se : K4Seated T b cells weights tokens look Q p blk)
    (hSit : K4Sits T b p) {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X}
    {E : Env} {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn} (hS : T.Stepped blk k s m E ds y cols s')
    {A : VerifiableInference.Desc.K9.Part} {o : Own} (hA : segAt? s' = some A)
    (ho : seatS.own s' = some o) {tl : HTailF2} {names : Array (Nat × String)}
    {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}
    (hC : K4CellsTieAt T cells weights tokens look Q tl names own rdOf k s m)
    {M : First.S → Bound GQ → OnBytes.Road.Mats GQ} (hM : ∀ t D, M t D = matsOfData tl names D)
    (hm : matsOf Q = tl.mats.map fun M => (M.m, M.k)) (hNM : tl.NM = tl.mats.size)
    (ds' : List Fmt.Drawn) :
    CellsAre Q (k4Wit Q cells weights tokens (look Q) m.st.input)
      (M s' (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds'))))) := by
  obtain ⟨a, _, _, ha, _, _, _, _, hdata⟩ := step_tape Se hSit hS hA ho
  obtain ⟨i1, i2⟩ := moved_state hS.1
  intro i hi r c hr hc
  obtain ⟨h1, h2, h3⟩ := sizes_at hm hr hc
  rw [hM, hdata, i1, i2, List.append_assoc]
  exact (hC a ha (ds ++ ds') i r c (hNM ▸ h1) hi h2 h3).symm

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.sizes_at
#print axioms ProofFile.Honest.K4.cellsAre_at
