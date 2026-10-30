-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerLast.lean: AT THE SHARED CHAIN's LAST BORDER THE TWO READERS OF A WITNESS
ARE ONE AT o_omega, FROM WHAT STANDS BESIDE shapeK THERE. The tie (same_omega,
Johnson/Desc/K14/Law/LedgerReader.lean) asks five things of the record. HERE THEY ARE HAD from three
tests with code at border 12: sharedX (the book in order; o_omega's number; its
place; its tree: sharedX_twelve, Johnson/Desc/Sound/SharedX.lean) and codY and omY
(Johnson/Desc/K14/Law/LedgerNew.lean).

  ent_at_omega    hent has a source: the seam's premises and one more fact on the plan's letter oNo.
  seat_at_last    the seat that the record's own book gives o_omega's number.
  omega_at_last   **the tie at the last border**: SameOmega's body
                  (Johnson/Desc/K14/Law/ClaimsRead.lean), at wordsSh.
WHAT STAYS, ALL ON THE PLAN: hnO (nO is the number of o_u's sending's messages) · hm (the plan's mem
lays a member at nO) · hent (it bears the plan's shape: ent_at_omega) · hten (it sits at t₁ + the
first tree + o_omega's place by the two layouts) · hin (the layout's indices lie inside the
message's range). The last border is written 12: the shared chain with a split.
IT HAS NO CALLER OF THE MEANT KIND, AND CAN HAVE NONE: this file stands over the fence
(Johnson/Desc/Sound/Fence.lean); the last chain's words stand over Johnson/Desc/Sound/WordsAt.lean;
each declares a structure Sound.Booked: no module can import both: so omega_at_last and wordsSh_is
(Johnson/Desc/K14/Law/LedgerReaderAt.lean) meet in no module, K14's included, until one of the two
is renamed. And codY 12 |
omY 12 are reached by no term until the two tests' clauses hand them on (LedgerNew.lean's head).
What is not claimed. No member. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.LedgerNew
import Johnson.Desc.K14.Law.LedgerReader

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Cb Johnson.Pack Desc.Plain
open OnBytes.Means (Words)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.K1 (shapesOf shapeAt)
open VerifiableInference.Desc.Sound
open Desc.K14.Law.Fence (sharedX sharedX_twelve)

/-- The seat that the record's own book gives o_omega's number. -/
theorem seat_at_last (Q : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (d : St)
    (hO : 0 < (withOmega Q.S).size) (hX : sharedX Q sentU layU layO 12 d = true) (t₁ : ℕ) :
    seatBy (noShared t₁) d.book sentU.size =
      some (t₁ + (Q.par.toGPar.firstTree + (layU.shapes.size + layO.tree.getD 0 0)),
        layO.part.getD 0 0) := by
  obtain ⟨⟨_, ho⟩, _, hp, ht⟩ := sharedX_twelve Q sentU layU layO d hO hX
  obtain ⟨T, hT, _⟩ := Option.map_eq_some_iff.1 ht
  rw [seatBy_some (noShared t₁) d.book sentU.size _ T hp hT]
  show some (t₁ + T.number, _) = _
  rw [ho _ T hT]

/-- **hent has a source**: a new member of "send o_omega" that bears o_omega's number is the first
message's, so it bears that message's shape. (The seam's premises all, hno, entry, Johnson/Desc/K14/
Law/LedgerSeamRow.lean, with ONE MORE FACT on the plan's letter oNo: hoO. Without it the premises
say that the member at o_omega's seat is memK k for SOME sampled k.) -/
theorem ent_at_omega (Q : P14) (rad : ℕ → ℕ) (oNo : Mem → ℕ) (nO : ℕ)
    (memK : Fin (shapesOf (parO Q)).length → Mem) (new : List Mem)
    (entry : ∀ k, (memK k).1.l.get (memK k).2 = (shapeAt (parO Q) k, rad k.val))
    (all : ∀ x ∈ new, ∃ k, VerifiableInference.Desc.K1.sampledAt (parO Q) k ∧ memK k = x)
    (hno : ∀ k, VerifiableInference.Desc.K1.sampledAt (parO Q) k → oNo (memK k) = nO + k.val)
    (h0 : 0 < (shapesOf (parO Q)).length) (x : Mem) (hx : x ∈ new) (hoO : oNo x = nO) :
    (x.1.l.get x.2).1 = shapeAt (parO Q) ⟨0, h0⟩ := by
  obtain ⟨k, hk, rfl⟩ := all x hx
  have e := hno k hk
  rw [hoO] at e
  have hk0 : k = ⟨0, h0⟩ := Fin.ext (by show k.val = 0; omega)
  rw [entry k, hk0]

variable {Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (mem : ℕ → Option Mem)

/-- **The tie at the last border.** -/
theorem omega_at_last (Q : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (d : St)
    (hO : 0 < (withOmega Q.S).size) (h0 : 0 < (shapesOf (parO Q)).length) (nO : ℕ)
    (hnO : nO = sentU.size) (hX : sharedX Q sentU layU layO 12 d = true)
    (hY : codY Q 12 d = true) (hZ : omY (shapeAt (parO Q) ⟨0, h0⟩) nO 12 d = true) (t₁ : ℕ)
    (S : LinShape) (w : Wit Cells Tok MsgT) (x : Mem) (hm : mem nO = some x)
    (hent : (x.1.l.get x.2).1 = shapeAt (parO Q) ⟨0, h0⟩)
    (hten : x.1.seat x.2 =
      (t₁ + (Q.par.toGPar.firstTree + (layU.shapes.size + layO.tree.getD 0 0)),
        layO.part.getD 0 0))
    (hin : ∀ y < S.matrixRows, (linLayOmega d.st.codes S).index y /
      2 ^ ceilLog2 (x.1.l.get x.2).1.mainRows < (pMain Q.codes (x.1.l.get x.2).1).ell) :
    ∀ y < S.matrixRows,
      wordsSh arr t₁ d.st d.book w d.loc.oOmega .main ((linLayOmega d.st.codes S).index y) =
        rgOf Q.codes arr mem (rdK Q.codes) w d.loc.oOmega .main
          ((linLayOmega d.st.codes S).index y) := by
  have eO : d.loc.oOmega = nO := by
    rw [hnO]
    exact (sharedX_twelve Q sentU layU layO d hO hX).2.1
  obtain ⟨X, hx, hs, _, _⟩ := ((omY_iff _ nO 12 d).1 hZ).resolve_left (by omega)
  refine same_omega Q.codes arr mem t₁ S d w x X (by rw [eO]; exact hm)
    (((codY_iff Q 12 d).1 hY).resolve_left (by omega)) (by rw [eO]; exact hx) (hs.trans hent.symm)
    ?_ hin
  rw [eO, hnO, hten]
  exact seat_at_last Q sentU layU layO d hO hX t₁

end Desc.K14.Law

#print axioms Desc.K14.Law.ent_at_omega
#print axioms Desc.K14.Law.seat_at_last
#print axioms Desc.K14.Law.omega_at_last
