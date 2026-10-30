-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ShapesAtFront.lean: the kind "the code switch" (K2): A LISTED
MESSAGE's SHAPE AND THE FRESH MASK's SHAPE IN THE FORM IN WHICH THE PREMISES ON THE CARRIED CLAIM
WRITE THEM: `(St.oracles.getD o default).shape`: at a statement St with the oracle messages of a
state reached without a mark, under the head. Statements with their proofs; no definition. On the
verifier's side and a place's public data alone.

  `getD_shape_of_map` `(Os[n]?).map (·.shape) = some sh` ⊢ `(Os.getD n default).shape = sh`
  `member_shape_getD` `AtMgA` · a reached at a border without a mark · `noK10 … l i` stated ·
                    St.oracles = a's ⊢ the shape at that number is `((loAt l).get i).1`
  `mask_shape_getD` the like, with the opening, p₀ ∈ `switchPlaces Zp Bs.G₀`, p₀.link < 25, `maskNo
                    … p₀.link` stated ⊢ the shape at that number is that of the last message of p₀'s
                    sending

By: `listed_reached` (Johnson/Desc/K2/Honest/Returns/SeatReached.lean) · `mask_shape_at_head`
(Honest/K2/Law/FirstShapes.lean) · the library's `shape_at_no` (Johnson/LPFE1R/ShapeAtNo.lean),
`AtMgA.fold_full` (Johnson/P5J/MaskLettersAtMg.lean), its field `msgShapes`.

Limits. No run is given at which the head's premise and "reached" hold together: the two laws under
the head could hold of nothing. That the number is stated is a premise (paid at a switch's fronts by
Returns/SeatReached.lean and Returns/FreshNumbered.lean). The full size and the format's second
hash function alone. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.FirstShapes
import Johnson.Desc.K2.Honest.Returns.SeatReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (noK10)
open VerifiableInference.Desc.LinkJoin (loAt shape_at_no)
open VerifiableInference.Desc.K2.Honest.Returns (listed_reached)
open VerifiableInference.Desc.Sound (allOf EAll)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- Where a list of oracle messages has a message of shape sh at number n, its entry there, read
with a default, has that shape. -/
theorem getD_shape_of_map {Os : Array OnBytes.Oracle} {n : Nat} {sh : OnBytes.OracleShape}
    (h : (Os[n]?).map (·.shape) = some sh) : (Os.getD n default).shape = sh := by
  obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 h
  rw [Array.getD_eq_getD_getElem?, hy]
  exact e

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- **A LISTED MESSAGE's SHAPE, AS THE CARRIED CLAIM's PREMISES WRITE IT**: at a statement St with
the oracle messages of a state reached without a mark, where the message's number is stated. -/
theorem member_shape_getD (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {k : Nat} (hk : k ≤ 358)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch k a) (hu : a.1.2.failed = none) {l : Nat} (hl : l < 25)
    (i : Fin (loAt l).length)
    (ho : noK10 (P5J.At.seats Zp) (loAt l) (P5J.At.pseats Zp) l i < a.1.2.st.oracles.size)
    {St : OnBytes.Statement} (hSt : St.oracles = a.1.2.st.oracles) :
    (St.oracles.getD (noK10 (P5J.At.seats Zp) (loAt l) (P5J.At.pseats Zp) l i) default).shape =
      ((loAt l).get i).1 := by
  rw [hSt]
  exact getD_shape_of_map (listed_reached h hk a hr hu hl i ho).2

/-- **THE FRESH MASK's SHAPE, THE LIKE**: it is the shape of the last message of the sending of the
switch that leads into the link. -/
theorem mask_shape_getD (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {k : Nat}
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch k a) (hu : a.1.2.failed = none)
    {p₀ : SwitchPlace} (hp₀ : p₀ ∈ switchPlaces Zp Bs.G₀) (hl : p₀.link < 25)
    (ho : VerifiableInference.Desc.First.Close.maskNo (P5J.At.seats Zp) (P5J.At.pseats Zp) p₀.link <
      a.1.2.st.oracles.size)
    {St : OnBytes.Statement} (hSt : St.oracles = a.1.2.st.oracles) :
    (St.oracles.getD (VerifiableInference.Desc.First.Close.maskNo (P5J.At.seats Zp)
      (P5J.At.pseats Zp) p₀.link) default).shape =
      ((switchSent p₀.sizes p₀.others).getD ((switchSent p₀.sizes p₀.others).size - 1)
        default).shape := by
  rw [hSt]
  exact getD_shape_of_map (shape_at_no (h.fold_full.msgShapes k a hr hu) ho
    (mask_shape_at_head h.toAtMg O hp₀ hl))

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.getD_shape_of_map
#print axioms ProofFile.Honest.K2.Law.member_shape_getD
#print axioms ProofFile.Honest.K2.Law.mask_shape_getD
