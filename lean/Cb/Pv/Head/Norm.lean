-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Head/Norm.lean: the first rounds of the final norm in the sub-proof of the output head, as one
chain of blocks: the point, the nine sums with their batch, the layer of the sum of squares.

The final norm is stated by 17 identities at every position (Inst/Model/Common/Ledger.lean: idn).
They read the sums W_s of limb products of the stream and the digits of a row. The chain of this
file leads
  from: the 17 identities hold at every position;
  to: the 17 identities hold at the drawn point, with the nine hidden values that the prover has
    sent in the place of the sums' extensions, and with the extensions of the digits and of the row
    products; the claim that the layer's sumcheck leaves holds; and each of the layer's two hidden
    end values is the extension of the limbs' batch at the point of challenges.
The rounds are those of the plan: ZERO; BAT-sigma with nine scalars; PSC epsilon, lPd + lt times
PSC round, PSC Y, PSC values; LINE.

Main definitions: normNums, normIdn, NormAt, prodTrue, normD, rideP, normFrame, rideS, toLayer,
normR, normErr, HNorm.
Main theorems: idnP_congr, idnP_congr_pv, norm_ext, norm_point, norm_layer, norm_knowAt, hNorm,
norm_nums.

Letters. limb, slot: as in Cb/Pv/Head/Squares.lean. dig m n a: digit n of the row at position a. Q:
whatever else is claimed rides along.

What is not claimed. The row products still stand as extensions of products of digits: the blocks
behind this chain reduce them. That the verifier's routine computes this chain's output is not shown
here. 2 must not be 0 in the field. Nothing is said about hiding.


-/
import Cb.Pv.Head.Point
import Cb.Pv.Head.Batch
import Cb.Pv.Head.SquaresSum
import Inst.Model.Common.LedgerForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Head
open Iop Prob TWhole Finset Inst.Model

/-- An identity reads the sums at the numbers below 9 alone. -/
theorem idnP_congr {K : Type} [CommRing K] (np : NormPar) {Ws Ws' : ℕ → K} (D pv : ℕ → K) (k : ℕ)
    (h : ∀ t < 9, Ws t = Ws' t) : Ledger.idnP np Ws D pv k = Ledger.idnP np Ws' D pv k := by
  by_cases hk : k < 9
  · rw [Ledger.idnP_j1 np _ _ _ hk, Ledger.idnP_j1 np _ _ _ hk, h k hk]
  · unfold Ledger.idnP
    rw [if_neg hk, if_neg hk]

/-- An identity reads the products at the numbers below 7 alone. -/
theorem idnP_congr_pv {K : Type} [CommRing K] (np : NormPar) (Ws D : ℕ → K) {pv pv' : ℕ → K}
    (k : ℕ) (h : ∀ j < 7, pv j = pv' j) :
    Ledger.idnP np Ws D pv k = Ledger.idnP np Ws D pv' k := by
  by_cases hk9 : k < 9
  · rw [Ledger.idnP_j1 np _ _ _ hk9, Ledger.idnP_j1 np _ _ _ hk9]
  · by_cases hk17 : 17 ≤ k
    · rw [Ledger.idnP_of_le np _ _ _ hk17, Ledger.idnP_of_le np _ _ _ hk17]
    · have hc : k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 := by omega
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · show pv 1 - Ledger.Blo D - 2 ^ 23 * Ledger.Bhi D =
          pv' 1 - Ledger.Blo D - 2 ^ 23 * Ledger.Bhi D
        rw [h 1 (by norm_num)]
      · show Ledger.Vlo D + (np.eps : K) - pv 0 - 2 ^ 25 * Ledger.Blo D - Ledger.l1 D +
            2 ^ 48 * Ledger.kc D =
          Ledger.Vlo D + (np.eps : K) - pv' 0 - 2 ^ 25 * Ledger.Blo D - Ledger.l1 D +
            2 ^ 48 * Ledger.kc D
        rw [h 0 (by norm_num)]
      · show Ledger.Vhi D - Ledger.Bhi D - pv 2 - Ledger.kc D =
          Ledger.Vhi D - Ledger.Bhi D - pv' 2 - Ledger.kc D
        rw [h 2 (by norm_num)]
      · rfl
      · show pv 4 + pv 5 - Ledger.q1 D = pv' 4 + pv' 5 - Ledger.q1 D
        rw [h 4 (by norm_num), h 5 (by norm_num)]
      · exact h 6 (by norm_num)
      · show 2 ^ (np.M + 1) + Ledger.sig D - Ledger.s0 D - 2 * pv 3 - 2 ^ 25 * Ledger.q1 D -
            2 * Ledger.rr D =
          2 ^ (np.M + 1) + Ledger.sig D - Ledger.s0 D - 2 * pv' 3 - 2 ^ 25 * Ledger.q1 D -
            2 * Ledger.rr D
        rw [h 3 (by norm_num)]
      · rfl

/-- The errors of the chain's rounds, as counts of draws, over a field of q elements: the point
lt q^(lt - 1) of the q^lt points; the batch of nine 8; then the layer's and LINE's. -/
def normNums (q : ℕ) (s : SqSize) : List ℕ := [s.lt * q ^ (s.lt - 1)] ++ ([8] ++ sqNums s)

section
variable {E : Type} [Field E] [Fintype E] {J P M Wp Kc : Type} [Fintype J] [DecidableEq J]
variable (np : NormPar) (limb : (J → E) → ℕ → ℕ → E) (dig : (J → E) → ℕ → ℕ → E) (slot : ℕ → J)

/-- Identity k of the final norm at position a. -/
def normIdn (s : SqSize) (m : J → E) (k a : ℕ) : E :=
  Ledger.idn np (Ledger.Wsum (2 ^ s.lPd) fun l j => limb m l (2 ^ s.lt * j + a))
    (fun n => dig m n a) k

/-- The 17 identities at the point pv, on the extensions of the digits, with W in the place of the
nine sums' extensions and V in the place of the seven row products' extensions. -/
def NormAt (s : SqSize) (pv : Fin s.lt → E) (W : Fin 9 → E) (V : Fin 7 → E) (m : J → E) : Prop :=
  ∀ k < 17, Ledger.idnP np (Blocks.nat W) (fun n => Blocks.ext s.lt (dig m n) (Blocks.nat pv))
    (Blocks.nat V) k = 0

/-- The true value of row product number j: its extension over the positions at the point pv. -/
def prodTrue (s : SqSize) (m : J → E) (pv : Fin s.lt → E) (j : ℕ) : E :=
  Blocks.ext s.lt (fun a => Ledger.prods (fun n => dig m n a) j) (Blocks.nat pv)

omit [Fintype E] [Fintype J] [DecidableEq J] in
/-- The extension of an identity is the identity on the extensions. -/
theorem norm_ext (s : SqSize) (m : J → E) (pv : Fin s.lt → E) (k : ℕ) :
    Blocks.ext s.lt (normIdn np limb dig s m k) (Blocks.nat pv) =
      Ledger.idnP np (fun t => sqTrue limb s m pv t)
        (fun n => Blocks.ext s.lt (dig m n) (Blocks.nat pv)) (fun j => prodTrue dig s m pv j) k :=
  (Blocks.ext_congr
    (w := fun a => Ledger.idnP np
      (Ledger.Wsum (2 ^ s.lPd) fun l j => limb m l (2 ^ s.lt * j + a)) (fun n => dig m n a)
      (Ledger.prods fun n => dig m n a) k)
    (fun _ _ => Ledger.idn_eq_idnP np _ _ k) (Blocks.nat pv)).trans
    (Ledger.ext_idnP s.lt (fun n a => dig m n a) (Blocks.nat pv) np
      (fun t a => Ledger.Wsum (2 ^ s.lPd) (fun l j => limb m l (2 ^ s.lt * j + a)) t)
      (fun j a => Ledger.prods (fun n => dig m n a) j) k)

variable (Ex : ExtSpec) (msg : M → J → E) (Q : IOR.Rels Kc P Ex (M × Wp))

/-- The family of the 17 vectors, as a function of the committed messages. -/
def normD (s : SqSize) : M → ℕ → ℕ → E := fun mm k a => normIdn np limb dig s (msg mm) k a

/-- What rides, on the statement with the point. -/
def rideP (s : SqSize) : IOR.Rels Kc (P × (Fin s.lt → E)) Ex (M × Wp) where
  rel := fun x y w => Q.rel x.1 y w
  relR := fun a w => Q.relR (a.1.1, a.2) w
  on := fun a => Q.on (a.1.1, a.2)
  core := Q.core

/-- The round of the nine sums: their places, their true values, and what is claimed of them. -/
@[reducible] def normFrame (s : SqSize) : Bat.BatFrame E 9 where
  X := P × (Fin s.lt → E)
  J := J
  Kc := Kc
  M := M
  Wp := Wp
  Ex := Ex
  A0 := rideP Ex Q s
  msg := msg
  msk := fun t => slot t
  tv := fun x m t => sqTrue limb s m x.2 t
  phi := fun x W m => NormAt np dig s x.2 W (fun j => prodTrue dig s m x.2 j) m

/-- What rides through the layer: Q, and the 17 identities on the nine hidden values. -/
def rideS (s : SqSize) : IOR.Rels Kc (SqSt E P s) Ex (M × Wp) where
  rel := fun x y w => Q.rel x.pub y w ∧
    NormAt np dig s x.pv (fun t => x.sent t - msg w.1 (slot t))
      (fun j => prodTrue dig s (msg w.1) x.pv j) (msg w.1)
  relR := fun a w => Q.relR (a.1.pub, a.2) w ∧
    NormAt np dig s a.1.pv (fun t => a.1.sent t - msg w.1 (slot t))
      (fun j => prodTrue dig s (msg w.1) a.1.pv j) (msg w.1)
  on := fun a => Q.on (a.1.pub, a.2)
  core := Q.core

/-- From what the round of the nine sums hands on to the layer's claim. -/
def toLayer (s : SqSize) (b : ((P × (Fin s.lt → E)) × (Fin 9 → E)) × E) : E × SqSt E P s :=
  (sqTarget s ⟨b.1.1.1, b.1.1.2, b.1.2, b.2⟩, ⟨b.1.1.1, b.1.1.2, b.1.2, b.2⟩)

omit [Fintype J] [DecidableEq J] in
/-- The point's block, up to the joint before the nine sums. -/
theorem norm_point (s : SqSize) :
    KnowAt (pointR (E := E) (P := P) Ex ⟨s.lt, 17⟩)
      (pointA Ex (normD np limb dig msg s) Q ⟨s.lt, 17⟩)
      (Bat.batIn (normFrame np limb dig slot Ex msg Q s)) (fun _ _ _ wp => wp)
      (pointErr (E := E) (P := P) (Kc := Kc) Ex ⟨s.lt, 17⟩) :=
  knowAt_mono (point_knowAt Ex (normD np limb dig msg s) Q ⟨s.lt, 17⟩) (fun _ h => h)
    (fun _ _ _ h => h)
    (fun b w _ h => ⟨h.1, fun k hk =>
      (norm_ext np limb dig s (msg w.1) b.1.2 k).trans
        ((idnP_congr np _ _ k fun t ht => by
          unfold Blocks.nat
          rw [dif_pos ht]).trans
          ((idnP_congr_pv np _ _ k fun j hj => by
            unfold Blocks.nat
            rw [dif_pos hj]).trans (h.2 k hk)))⟩)
    (fun _ h => h)

/-- The layer's block, from the joint behind the nine sums. -/
theorem norm_layer (s : SqSize) (h2 : (2 : E) ≠ 0) :
    KnowAt ((sqR (P := P) limb slot Ex s).pre (fun x => some (toLayer s x)) (ExtMap.id Ex))
      (Bat.batOut (normFrame np limb dig slot Ex msg Q s))
      (sqB limb slot Ex msg s (rideS np dig slot Ex msg Q s)) (fun _ _ _ wp => wp)
      (sqErr (P := P) (Kc := Kc) limb slot Ex s) :=
  knowAt_preMap (A' := Bat.batOut (normFrame np limb dig slot Ex msg Q s)) (toLayer s)
    (fun _ _ h => h)
    (fun _ _ _ _ h => by exact ⟨h.1.1, h.1.2, (sq_batch limb slot s h2 _ _).1 h.2⟩)
    (sq_knowAt limb slot Ex msg s (rideS np dig slot Ex msg Q s))

/-- The chain. -/
noncomputable def normR (s : SqSize) :
    IOR P Ex ((sqKind (P := P) limb slot s).par.Out × E) Ex :=
  (pointR (E := E) (P := P) Ex ⟨s.lt, 17⟩).seq
    ((Bat.batR E (P × (Fin s.lt → E)) 9 Ex).seq
      ((sqR (P := P) limb slot Ex s).pre (fun x => some (toLayer s x)) (ExtMap.id Ex)))

/-- Its errors. -/
noncomputable def normErr (s : SqSize) : Err (normR (P := P) limb slot Ex s).shape :=
  Err.app (pointErr (E := E) (P := P) (Kc := Kc) Ex ⟨s.lt, 17⟩)
    (Err.app (Bat.batErr E (P × (Fin s.lt → E)) 9 Ex) (sqErr (P := P) (Kc := Kc) limb slot Ex s))

/-- The chain between its joints, for all sizes. -/
theorem norm_knowAt (s : SqSize) (h2 : (2 : E) ≠ 0) :
    KnowAt (normR (P := P) limb slot Ex s) (pointA Ex (normD np limb dig msg s) Q ⟨s.lt, 17⟩)
      (sqB limb slot Ex msg s (rideS np dig slot Ex msg Q s)) (fun _ _ _ wp => wp)
      (normErr (P := P) (Kc := Kc) limb slot Ex s) :=
  knowAt_seq (norm_point np limb dig slot Ex msg Q s)
    (knowAt_seq (Bat.bat_knowAt (normFrame np limb dig slot Ex msg Q s))
      (norm_layer np limb dig slot Ex msg Q s h2))

/-- The chain's soundness property, at the sizes of the list. -/
def HNorm : Prop :=
  ∀ s ∈ sqSizes, ∀ m : M,
    (normR (P := P) limb slot Ex s).red.Know (pointA Ex (normD np limb dig msg s) Q ⟨s.lt, 17⟩).on
      (fun a wp => (pointA Ex (normD np limb dig msg s) Q ⟨s.lt, 17⟩).relR a (m, wp))
      (fun b wp => (sqB limb slot Ex msg s (rideS np dig slot Ex msg Q s)).relR b (m, wp))
      (fun _ _ wp => wp) (normErr (P := P) (Kc := Kc) limb slot Ex s)

/-- The property holds where 2 is not 0. -/
theorem hNorm (h2 : (2 : E) ≠ 0) : HNorm np limb dig slot Ex msg Q :=
  fun s _ m => (norm_knowAt np limb dig slot Ex msg Q s h2).know m

/-- The errors are the written list, in the order of the plan's rounds. -/
theorem norm_nums (s : SqSize) :
    errList (normErr (P := P) (Kc := Kc) limb slot Ex s) = normNums (Fintype.card E) s := by
  have h1 := errList_app (pointErr (E := E) (P := P) (Kc := Kc) Ex ⟨s.lt, 17⟩)
    (Err.app (Bat.batErr E (P × (Fin s.lt → E)) 9 Ex) (sqErr (P := P) (Kc := Kc) limb slot Ex s))
  have h2 := errList_app (Bat.batErr E (P × (Fin s.lt → E)) 9 Ex)
    (sqErr (P := P) (Kc := Kc) limb slot Ex s)
  have h3 := sq_nums (P := P) (Kc := Kc) limb slot Ex s
  exact h1.trans (by
    rw [h2, h3]
    rfl)

end

end Cb.Pv.Head

#print axioms Cb.Pv.Head.norm_knowAt
#print axioms Cb.Pv.Head.hNorm
#print axioms Cb.Pv.Head.norm_nums
