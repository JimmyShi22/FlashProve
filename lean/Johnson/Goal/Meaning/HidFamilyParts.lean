-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HidFamilyParts.lean: Means at a witness's hidden values from single clauses,
one premise a clause, where each sub-proof reads messages of its own.

means_of_fifteen (Johnson/Goal/Meaning/MeansParts.lean) gives Means at hidAt from fifteen clauses,
each at the sub-proof's own list ownAt, at ONE family of messages. Here the same at a family msgF of
readings (Johnson/Goal/Meaning/HidFamily.lean), with the one premise more: MsgsOne, reader's and
owner's messages agree at the shared seats.

THREE OF THE FIFTEEN ARE IDLE AT THESE LISTS. The three clauses on smallness (SmallM, AttSmall,
Hd.SmallH) hold at these lists by the make, for every msgF, where the shift is not 0 and twice the
shift is at most 2^18 (small_ownAt): a list behind symbols is made of small integers or 0. So they
say nothing of a witness, and MEANS AT hidAtF IS NO EVIDENCE THAT THE COMMITTED SYMBOLS ARE SMALL OR
ARE A PACKING: that is BaseSegF's claim, which no theorem here gives. DROPPING THE THREE MAKES
NOTHING CHEAPER TO PAY: their work moves to BaseSegF, which is needed wherever a law on the messages
is carried to these lists (the head of Johnson/Goal/Meaning/HidBase.lean). The debt has moved, not
shrunk.

Main names:
  small_ownAt, small_ownAtF   where the shift is not 0 and twice the shift is at most 2^18: every
    entry of a witness's list is below 2^18 in absolute value.
  means_of_fifteenF   at all public files in the goals' scope: Means at hidAtF from the fifteen
    clauses at ownAtF.
  means_of_twelveF   the same from the twelve that are left:
      the layers, at ownAtF (2 g):      NormField · EmbField · HotField · KeyField
      attention, at ownAtF (2 g + 1):   AttOwn1 · AttOwn2 · AttRidden · AttKey
      the head, at ownAtF 24:           the 17 identities of the final normalisation · the cost
                                        ledger's two lines at every position · the ledger's two sums
                                        · HeadKeys.

Premises beside the clauses: the three facts on the files; Follows; the seats' form seatBy f;
MsgsOne; Head3 x; for the twelve: the two inequalities on the shift.
What is not claimed. Any clause of anything; which law ends in which clause; MsgsOne of any witness.
THE SEAMS ARE STILL MOVED, NOT PAID. The program does not import this file.
-/
import Johnson.Goal.Meaning.HidFamily
import Johnson.Goal.Meaning.MeansParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open OnBytes OnBytes.Road OnBytes.Road.L5 OnBytes.Road.Rows.Norms
open OnBytes.Model.Verify (publicOf layerShape borderOf)
open Cb.Pv.Tail (Size)
open Inst.Model (ppref Instance NormPar AcceptancePolicy Mat)

/-- **By the make**: every entry of a witness's list is small. -/
theorem small_ownAt {s : ℕ → Size} {seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ} {msg : Msgs}
    {k : ℕ} (h0 : (0 : ℤ) < ((s k).beta : ℤ)) (h2 : 2 * ((s k).beta : ℤ) ≤ 2 ^ 18) (a r c : ℕ) :
    |ownAt s seat msg k a r c| < 2 ^ 18 := by
  unfold ownAt ownOf mzTot
  split_ifs with h hc hr
  · exact lt_of_lt_of_le (small_mzAt _ h0 _ _ _) h2
  · simp
  · simp
  · simp

theorem small_ownAtF {s : ℕ → Size} {seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ}
    {msgF : ℕ → Msgs} {k : ℕ} (h0 : (0 : ℤ) < ((s k).beta : ℤ))
    (h2 : 2 * ((s k).beta : ℤ) ≤ 2 ^ 18) (a r c : ℕ) : |ownAtF s seat msgF k a r c| < 2 ^ 18 :=
  small_ownAt (msg := msgF k) h0 h2 a r c

/-- **THE SUM FROM FIFTEEN CLAUSES, AT A FAMILY**, at all public files in the goals' scope. -/
theorem means_of_fifteenF {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : Model.Verify.Public} (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {s : ℕ → Size} (F : Follows X s)
    {f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ} {msgF : ℕ → Msgs} (E : MsgsOne X s f msgF) {i : Cm.Idx}
    {x : Instance ppref} (tok : Fin ppref.V) (hx : Inst.Model.Head3 x)
    (gSmall : ∀ g < 12, SmallM X.y (ownAtF s (seatBy f X s) msgF (2 * g)))
    (gNorm : ∀ g < 12, NormField (layerShape X.P) X.layers.sc X.y g
      (ownAtF s (seatBy f X s) msgF (2 * g)) i.mat x)
    (gEmb : ∀ g < 12, EmbField (layerShape X.P) X.layers.sc X.y g
      (ownAtF s (seatBy f X s) msgF (2 * g)) i.mat x)
    (gHot : ∀ g < 12, HotField (layerShape X.P) X.layers.sc X.y g
      (ownAtF s (seatBy f X s) msgF (2 * g)) i.mat x)
    (gKey : ∀ g < 12, KeyField (layerShape X.P) X.layers.sc X.y g
      (ownAtF s (seatBy f X s) msgF (2 * g)) i.mat)
    (aSmall : ∀ g < 12, AttSmall (Hd.shapeA X g) (ownAtF s (seatBy f X s) msgF (2 * g + 1)))
    (aOwn1 : ∀ g < 12, AttOwn1 (Hd.shapeA X g) (ownAtF s (seatBy f X s) msgF (2 * g + 1)))
    (aOwn2 : ∀ g < 12, AttOwn2 (Hd.shapeA X g) (ownAtF s (seatBy f X s) msgF (2 * g + 1)))
    (aRidden : ∀ g < 12, AttRidden (Hd.shapeA X g) (ownAtF s (seatBy f X s) msgF (2 * g + 1)))
    (aKey : ∀ g < 12, AttKey (Hd.shapeA X g) (ownAtF s (seatBy f X s) msgF (2 * g + 1)))
    (hSmall : Hd.SmallH X.hS X.HLy (borderOf X.y) (ownAtF s (seatBy f X s) msgF 24))
    (hIdn : ∀ p < Inst.Model.Head.nT, ∀ k < 17,
      Inst.Model.Head.N.idn (Hd.npOf X.hS)
        ((Hd.cellsH X.hS X.HLy (borderOf X.y) (ownAtF s (seatBy f X s) msgF 24)).cast Cb.Gl.F)
        p k = 0)
    (hLines : ∀ p < Inst.Model.Head.nT,
      Inst.Model.Head.dB4
          ((Hd.cellsH X.hS X.HLy (borderOf X.y) (ownAtF s (seatBy f X s) msgF 24)).cast Cb.Gl.F)
          (Inst.Model.Head.Req.of (Hd.polOf X.hS) x) p = 0 ∧
        Inst.Model.Head.dZ
          ((Hd.cellsH X.hS X.HLy (borderOf X.y) (ownAtF s (seatBy f X s) msgF 24)).cast Cb.Gl.F)
          (Inst.Model.Head.Req.of (Hd.polOf X.hS) x) p = 0)
    (hSums : Inst.Model.Head.sB2
          ((Hd.cellsH X.hS X.HLy (borderOf X.y) (ownAtF s (seatBy f X s) msgF 24)).cast Cb.Gl.F)
          (Inst.Model.Head.Req.of (Hd.polOf X.hS) x) = 0 ∧
      Inst.Model.Head.sB3
          ((Hd.cellsH X.hS X.HLy (borderOf X.y) (ownAtF s (seatBy f X s) msgF 24)).cast Cb.Gl.F)
          (Inst.Model.Head.Req.of (Hd.polOf X.hS) x) = 0)
    (hKey : HeadKeys X.hS X.HLy X.y (Hd.npOf X.hS) (Hd.polOf X.hS) i.mat x
      (ownAtF s (seatBy f X s) msgF 24)) :
    Means X pp i x (hidAtF X s (seatBy f X s) tok msgF) :=
  means_followsF h (Hd.core_of_scope hZ hR h) F E tok
    (fun g hg => ord_of_ownG ⟨gSmall g hg, gNorm g hg, gHot g hg, gEmb g hg, gKey g hg⟩)
    (fun g hg => ord_of_ownA ⟨aSmall g hg, aKey g hg, aOwn1 g hg, aOwn2 g hg, aRidden g hg⟩)
    (headPlain_of_ord hZ hR h i x _ hx (headOrd_of_clauses hx hSmall hIdn hLines hSums hKey))

/-- **The sum from twelve clauses**: the three on smallness hold at these lists by the make, of
every witness. That makes nothing cheaper to pay: see the file's head. -/
theorem means_of_twelveF {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : Model.Verify.Public} (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {s : ℕ → Size} (F : Follows X s)
    {f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ} {msgF : ℕ → Msgs} (E : MsgsOne X s f msgF) {i : Cm.Idx}
    {x : Instance ppref} (tok : Fin ppref.V) (hx : Inst.Model.Head3 x)
    (h0 : ∀ k < 25, (0 : ℤ) < ((s k).beta : ℤ)) (h2 : ∀ k < 25, 2 * ((s k).beta : ℤ) ≤ 2 ^ 18)
    (gNorm : ∀ g < 12, NormField (layerShape X.P) X.layers.sc X.y g
      (ownAtF s (seatBy f X s) msgF (2 * g)) i.mat x)
    (gEmb : ∀ g < 12, EmbField (layerShape X.P) X.layers.sc X.y g
      (ownAtF s (seatBy f X s) msgF (2 * g)) i.mat x)
    (gHot : ∀ g < 12, HotField (layerShape X.P) X.layers.sc X.y g
      (ownAtF s (seatBy f X s) msgF (2 * g)) i.mat x)
    (gKey : ∀ g < 12, KeyField (layerShape X.P) X.layers.sc X.y g
      (ownAtF s (seatBy f X s) msgF (2 * g)) i.mat)
    (aOwn1 : ∀ g < 12, AttOwn1 (Hd.shapeA X g) (ownAtF s (seatBy f X s) msgF (2 * g + 1)))
    (aOwn2 : ∀ g < 12, AttOwn2 (Hd.shapeA X g) (ownAtF s (seatBy f X s) msgF (2 * g + 1)))
    (aRidden : ∀ g < 12, AttRidden (Hd.shapeA X g) (ownAtF s (seatBy f X s) msgF (2 * g + 1)))
    (aKey : ∀ g < 12, AttKey (Hd.shapeA X g) (ownAtF s (seatBy f X s) msgF (2 * g + 1)))
    (hIdn : ∀ p < Inst.Model.Head.nT, ∀ k < 17,
      Inst.Model.Head.N.idn (Hd.npOf X.hS)
        ((Hd.cellsH X.hS X.HLy (borderOf X.y) (ownAtF s (seatBy f X s) msgF 24)).cast Cb.Gl.F)
        p k = 0)
    (hLines : ∀ p < Inst.Model.Head.nT,
      Inst.Model.Head.dB4
          ((Hd.cellsH X.hS X.HLy (borderOf X.y) (ownAtF s (seatBy f X s) msgF 24)).cast Cb.Gl.F)
          (Inst.Model.Head.Req.of (Hd.polOf X.hS) x) p = 0 ∧
        Inst.Model.Head.dZ
          ((Hd.cellsH X.hS X.HLy (borderOf X.y) (ownAtF s (seatBy f X s) msgF 24)).cast Cb.Gl.F)
          (Inst.Model.Head.Req.of (Hd.polOf X.hS) x) p = 0)
    (hSums : Inst.Model.Head.sB2
          ((Hd.cellsH X.hS X.HLy (borderOf X.y) (ownAtF s (seatBy f X s) msgF 24)).cast Cb.Gl.F)
          (Inst.Model.Head.Req.of (Hd.polOf X.hS) x) = 0 ∧
      Inst.Model.Head.sB3
          ((Hd.cellsH X.hS X.HLy (borderOf X.y) (ownAtF s (seatBy f X s) msgF 24)).cast Cb.Gl.F)
          (Inst.Model.Head.Req.of (Hd.polOf X.hS) x) = 0)
    (hKey : HeadKeys X.hS X.HLy X.y (Hd.npOf X.hS) (Hd.polOf X.hS) i.mat x
      (ownAtF s (seatBy f X s) msgF 24)) :
    Means X pp i x (hidAtF X s (seatBy f X s) tok msgF) :=
  means_of_fifteenF hZ hR h F E tok hx
    (fun g hg _ r c _ => small_ownAtF (h0 _ (by omega)) (h2 _ (by omega)) _ r c)
    gNorm gEmb gHot gKey
    (fun g hg _ _ => small_ownAtF (h0 _ (by omega)) (h2 _ (by omega)) _ _ _)
    aOwn1 aOwn2 aRidden aKey
    (Hd.smallH_of_all fun a r c => small_ownAtF (h0 24 (by norm_num)) (h2 24 (by norm_num)) a r c)
    hIdn hLines hSums hKey

end Meaning

#print axioms Meaning.small_ownAt
#print axioms Meaning.small_ownAtF
#print axioms Meaning.means_of_fifteenF
#print axioms Meaning.means_of_twelveF
