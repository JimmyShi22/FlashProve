-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/MeansParts.lean: the sum means_follows (Johnson/Goal/Meaning/HidPlanFit.lean)
from single clauses: one premise a clause, each at the sub-proof's own list, each under the name
under which the clause stands in Johnson/Road/Rows/LayerTop.lean, Johnson/Goal/Meaning/Row.lean and
Johnson/Road/Lane5SplitH.lean.

LayerR0, AttR0 and HeadR0 (MeansJoints.lean, MeansSix.lean) are bundles: no one law ends in one of
them. Here they are cut.
  attKeys_is_attKey: AttKeys (Johnson/Road/Lane5SplitA.lean:63) is AttKey (Row.lean): one
    term.
  attR0_iff: AttR0 is AttSmall, AttOwn1, AttOwn2 and AttRidden together. With
    attOrd_iff_split this is the cut of attention's five: AttR0 carries four, AttKeys one.
  means_of_parts: from the records OwnG and OwnA (Johnson/Goal/Meaning/HidOwn.lean) and HeadPlain.
    Under the public core.
  means_of_clauses: the same with the ten clauses as ten premises:
      the layers, at own (2 g):        SmallM · NormField · EmbField · HotField · KeyField
      attention, at own (2 g + 1):     AttSmall · AttOwn1 · AttOwn2 · AttRidden · AttKey
  headOrd_of_clauses: Hd.HeadOrdLB from five clauses on the head's list and Head3 of the request:
      Hd.SmallH · the 17 identities of the final normalisation · the cost ledger's two lines at
      every position · the ledger's two sums · HeadKeys. (The record's sixth clause, y = 0 where the
      request ends before the window's end, follows from Head3.)
  means_of_fifteen: at all public files in the goals' scope: Means from these fifteen clauses.
Premises beside the clauses: publicOf's line with the public core, or the three facts on the files;
Follows, the seats' form and the messages (see the head of HidPlanFit.lean); Head3 x.
Not claimed: any clause of anything; which law ends in which clause.
-/
import Johnson.Goal.Meaning.HidPlanFit
import Johnson.Goal.Meaning.HeadOrdPlain
import Johnson.Road.Lane5SplitA
import Johnson.Road.Lane5SplitH

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open OnBytes OnBytes.Road OnBytes.Road.L5 OnBytes.Road.Rows.Norms
open OnBytes.Model.Verify (publicOf layerShape borderOf)
open Cb.Pv.Tail (Size)
open Inst.Model (ppref Instance NormPar AcceptancePolicy Mat)

/-! ## Attention's cut -/

/-- One term under two names. -/
theorem attKeys_is_attKey {S : Attention.Shape} {Za : Zs} : AttKeys S Za ↔ AttKey S Za := Iff.rfl

/-- AttR0 is four of attention's five clauses. -/
theorem attR0_iff {S : Attention.Shape} {Za : Zs} :
    AttR0 S Za ↔ AttSmall S Za ∧ AttOwn1 S Za ∧ AttOwn2 S Za ∧ AttRidden S Za :=
  ⟨fun R => ⟨R.1, fun k b g' n hv => R.2 (.at1 k b g' n) hv, fun b g' n hv => R.2 (.at2 b g' n) hv,
      fun b g' n hv => R.2 (.at3 b g' n) hv⟩,
    fun ⟨hS, h1, h2, h3⟩ => ⟨hS, fun j hj => by
      cases j with
      | at1 k b g' n => exact h1 k b g' n hj
      | at2 b g' n => exact h2 b g' n hj
      | at3 b g' n => exact h3 b g' n hj⟩⟩

/-! ## The sum from the layers' and attention's clauses -/

section Core
variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- The sum from the two records of clauses. -/
theorem means_of_parts (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {s : ℕ → Size}
    (F : Follows X s) (f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ) {pp : Inst.Model.ScalesAndPolicy} {i : Cm.Idx}
    {x : Instance ppref} (tok : Fin ppref.V) (msg : Msgs)
    (OG : ∀ g < 12, OwnG X i x (ownAt s (seatBy f X s) msg (2 * g)) g)
    (OA : ∀ g < 12, OwnA (Hd.shapeA X g) (ownAt s (seatBy f X s) msg (2 * g + 1)))
    (H : HeadPlain pp i x (headStream X (ownAt s (seatBy f X s) msg 24))) :
    Means X pp i x (hidAt X s (seatBy f X s) tok msg) :=
  means_follows h C F f tok msg (fun g hg => ord_of_ownG (OG g hg))
    (fun g hg => ord_of_ownA (OA g hg)) H

/-- THE SUM, ONE PREMISE A CLAUSE: ten clauses and the head's. -/
theorem means_of_clauses (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P)
    {s : ℕ → Size} (F : Follows X s) (f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ) {pp : Inst.Model.ScalesAndPolicy}
    {i : Cm.Idx} {x : Instance ppref} (tok : Fin ppref.V) (msg : Msgs)
    (gSmall : ∀ g < 12, SmallM X.y (ownAt s (seatBy f X s) msg (2 * g)))
    (gNorm : ∀ g < 12, NormField (layerShape X.P) X.layers.sc X.y g
      (ownAt s (seatBy f X s) msg (2 * g)) i.mat x)
    (gEmb : ∀ g < 12, EmbField (layerShape X.P) X.layers.sc X.y g
      (ownAt s (seatBy f X s) msg (2 * g)) i.mat x)
    (gHot : ∀ g < 12, HotField (layerShape X.P) X.layers.sc X.y g
      (ownAt s (seatBy f X s) msg (2 * g)) i.mat x)
    (gKey : ∀ g < 12, KeyField (layerShape X.P) X.layers.sc X.y g
      (ownAt s (seatBy f X s) msg (2 * g)) i.mat)
    (aSmall : ∀ g < 12, AttSmall (Hd.shapeA X g) (ownAt s (seatBy f X s) msg (2 * g + 1)))
    (aOwn1 : ∀ g < 12, AttOwn1 (Hd.shapeA X g) (ownAt s (seatBy f X s) msg (2 * g + 1)))
    (aOwn2 : ∀ g < 12, AttOwn2 (Hd.shapeA X g) (ownAt s (seatBy f X s) msg (2 * g + 1)))
    (aRidden : ∀ g < 12, AttRidden (Hd.shapeA X g) (ownAt s (seatBy f X s) msg (2 * g + 1)))
    (aKey : ∀ g < 12, AttKey (Hd.shapeA X g) (ownAt s (seatBy f X s) msg (2 * g + 1)))
    (H : HeadPlain pp i x (headStream X (ownAt s (seatBy f X s) msg 24))) :
    Means X pp i x (hidAt X s (seatBy f X s) tok msg) :=
  means_of_parts h C F f tok msg
    (fun g hg => ⟨gSmall g hg, gNorm g hg, gHot g hg, gEmb g hg, gKey g hg⟩)
    (fun g hg => ⟨aSmall g hg, aKey g hg, aOwn1 g hg, aOwn2 g hg, aRidden g hg⟩) H

end Core

/-! ## The head's cut -/

/-- The head's record from five clauses and Head3. -/
theorem headOrd_of_clauses {h : Model.Head.Shape} {L : Model.Head.HL} {y : Model.Layer.Lay}
    {np : NormPar} {pl : AcceptancePolicy} {Wz : Mat} {x : Instance ppref} {Mh : Mats ℤ}
    (hx : Inst.Model.Head3 x)
    (hSmall : Hd.SmallH h L (borderOf y) Mh)
    (hIdn : ∀ i < Inst.Model.Head.nT, ∀ k < 17,
      Inst.Model.Head.N.idn np ((Hd.cellsH h L (borderOf y) Mh).cast Cb.Gl.F) i k = 0)
    (hLines : ∀ i < Inst.Model.Head.nT,
      Inst.Model.Head.dB4 ((Hd.cellsH h L (borderOf y) Mh).cast Cb.Gl.F)
          (Inst.Model.Head.Req.of pl x) i = 0 ∧
        Inst.Model.Head.dZ ((Hd.cellsH h L (borderOf y) Mh).cast Cb.Gl.F)
          (Inst.Model.Head.Req.of pl x) i = 0)
    (hSums : Inst.Model.Head.sB2 ((Hd.cellsH h L (borderOf y) Mh).cast Cb.Gl.F)
        (Inst.Model.Head.Req.of pl x) = 0 ∧
      Inst.Model.Head.sB3 ((Hd.cellsH h L (borderOf y) Mh).cast Cb.Gl.F)
        (Inst.Model.Head.Req.of pl x) = 0)
    (hKey : HeadKeys h L y np pl Wz x Mh) : Hd.HeadOrdLB h L y np pl Wz x Mh :=
  headOrdLB_iff_split.2 ⟨⟨hSmall, ⟨hIdn, hLines, hSums⟩, fun he => by
    rw [hx.2.2 he]
    rfl⟩, hKey⟩

/-- THE SUM FROM FIFTEEN CLAUSES, at all public files in the goals' scope. -/
theorem means_of_fifteen {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : Model.Verify.Public} (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {s : ℕ → Size} (F : Follows X s)
    (f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ) {i : Cm.Idx} {x : Instance ppref} (tok : Fin ppref.V)
    (msg : Msgs) (hx : Inst.Model.Head3 x)
    (gSmall : ∀ g < 12, SmallM X.y (ownAt s (seatBy f X s) msg (2 * g)))
    (gNorm : ∀ g < 12, NormField (layerShape X.P) X.layers.sc X.y g
      (ownAt s (seatBy f X s) msg (2 * g)) i.mat x)
    (gEmb : ∀ g < 12, EmbField (layerShape X.P) X.layers.sc X.y g
      (ownAt s (seatBy f X s) msg (2 * g)) i.mat x)
    (gHot : ∀ g < 12, HotField (layerShape X.P) X.layers.sc X.y g
      (ownAt s (seatBy f X s) msg (2 * g)) i.mat x)
    (gKey : ∀ g < 12, KeyField (layerShape X.P) X.layers.sc X.y g
      (ownAt s (seatBy f X s) msg (2 * g)) i.mat)
    (aSmall : ∀ g < 12, AttSmall (Hd.shapeA X g) (ownAt s (seatBy f X s) msg (2 * g + 1)))
    (aOwn1 : ∀ g < 12, AttOwn1 (Hd.shapeA X g) (ownAt s (seatBy f X s) msg (2 * g + 1)))
    (aOwn2 : ∀ g < 12, AttOwn2 (Hd.shapeA X g) (ownAt s (seatBy f X s) msg (2 * g + 1)))
    (aRidden : ∀ g < 12, AttRidden (Hd.shapeA X g) (ownAt s (seatBy f X s) msg (2 * g + 1)))
    (aKey : ∀ g < 12, AttKey (Hd.shapeA X g) (ownAt s (seatBy f X s) msg (2 * g + 1)))
    (hSmall : Hd.SmallH X.hS X.HLy (borderOf X.y) (ownAt s (seatBy f X s) msg 24))
    (hIdn : ∀ p < Inst.Model.Head.nT, ∀ k < 17,
      Inst.Model.Head.N.idn (Hd.npOf X.hS)
        ((Hd.cellsH X.hS X.HLy (borderOf X.y) (ownAt s (seatBy f X s) msg 24)).cast Cb.Gl.F)
        p k = 0)
    (hLines : ∀ p < Inst.Model.Head.nT,
      Inst.Model.Head.dB4
          ((Hd.cellsH X.hS X.HLy (borderOf X.y) (ownAt s (seatBy f X s) msg 24)).cast Cb.Gl.F)
          (Inst.Model.Head.Req.of (Hd.polOf X.hS) x) p = 0 ∧
        Inst.Model.Head.dZ
          ((Hd.cellsH X.hS X.HLy (borderOf X.y) (ownAt s (seatBy f X s) msg 24)).cast Cb.Gl.F)
          (Inst.Model.Head.Req.of (Hd.polOf X.hS) x) p = 0)
    (hSums : Inst.Model.Head.sB2
          ((Hd.cellsH X.hS X.HLy (borderOf X.y) (ownAt s (seatBy f X s) msg 24)).cast Cb.Gl.F)
          (Inst.Model.Head.Req.of (Hd.polOf X.hS) x) = 0 ∧
      Inst.Model.Head.sB3
          ((Hd.cellsH X.hS X.HLy (borderOf X.y) (ownAt s (seatBy f X s) msg 24)).cast Cb.Gl.F)
          (Inst.Model.Head.Req.of (Hd.polOf X.hS) x) = 0)
    (hKey : HeadKeys X.hS X.HLy X.y (Hd.npOf X.hS) (Hd.polOf X.hS) i.mat x
      (ownAt s (seatBy f X s) msg 24)) :
    Means X pp i x (hidAt X s (seatBy f X s) tok msg) :=
  means_of_clauses h (Hd.core_of_scope hZ hR h) F f tok msg gSmall gNorm gEmb gHot gKey aSmall
    aOwn1 aOwn2 aRidden aKey
    (headPlain_of_ord hZ hR h i x _ hx (headOrd_of_clauses hx hSmall hIdn hLines hSums hKey))

#print axioms attKeys_is_attKey
#print axioms attR0_iff
#print axioms means_of_parts
#print axioms means_of_clauses
#print axioms headOrd_of_clauses
#print axioms means_of_fifteen

end Meaning
