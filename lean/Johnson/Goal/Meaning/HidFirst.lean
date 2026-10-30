-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HidFirst.lean: the relation at the first boundary, firstMeans
(Johnson/Goal/Meaning/Row.lean), at a witness's hidden values, from twelve clauses at the
sub-proofs' OWN lists.

firstMeans X pp put dec p w asks Means X pp i (put p w.tok).val w at every index i that the decoded
matrix holds. Here w is hidAtF X s seat tok msgF (Johnson/Goal/Meaning/HidFamily.lean): the hidden
values of a witness whose sub-proof k reads the messages msgF k at the seats seat k. A law on one
sub-proof ends in clauses at that sub-proof's own list, ownAtF s seat msgF k. This file leads from
these to firstMeans in one step.

Main names:
  Twelve X i x own   the twelve clauses as one record, at a family own of 25 lists: the layers'
    NormField, EmbField, HotField, KeyField at own (2 g); attention's AttOwn1, AttOwn2, AttRidden,
    AttKey at own (2 g + 1); the head's 17 identities, the ledger's two lines, its two sums and
    HeadKeys at own 24.
  means_of_twelve_seat   in scope, at ANY seats: under the test on sizes (sizesFit), agreeing
    readings (ReadsOne), the two inequalities on the shift and Head3 x: Twelve at ownAtF gives Means
    at hidAtF.
  firstMeans_of_twelve_seat   so: Twelve at every index that the decoded matrix holds, at the
    request with the token put in, gives firstMeans at hidAtF.
  firstMeans_of_twelveF   the same at seats seatBy f and sizes that follow the plans, under MsgsOne.
  twelve_of_records   OwnG, OwnA and Hd.HeadOrdLB give Twelve.

What is not claimed. Twelve of anything; ReadsOne or MsgsOne of any witness. MEANS AT hidAtF IS NO
EVIDENCE THAT THE COMMITTED SYMBOLS ARE SMALL OR ARE A PACKING (the head of
Johnson/Goal/Meaning/HidFamilyParts.lean). THE SEAMS ARE STILL MOVED, NOT PAID: they stand in
ReadsOne now. The program does not import this file.
-/
import Johnson.Goal.Meaning.HidFamilyParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open OnBytes OnBytes.Road OnBytes.Road.L5 OnBytes.Road.Rows.Norms
open OnBytes.Model.Verify (publicOf layerShape borderOf)
open VerifiableInference.OnPublicFiles.Flat (Holds GE Req)
open Cb.Pv.Tail (Size)
open Inst.Model (ppref Instance NormPar AcceptancePolicy Mat)

/-- **The twelve clauses, at a family of 25 lists.** -/
structure Twelve (X : Model.Verify.Public) (i : Cm.Idx) (x : Instance ppref) (own : ℕ → Mats ℤ) :
    Prop where
  gNorm : ∀ g < 12, NormField (layerShape X.P) X.layers.sc X.y g (own (2 * g)) i.mat x
  gEmb : ∀ g < 12, EmbField (layerShape X.P) X.layers.sc X.y g (own (2 * g)) i.mat x
  gHot : ∀ g < 12, HotField (layerShape X.P) X.layers.sc X.y g (own (2 * g)) i.mat x
  gKey : ∀ g < 12, KeyField (layerShape X.P) X.layers.sc X.y g (own (2 * g)) i.mat
  aOwn1 : ∀ g < 12, AttOwn1 (Hd.shapeA X g) (own (2 * g + 1))
  aOwn2 : ∀ g < 12, AttOwn2 (Hd.shapeA X g) (own (2 * g + 1))
  aRidden : ∀ g < 12, AttRidden (Hd.shapeA X g) (own (2 * g + 1))
  aKey : ∀ g < 12, AttKey (Hd.shapeA X g) (own (2 * g + 1))
  hIdn : ∀ p < Inst.Model.Head.nT, ∀ k < 17,
    Inst.Model.Head.N.idn (Hd.npOf X.hS)
      ((Hd.cellsH X.hS X.HLy (borderOf X.y) (own 24)).cast Cb.Gl.F) p k = 0
  hLines : ∀ p < Inst.Model.Head.nT,
    Inst.Model.Head.dB4 ((Hd.cellsH X.hS X.HLy (borderOf X.y) (own 24)).cast Cb.Gl.F)
        (Inst.Model.Head.Req.of (Hd.polOf X.hS) x) p = 0 ∧
      Inst.Model.Head.dZ ((Hd.cellsH X.hS X.HLy (borderOf X.y) (own 24)).cast Cb.Gl.F)
        (Inst.Model.Head.Req.of (Hd.polOf X.hS) x) p = 0
  hSums : Inst.Model.Head.sB2 ((Hd.cellsH X.hS X.HLy (borderOf X.y) (own 24)).cast Cb.Gl.F)
        (Inst.Model.Head.Req.of (Hd.polOf X.hS) x) = 0 ∧
      Inst.Model.Head.sB3 ((Hd.cellsH X.hS X.HLy (borderOf X.y) (own 24)).cast Cb.Gl.F)
        (Inst.Model.Head.Req.of (Hd.polOf X.hS) x) = 0
  hKey : HeadKeys X.hS X.HLy X.y (Hd.npOf X.hS) (Hd.polOf X.hS) i.mat x (own 24)

/-- The three records give the twelve clauses. -/
theorem twelve_of_records {X : Model.Verify.Public} {i : Cm.Idx} {x : Instance ppref}
    {own : ℕ → Mats ℤ} (G : ∀ g < 12, OwnG X i x (own (2 * g)) g)
    (At : ∀ g < 12, OwnA (Hd.shapeA X g) (own (2 * g + 1)))
    (H : Hd.HeadOrdLB X.hS X.HLy X.y (Hd.npOf X.hS) (Hd.polOf X.hS) i.mat x (own 24)) :
    Twelve X i x own :=
  ⟨fun g hg => (G g hg).norm, fun g hg => (G g hg).emb, fun g hg => (G g hg).hot,
    fun g hg => (G g hg).key, fun g hg => (At g hg).own1, fun g hg => (At g hg).own2,
    fun g hg => (At g hg).ridden, fun g hg => (At g hg).key,
    (headOrdLB_iff_split.1 H).1.2.1.1, (headOrdLB_iff_split.1 H).1.2.1.2.1,
    (headOrdLB_iff_split.1 H).1.2.1.2.2, (headOrdLB_iff_split.1 H).2⟩

section
variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}
  {s : ℕ → Size}

/-- **Means from the twelve clauses at the sub-proofs' own lists, at any seats.** -/
theorem means_of_twelve_seat (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ}
    {msgF : ℕ → Msgs} (fit : sizesFit X s = true) (R : ReadsOne X s seat msgF)
    (h0 : ∀ k < 25, (0 : ℤ) < ((s k).beta : ℤ)) (h2 : ∀ k < 25, 2 * ((s k).beta : ℤ) ≤ 2 ^ 18)
    {i : Cm.Idx} {x : Instance ppref} (tok : Fin ppref.V) (hx : Inst.Model.Head3 x)
    (Tw : Twelve X i x (ownAtF s seat msgF)) : Means X pp i x (hidAtF X s seat tok msgF) :=
  means_hidAtF h (Hd.core_of_scope hZ hR h) fit R tok
    (fun g hg => ord_of_ownG ⟨fun _ r c _ => small_ownAtF (h0 _ (by omega)) (h2 _ (by omega)) _ r c,
      Tw.gNorm g hg, Tw.gHot g hg, Tw.gEmb g hg, Tw.gKey g hg⟩)
    (fun g hg => ord_of_ownA ⟨fun _ _ => small_ownAtF (h0 _ (by omega)) (h2 _ (by omega)) _ _ _,
      Tw.aKey g hg, Tw.aOwn1 g hg, Tw.aOwn2 g hg, Tw.aRidden g hg⟩)
    (headPlain_of_ord hZ hR h i x _ hx (headOrd_of_clauses hx
      (Hd.smallH_of_all fun a r c =>
        small_ownAtF (h0 24 (by norm_num)) (h2 24 (by norm_num)) a r c)
      Tw.hIdn Tw.hLines Tw.hSums Tw.hKey))

/-- **The relation at the first boundary, from the twelve clauses at the sub-proofs' own lists.** -/
theorem firstMeans_of_twelve_seat (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : publicOf Z.pol Z.KL lay = .ok X)
    {seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ} {msgF : ℕ → Msgs}
    (fit : sizesFit X s = true) (R : ReadsOne X s seat msgF)
    (h0 : ∀ k < 25, (0 : ℤ) < ((s k).beta : ℤ)) (h2 : ∀ k < 25, 2 * ((s k).beta : ℤ) ≤ 2 ^ 18)
    {rows cols : ℕ} (put : Req → Fin ppref.V → Req) (dec : Option (Fin rows → Fin cols → GE))
    (p : Req) (tok : Fin ppref.V)
    (cl : ∀ M (i : Cm.Idx), dec = some M → Holds M i →
      Twelve X i (put p tok).val (ownAtF s seat msgF)) :
    firstMeans X pp put dec p (hidAtF X s seat tok msgF) := fun M i hM hi =>
  means_of_twelve_seat hZ hR h fit R h0 h2 tok (head3_of_req _) (cl M i hM hi)

/-- The same at seats that are a function of the label and sizes that follow the plans. -/
theorem firstMeans_of_twelveF (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (F : Follows X s) {f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ}
    {msgF : ℕ → Msgs} (E : MsgsOne X s f msgF) (h0 : ∀ k < 25, (0 : ℤ) < ((s k).beta : ℤ))
    (h2 : ∀ k < 25, 2 * ((s k).beta : ℤ) ≤ 2 ^ 18) {rows cols : ℕ}
    (put : Req → Fin ppref.V → Req) (dec : Option (Fin rows → Fin cols → GE)) (p : Req)
    (tok : Fin ppref.V)
    (cl : ∀ M (i : Cm.Idx), dec = some M → Holds M i →
      Twelve X i (put p tok).val (ownAtF s (seatBy f X s) msgF)) :
    firstMeans X pp put dec p (hidAtF X s (seatBy f X s) tok msgF) :=
  firstMeans_of_twelve_seat hZ hR h
    (sizesFit_of_planFit F (planFit_of_core h (Hd.core_of_scope hZ hR h)))
    (readsOne_of_msgs h (Hd.core_of_scope hZ hR h) E) h0 h2 put dec p tok cl

end

end Meaning

#print axioms Meaning.twelve_of_records
#print axioms Meaning.means_of_twelve_seat
#print axioms Meaning.firstMeans_of_twelve_seat
#print axioms Meaning.firstMeans_of_twelveF
