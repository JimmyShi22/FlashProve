-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/OffAt.lean: the code switch's law at the closed constant (mgAtAll):
THE NAMED TEST offC (P5J.AtMg.offC, Johnson/P5J/HidBearsAtMg.lean: placesOffC at the constant's own
terms: «every named place is off the pads»), ON WHICH K2's hidBears HANGS, IS A THEOREM UNDER THE
HEAD AND THE PIN.
WHAT THE TEST READS. At each segment k < 25 and each committed matrix a of its list: the array that
the matrix's label names is in the layout, and every member of the table that sits in the segment's
group under that array's number has a shape at which the array misses the pad. So: the codes · arr ·
num · the layout · the numbers' groups (all fields of WrittenAt.lean's AtWritten) · the members'
shapes and tenants (placesOffC_rad: blind to the radii) · and of the public parameters X
the 25 lists of labels and their lengths.
  offV         the test, read off the view of X's shape (PlanWritten.XShape)
  placesOffC_view  the test reads X through the view alone, at the full size's shape. By
               tailV_at · entryV_at · tlK_eq (Goal/Meaning/NamedView.lean |
               NamedAskLaw.lean)
  offV_group   it reads of the table's numbers the groups alone
  msW          the table's members at the written seats, every radius 0
  off_written  IT ACCEPTS AT THE WRITTEN VALUES: by decide +kernel. (It walks the entries that
               named_walks (Goal/Meaning/NamedViewFull.lean) counts: 176.)
  layoutShoved · off_rejects  a negative test, by the kernel: with every laid block shoved far down
               and to the right it rejects: it bites where a copy's shape has no mask row
  offC_at      h.offC = true from AtWritten · hs: the first chain's sendings are proofSends0 · hx:
               X's view is xShapeFull · hF: X has the full size's shape
  offC_const   the same under the head at the concrete second hash function, pin madePinnedAt and hF
hF's PAYER: fullShaped_scope (in scope, where the files are read).
WITH IT: hidBears_at h (offC_const …) T m (K2Ties/AtConstant.lean).
LIMITS. The full size alone. Under the pin, which is row 9 of the fourteen entry tests that the
verifier asks (row 10 is the written cut; AtHead.lean reads both off the head): a verifier whose
entry tests lack these two rows gives no such head. A member of the head is proved at storedPublicFiles and zGap
alone (at secondHashFunction; side library AtFullSide/Top/). No soundness is claimed.
-/
import Johnson.Top.H0.K2Ties.MembersShapeAt
import Johnson.P5J.HidBearsAtMg
import Johnson.P5J.PlacesOffRad
import Johnson.Goal.Meaning.NamedViewFull
import Johnson.Goal.Meaning.NamedAskLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open OnBytes
open OnBytes.Params (ReqLayout)
open VerifiableInference.Desc (Chain arrayOf)
open VerifiableInference.Desc.Sound (Mem msOf)
open VerifiableInference.Desc.Kinds.Head.Law.OffPad (copiesMiss)
open VerifiableInference.PlanWritten (XShape xShapeOf tailView)
open _root_.Meaning (labAt sizesOf ownerK ownerA nameOf)
open _root_.Meaning.NamedAsk (tailV entryV tailV_at entryV_at tlK_eq fullShaped all_range_congr)
open P5J (placesOffC)
open P5T (psFull seatsAllFull N0Full memberListsR)
open Johnson.G (proofSends0 xShapeFull layoutFull)
open VerifiableInference.PlanWritten (madePinnedAt proofSizedFull)
open VerifiableInference.PlanWritten.Joined (xShape_in_scope)

/-- **THE TEST, READ OFF THE VIEW OF THE PUBLIC PARAMETERS' SHAPE.** -/
def offV (cs : Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers) (V : XShape)
    (layout : ReqLayout) (num : ℕ → ℕ → ℕ) : Bool :=
  (List.range 25).all fun k => (List.range (tailV V k).1).all fun a =>
    match arrayOf layout (ownerK (entryV (tailV V k) a).1)
        (nameOf (ownerA (entryV (tailV V k) a).1)) with
    | none => false
    | some A => copiesMiss cs arr ms N k (num (ownerK (entryV (tailV V k) a).1) A.message) A

/-- **The test reads the public parameters through the view alone**, at the full size's shape. -/
theorem placesOffC_view (cs : Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers)
    {X : Model.Verify.Public} (hF : fullShaped X = true) (layout : ReqLayout)
    (num : ℕ → ℕ → ℕ) :
    placesOffC cs arr ms N X (sizesOf X) layout num =
      offV cs arr ms N (xShapeOf X) layout num := by
  unfold placesOffC offV
  refine all_range_congr fun k hk => ?_
  rw [tailV_at X hk, tlK_eq hF hk]
  have e1 : (tailView (_root_.Meaning.tlAt X k)).1 = (sizesOf X k).NM := rfl
  rw [e1]
  refine all_range_congr fun a _ => ?_
  rw [entryV_at]
  rfl

/-- The test reads of the table's numbers the groups alone. -/
theorem offV_group (cs : Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) {N N' : Numbers}
    (h : ∀ k, N.group k = N'.group k) (V : XShape) (layout : ReqLayout) (num : ℕ → ℕ → ℕ) :
    offV cs arr ms N V layout num = offV cs arr ms N' V layout num := by
  unfold offV copiesMiss
  simp only [h]

/-- The table's members at the written seats, every radius 0. -/
def msW : List Mem := msOf (memberListsR proofSends0.sends.length (fun _ _ => 0) psFull)

set_option maxRecDepth 1000000 in
/-- **THE TEST ACCEPTS AT THE WRITTEN VALUES**: all 176 entries. -/
theorem off_written :
    offV proofSizedFull.codes (P5T.arrOf seatsAllFull) msW N0Full xShapeFull layoutFull
      (P5T.numOfPlan seatsAllFull) = true := by decide +kernel

/-- The written layout with every laid block shoved far down and to the right. -/
def layoutShoved : ReqLayout :=
  ⟨layoutFull.link.map fun as => as.map fun a =>
    { a with blocks := a.blocks.map fun b =>
        { b with firstRow := b.firstRow + 1000000, firstPlace := b.firstPlace + 1000000 } }⟩

set_option maxRecDepth 1000000 in
/-- **A negative test**: with the blocks shoved the test rejects: it bites where a copy's shape has
no mask row, so that the blocks are walked. -/
theorem off_rejects :
    offV proofSizedFull.codes (P5T.arrOf seatsAllFull) msW N0Full xShapeFull layoutShoved
      (P5T.numOfPlan seatsAllFull) = false := by decide +kernel

section
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- **THE NAMED TEST offC ACCEPTS AT THE CONSTANT's OWN TERMS.** -/
theorem offC_at (h : P5J.AtMg o Z D r Zp Np cF) (A : AtWritten Zp cF)
    (hs : Zp.made.proof.1 = proofSends0) (hx : xShapeOf Zp.p.X = xShapeFull)
    (hF : fullShaped Zp.p.X = true) : h.offC = true := by
  have hm : P5T.msAtR Zp (fun _ _ => 0) = msW := by
    unfold P5T.msAtR msW
    rw [hs, show P5T.planSeats Zp Zp.D.1 = psFull from A.pseats]
  unfold P5J.AtMg.offC P5J.At.ms
  rw [P5J.placesOffC_rad _ _ _ Zp _ (fun _ _ => 0)]
  show placesOffC (P5J.At.cs Zp) (P5J.At.arr Zp) (P5T.msAtR Zp fun _ _ => 0) (P5J.At.N Zp cF)
    Zp.p.X (sizesOf Zp.p.X) (P5J.At.layout Zp) (P5J.At.num Zp) = true
  rw [placesOffC_view _ _ _ _ hF, hx, offV_group _ _ _ A.group, A.cs, A.arr, A.layout, A.num, hm]
  exact off_written

/-- The same under the head and the pin. -/
theorem offC_const (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
    (hF : fullShaped Zp.p.X = true) : h.offC = true :=
  offC_at h (at_written h.scope h.laid hy) (sends_at h.scope h.laid hy)
    (xShape_in_scope h.scope h.laid.pub hy) hF

end

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.off_written
#print axioms VerifiableInference.Desc.First.K2Ties.off_rejects
#print axioms VerifiableInference.Desc.First.K2Ties.offC_at
#print axioms VerifiableInference.Desc.First.K2Ties.offC_const

#print axioms VerifiableInference.Desc.First.K2Ties.placesOffC_view
#print axioms VerifiableInference.Desc.First.K2Ties.offV_group
