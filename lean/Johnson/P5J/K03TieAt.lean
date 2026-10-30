-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03TieAt.lean: THE KIND "LOOKUP" (K3): THE NAMED TEST tie (linkTieB, Johnson/Goal/Meaning/ReadingsOne.lean: "the public ties at a segment") UNDER THE HEAD: AT ANY OF THE 25 SEGMENTS FROM THE NAMES' TIE THERE; AT THE TWELVE FEED-FORWARD SEGMENTS FROM THE HEAD ALONE.
 THE ARGUMENT. The test takes as arguments: the public parameters X (a segment's tail: how many matrices, each one's label, rows, columns, tree) · the lookups' public data D (codes · shape · layout · the built segments' tables of names D.arrayOf) · the radii · the messages' numbers. Under the head the two pins fix all of these BUT TWO: the radii, which the test does not read; and D.arrayOf, which no pin holds, and which the test reads AT THE MATRICES' TREES ALONE: there the names' tie says what stands.
  Meaning.entryTieV | linkTieV   the test's text off the view of X (Johnson/Desc/Ok/PlanWritten/XShape.lean), the radii at 0.
  Meaning.symArrB_rad            the test on an array does not read the radii (sig_fst: the shapes are one list).
  Meaning.linkTieB_view          in scope's two facts (p4; twelve groups): the test IS its text off the view (viewTail_at | viewEntry_at; gt_view).
  Meaning.linkTieV_arr           THE TEST READS D.arrayOf AT THE MATRICES' TREES ALONE: D.arrayOf may be swapped for any table that agrees there.
  P5T.tableFull · sentStar · numFull   closed terms: 25 tables of names MADE OFF THE WRITTEN VIEW (at a matrix's tree: the owner and the name by its label; elsewhere (0, "")) · the written codes, shape, layout with these tables · the numbers off the written seats.
  WHY tableFull IS NO CHEAT: IT IS NOT SAID TO BE D.arrayOf. linkTieV_arr swaps D.arrayOf for it ONLY at indices where both are shown equal: D's entry by the names' tie (a premise, or a theorem); tableFull's by tieFull's own first conjunct. Of D.arrayOf elsewhere nothing is said.
  P5T.tieFull (BY THE KERNEL)    at the written values the test accepts at all 25 segments · tieFull_control: A NEGATIVE TEST: every place one higher: it rejects AT EACH of the 25.
  P5J.sent_at_head · num_at_head  the pins' ties (first_written_in_scope · seats_in_scope: called).
  **P5J.k03_tie_of_names (h : AtMgA OnBytes.secondHashFunction …) (hk : k < 25) (hn : the names' tie at k, in entryTieB's first conjunct's own letters): the test accepts at the head's letters.**
  **P5J.k03_tie_even h (hg : g < 12): at k := 2 * g: NO PREMISE BUT THE HEAD** (names_tie_plain, Johnson/Road/K4/NamesTie.lean).
Limits. The head is a premise. At OnBytes.secondHashFunction. The full size alone. The written values rest on their files' own heads. The ledger's tie stands at (x.link, tl) off attAt | layAt: that these are (k, Meaning.tlAt X k) is the lookups' attAt_letters | layAt_letters: whoever joins calls them. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.MgAtAll
import Johnson.P5J.FourAtMg
import Johnson.Goal.Skeleton.PinsOfLaid
import Johnson.Goal.Meaning.ReadingsOne
import Johnson.HB.LLHARD.TailAtView
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Goal.Numbers.RequestWritten
import Johnson.P5T.PlanSeatsTie
import Johnson.Desc.First.Look.K3IdxAt
import Johnson.Road.K4.NamesTie
import Johnson.G.XShapeLit
import Johnson.G.LayoutLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Meaning
open OnBytes OnBytes.Model
open VerifiableInference.PlanWritten (XShape xShapeOf)
open VerifiableInference.Desc (arrayOf)
open VerifiableInference.Desc.First.Look (Sent sigListCalls sigList szOf symArrB msgIn)

/-- entryTieB's text off a view; the radii at 0. -/
def entryTieV (V : XShape) (D : Sent) (num : ℕ → ℕ → ℕ) (idx : ℕ → ℕ) (k μ : ℕ) : Bool :=
  decide ((D.arrayOf.getD k #[])[(viewTail V k).2.2.getD μ 0]? =
      some (ownerK (viewEntry V k μ).1, nameOf (ownerA (viewEntry V k μ).1))) &&
    symArrB D (sigListCalls D (fun _ => 0) k) k ((viewTail V k).2.2.getD μ 0)
      (Alg.symRows (viewEntry V k μ).2.1) (viewEntry V k μ).2.2 &&
    match arrayOf D.layout (ownerK (viewEntry V k μ).1) (nameOf (ownerA (viewEntry V k μ).1)) with
    | some A => decide (msgIn D k (ownerK (viewEntry V k μ).1) A.message =
        some (idx (num (ownerK (viewEntry V k μ).1) A.message)))
    | none => false

def linkTieV (V : XShape) (D : Sent) (num : ℕ → ℕ → ℕ) (idx : ℕ → ℕ) (k : ℕ) : Bool :=
  (List.range (viewTail V k).1).all fun μ => entryTieV V D num idx k μ

theorem sig_fst (D : Sent) (rad rad' : OracleShape → ℕ) (k : ℕ) :
    (sigListCalls D rad k).map (·.1) = (sigListCalls D rad' k).map (·.1) := by
  unfold sigListCalls sigList
  simp only [List.map_append, List.map_map, Function.comp_def]

/-- **The test on an array does not read the radii.** -/
theorem symArrB_rad (D : Sent) (rad rad' : OracleShape → ℕ) (k t R K : ℕ) :
    symArrB D (sigListCalls D rad k) k t R K = symArrB D (sigListCalls D rad' k) k t R K := by
  unfold symArrB
  cases (D.arrayOf.getD k #[])[t]? with
  | none => rfl
  | some bn =>
    dsimp only
    cases OnBytes.reqArray D.layout bn.1 bn.2 with
    | none => rfl
    | some a =>
      dsimp only
      cases msgIn D k bn.1 a.message with
      | none => rfl
      | some j =>
        dsimp only
        have hk := congrArg (fun L => L[j]?) (sig_fst D rad rad' k)
        simp only [List.getElem?_map] at hk
        cases h1 : (sigListCalls D rad k)[j]? with
        | none =>
          rw [h1] at hk
          cases h2 : (sigListCalls D rad' k)[j]? with
          | none => rfl
          | some o' =>
            rw [h2] at hk
            cases hk
        | some o =>
          rw [h1] at hk
          cases h2 : (sigListCalls D rad' k)[j]? with
          | none =>
            rw [h2] at hk
            cases hk
          | some o' =>
            rw [h2] at hk
            have e : o.1 = o'.1 := Option.some.inj hk
            dsimp only
            rw [e]

theorem gt_view (t : HTailF2) (μ : ℕ) :
    (VerifiableInference.PlanWritten.tailView t).2.2.getD μ 0 = t.gtTree.getD μ 0 := by
  show t.gtTree.toList.getD μ 0 = _
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getD_eq_getD_getElem?]

/-- **The test, off the view.** -/
theorem linkTieB_view {X : Verify.Public} (h4 : X.p4 = true) (hN : X.NGr = 12) {k : ℕ}
    (hk : k < 25) (D : Sent) (rad : OracleShape → ℕ) (num : ℕ → ℕ → ℕ) (idx : ℕ → ℕ) :
    linkTieB X D rad num idx k (tlAt X k) = linkTieV (xShapeOf X) D num idx k := by
  unfold linkTieB linkTieV
  have e1 : (viewTail (xShapeOf X) k).1 = (szOf (tlAt X k)).NM := by
    rw [viewTail_at h4 hN hk]
    rfl
  rw [e1]
  refine all_range_same fun μ _ => ?_
  unfold entryTieB entryTieV
  rw [viewEntry_at h4 hN hk μ, viewTail_at h4 hN hk, gt_view,
    symArrB_rad D rad (fun _ => 0) k]
  rfl

/-- **The test reads D.arrayOf at the matrices' trees alone.** -/
theorem linkTieV_arr (V : XShape) (D : Sent) (num : ℕ → ℕ → ℕ) (idx : ℕ → ℕ) (k : ℕ)
    (T : Array (Array (ℕ × String)))
    (h : ∀ μ < (viewTail V k).1, (D.arrayOf.getD k #[])[(viewTail V k).2.2.getD μ 0]? =
      (T.getD k #[])[(viewTail V k).2.2.getD μ 0]?) :
    linkTieV V D num idx k = linkTieV V { D with arrayOf := T } num idx k := by
  unfold linkTieV
  refine all_range_same fun μ hμ => ?_
  unfold entryTieV symArrB
  dsimp only
  rw [h μ hμ]
  rfl

end Meaning

namespace P5T
open VerifiableInference.Desc.First.Look (Sent idxAt)
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.G (xShapeFull layoutFull)

/-- The 25 tables of names MADE OFF THE VIEW: at a matrix's tree: the owner and the name by its label. -/
def tableFull : Array (Array (ℕ × String)) :=
  ((List.range 25).map fun k =>
    ((List.range (((Meaning.viewTail xShapeFull k).2.2.foldl max 0) + 1)).map fun t =>
      match (List.range (Meaning.viewTail xShapeFull k).1).find? fun μ =>
          (Meaning.viewTail xShapeFull k).2.2.getD μ 0 == t with
      | some μ => (Meaning.ownerK (Meaning.viewEntry xShapeFull k μ).1,
          Meaning.nameOf (Meaning.ownerA (Meaning.viewEntry xShapeFull k μ).1))
      | none => (0, "")).toArray).toArray

def sentStar : Sent :=
  ⟨proofSizedFull.codes, VerifiableInference.Desc.ReqLit.shapeFull, layoutFull, tableFull⟩

def numFull : ℕ → ℕ → ℕ := numOfPlan seatsAllFull

set_option maxRecDepth 1000000 in
theorem tieFull :
    (List.range 25).all (fun k =>
      Meaning.linkTieV xShapeFull sentStar numFull (idxAt sentStar numFull k) k) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: every place one higher: the test rejects AT EACH of the 25 segments. -/
theorem tieFull_control :
    (List.range 25).all (fun k =>
      !Meaning.linkTieV xShapeFull sentStar numFull (fun n => idxAt sentStar numFull k n + 1) k) =
      true := by
  decide +kernel

end P5T

namespace P5J
open VerifiableInference.Desc
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc.First.Look (idxAt)
open Meaning (linkTieB linkTieV entryTieV ownerK ownerA nameOf labAt viewTail viewEntry viewTail_at
  viewEntry_at gt_view)
open VerifiableInference.PlanWritten (xShapeOf request_shape_written)
open VerifiableInference.PlanWritten.Joined (first_written_in_scope xShape_in_scope)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- Under the head the lookups' public data are the written ones, but for the tables of names. -/
theorem sent_at_head (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    At.sentAt Zp = { P5T.sentStar with arrayOf := Zp.made.p.built.links.map (·.arrayOf) } := by
  have hF := first_written_in_scope h.scope h.laid.pub (pins_of_laid h.scope h.laid).1
  have c : At.cs Zp = VerifiableInference.PlanWritten.proofSizedFull.codes := hF.1
  have s : At.shape Zp = ReqLit.shapeFull := hF.2.2.1.trans request_shape_written
  have l : At.layout Zp = Johnson.G.layoutFull := hF.2.2.2.2.2
  unfold At.sentAt
  rw [c, s, l]
  rfl

/-- Under the head the messages' numbers are the written seats'. -/
theorem num_at_head (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) : At.num Zp = P5T.numFull := by
  have hv := LPFD.Full.laidPOf_of h.laid.value h.laid.planOk h.laid.data h.laid.asks
  have hS := (P5T.seats_in_scope h.scope h.laid.pub (pins_of_laid h.scope h.laid).1 hv).2.1
  unfold At.num At.pseatsAll P5T.numFull
  rw [hS]

/-- **THE TEST tie AT ANY OF THE 25 SEGMENTS, FROM THE HEAD AND THE NAMES' TIE THERE.** -/
theorem k03_tie_of_names (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {k : ℕ} (hk : k < 25)
    (hn : ∀ μ < (Meaning.sizesOf (At.X Zp) k).NM,
      ((Zp.p.built.links.map (·.arrayOf)).getD k #[])[(Meaning.tlAt (At.X Zp) k).gtTree.getD μ 0]? =
        some (ownerK (labAt (At.X Zp) k μ), nameOf (ownerA (labAt (At.X Zp) k μ)))) :
    linkTieB (At.X Zp) (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).rad3 (At.num Zp)
      (idxAt (At.sentAt Zp) (At.num Zp) k) k (Meaning.tlAt (At.X Zp) k) = true := by
  obtain ⟨h4, hN, -, -⟩ := Meaning.scope_plans h.toAtMg.scope h.toAtMg.reads h.toAtMg.pubOne
  have hV : xShapeOf (At.X Zp) = Johnson.G.xShapeFull :=
    xShape_in_scope h.toAtMg.scope h.toAtMg.laid.pub (pins_of_laid h.toAtMg.scope h.toAtMg.laid).1
  have hfull : linkTieV Johnson.G.xShapeFull P5T.sentStar P5T.numFull
      (idxAt P5T.sentStar P5T.numFull k) k = true :=
    List.all_eq_true.1 P5T.tieFull k (List.mem_range.2 hk)
  have a1 : (viewTail Johnson.G.xShapeFull k).1 = (Meaning.sizesOf (At.X Zp) k).NM := by
    rw [← hV, viewTail_at h4 hN hk]
    rfl
  have a2 : ∀ μ, (viewTail Johnson.G.xShapeFull k).2.2.getD μ 0 =
      (Meaning.tlAt (At.X Zp) k).gtTree.getD μ 0 := fun μ => by
    rw [← hV, viewTail_at h4 hN hk, gt_view]
  have a3 : ∀ μ, (viewEntry Johnson.G.xShapeFull k μ).1 = labAt (At.X Zp) k μ := fun μ => by
    rw [← hV, viewEntry_at h4 hN hk μ]
  have hag : ∀ μ < (viewTail Johnson.G.xShapeFull k).1,
      (({ P5T.sentStar with arrayOf := Zp.made.p.built.links.map (·.arrayOf) } :
        VerifiableInference.Desc.First.Look.Sent).arrayOf.getD k #[])[
          (viewTail Johnson.G.xShapeFull k).2.2.getD μ 0]? =
        (P5T.tableFull.getD k #[])[(viewTail Johnson.G.xShapeFull k).2.2.getD μ 0]? := by
    intro μ hμ
    have e1 : entryTieV Johnson.G.xShapeFull P5T.sentStar P5T.numFull
        (idxAt P5T.sentStar P5T.numFull k) k μ = true :=
      List.all_eq_true.1 hfull μ (List.mem_range.2 hμ)
    unfold entryTieV at e1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at e1
    have e2 : (P5T.tableFull.getD k #[])[(viewTail Johnson.G.xShapeFull k).2.2.getD μ 0]? =
        some (ownerK (viewEntry Johnson.G.xShapeFull k μ).1,
          nameOf (ownerA (viewEntry Johnson.G.xShapeFull k μ).1)) := e1.1.1
    rw [e2, a3 μ, a2 μ]
    exact hn μ (a1 ▸ hμ)
  show linkTieB (At.X Zp) (At.sentAt Zp) _ (At.num Zp) (idxAt (At.sentAt Zp) (At.num Zp) k) k _ =
    true
  rw [Meaning.linkTieB_view h4 hN hk, hV, sent_at_head h.toAtMg, num_at_head h.toAtMg,
    Meaning.linkTieV_arr _ _ _ _ k P5T.tableFull hag]
  exact hfull

/-- **THE TEST tie AT THE TWELVE FEED-FORWARD SEGMENTS, FROM THE HEAD ALONE.** -/
theorem k03_tie_even (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12) :
    linkTieB (At.X Zp) (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).rad3 (At.num Zp)
      (idxAt (At.sentAt Zp) (At.num Zp) (2 * g)) (2 * g) (Meaning.tlAt (At.X Zp) (2 * g)) = true :=
  k03_tie_of_names h (by omega) fun _ hμ =>
    OnBytes.Road.K4.names_tie_plain h.toAtMg.scope h.toAtMg.reads h.toAtMg.laid.pub hg hμ

end P5J

#print axioms Meaning.sig_fst
#print axioms Meaning.symArrB_rad
#print axioms Meaning.gt_view
#print axioms Meaning.linkTieB_view
#print axioms Meaning.linkTieV_arr
#print axioms P5T.tieFull
#print axioms P5T.tieFull_control
#print axioms P5J.sent_at_head
#print axioms P5J.num_at_head
#print axioms P5J.k03_tie_of_names
#print axioms P5J.k03_tie_even
