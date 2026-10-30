-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K8OpenAtK4.lean: THE THREE NAMES OF THE APPROXIMATE RANGE PROOF AT K4's TWO BORDERS,
AT THE WIDER MEANING's LIST OF EXTRA PUBLIC TESTS OVER THE CLOSED BASE: which of "K8.lay7",
"K8.onThird", "K8.funsThird" is open in front of and behind K4's sub-protocol (by Lean's kernel, at
the written lists), and, at the reached states of these two borders, the three clauses on them that
the tight form of the bridge's premise asks (the premise hK of factsAt_at,
Johnson/Desc/Sound/MgWideFacts.lean: NOT IMPORTED: its text is stated), out of ONE
premise: the clause on "K8.lay7" at the reached states IN FRONT of K4's sub-protocol.

  `nameIs`, `k8OpenFit`, `k8_of_fit`: the test and what an accept gives at a place of K4's.
  `k8_open_wide`: it accepts at moreWideAll, at the full lists: by the kernel. `k8_funs_open`,
    `k8_lay7_open`: TWO NEGATIVE TESTS of its silence: "K8.funsThird" m IS open behind, "K8.lay7" m
    IS open at both borders. `k8_open_shift`: asked one border later, the test rejects ×12.
  `K8At M E j s`: the three clauses at border j and state s: the text of hK behind its "no mark".
  `hK_front`, `hK_behind`: K8At at k and k + 1, at moreW Dm mgBase, H : AtK4 at the written lists.
  `kept_rchAt`: a state reached behind K4's sub-protocol comes of one reached in front of it by an
    accept: KeptAtS (Johnson/Road/K4/KeptAtS.lean).
  **`hK_at_k4`**: in the goals' scope, at an opening, g < 12, under L7: K8At at every state without
    a mark that is reached at border 28 g + 4, and at every such state reached at border 28 g + 5.
    L7 and both ends are fenced to a state without a mark (
    the payers' facts are so fenced); an accept of K4's leaves the mark as it was.
WHO OWES L7: "K8.lay7" (2 g) is made by the sub-protocol at piece 1 of the segment (number 28 g + 2
of the flat list: the frame's) and passes piece 2 (28 g + 3: the lookup on the digits):
by reading of rowK8 (Johnson/Top/H0/Fill/FillP1Plus.lean). Across K4's own piece it is kept HERE:
lay7B reads the state's planned data alone, which an accept of K4's leaves.
Limits. THE WIDER MEANING IS A BRIDGE's SIDE. L7 is shown by nobody. That there is an opening is
shown by no theorem. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on
soundness.


-/
import Johnson.Road.K4.FunsThirdReached
import Johnson.Road.K4.K04Tied
import Johnson.Road.K4.Riders.PlanTests
import Johnson.Desc.Sound.MgWide

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Road.K4.Riders (atK4s atK4s_at funsThirdB_made)
open VerifiableInference.Desc (Block FileDescription Place)
open VerifiableInference.Desc.First (S ModelPart More Pub pubSets flatPlacesOf)
open VerifiableInference.Desc.First.K8.Ready (lay7B onThirdB funsThirdB)
open VerifiableInference.Desc.Sound (linksFull moreWideAll MgData WideData mgBase moreW moreW_base
  below)
open Johnson.Desc.First.Walk.Tied (Reach StepYes RchAt stepYes_raw stepYes_decide)

/-- Is the item an extra public test of a segment, of this name? -/
def nameIs (q : Pub) (n : String) : Bool :=
  match q with
  | .more (some _) n' => n' == n
  | _ => false

/-- At every place of K4's: in front, "K8.onThird" and "K8.funsThird" are open at no segment;
behind, "K8.onThird" at none; at both borders "K8.lay7" at the segment's own number alone. -/
def k8OpenFit (M : More) (links : List ModelPart) (ps : List Place) : Bool :=
  atK4s links ps fun k m =>
    (((pubSets M links ps)[k]?.getD []).all fun q =>
      !nameIs q "K8.onThird" && !nameIs q "K8.funsThird" &&
        (!nameIs q "K8.lay7" || q == .more (some m) "K8.lay7")) &&
    (((pubSets M links ps)[k + 1]?.getD []).all fun q =>
      !nameIs q "K8.onThird" && (!nameIs q "K8.lay7" || q == .more (some m) "K8.lay7"))

variable {M : More} {links : List ModelPart} {ps : List Place} {k m : ℕ} {pl : Place}

/-- What an accept gives at a place of K4's. -/
theorem k8_of_fit (H : AtK4 links ps k m pl) (h : k8OpenFit M links ps = true) :
    (∀ m', Pub.more (some m') "K8.onThird" ∉ (pubSets M links ps)[k]?.getD []) ∧
      (∀ m', Pub.more (some m') "K8.funsThird" ∉ (pubSets M links ps)[k]?.getD []) ∧
      (∀ m', Pub.more (some m') "K8.lay7" ∈ (pubSets M links ps)[k]?.getD [] → m' = m) ∧
      (∀ m', Pub.more (some m') "K8.onThird" ∉ (pubSets M links ps)[k + 1]?.getD []) ∧
      ∀ m', Pub.more (some m') "K8.lay7" ∈ (pubSets M links ps)[k + 1]?.getD [] → m' = m := by
  have h1 := atK4s_at (t := fun k m =>
    (((pubSets M links ps)[k]?.getD []).all fun q =>
      !nameIs q "K8.onThird" && !nameIs q "K8.funsThird" &&
        (!nameIs q "K8.lay7" || q == .more (some m) "K8.lay7")) &&
    (((pubSets M links ps)[k + 1]?.getD []).all fun q =>
      !nameIs q "K8.onThird" && (!nameIs q "K8.lay7" || q == .more (some m) "K8.lay7"))) H h
  rw [Bool.and_eq_true] at h1
  obtain ⟨a, b⟩ := h1
  refine ⟨fun m' hm => ?_, fun m' hm => ?_, fun m' hm => ?_, fun m' hm => ?_, fun m' hm => ?_⟩
  · have := List.all_eq_true.1 a _ hm
    simp [nameIs] at this
  · have := List.all_eq_true.1 a _ hm
    simp [nameIs] at this
  · have := List.all_eq_true.1 a _ hm
    simpa [nameIs] using this
  · have := List.all_eq_true.1 b _ hm
    simp [nameIs] at this
  · have := List.all_eq_true.1 b _ hm
    simpa [nameIs] using this

set_option maxRecDepth 1000000 in
theorem k8_open_wide :
    k8OpenFit moreWideAll linksFull (flatPlacesOf linksFull true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test of the silence on "K8.funsThird" behind**: it is open there, ×12. -/
theorem k8_funs_open :
    (atK4s linksFull (flatPlacesOf linksFull true) fun k m =>
      ((pubSets moreWideAll linksFull (flatPlacesOf linksFull true))[k + 1]?.getD []).contains
        (.more (some m) "K8.funsThird")) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **"K8.lay7" at the segment's own number is open at both borders**, ×12. -/
theorem k8_lay7_open :
    (atK4s linksFull (flatPlacesOf linksFull true) fun k m =>
      ((pubSets moreWideAll linksFull (flatPlacesOf linksFull true))[k]?.getD []).contains
          (.more (some m) "K8.lay7") &&
        ((pubSets moreWideAll linksFull (flatPlacesOf linksFull true))[k + 1]?.getD []).contains
          (.more (some m) "K8.lay7")) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test**: asked one border later, the first half of the test rejects, ×12. -/
theorem k8_open_shift :
    (atK4s linksFull (flatPlacesOf linksFull true) fun k _ =>
      !(((pubSets moreWideAll linksFull (flatPlacesOf linksFull true))[k + 1]?.getD []).all
        fun q => !nameIs q "K8.onThird" && !nameIs q "K8.funsThird")) = true := by
  decide +kernel

/-- The three clauses at border j and state s. -/
def K8At {P : Type} (M : More) (E : WideData P) (j : ℕ) (s : S) : Prop :=
  ∀ m, (Pub.more (some m) "K8.lay7" ∈
        (pubSets M linksFull (flatPlacesOf linksFull true))[j]?.getD [] →
      ((E.dP.tl m).any fun tlP => lay7B tlP s) = true) ∧
    (Pub.more (some m) "K8.onThird" ∈
        (pubSets M linksFull (flatPlacesOf linksFull true))[j]?.getD [] → onThirdB s = true) ∧
    (Pub.more (some m) "K8.funsThird" ∈
        (pubSets M linksFull (flatPlacesOf linksFull true))[j]?.getD [] → funsThirdB s = true)

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR X) (E : WideData P)

/-- In front of K4's sub-protocol. -/
theorem hK_front (H : AtK4 linksFull (flatPlacesOf linksFull true) k m pl) {s : S}
    (hl : ((E.dP.tl m).any fun tlP => lay7B tlP s) = true) :
    K8At (moreW Dm mgBase) E k s := by
  rw [moreW_base]
  obtain ⟨a1, a2, a3, _, _⟩ := k8_of_fit H k8_open_wide
  exact fun m' => ⟨fun hm => by rw [a3 m' hm]; exact hl, fun hm => absurd hm (a1 m'),
    fun hm => absurd hm (a2 m')⟩

/-- Behind K4's sub-protocol. -/
theorem hK_behind (H : AtK4 linksFull (flatPlacesOf linksFull true) k m pl) {s : S}
    (hl : ((E.dP.tl m).any fun tlP => lay7B tlP s) = true) (hf : funsThirdB s = true) :
    K8At (moreW Dm mgBase) E (k + 1) s := by
  rw [moreW_base]
  obtain ⟨_, _, _, a4, a5⟩ := k8_of_fit H k8_open_wide
  exact fun m' => ⟨fun hm => by rw [a5 m' hm]; exact hl, fun hm => absurd hm (a4 m'),
    fun _ => hf⟩

end

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
  {g : ℕ}

/-- **A state reached behind K4's sub-protocol comes of one reached in front of it by an
accept.** -/
theorem kept_rchAt (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hg : g < 12) {Str : Type}
    {a : ((descAt Z A B c).XiPub × (descAt Z A B c).S₁) × Str}
    (h : RchAt (descAt Z A B c) (28 * g + 5) a) :
    ∃ (s : S) (p : Par), RchAt (descAt Z A B c) (28 * g + 4) ((a.1.1, s), a.2) ∧
      KeptAtS p s a.1.2 := by
  have h' : Reach 0 (c.blocksInOrder.map below) (descAt Z A B c).start₁ (28 * g + 4 + 1) a.1 := h
  obtain ⟨z, s, s', b', e, hr, hb, hy⟩ := reach_pred h'
  obtain ⟨Lk, b₀, x, e1, e2, _, e4, _⟩ := IM.k4_of hS hR O g hg
  have hi : IM.flatIx c (2 * g) 2 = 28 * g + 4 := by
    rw [IM.flatIx_scope hS hR O (by omega) 2]
    omega
  have hf : c.blocksInOrder[28 * g + 4]? = some b₀ := by
    rw [← hi]
    exact IM.hear_at_flat e1 e2
  rw [List.getElem?_map, hf] at hb
  obtain rfl : below b₀ = b' := Option.some.inj hb
  obtain ⟨rs, gs, hd⟩ := stepYes_decide (stepYes_raw hy)
  have K := kept_atS ((IM.k4_yes e4 s s' rs gs).1 hd).1
  have ez : a.1.1 = z := congrArg Prod.fst e
  have es : a.1.2 = s' := congrArg Prod.snd e
  refine ⟨s, { x.2 with k3Runs := true }, ?_, ?_⟩
  · show Reach 0 (c.blocksInOrder.map below) (descAt Z A B c).start₁ (28 * g + 4) (a.1.1, s)
    rw [ez]
    exact hr
  · rw [es]
    exact K

/-- **The three clauses at the reached states of K4's two borders, out of the clause on "K8.lay7" in
front.** -/
theorem hK_at_k4 {Xi Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
    (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR X) (E : WideData ProofFile.InstPub)
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hg : g < 12) {Str : Type}
    (L7 : ∀ a : ((descAt Z A B c).XiPub × (descAt Z A B c).S₁) × Str,
      RchAt (descAt Z A B c) (28 * g + 4) a → S.failed a.1.2 = none →
        ((E.dP.tl (2 * g)).any fun tlP => lay7B tlP a.1.2) = true) :
    (∀ a : ((descAt Z A B c).XiPub × (descAt Z A B c).S₁) × Str,
        RchAt (descAt Z A B c) (28 * g + 4) a → S.failed a.1.2 = none →
          K8At (moreW Dm mgBase) E (28 * g + 4) a.1.2) ∧
      ∀ a : ((descAt Z A B c).XiPub × (descAt Z A B c).S₁) × Str,
        RchAt (descAt Z A B c) (28 * g + 5) a → S.failed a.1.2 = none →
          K8At (moreW Dm mgBase) E (28 * g + 5) a.1.2 := by
  refine ⟨fun a h hm => hK_front Dm E (atK4_full g hg) (L7 a h hm), fun a h hm => ?_⟩
  obtain ⟨s, p, hr, K⟩ := kept_rchAt hS hR O hg h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hRest, _⟩ := K
  have hl := L7 _ hr (hRest.failed.symm.trans hm)
  refine hK_behind Dm E (atK4_full g hg) ?_ (funsThird_rchAt hS hR O hg h)
  unfold lay7B at hl ⊢
  rw [hRest.tl]
  exact hl

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k8_of_fit
#print axioms OnBytes.Road.K4.k8_open_wide
#print axioms OnBytes.Road.K4.k8_funs_open
#print axioms OnBytes.Road.K4.k8_lay7_open
#print axioms OnBytes.Road.K4.k8_open_shift
#print axioms OnBytes.Road.K4.hK_front
#print axioms OnBytes.Road.K4.hK_behind
#print axioms OnBytes.Road.K4.kept_rchAt
#print axioms OnBytes.Road.K4.hK_at_k4
