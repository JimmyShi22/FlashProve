-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/SecondTieFull.lean: THE SECOND TIE OF THE MERGE OF THE CLAIMS ON THE
COMMITTED TABLE (kind K11), AT THE COMPOSED MEANING OVER ITS BASE `mgAll D mgBase`, IN THE FORM THAT
THE LAW WITH "REACHED" TAKES (`merge_tiedAtR`'s t2, TiesReached.lean). One lemma, one theorem: a
joining.

What is said.
  `freeAbove_of_tests`: nothing at or above the next free number of the open segment's ledger is
    filled: from the table's two public tests on that ledger.
  `merge_t2_full`: the table's condition at 346, no mark, `MergeFront` (EntryFront.lean: four facts
    on the state in front), the merge's accepting step and "b's strings are what the merge's stretch
    leaves of a's" give the table's condition at 347. It is `merge_t2_all` (SecondTieAt.lean) with
    FOUR more of its premises PAID (hIn, hbP, hnl, hPub): "in order" rides (`mgAll_inOrder_rides`,
    Johnson/Desc/Sound/MgAt/InOrderBlind.lean); the base says of b what it
    says of a; no "left m" is open in front (`k11_noLeft_front`, K11PubClosed.lean, by the kernel);
    and the public tests behind: `merge_pubHeld_full` (the same file), whose hRow is drawn from
    `MergeFront.hasRow` and whose hMade from `merge_makes_formsIn` (MergeMakesForms.lean),
    both with the tests in front that the table's condition holds.

THE PREMISES THAT ARE LEFT. On D's parameters: hl, hlay, hncl, hns, hB (a closed test), hlk, hst,
hr, htr, hms, hdec, hsmp. low: every sampled place that is open at 346 was sent in front of the
merge's stretch. hkeep: eight public items that other files' lemmas carry across the merge. hmk:
what the items that the merge's row makes anew say.

Limits. Shown at no closed value of D. Nothing on soundness.
-/
import Johnson.Top.H0.MergeLaw.SecondTieAt
import Johnson.Top.H0.MergeLaw.K11PubClosed
import Johnson.Top.H0.MergeLaw.MergeMakesForms
import Johnson.Top.H0.MergeLaw.EntryFront
import Johnson.Desc.Sound.MgAt.InOrderBlind
import Johnson.Desc.Sound.MgAt.K11Closed

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.First.MergeLaw
open Iop
open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open OnBytes.PscRun (Sized Filled FreeAbove)
open _root_.Run (ckP)
open VerifiableInference.Desc (Link Claim Place Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S HeadOwn ModelPart Item Pub Meaning Numbers start flatPlacesOf
  openSets pubSets stepOpen pubStep pubRowM rowOf pubOfItems sampledIn ledgerB freeAboveB pubHeld)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeClaim headMergeDecide)
open Johnson.Desc.First.Walk.Law (hasRow)
open VerifiableInference.Desc.Sound.MgAt (mergeAt behindAt k11_hp)

/-- **Nothing at or above the next free number is filled**, from the table's two public tests on the
open segment's ledger. -/
theorem freeAbove_of_tests {s : S} {n : ℕ} (hl : ledgerB s = true) (hf : freeAboveB n s = true) :
    ∀ a, s.here = .head a → FreeAbove a.F := by
  intro a ha j hj hF
  unfold ledgerB at hl
  unfold freeAboveB at hf
  cases e : s.fork? with
  | none => simp [e] at hl
  | some G =>
    rw [e] at hl hf
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
      Bool.not_eq_true'] at hl hf
    have eG : G = a.F := by
      unfold S.fork? at e
      rw [ha] at e
      by_cases ho : a.opened = true
      · simp only [ho, if_true] at e
        exact (Option.some.inj e).symm
      · simp [ho] at e
    subst eG
    unfold Filled at hF
    by_cases hj' : j < a.F.ns
    · have h0 := hf.1 (j - a.F.next) (by omega)
      rw [show a.F.next + (j - a.F.next) = j by omega] at h0
      have hb : j < a.F.gotF.size := by rw [hl.2]; exact hj'
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hb] at h0 hF
      rw [Option.getD_some] at h0 hF
      rw [h0] at hF
      exact Bool.false_ne_true hF
    · have hb : a.F.gotF.size ≤ j := by rw [hl.2]; omega
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hb] at hF
      exact Bool.false_ne_true hF

variable {Xi Pp Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public} {Fr : Frame}
  (D : MgData Xi Pp Tok rows cols nR X)

/-- **THE MERGE's SECOND TIE, AT THE COMPOSED MEANING OVER ITS BASE, IN THE FORM THAT THE LAW WITH
"REACHED" TAKES**: the table's condition at 346, no mark, the four facts on the state in front, and
the accepting step give the table's condition at 347. -/
theorem merge_t2_full (hl : D.links = linksFull) (Pm : HeadMergeP) (base : ℕ) (ds : List RDT)
    (xM : Mem) (R ni : ℕ)
    -- on D's parameters
    (hlay : D.d1.lay = Pm.lay) (hncl : D.d1.ncl 24 = 1)
    (hns : (D.built[24]?).map (·.ns) = some Pm.nMsg)
    (hB : pendAllB Pm.lay D.d1.lin = true)
    (l : Link S Claim) (name : String) (r : ℕ → S → Except String (List Claim × S))
    (hlk : D.lk 24 = some l)
    (hst : ((K9.statesOfLink l 8).find? fun x => x.1 == "the merge") = some (name, r))
    (hr : ∀ n t y, r n t = .ok y ↔ headMergeClaim n t = .ok y)
    (htr : D.N.treesAt (some behindAt) = D.N.treesAt (some mergeAt))
    (hms : D.N.msgsAt (some behindAt) = D.N.msgsAt (some mergeAt))
    (hdec : ∀ z c (s : S) (a' : HeadOwn),
      D.decT c (z, { s with rowsOwed := none, here := .head a' }) = D.decT c (z, s))
    (hsmp : ∀ z (s : S) (a' : HeadOwn),
      D.smp (z, { s with rowsOwed := none, here := .head a' }) = D.smp (z, s))
    (low : ∀ x ∈ sampledIn D.N ((openSets linksFull (flatPlacesOf linksFull true)
      (start linksFull))[346]?.getD []), x.1 < base)
    (z : Pp) (a b : S × Fr.E.Str)
    (ha : onQ D.N (mgAll D mgBase) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a)
    (hm : ¬ a.1.failed ≠ none)
    (F : MergeFront (D.N.group 24) xM R ni a.1)
    (hy : ∃ rs, headMergeDecide Pm a.1 rs = .ok b.1)
    (hb : ∃ τ : Iop.Tr (uLT (ckP .two) ds), b.2 = behind (ckP .two) Fr base ds a.2 τ)
    -- what other authors' lemmas carry
    (hkeep : ∀ q ∈ keep24, (mgAll D mgBase).pub q (z, a.1) = true →
      (mgAll D mgBase).pub q (z, b.1) = true)
    (hmk : ∀ q ∈ (pubRowM (mgAll D mgBase).more linksFull mergeAt).makes,
      q ∉ (pubSets (mgAll D mgBase).more linksFull (flatPlacesOf linksFull true))[346]?.getD [] →
      (mgAll D mgBase).pubP q (z, b.1)) :
    onQ D.N (mgAll D mgBase) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) (346 + 1)
      b := by
  obtain ⟨rs, hyes⟩ := hy
  -- the public tests in front
  have hP : pubHeld (mgAll D mgBase)
      ((openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[346]?.getD [])
      ((pubSets (mgAll D mgBase).more linksFull (flatPlacesOf linksFull true))[346]?.getD [])
      (z, a.1) = true := by
    have ha' := ha
    unfold onQ onAt at ha'
    rcases ha'.2 with h | ⟨hBk, _⟩
    · exact absurd h hm
    · simp only [Bool.and_eq_true] at hBk
      exact hBk.1.2
  obtain ⟨_, _, _, c4, c5, _⟩ := k11_six D mgBase hl rfl
  rw [hl] at c4 c5
  have hall := List.all_eq_true.1 (by unfold pubHeld at hP; exact hP)
  have e1 : ledgerB a.1 = true := hall _ (List.mem_append_left _ c4)
  have e2 : ((D.pubD.nsOf 24).any fun n => freeAboveB n a.1) = true :=
    hall _ (List.mem_append_left _ c5)
  have e2' : freeAboveB Pm.nMsg a.1 = true := by
    have : D.pubD.nsOf 24 = some Pm.nMsg := hns
    rw [this] at e2
    exact e2
  have hfr : frontR Pm a.1 = true := frontR_of_tests Pm e1 e2'
  have hRow : Johnson.Desc.First.Walk.Law.hasRow D.d1.lay (D.d1.ncl 24) D.d1.lin b.1 = true := by
    rw [hlay, hncl]
    exact F.hasRow hyes hB
  have hMade := merge_makes_formsIn Pm hyes hfr (freeAbove_of_tests e1 e2') (D.N.group 24) xM R
    F.mask
  exact merge_t2_all D mgBase Pm D.N base ds htr hms hdec hsmp low z a b ha ⟨rs, hyes⟩ hb
    (mgAll_inOrder_rides D z a.1 b.1) (fun _ h => h)
    (merge_pubHeld_full D mgBase hl rfl Pm mergeAt k11_hp z hyes hkeep hRow l name r hlk hst hr
      hMade)
    (fun q hq _ m e => k11_noLeft_front D mgBase rfl m (e ▸ hq)) hmk

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.freeAbove_of_tests
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_t2_full
