-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Exchange/Proofs.lean: the proofs of `FormsOfIn`, `FormsOfRun` and `MergedBehind`
(Johnson/Desc/K11/Exchange/Statement.lean), to the letter. Lemmas; none of the library's goals.

How. The first: by unfolding. The second: the reader's answer is written out; a form's worth reads a
world at the entries and slots that the form names (the library's `value_eq`,
Johnson/Desc/Sound/FormsQ.lean); the public test says of each named slot that it is late, or filled
in front: at a late slot the table's world reads what the ledger behind holds (`lateAt_holds`); at a
slot that is filled in front a later ledger holds what the one in front held (`Later.keep`,
OnBytes/Tie/Pv/Psc/PscLater.lean). The third: the run is the flat text's row under a name; its
ledger is later (the library's `run_later`, Johnson/Top/H0/MergeLaw/Keeps.lean).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.K11.Exchange.Statement
import Johnson.Desc.Kinds.Law.K6Silent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Exchange
open OnBytes (E zeroE)
open OnBytes.Model (Fork Psc Aff Reading World WsForkOut)
open OnBytes.PscRun (Later Filled)
open OnBytes.K.Kc (Fl)
open VerifiableInference.Desc (Claim named)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.First.MergeLaw (mergeStates mem_lateOf run_later)
open VerifiableInference.Desc.K9 (segAt? formsIn Readers RunOf readerOf lateOf lateAt affIn slotIn
  Read)
open VerifiableInference.Desc.Sound (formsQ worldOwn dataQ MsgQ value_eq slotW slotW_late
  slotW_ledger)
open VerifiableInference.Desc.Kinds.Head.Law (seg_fork)
open Johnson.Desc.First.ForkMerge (headMergeClaim)

/-- **The public test and the forms' worths give the table's sentence.** -/
theorem formsOfIn : FormsOfIn := by
  intro Rd own piece run s rd hin hv
  unfold formsIn at hin
  cases ha : segAt? s with
  | none => simp [ha] at hin
  | some a =>
    cases hs : Rd.forms piece run s with
    | none => simp [ha, hs] at hin
    | some R =>
      rw [ha, hs] at hin
      obtain ⟨hl, hall⟩ := Eq.mp (Bool.and_eq_true _ _) hin
      exact ⟨a, R, ha, hs, hl, fun f hf => ⟨List.all_eq_true.1 hall f hf, hv a R ha hs f hf⟩⟩

/-- What the list of late slots says of a slot is what the ledger behind holds there. -/
theorem lateAt_holds {F G : Fork} {j : ℕ} {y : E × E} (h : lateAt (lateOf F G) j = some y) :
    y = (G.vp.getD j zeroE, G.mf.getD j zeroE) := by
  unfold lateAt at h
  obtain ⟨x, hx, hy⟩ := Option.map_eq_some_iff.1 h
  have hj : x.1 = j := by
    have h0 := List.find?_some hx
    exact of_decide_eq_true (by simpa using h0)
  have hm := (mem_lateOf (List.mem_of_find?_eq_some hx)).2.2
  rw [← hy, hm, hj]

/-- **At a reader that is the run itself.** -/
theorem formsOfRun : FormsOfRun := by
  intro states own piece run name r s s₃ cls F G a rd hst hr hF hG hlat ha hin hv
  refine formsOfIn (Readers.ofStates states) own piece run s rd hin ?_
  intro a' R ha' hR f hf
  have ea : a' = a := by
    rw [ha] at ha'
    exact (Option.some.inj ha').symm
  subst ea
  have eF : a'.F = F := by
    have h0 := seg_fork ha
    rw [hF] at h0
    exact (Option.some.inj h0).symm
  -- the reader's answer, written out
  have hR' : readerOf states piece run s = some R := hR
  unfold readerOf at hR'
  rw [hst] at hR'
  simp only [Option.bind_some, hr, hF, hG] at hR'
  split at hR'
  · obtain rfl := Option.some.inj hR'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hf
    -- the public test at this form
    unfold formsIn at hin
    rw [ha, hR] at hin
    obtain ⟨_, hall⟩ := Eq.mp (Bool.and_eq_true _ _) hin
    have haff := List.all_eq_true.1 hall c.form hf
    unfold affIn at haff
    obtain ⟨_, hsl⟩ := Eq.mp (Bool.and_eq_true _ _) haff
    rw [← hv c hc]
    refine value_eq _ _ c.form (fun _ _ => rfl) fun x hx => ?_
    have h1 := List.all_eq_true.1 hsl x hx
    unfold slotIn at h1
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h1
    show slotW a'.F (lateOf F G) (dataQ own a' rd).mask x.1 =
      Reading.gl.val (G.vp.getD x.1 zeroE) - Reading.gl.val (G.mf.getD x.1 zeroE) *
        (dataQ own a' rd).mask x.1
    cases hl : lateAt (lateOf F G) x.1 with
    | some y =>
      rw [slotW_late _ _ _ _ y hl, lateAt_holds hl]
    | none =>
      rw [slotW_ledger _ _ _ _ hl]
      have hfil : Filled F x.1 := by
        rcases h1.2.2.2 with h2 | h2
        · rw [hl] at h2
          cases h2
        · rw [eF] at h2
          exact h2.1
      obtain ⟨_, k1, k2⟩ := hlat.keep x.1 hfil
      rw [eF, k1, k2]
  · cases hR'

/-- **At the merge's run.** -/
theorem mergedBehind : MergedBehind := by
  intro own s a wo a9 rd ent G p' hhere hop hwo ha9 hents hrow hval hin
  have hrun : headMergeClaim 0 s =
      .ok ([{ form := wo.p.rowForm wo.fvp {} }], { s with here := .head { a with F := G } }) := by
    unfold headMergeClaim
    simp only [hhere, hwo, hrow, named, bind, Except.bind, pure, Except.pure]
  obtain ⟨b, b', e1, e2, hlat⟩ := run_later hrun
  have eb : b = a := by
    rw [hhere] at e1
    exact (VerifiableInference.Desc.First.Here.head.inj e1).symm
  have eb' : b' = { a with F := G } := (VerifiableInference.Desc.First.Here.head.inj e2).symm
  rw [eb, eb'] at hlat
  refine formsOfRun (mergeStates "the merge") own 8 "the merge" "the merge" headMergeClaim s _ _ a.F
    G a9 rd rfl hrun ?_ ?_ hlat ha9 hin ?_
  · unfold S.fork?
    rw [hhere]
    simp [hop]
  · show (if a.opened then some G else none) = some G
    rw [hop]
    rfl
  · intro c hc
    rw [List.mem_singleton.1 hc, ← hval]
    refine value_eq _ _ _ (fun x hx => ?_) fun _ _ => rfl
    rw [hents] at hx
    cases hx

end Johnson.Desc.First.ForkMerge.Exchange

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Exchange.formsOfIn
#print axioms Johnson.Desc.First.ForkMerge.Exchange.lateAt_holds
#print axioms Johnson.Desc.First.ForkMerge.Exchange.formsOfRun
#print axioms Johnson.Desc.First.ForkMerge.Exchange.mergedBehind
