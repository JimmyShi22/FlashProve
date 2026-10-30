-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/EqStill.lean: FOR THE ITEM "totalB": AT AN ENTRY WHOSE RUN LEAVES THE STATE AS IT IS,
AND AT THE HEAD's MERGE: THE TERMS' COEFFICIENTS ARE THE WORTHS OF THE ITEM's FORMS: `ItemEq` (Honest/K9/EqItem.lean).
Statements and proofs over the sealed library's laws; no goal is stated.
  **`eq_still`**, **`eq_still_in`**   `ItemEq` at an entry whose run stands under a run r with the library's `Still φ
      Ok r fs`, the table of terms there being `plainTm (valsStill … fs entUnit)`; the second from three facts at the
      state and a silent hole, as the library's `item_still_in`
  **`eq_merge`**   `ItemEq` at an entry whose run stands under `headMergeClaim`, the table there being `plainTm
      (valsMerge …)`
THE PROOFS ARE THE LIBRARY's OWN PROOFS OF `item_still`, `item_still_in`
(Johnson/Desc/First/Link/Law/HitemsStill.lean) AND `item_merge` (HitemsMerge.lean), CUT BY PROGRAM OFF THESE FILES, as
in Honest/K9/EqK4.lean. No member. `eq_still` is called by `eq_still_in`; the others by Honest/K9/EqAt.lean.
WHAT IS NOT CLAIMED. Any premise at any state or link. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.EqItem
import Johnson.Desc.First.Link.Law.HitemsMerge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference
open OnBytes.PscRun (Filled Sized Same hideRun_ok)
open VerifiableInference.Desc (Link Claim)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.First.MergeLaw (claim_inv)
open Johnson.Desc.First.ForkMerge (headMergeClaim)
open VerifiableInference.Desc.K4Values (InWin LaidAt winOf)
open VerifiableInference.Desc.K11Run (valsMerge get_head)
open VerifiableInference.Desc.StillRun
open VerifiableInference.Desc.EntryUnit (entUnit)
open VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc

variable {α : Type}

/-- **The equation at an entry whose run leaves the state as it is.** -/
theorem eq_still (H : Desc.K9.LinkHoles) (L : Link S Claim) (φ : S → α)
    (Ok : α × Option Pub9 → Prop)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → MsgQ) (o : ℕ × String)
    (hne : (o.2 == "K8.equations") = false)
    (run r : ℕ → S → Except String (List Claim × S)) (hAt : At L o run)
    (fs : α × Option Pub9 → Option (List Aff)) (hu : Under run r) (hS : Still φ Ok r fs)
    (ht : tmOf o = plainTm (valsStill Reading.gl fs entUnit))
    (s : S) (b : Desc.K9.Part) (hb : atS.get? s = some b)
    (hf : Fx9 φ Ok (fixed9 φ s) s) (z : List Claim × S) (hz : run 0 s = .ok z)
    (hc : (z.1.all fun c => c.runs.isEmpty && c.eqFirst.isNone &&
      c.form.ents.all (Desc.K9.ownRow b.F)) = true)
    (hin : Desc.K9.formsIn (Desc.K9.readersOfLink H L) own o.1 o.2 s = true) :
    ItemEq φ tmOf (Desc.K9.readersOfLink H L) own rd o s b := by
  have h0 : s.fork? = some b.F := Desc.K9.get_fork s b hb
  obtain ⟨l, hl, hfm, hz2, _⟩ := reader_still φ Ok run r fs hu hS _ s hf z hz b.F h0
  have hG : z.2.fork? = some b.F := by rw [hz2]; exact h0
  have hR := reader_of_run H L o hne run hAt s z hz b.F b.F h0 hG hc
  rw [hfm, lateOf_self] at hR
  have hq : (fixed9 φ s).2 = some (pubOf b) := by
    show (atS.get? s).map pubOf = _
    rw [hb]
    rfl
  refine ⟨_, hR, fun n => ?_⟩
  have he := named_of_formsIn (Desc.K9.readersOfLink H L) own o.1 o.2 s b ⟨l, []⟩ hb hR hin
  rw [ht]
  show (Desc.K9L.numbered n (valsStill Reading.gl fs entUnit (fixed9 φ s) (dataQ own b rd))).map (·.2) = _
  rw [numbered_snd]
  unfold valsStill
  rw [hq, hl]
  exact List.map_congr_left fun f hf' =>
    value_meets_still b (dataQ own b rd) (fixed9 φ s) hq f (he f hf')

/-- **The same on three facts at the state and a silent hole.** -/
theorem eq_still_in (H : Desc.K9.LinkHoles) (L : Link S Claim) (φ : S → α)
    (Ok : α × Option Pub9 → Prop)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → MsgQ) (o : ℕ × String)
    (hne : (o.2 == "K8.equations") = false)
    (run r : ℕ → S → Except String (List Claim × S)) (hAt : At L o run)
    (fs : α × Option Pub9 → Option (List Aff)) (hu : Under run r) (hS : Still φ Ok r fs)
    (ht : tmOf o = plainTm (valsStill Reading.gl fs entUnit))
    (s : S) (b : Desc.K9.Part) (hb : atS.get? s = some b)
    (hf : Fx9 φ Ok (fixed9 φ s) s) (hsil : H.silent o.1 o.2 s = none)
    (hin : Desc.K9.formsIn (Desc.K9.readersOfLink H L) own o.1 o.2 s = true) :
    ItemEq φ tmOf (Desc.K9.readersOfLink H L) own rd o s b := by
  obtain ⟨R, hR⟩ := reader_of_formsIn _ own o.1 o.2 s hin
  obtain ⟨z, G0, _, hz, h0, _, hc, _⟩ := run_of_reader H L o hne run hAt s hsil R hR
  obtain rfl : G0 = b.F := Option.some.inj (h0.symm.trans (Desc.K9.get_fork s b hb))
  exact eq_still H L φ Ok tmOf own rd o hne run r hAt fs hu hS ht s b hb hf z hz hc hin

/-- **The equation at the head's merge.** -/
theorem eq_merge (H : Desc.K9.LinkHoles) (L : Link S Claim) (φ : S → α)
    (Ok : α × Option Pub9 → Prop)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → MsgQ) (o : ℕ × String)
    (hne : (o.2 == "K8.equations") = false)
    (run : ℕ → S → Except String (List Claim × S)) (hAt : At L o run)
    (hu : Under run headMergeClaim) (π : α → Option WsForkOut)
    (hπ : ∀ s a, s.here = .head a → π (φ s) = a.wo)
    (hOk : ∀ q wo u, Ok q → π q.1 = some wo → q.2 = some u → Sized u.F ∧
      ∀ x ∈ (wo.p.rowForm wo.fvp {}).slots.toList, InWin (winOf wo.p) x.1 ∨ Filled u.F x.1)
    (ht : tmOf o = plainTm (valsMerge Reading.gl π entUnit))
    (s : S) (b : Desc.K9.Part) (hb : atS.get? s = some b)
    (hf : Fx9 φ Ok (fixed9 φ s) s) (hsil : H.silent o.1 o.2 s = none)
    (hin : Desc.K9.formsIn (Desc.K9.readersOfLink H L) own o.1 o.2 s = true) :
    ItemEq φ tmOf (Desc.K9.readersOfLink H L) own rd o s b := by
  obtain ⟨R, hR⟩ := reader_of_formsIn _ own o.1 o.2 s hin
  obtain ⟨⟨c, s'⟩, G0, G', hz, h0, hG', _, rfl⟩ := run_of_reader H L o hne run hAt s hsil R hR
  obtain rfl : G0 = b.F := Option.some.inj (h0.symm.trans (Desc.K9.get_fork s b hb))
  obtain ⟨ah, wo, G, h1, hwo, rfl, rfl, hrunG⟩ := claim_inv (hu 0 s c s' hz)
  obtain ⟨a₁, ha₁, f1, _, _, f4⟩ := get_head s b hb ah h1 G
  obtain rfl : G' = G := by
    have e := Desc.K9.get_fork _ a₁ ha₁
    rw [f1] at e
    exact Option.some.inj (hG'.symm.trans e)
  have hq : (fixed9 φ s).2 = some (pubOf b) := by
    show (atS.get? s).map pubOf = _
    rw [hb]
    rfl
  have hq1 : π (fixed9 φ s).1 = some wo := by
    show π (φ s) = _
    rw [hπ s ah h1, hwo]
  obtain ⟨hsz, hsl⟩ := hOk _ wo (pubOf b) hf.1 hq1 hq
  have hrun' : b.F.hideRun wo.p.first (Array.replicate wo.p.walk.1.length zeroE)
      (subE zeroE oneE) = some G' := by rw [f4]; exact hrunG
  obtain ⟨hlaid, hwin⟩ := window_of_run (show Sized b.F from hsz) hrun'
  refine ⟨_, hR, fun n => ?_⟩
  have he := named_of_formsIn (Desc.K9.readersOfLink H L) own o.1 o.2 s b _ hb hR hin
  rw [ht]
  show (Desc.K9L.numbered n (valsMerge Reading.gl π entUnit (fixed9 φ s) (dataQ own b rd))).map (·.2) = _
  rw [numbered_snd]
  simp only [valsMerge, hq1, hq]
  show [_] = [_]
  refine congrArg (fun v => [v]) ?_
  refine value_meets_windows b G' [winOf wo.p] (dataQ own b rd) (fixed9 φ s) hq _
    (he _ (List.mem_singleton.2 rfl)) fun x hx => ?_
  by_cases hw : InWin (winOf wo.p) x.1
  · obtain ⟨k1, k2, k3⟩ := hwin x.1 hw
    exact Or.inl ⟨_, List.mem_singleton.2 rfl, hw, hlaid, k1, k2, k3⟩
  · refine Or.inr ⟨?_, (hsl x hx).resolve_left hw⟩
    rintro ⟨w', hw', hj⟩
    obtain rfl := List.mem_singleton.1 hw'
    exact hw hj

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.eq_still
#print axioms ProofFile.Honest.K9.eq_still_in
#print axioms ProofFile.Honest.K9.eq_merge
