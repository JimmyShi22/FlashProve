-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3StatedSteps.lean. At no real record has a yes of
the block been shown for this file. The kind "lookup" (K3): THE WHOLE SEATED BLOCK STEPS AS A LINK's
FRAME ASKS: the value B of K3.theStated at an address (Law.blockVia, AND BEHIND IT THE STEP WITHOUT
A ROUND
that K3.theWhole lays: quietLook | quietDigits | quietHead; with the run "planes" where it is stated): WHERE B.planOk = true: B.Steps (CarriesFo S.fork? hd), at hd := S.lookHeard? and at hd := the smallness test's record's field (tlHeard). At both lookups and all three sorts of link: general in the address.
  quietLook_frame | quietDigits_frame | quietHead_frame | quietAt_frame: each step without a round leaves what hd reads and leads the ledger to a later one, for every reader hd that S.putFork and the laying of the head's claim leave.
  stated_frame_of: the whole block's decision, at such an hd that K3.block's decision at the two seats frames.
  stated_steps_look | stated_steps_tl: THE TWO LAWS. steps_narrows: Steps passes along Block.Narrows: so they hold of every block that narrows B (a seat's guards).
OBJECT: K3.theStated claim readers X codes shape a (Johnson/Desc/First/Look/K3Stated.lean).
Used by K03Ran.lean (Johnson/Desc/First/K9x/) · K03RowsBare.lean (Johnson/Desc/First/Look/) ·
  LeavesAt346.lean (Johnson/K11R/).
LETTERS: general in claim, readers, X, codes, shape, a, B.
OVER: Johnson/Top/H/K3Steps.lean | K3StepsAt.lean | K3Via/Blocks.lean · Look/K3OwnIs.lean
  (theStated_is | theWhole_is | theOwn_is) and Look/K3QuietLaws.lean (quietLook_ok | quietDigits_ok
  | quietDigits_fork | quietHead_ok).
Limits. planOk = true IS A PREMISE. One direction: from a yes. A frame's law: no error term. Of the runs of claims: K3StatedRuns.lean. Nothing on soundness, completeness or hiding.
-/
import Johnson.Top.H.K3StepsAt
import Johnson.Top.H.K3Via.Blocks
import Johnson.Desc.First.Look.K3OwnIs
import Johnson.Desc.First.Look.K3QuietLaws
import Johnson.Desc.Sound.MergeNarrow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Carries CarriesFo)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits)

section Quiet
variable {Γ : Type} (hd : S → Option Γ)

theorem quietLook_frame (fs : Forest.Shape) (s t : S) (h : Desc.K3.quietLook fs s = .ok t) :
    Frame S.fork? hd s t := by
  obtain ⟨rfl, -⟩ := Desc.K3.quietLook_ok fs s t h
  exact Frame.refl _ _ _

theorem quietDigits_frame (hF : ∀ s G, hd (S.putFork s G) = hd s) (used claims : ℕ) (s t : S)
    (h : Desc.K3.quietDigits used claims s = .ok t) : Frame S.fork? hd s t := by
  obtain ⟨F₂, hF₂, hG₂⟩ := Desc.K3.quietDigits_fork used claims s t h
  obtain ⟨F, -, -, rfl⟩ := Desc.K3.quietDigits_ok used claims s t h
  refine ⟨fun g hg => by rw [hF]; exact hg, fun F' hF' => ?_⟩
  obtain rfl : F₂ = F' := Option.some.inj (hF₂.symm.trans hF')
  exact ⟨_, hG₂, ⟨Nat.le_refl _, rfl, fun z => z, fun _ k => ⟨k, rfl, rfl⟩⟩⟩

theorem quietHead_frame
    (hH : ∀ (s : S) a c, s.here = .head a →
      hd { s with here := .head { a with claim := some c } } = hd s)
    (X : Verify.Public) (s t : S) (h : Desc.K3.quietHead X s = .ok t) : Frame S.fork? hd s t := by
  obtain ⟨a, c, ha, ho, rfl⟩ := Desc.K3.quietHead_ok X s t h
  refine ⟨fun g hg => by rw [hH s a c ha]; exact hg,
    fun F hF => ⟨F, ?_, OnBytes.PscRun.Later.refl F⟩⟩
  simpa [S.fork?, ha, ho] using hF

/-- **Every step that stands behind a lookup.** -/
theorem quietAt_frame (hF : ∀ s G, hd (S.putFork s G) = hd s)
    (hH : ∀ (s : S) a c, s.here = .head a →
      hd { s with here := .head { a with claim := some c } } = hd s)
    (X : Verify.Public) (i : ℕ) (d : Bool) (f : S → Except String S)
    (hf : Desc.K3.quietAt X i d = some f) (s t : S) (h : f s = .ok t) : Frame S.fork? hd s t := by
  unfold Desc.K3.quietAt at hf
  try dsimp only at hf
  repeat' split at hf
  all_goals first
    | (obtain rfl := Option.some.inj hf
       exact quietHead_frame hd hH X s t h)
    | (obtain rfl := Option.some.inj hf
       exact quietLook_frame hd _ s t h)
    | (obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 hf
       exact quietDigits_frame hd hF _ _ s t h)
    | exact absurd hf (by simp)

end Quiet

section Stated
variable {Cl Γ : Type}

theorem steps_narrows {T : Type} {R : T → T → Prop} {b' b : Block T Cl} (hN : b'.Narrows b)
    (h : b.Steps R) : b'.Steps R :=
  fun s rs gs s' e => h s rs gs s' (hN.2 s rs gs s' e)

/-- **The whole seated block's decision.** -/
theorem stated_frame_of (hd : S → Option Γ) (claim : Aff → Cl)
    (hC : ∀ piece laid before p guests s s' rs cols,
      (Desc.K3.block (seatCalls claim) piece laid before p guests).decide s rs cols = .ok s' →
        Frame S.fork? hd s s')
    (hD : ∀ piece laid before p guests s s' rs cols,
      (Desc.K3.block (seatDigits claim) piece laid before p guests).decide s rs cols = .ok s' →
        Frame S.fork? hd s s')
    (hF : ∀ s G, hd (S.putFork s G) = hd s)
    (hH : ∀ (s : S) a c, s.here = .head a →
      hd { s with here := .head { a with claim := some c } } = hd s)
    (readers : ℕ → Option (Desc.K3.Readers S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Block S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hdec : B.decide s rs gs = .ok s') : Frame S.fork? hd s s' := by
  obtain ⟨B₁, h1, -, ed, -, ep⟩ := Desc.K3.theStated_is claim readers X codes shape a B h
  obtain ⟨b, hb, hw⟩ := Desc.K3.theWhole_is claim true X codes shape a B₁ h1
  obtain ⟨i, digits, p, sent, laid, -, -, -, -, -, -, edb, -, hpb⟩ :=
    Desc.K3.theOwn_is claim true X codes shape a b hb
  rw [ed] at hdec
  rw [ep] at hOk
  have own : ∀ (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))),
      b.planOk = true → b.decide s rs gs = .ok s' → Frame S.fork? hd s s' := by
    intro s s' rs gs hp hdc
    rw [edb] at hdc
    have hv := hpb hp
    cases digits with
    | false =>
      have e : Desc.K3.seatOfLookupOnDigitsOrCalls claim false = seatCalls claim := by simp [Desc.K3.seatOfLookupOnDigitsOrCalls]
      rw [e] at hdc hv
      exact hC _ _ _ _ _ s s' rs gs (Desc.K3.Law.blockVia_decide hv hdc)
    | true =>
      have e : Desc.K3.seatOfLookupOnDigitsOrCalls claim true = seatDigits claim := by simp [Desc.K3.seatOfLookupOnDigitsOrCalls]
      rw [e] at hdc hv
      exact hD _ _ _ _ _ s s' rs gs (Desc.K3.Law.blockVia_decide hv hdc)
  rcases hw with ⟨-, rfl⟩ | ⟨f, hf, rfl⟩
  · exact own s s' rs gs hOk hdec
  · have hp : b.planOk = true := by
      simpa [Desc.Block.andThen, Desc.roundlessBlock] using hOk
    obtain ⟨i', -, hf'⟩ := Option.bind_eq_some_iff.1 hf
    have hdec' : (b.decide s (rs.take b.rounds.length) (gs.take b.openings)).bind
        (fun s₁ => f s₁) = .ok s' := hdec
    cases hb1 : b.decide s (rs.take b.rounds.length) (gs.take b.openings) with
    | error e =>
      rw [hb1] at hdec'
      have k : (Except.error e : Except String S) = .ok s' := hdec'
      cases k
    | ok s₁ =>
      rw [hb1] at hdec'
      have hq : f s₁ = .ok s' := hdec'
      exact (own s s₁ _ _ hp hb1).trans (quietAt_frame hd hF hH X i' _ f hf' s₁ s' hq)

/-- **THE LAW, at what the lookup on the calls was heard to return.** -/
theorem stated_steps_look (claim : Aff → Cl) (readers : ℕ → Option (Desc.K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Desc.Place) (B : Block S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true) :
    B.Steps (CarriesFo S.fork? S.lookHeard?) :=
  fun s rs gs s' hdec =>
    (stated_frame_of S.lookHeard? claim
      (fun piece laid before p guests s s' rs cols e =>
        calls_decide_calls claim piece laid before p guests s s' rs cols e)
      (fun piece laid before p guests s s' rs cols e =>
        digits_decide_calls claim piece laid before p guests s s' rs cols e)
      (fun s G => lookHeard_putFork s G)
      (fun s a c ha => by simp [S.lookHeard?, ha])
      readers X codes shape a B h hOk s s' rs gs hdec).carriesFo

/-- **THE LAW, at what the lookup on the digits was heard to return.** -/
theorem stated_steps_tl (claim : Aff → Cl) (readers : ℕ → Option (Desc.K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Desc.Place) (B : Block S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true) :
    B.Steps (CarriesFo S.fork? tlHeard) :=
  fun s rs gs s' hdec =>
    (stated_frame_of tlHeard claim
      (fun piece laid before p guests s s' rs cols e =>
        calls_decide_digits claim piece laid before p guests s s' rs cols e)
      (fun piece laid before p guests s s' rs cols e =>
        digits_decide_digits claim piece laid before p guests s s' rs cols e)
      (fun s G => congrArg (fun x : Option HTailF2 => x.bind (·.heard)) (tl_putFork s G))
      (fun s a c ha => by simp [tlHeard, S.tl?, ha])
      readers X codes shape a B h hOk s s' rs gs hdec).carriesFo

end Stated

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.quietAt_frame
#print axioms VerifiableInference.OnPublicFiles.stated_frame_of
#print axioms VerifiableInference.OnPublicFiles.stated_steps_look
#print axioms VerifiableInference.OnPublicFiles.stated_steps_tl
