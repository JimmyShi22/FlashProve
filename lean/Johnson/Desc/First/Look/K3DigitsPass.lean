-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3DigitsPass.lean: the lookup on the digits of a segment's approximate range
proof: AN ACCEPT OF THE WHOLE SEATED SUB-PROTOCOL (K3.theStated's value at the digits' address) IS A
K3Pass (Johnson/Top/H/Keep/FormsPassK3.lean: what a sub-protocol may turn so that the sentences
«forms» of other runs and their public tests pass it). At the sub-protocol's own decide, whatever
the rounds' words. NO SOUNDNESS IS CLAIMED.

Main names.
  mergeOf_putFork: laying a ledger leaves the slot of the merge's end value.
  quietAt_pass: the step without a round behind the digits' rounds is a K3Pass: its ledger is the
    one in front but for the count of planned claims.
  k3_digits_step_pass: so the whole: k3_digits_pass (Johnson/Top/H/Keep/K3PassOf.lean) at the
    lookup's own rounds, then quietAt_pass, by K3Pass.trans.
OBJECT. Desc.K3.theStated's value at the digits' address.
USER. Whoever carries formsIn of other runs over the digits' sub-protocol (k3_formsIn_fwd):
among others K3RidesDig.lean and K3DigitsFormsJoinAtt.lean (Johnson/Desc/Sound/MgAt/) and
Johnson/P5J/K03HeadOwnAt.lean call k3_digits_step_pass.
LETTERS. Those of k3_digits_step_turns; F.
IS IT EMPTY? The premises are an .ok of decide and a ledger with its sizes.
Compiled with the whole library.



Limits. Nothing on Fwd, RunSame or the late slots: by run.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.K3PassOf
import Johnson.Desc.First.Look.K3DigitsStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K9 (mergeOf)

/-- Laying a ledger leaves the slot of the merge's end value. -/
theorem mergeOf_putFork (s : Desc.First.S) (G : Fork) : mergeOf (s.putFork G) = mergeOf s := by
  cases hh : s.here with
  | between => simp [mergeOf, Desc.First.S.putFork, hh]
  | fin _ => simp [mergeOf, Desc.First.S.putFork, hh]
  | mem _ => simp [mergeOf, Desc.First.S.putFork, hh]
  | lay a => simp [mergeOf, Desc.First.S.putFork, hh]
  | att a => simp [mergeOf, Desc.First.S.putFork, hh]
  | head a =>
    cases ho : a.opened with
    | false => simp [mergeOf, Desc.First.S.putFork, hh, ho]
    | true => simp [mergeOf, Desc.First.S.putFork, hh, ho]

/-- **The step without a round is a K3Pass.** -/
theorem quietAt_pass (X : Verify.Public) (i : ℕ)
    (f : Desc.First.S → Except String Desc.First.S) (hf : Desc.K3.quietAt X i true = some f)
    (s t : Desc.First.S) (h : f s = .ok t) {F : Fork} (hF : s.fork? = some F)
    (hS : OnBytes.PscRun.Sized F) : ∃ G, K3Pass s t F G := by
  obtain ⟨F₂, c, hF₂, hG₂, -⟩ := quietAt_ledger X i f hf s t h
  obtain rfl : F = F₂ := Option.some.inj (hF.symm.trans hF₂)
  have three : SameBut s t ∧ mergeOf t = mergeOf s ∧ t.tl? = s.tl? := by
    unfold Desc.K3.quietAt at hf
    simp only [if_true] at hf
    split at hf
    · obtain rfl := Option.some.inj hf
      obtain ⟨ah, c', ha, ho, e⟩ := Desc.K3.quietHead_ok X s t h
      rw [e]
      exact ⟨headClaim_sameBut s ah c' ha ho, by simp [mergeOf, ha],
        by simp [Desc.First.S.tl?, ha]⟩
    · split at hf <;> split at hf <;>
        (obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 hf
         obtain ⟨F', hF', -, e⟩ := Desc.K3.quietDigits_ok _ _ s t h
         rw [e]
         exact ⟨putFork_sameBut s F' _ hF', mergeOf_putFork s _, tl_putFork s _⟩)
  exact ⟨{ F with planClaimsF := c },
    { same := three.1
      front := hF
      behind := hG₂
      later := later_planClaims F c
      sizedF := hS
      sizedG := hS
      trees := rfl
      below := fun _ _ hj => hj
      owed := fun _ hi => hi
      merge := three.2.1
      tl := fun ht => by rw [three.2.2]; exact ht }⟩

/-- **AN ACCEPT OF THE WHOLE SEATED SUB-PROTOCOL IS A K3Pass.** -/
theorem k3_digits_step_pass {Cl : Type} (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i true)
    (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂) {F : Fork} (hF : s.fork? = some F)
    (hS : OnBytes.PscRun.Sized F) : ∃ G, K3Pass s s₂ F G := by
  obtain ⟨P', sent, laid, n, gs', s', -, hyes, hstep⟩ :=
    theStated_yes_digits claim readers X codes shape a B h hOk i hi hpc s s₂ rs gs hd
  obtain ⟨G, Q⟩ := k3_digits_pass claim a.piece laid sent P' [] s s' _ gs' hyes hF hS
  rcases hstep with e | ⟨f, hf, hfs⟩
  · rw [e]
    exact ⟨G, Q⟩
  · obtain ⟨G₂, Q₂⟩ := quietAt_pass X i f hf s' s₂ hfs Q.behind Q.sizedG
    exact ⟨G₂, Q.trans Q₂⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.mergeOf_putFork
#print axioms VerifiableInference.OnPublicFiles.quietAt_pass
#print axioms VerifiableInference.OnPublicFiles.k3_digits_step_pass
