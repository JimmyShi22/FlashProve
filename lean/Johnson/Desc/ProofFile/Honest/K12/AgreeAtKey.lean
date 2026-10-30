-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AgreeAtKey.lean: RunPlays.agree
at the key's two shared tests, at every coin that the frame lends: a debt that the placing names. IT IS
A COMPOSITION: the tests on the book have spoken (full_ties, ties_O), and what is new is one closed line
and the two letters' twins.

  agree_of_ties_letter   COPIED, under another name, from agree_of_ties' of K12/RunOfThr.lean

  agree_of_tiesO_letter  its twin at J.fresh = none
  ties_folded            tiesB at the test on G_u, out of full_ties, as ties_ranges is
  agree_at_U, agree_at_O  the two laws, general in the ManyJob

NO Thr, NO m: the laws hold at every w, fr, rows and look that lend, so RunPlays.agree is an instance.

A YES WOULD NOT SHOW: RunPlays whole: old, widths, is a law at keyBook and asks another file · that play
returns · at O the run's steps are guarded, so its coins are guardCoins of a plain c, and the carry is
the caller's (lendRow_guarded) · Plays · anything over coins, and nothing on hiding.

Limits. At written values, under hK₀. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AgreeBook
import Johnson.Desc.ProofFile.Honest.K12.Own.AgreeOwn
import Johnson.Desc.ProofFile.Honest.K12.TiesAtKey
import Johnson.Desc.ProofFile.Honest.K12.Sim.ExactFirstAtU
import Johnson.Desc.ProofFile.Honest.K12.OmegaAtKeyBookKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open H2K.Member (piKUFull piKOFull)
open AtPublicFiles.KeyBook (KeyPub keyBook atFull fullPub)
open AtPublicFiles.KeyTest (jobFolded jobOmega)

variable {V W X : Type}

/-- COPIED from agree_of_ties' (K12/RunOfThr.lean): agree_of_ties at a job
that is a letter. -/
theorem agree_of_ties_letter (J : TestJob W X) (f : Addr × ℕ) (hfr : J.fresh = some f) (B : ProverCoinCounts)
    (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (c : RowCoins [(firstPart J : Part V W X), restPart J])
    (h : lendRow B rows look J.p.place [(firstPart J : Part V W X), restPart J] 0 = .ok c) (w : W)
    (fr : Front X) (hT : tiesB B J.p.place J.members.length = true)
    (hk : J.s₀.k = (sgOf J.s₀).h + (sgOf J.s₀).g)
    (hrows : ∀ mem mem' : ℕ → Stretch, (∀ t, t < J.members.length → mem t = mem' t) →
      μOf (sgOf J.s₀) (J.rows₀ w fr mem) = μOf (sgOf J.s₀) (J.rows₀ w fr mem')) :
    Agree J w fr J.s₀ (firstRd J c.1) (restCoins J c.2.1) := by
  cases J with
  | mk p ms fresh r ro tr =>
    have e : fresh = some f := hfr
    subst e
    exact agree_of_ties p ms f r ro tr B rows look c h w fr hT hk hrows

/-- The twin at J.fresh = none. -/
theorem agree_of_tiesO_letter (J : TestJob W X) (hfr : J.fresh = none) (B : ProverCoinCounts)
    (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (c : RowCoins [(firstPart J : Part V W X), restPart J])
    (h : lendRow B rows look J.p.place [(firstPart J : Part V W X), restPart J] 0 = .ok c) (w : W)
    (fr : Front X) (hT : Own.tiesOB B J.p.place J.members.length = true)
    (hrows : ∀ mem mem' : ℕ → Stretch, (∀ t, t < J.members.length → mem t = mem' t) →
      μOf (sgOf J.s₀) (J.rows₀ w fr mem) = μOf (sgOf J.s₀) (J.rows₀ w fr mem')) :
    Agree J w fr J.s₀ (firstRd J c.1) (restCoins J c.2.1) := by
  cases J with
  | mk p ms fresh r ro tr =>
    have e : fresh = none := hfr
    subst e
    exact Own.agree_of_tiesO p ms r ro tr B rows look c h w fr hT hrows

/-- tiesB at the test on G_u, out of full_ties. -/
theorem ties_folded (K : KeyPub) (hK : fullPub = some K) :
    tiesB (keyBook K) jobFolded.p.place jobFolded.members.length = true := by
  have h := full_ties
  unfold atFull at h
  rw [hK] at h
  exact List.all_eq_true.1 h jobFolded (by simp)

/-- k = h + g at the first stage of the test on G_u. By the kernel. -/
theorem first_k_U : (piKUFull.nums.stages.headD default).k =
    (sgOf (piKUFull.nums.stages.headD default)).h + (sgOf (piKUFull.nums.stages.headD default)).g := by
  decide +kernel

theorem place_U : piKUFull.place = jobFolded.p.place := by decide +kernel

theorem fresh_some_U : jobFolded.fresh.isSome = true := by decide +kernel

theorem fresh_none_O : jobOmega.fresh = none := by decide +kernel

theorem members_two_O : jobOmega.members.length = 2 := by decide +kernel

/-- **RunPlays.agree at the test on G_u, at every coin that the frame lends.** -/
theorem agree_at_U (K₀ : KeyPub) (hK₀ : fullPub = some K₀) (A : Light.ManyJob W X)
    (hp : A.toRun.toTest.p = piKUFull) (hm : A.toRun.toTest.members = jobFolded.members)
    (hf : A.toRun.toTest.fresh = jobFolded.fresh) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d)
    (c : RowCoins [(firstPart A.toRun.toTest : Part V W X), restPart A.toRun.toTest])
    (hc : lendRow (keyBook K₀) rows look A.toRun.toTest.p.place
      [(firstPart A.toRun.toTest : Part V W X), restPart A.toRun.toTest] 0 = .ok c)
    (w : W) (fr : Front X) :
    Agree A.toRun.toTest w fr A.toRun.toTest.s₀ (firstRd A.toRun.toTest c.1)
      (restCoins A.toRun.toTest c.2.1) := by
  obtain ⟨f, hf'⟩ := Option.isSome_iff_exists.1 fresh_some_U
  have hT : tiesB (keyBook K₀) A.toRun.toTest.p.place A.toRun.toTest.members.length = true := by
    rw [hp, hm, place_U]
    exact ties_folded K₀ hK₀
  have hk : A.toRun.toTest.s₀.k = (sgOf A.toRun.toTest.s₀).h + (sgOf A.toRun.toTest.s₀).g := by
    unfold TestJob.s₀
    rw [hp]
    exact first_k_U
  exact agree_of_ties_letter A.toRun.toTest f (hf.trans hf') (keyBook K₀) rows look c hc w fr hT hk
    fun mem mem' h => Light.rowsMu_many A _ w fr mem mem' h

/-- **RunPlays.agree at the test on G_omega, at every coin that the frame lends**, at plain coins. -/
theorem agree_at_O (K₀ : KeyPub) (hK₀ : fullPub = some K₀) (A : Light.ManyJob W X)
    (hp : A.toRun.toTest.p = piKOFull) (hm : A.toRun.toTest.members = jobOmega.members)
    (hf : A.toRun.toTest.fresh = jobOmega.fresh) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d)
    (c : RowCoins [(firstPart A.toRun.toTest : Part V W X), restPart A.toRun.toTest])
    (hc : lendRow (keyBook K₀) rows look A.toRun.toTest.p.place
      [(firstPart A.toRun.toTest : Part V W X), restPart A.toRun.toTest] 0 = .ok c)
    (w : W) (fr : Front X) :
    Agree A.toRun.toTest w fr A.toRun.toTest.s₀ (firstRd A.toRun.toTest c.1)
      (restCoins A.toRun.toTest c.2.1) := by
  have hT : Own.tiesOB (keyBook K₀) A.toRun.toTest.p.place A.toRun.toTest.members.length = true := by
    rw [hp, hm, members_two_O]
    have h := OmegaAtKeyBook.ties_O
    unfold atFull at h
    rw [hK₀] at h
    exact h
  exact agree_of_tiesO_letter A.toRun.toTest (hf.trans fresh_none_O) (keyBook K₀) rows look c hc w fr
    hT fun mem mem' h => Light.rowsMu_many A _ w fr mem mem' h

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.agree_of_ties_letter
#print axioms ProofFile.Honest.K12.agree_of_tiesO_letter
#print axioms ProofFile.Honest.K12.ties_folded
#print axioms ProofFile.Honest.K12.first_k_U
#print axioms ProofFile.Honest.K12.place_U
#print axioms ProofFile.Honest.K12.fresh_some_U
#print axioms ProofFile.Honest.K12.fresh_none_O
#print axioms ProofFile.Honest.K12.members_two_O
#print axioms ProofFile.Honest.K12.agree_at_U
#print axioms ProofFile.Honest.K12.agree_at_O
