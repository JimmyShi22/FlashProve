-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyOwnAgree.lean: at the key file's own test the two parts' readers agree, at every coin that the frame lends at the
key file's book: the clause `agree` of `OwnAsks` and of `RunPlays`. The twin at W of `agree_at_U` (IOP's K12/AgreeAtKey.lean):
`tiesB` at `jobOwn` is in the library's `full_ties`.

  `ties_own`, `first_k_W`, `place_W`, `fresh_some_W`: the closed facts.
  `agree_at_W`: the law, general in the `ManyJob`.

What stays open. hm, hf: the job has as many members as `jobOwn`, and a fresh table of an earlier sender (`tiesB` reads the place and the count alone). K₀: 'fullPub = some K₀'.
Nothing on soundness, completeness, hiding or binding.
-/
import Johnson.Desc.ProofFile.Honest.K12.TiesAtKey
import Johnson.Desc.ProofFile.Honest.K12.AgreeBook
import Johnson.Desc.ProofFile.Honest.K12.RunMany
import Johnson.Desc.ProofFile.Honest.K12.Sim.ExactFirstAtU
import Johnson.Desc.K12.Law.PlacesKeyFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyLastChain
open OnBytes OnBytes.Slice Cb
open ProofFile.Honest ProofFile.Honest.K12
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open H2K.Member (piKWFull)
open AtPublicFiles.KeyBook (KeyPub keyBook atFull fullPub)
open AtPublicFiles.KeyTest (jobOwn)

variable {V W X : Type}

/-- `tiesB` at the own test, out of `full_ties`. -/
theorem ties_own (K : KeyPub) (hK : fullPub = some K) :
    tiesB (keyBook K) jobOwn.p.place jobOwn.members.length = true := by
  have h := full_ties
  unfold atFull at h
  rw [hK] at h
  exact List.all_eq_true.1 h jobOwn (by simp)

theorem first_k_W : (piKWFull.nums.stages.headD default).k =
    (sgOf (piKWFull.nums.stages.headD default)).h + (sgOf (piKWFull.nums.stages.headD default)).g := by
  decide +kernel

theorem place_W : piKWFull.place = jobOwn.p.place := by decide +kernel

theorem fresh_some_W : jobOwn.fresh.isSome = true := by decide +kernel

/-- `agree_of_ties` at a job that is a letter. -/
theorem agree_of_ties_job (J : TestJob W X) (f : Addr × ℕ) (hfr : J.fresh = some f) (B : ProverCoinCounts)
    (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (c : RowCoins [(firstPart J : Part V W X), restPart J])
    (h : lendRow B rows look J.p.place [(firstPart J : Part V W X), restPart J] 0 = .ok c) (w : W)
    (fr : Front X) (hT : tiesB B J.p.place J.members.length = true)
    (hk : J.s₀.k = (sgOf J.s₀).h + (sgOf J.s₀).g)
    (hrows : ∀ mem mem' : ℕ → ProofFile.Honest.K12.Stretch, (∀ t, t < J.members.length → mem t = mem' t) →
      μOf (sgOf J.s₀) (J.rows₀ w fr mem) = μOf (sgOf J.s₀) (J.rows₀ w fr mem')) :
    Agree J w fr J.s₀ (firstRd J c.1) (restCoins J c.2.1) := by
  cases J with
  | mk p ms fresh r ro tr =>
    have e : fresh = some f := hfr
    subst e
    exact agree_of_ties p ms f r ro tr B rows look c h w fr hT hk hrows

/-- **The clause `agree` at the own test, at every coin that the frame lends.** -/
theorem agree_at_W (K₀ : KeyPub) (hK₀ : fullPub = some K₀) (A : Light.ManyJob W X)
    (hp : A.toRun.toTest.p = piKWFull) (hm : A.toRun.toTest.members.length = jobOwn.members.length)
    (f : Addr × ℕ) (hf : A.toRun.toTest.fresh = some f) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d)
    (c : RowCoins [(firstPart A.toRun.toTest : Part V W X), restPart A.toRun.toTest])
    (hc : lendRow (keyBook K₀) rows look A.toRun.toTest.p.place
      [(firstPart A.toRun.toTest : Part V W X), restPart A.toRun.toTest] 0 = .ok c)
    (w : W) (fr : Front X) :
    Agree A.toRun.toTest w fr A.toRun.toTest.s₀ (firstRd A.toRun.toTest c.1)
      (restCoins A.toRun.toTest c.2.1) := by
  have hT : tiesB (keyBook K₀) A.toRun.toTest.p.place A.toRun.toTest.members.length = true := by
    rw [hp, hm, place_W]
    exact ties_own K₀ hK₀
  have hk : A.toRun.toTest.s₀.k = (sgOf A.toRun.toTest.s₀).h + (sgOf A.toRun.toTest.s₀).g := by
    unfold TestJob.s₀
    rw [hp]
    exact first_k_W
  exact agree_of_ties_job A.toRun.toTest f hf (keyBook K₀) rows look c hc w fr hT hk
    fun mem mem' h => Light.rowsMu_many A _ w fr mem mem' h

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.ties_own
#print axioms AtPublicFiles.KeyLastChain.first_k_W
#print axioms AtPublicFiles.KeyLastChain.place_W
#print axioms AtPublicFiles.KeyLastChain.fresh_some_W
#print axioms AtPublicFiles.KeyLastChain.agree_of_ties_job
#print axioms AtPublicFiles.KeyLastChain.agree_at_W
