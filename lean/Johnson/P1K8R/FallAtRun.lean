-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/FallAtRun.lean: THE SMALLNESS TEST: THE CHANCE OF Johnson/P1K8R/FallChanceAgree.lean
AT THE HONEST SIDE's OWN RUN (`runC`, Johnson/Desc/ProofFile/Honest/Walk.lean) OF THE PROOF FILE's
DESCRIPTION: NO FUNCTION front IS LEFT AS A LETTER. LEMMAS; NONE OF THE LIBRARY's GOALS. Nothing on
completeness, soundness or hiding. An assembly: no new argument.

The description: `descAt Z A₂ B₂ c`: the term that an opening (IM.Open, Johnson/IMR/SeatOpen.lean)
says the proof file's description is. Its first chain is c, its first state ProofFile.startS Z, by its
make. The law is that of Johnson/Desc/K8/Honest/ChanceOfCounts.lean: ι a finite type of rounds, A i
round i's challenges, the list f : ∀ i, A i uniform. j: the batching's round. el: the field element
that round j's challenge gives, at most w challenges to one element. shows: the challenges of the
three chains that a list shows.
  `batch_round`   in the goals' scope the seated batching block of each of the 25 segments has one
      round
  **`fall_at_run`**   in the goals' scope, at every segment l < 25, K := 14 l + 9, or 347 at the
      head's; at every book, prover, input and coins; if (hj) round j's challenge is shown at or
      behind the batching's round of the first chain, (hshow) that round shows round j's element in
      reduced words, (bound) d bounds the exponents at whatever the state in front of the batching
      holds along a run: the chance, over the list, that the run returns, that its verifier comes to
      stand in front of the member behind the batching, and that `selfUnits` says no at the state
      there, is at most nU[2] * d * w / (the number of round j's challenges)
By: `fall_chance_agree` at `frontAt`; `frontAt_agree`, `frontAt_reach`
(Johnson/Desc/ProofFile/Honest/K8/FrontsAgree.lean); `quiet_in_event` (FrontsStep.lean); IM.k9_of,
IM.alone_rounds.
Limits. (bound) is a premise: d is tied to no number of the plan. By number, not by place: the event
speaks of entry K + 1 of `frontsOf`. (hj) and (hshow) are premises on shows. The law is named, not
derived (the test of work; that a random oracle's answers along a run are such a list). One segment,
and one of the tests that the member behind the batching makes. No number is evaluated. That a run
returns is not said.
-/
import Johnson.P1K8R.FallChanceAgree
import Johnson.Desc.ProofFile.Honest.K8.FrontsStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Tie.Pv.Tail.Port (topOf)
open ProofFile.Honest (ProverCoinCounts Prover Coins Draws RunC runC frontsOf)
open ProofFile.Honest.K8 (frontAt rnds)
open scoped ENNReal

/-- The term that an opening says the proof file's description is. -/
def descAt (Z : ProofFile.Pub) (A₂ : ProofFile.SharedSeat) (B₂ : ProofFile.SecondSeat) (c : Chain S Claim) :
    FileDescription ProofFile.Inst :=
  ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A₂ B₂ (fun s => s) (ProofFile.startS Z) c

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

theorem desc_is (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) :
    F = descAt Z A₂ B₂ c := O.desc

/-- The seated batching block has one round. -/
theorem batch_round (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25)
    (b : Block S Claim) (hb : c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b) :
    b.rounds.length = 1 := by
  obtain ⟨Lk', p', w, T, e1', -, -, -, -, -, hbL, -⟩ := (IM.k9_of hS hR O).2 l hl
  have key : ∀ Lk : Link S Claim, c.links[l]? = some Lk →
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? =
        some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) → b.rounds.length = 1 := by
    intro Lk e1 hflat
    obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
    obtain rfl := Option.some.inj (hflat.symm.trans hb)
    rw [IM.alone_rounds (hbL _)]
    rfl
  by_cases h24 : l = 24
  · subst h24
    obtain ⟨Lk, p, X, e1, -, -, hflat, -⟩ := fall_at_reached_head hS hR O
    exact key Lk e1 hflat
  · rw [if_neg h24] at key
    by_cases he : l % 2 = 0
    · obtain ⟨Lk, p, X, e1, -, -, hflat, -⟩ := fall_at_reached hS hR O hl
        (by unfold IM.subAt; rw [if_neg h24, if_pos he])
      exact key Lk e1 hflat
    · obtain ⟨Lk, p, X, e1, -, -, hflat, -⟩ := fall_at_reached_att hS hR O hl
        (by unfold IM.subAt; rw [if_neg h24, if_neg he])
      exact key Lk e1 hflat

/-- **The chance at the honest side's own run.** -/
theorem fall_at_run (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25)
    {W₀ Rc Ky Tr X₀ X' : Type} (Bk : ProverCoinCounts) (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X') (w₀ : W₀)
    (rc : Rc) (x : ProofFile.Inst) (k : Coins Bk)
    {ι : Type} [Fintype ι] [DecidableEq ι] {A : ι → Type} [∀ i, Fintype (A i)]
    [∀ i, Nonempty (A i)] (j : ι) (el : A j → Cb.Gl.E) (w : ℕ)
    (hw : ∀ y, Prob.cnt (fun a => el a = y) ≤ w) (shows : (∀ i, A i) → Draws)
    (hj : ∀ f a, (shows (Function.update f j a)).first.take
        (rnds (c.blocksInOrder.take (14 * l + (if l = 24 then 11 else 9)))) =
      (shows f).first.take (rnds (c.blocksInOrder.take (14 * l + (if l = 24 then 11 else 9)))))
    (hshow : ∀ f dr, (shows f).first[rnds (c.blocksInOrder.take (14 * l + (if l = 24 then 11 else 9)))]? =
      some dr → dr.elems = [Slice.ofE (el (f j))]) (d : ℕ)
    (hbound : ∀ f (zs : ProofFile.InstPub × S),
      frontAt (descAt Z A₂ B₂ c) Bk H w₀ rc x k (14 * l + (if l = 24 then 11 else 9)) (shows f) =
        some zs →
      ∀ tl F' funs, zs.2.tl? = some tl → zs.2.fork? = some F' → zs.2.funs? = some funs →
        F'.planClaimsF + topOf tl funs ≤ d + 1) :
    ∃ (p : K9.Where) (X : LinkH), IM.k9At Z l = some p ∧ Bs.G₀.built.toList[l]? = some X ∧
      Prob.pr (Prob.unif (∀ i, A i)) {f | ∃ (r : RunC (descAt Z A₂ B₂ c))
          (e' : Place × S × List Fmt.Drawn),
          runC (descAt Z A₂ B₂ c) Bk H w₀ rc x k (shows f) = .ok r ∧
          (frontsOf 0 c.blocksInOrder (ProofFile.startS Z x.pub) (withEmptySealRound r.run.views.1).rounds
            (withEmptySealRound r.run.views.1).opened)[14 * l + (if l = 24 then 11 else 9) + 1]? =
              some e' ∧
          zeroUnitAt (ProofFile.k8NU Bs.G₀ X) e'.2.1 = true} ≤
        (((ProofFile.k8NU Bs.G₀ X).getD 2 0 * d * w : ℕ) : ℝ≥0∞) / Fintype.card (A j) := by
  obtain ⟨b, p, X, hb, hp, hX, hall⟩ := fall_chance_agree hS hR O hl
  have h1 := batch_round hS hR O hl b hb
  refine ⟨p, X, hp, hX, ?_⟩
  have hbD : (descAt Z A₂ B₂ c).first.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b := hb
  refine (Prob.pr_mono _ fun f hf => ?_).trans (hall j el w hw
    (fun f => frontAt (descAt Z A₂ B₂ c) Bk H w₀ rc x k (14 * l + (if l = 24 then 11 else 9))
      (shows f))
    (ProofFile.Honest.K8.frontAt_agree j shows hbD (by rw [h1]; exact Nat.one_pos) hj)
    (fun f zs hz => ProofFile.Honest.K8.frontAt_reach hz) d hbound)
  obtain ⟨r, e', hr, he', hz⟩ := hf
  obtain ⟨zs, r₀, cols, m, g1, g2, g3⟩ := ProofFile.Honest.K8.quiet_in_event hr hbD h1 he'
  exact ⟨zs, g1, r₀, cols, e'.2.1, m, hshow f _ g2, g3, hz⟩

end

end P1K8

#print axioms P1K8.batch_round
#print axioms P1K8.fall_at_run
#print axioms P1K8.descAt
#print axioms P1K8.desc_is
