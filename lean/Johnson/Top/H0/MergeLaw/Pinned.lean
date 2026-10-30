-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/Pinned.lean: two strengthenings of the merge's law: the witnesses of
`claim_says` pinned to the rounds, and the three first tests of `mergeHear` as conjuncts. Theorems
with their proofs.

Main names:
  `hear_tests`: where `mergeHear` says yes: there is a claim, at most 4096, as many slots as claims;
    each claim's unit is in the layout; each claim's factors fit its unit (`claimFits`).
  `claim_says_pinned`: `claim_says` (Johnson/Top/H0/MergeLaw/Says.lean) with four witnesses more
    (the batching element x; the word "rows" of the plan's entry of each of three rounds: r1, rY,
    rV) and one conjunct more: the tape that the merge's maker makes of the rounds IS the tape of
    x, mu, the sumcheck's eps, the rounds qs, c with beta, and v. So the typed output on the right
    side can be held against the rounds.

Limits: those of Says.lean. `merge_plain` and `merge_closed` (Plain.lean, Closed.lean) go by
`decide_view`, which has the pins already; this file is for whoever spends `claim_says`. Nothing on
soundness or on hiding.

-/
import Johnson.Top.H0.MergeLaw.Says

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open Iop Cb Cb.Pv.Lay
open OnBytes (E addE mulE zeroE)
open OnBytes.K.Kc (Tape flatOf)
open OnBytes.Model (Reading World Fork WsLay WsClaim WsForkOut wsForkStart)
open OnBytes.Model.Road (Sized)
open OnBytes.Tie.Pv.Lay.Eng (SumSaid sumOut)
open VerifiableInference.Desc (Claim need named)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide headMergeClaim mergeTapeE mergeHear
  mergeEntries claimFits)

/-- The three first tests of what is heard. -/
theorem hear_tests {lay : WsLay} {cl : Array WsClaim} {sv : Array Nat} {F F' : Fork} {t t' : Tape}
    {wo : WsForkOut} (h : mergeHear lay cl sv F t = .ok (wo, F', t')) :
    (!cl.isEmpty && cl.size ≤ 4096 && sv.size == cl.size) = true ∧
      (cl.all fun c => c.ui < lay.U.size) = true ∧ (cl.all fun c => claimFits lay c) = true := by
  unfold mergeHear at h
  obtain ⟨_, a1, k1⟩ := ebind_inv h
  obtain ⟨_, a2, k2⟩ := ebind_inv k1
  obtain ⟨_, a3, _⟩ := ebind_inv k2
  exact ⟨need_ok a1, need_ok a2, need_ok a3⟩

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

/-- **What the merge's claim says, its witnesses pinned to the rounds.** -/
theorem claim_says_pinned (P : HeadMergeP) (L : MergeL K) (hk : L.k = P.lay.lk) {s s' : S}
    {rs : List Fmt.RoundView} (h : headMergeDecide P s rs = .ok s') (st : L.St) :
    ∃ (a a' : HeadOwn) (wo : WsForkOut) (x mu c beta v : E) (r1 rY rV : Nat)
      (qs : List (Nat × List E × E)),
      s.here = .head a ∧ s'.here = .head a' ∧ a'.wo = some wo ∧ wo.beta = beta ∧
      mergeTapeE rs (mergeEntries P.lay.lk 1 P.work) = .ok
        (⟨some OnBytes.Model.RoundName.batSigma.name, 0, 1, [], [x]⟩ ::
          ⟨some OnBytes.Model.RoundName.pscEpsilon.name, 0, r1, [mu], [wo.p.eps]⟩ ::
          (qs.map (rd OnBytes.Model.RoundName.pscRound.name 0) ++
            [⟨some OnBytes.Model.RoundName.pscY.name, 1, rY, [c], [beta]⟩,
              ⟨some OnBytes.Model.RoundName.pscValues.name, 0, rV, [v], []⟩])) ∧
      ∀ (_ : Sized a.F) (hβ : ρ.val beta ≠ 0) (n : Nat) (s₂ s₃ : S) (a₂ : HeadOwn)
        (cls : List Claim),
        s₂.here = .head a₂ → a₂.wo = a'.wo → headMergeClaim n s₂ = .ok (cls, s₃) →
        ∃ form, cls = [{ form := form }] ∧
          ∀ (Ex : ExtSpec) (_ : Ex.Str) (W : World K) (m : L.J → K),
            L.toSum.T.par.W st m = OnBytes.Road.Hd.place W.slot (L.toSum.T.par.vars st) wo.p.first →
            L.toSum.T.par.inc st m = ρ.val wo.p.target - wo.p.start.value ρ W →
            (form.value ρ W = 0 ↔
              L.toSum.T.par.UHolds (sumOut ρ L.toSum (fun st => pick (L.toSum.T.par.vars st)) st
                wo.p.target mu wo.p.eps (qs.map fun q => (q.2.1, q.2.2)) [c] beta hβ
                fun _ => ρ.val v) m) := by
  obtain ⟨a, a', tp, G, claim, x0, wo, ha, ha', _, _, hwo', ht, hm, _⟩ := decide_inv h
  obtain ⟨x, mu, c, beta, v, T, r1, rY, rV, qs, et, _, _, _, hbeta, hhide, hshown, H⟩ :=
    hear_tie ρ L hk hm st
  refine ⟨a, a', wo, x, mu, c, beta, v, r1, rY, rV, qs, ha, ha', hwo', hbeta, ?_, ?_⟩
  · rw [ht, et]
    rfl
  intro hz hβ n s₂ s₃ a₂ cls h₂ hwo hrun
  obtain ⟨b, wo₂, _, hb, hbwo, _, hcls, _⟩ := claim_inv hrun
  have hab : b = a₂ := by
    rw [h₂] at hb
    exact (Here.head.inj hb).symm
  subst hab
  have hfv : wo.fvp = v := fvp_sized hhide hshown hz
  have hw2 : wo₂ = wo := by
    rw [hwo, hwo'] at hbwo
    exact (Option.some.inj hbwo).symm
  refine ⟨_, hcls, ?_⟩
  rw [hw2, hfv]
  exact (H hβ).2.1

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.hear_tests
#print axioms VerifiableInference.Desc.First.MergeLaw.claim_says_pinned
