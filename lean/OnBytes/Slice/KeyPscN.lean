-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/KeyPscN.lean: the written zero-knowledge sumcheck without a shown map, as a step, with
its soundness.

OnBytes/Slice/KeyPsc.lean has the sumcheck whose summand shows the value of some map: it has a round
of one more variable Y and a round of the shown values. If the summand shows no map, these two
rounds are missing (OnBytes/Iop/Psc.lean: hear), and the run hands on its row alone. This file has
that case: the step (pscStepN) and its soundness (psc_sem_n). The next state and the test are those
of OnBytes/Slice/KeyPscRun.lean, as in the other case.

The proof is our own, like that of the other case, and has the same argument. The error counts: 1 in
the first round, and d - 1 in the round of a variable whose polynomials have d coefficients, each
times the number in the law of the format's sampler.

Main definitions: heardN, pscErrN, pscStepN, PscSideN.

Main theorems: rounds_doomed_end, psc_sem_n.

Not claimed. What OnBytes/Slice/KeyPsc.lean does not claim. That a summand has a tower.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.KeyPsc

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb _root_.Run

/-- The rounds of a list of variables are taken off, with no rounds behind. T is a tower over
the weights ws. R, the running claim, is not the tower's sum. Then the prover has lost before the
rounds ds towards any goal that holds where a test of work fails, where a number of sent
coefficients does not fit, and where the running claim after the rounds is not the tower's value at
the challenges. -/
theorem rounds_doomed_end : ∀ (ws : List PscF.Weight) (ds : List PQ.RD), ws.length = ds.length →
    (∀ w ∈ ws, w.OK) → (∀ d ∈ ds, OneEl d) → ∀ T : List GE → GE, PscF.Tower ws T →
    ∀ R : GE, R ≠ T [] → ∀ bad : Tr (uW ds) → Prop, (∀ a, ¬ passT ds a → bad a) →
    (∀ a, ¬ Lens ws (heardR ds a) → bad a) →
    (∀ a, PscF.claimAfter ws (heardR ds a) R ≠ T ((heardR ds a).map (·.2)) → bad a) →
    Doomed (uW ds) (errR (ws.map (·.d)) ds) bad
  | [], [], _, _, _, _, _, _, hR, _, _, _, H => H () hR
  | w :: ws, d :: ds, hlen, hw, hd, T, hT, R, hR, bad, hp, hl, H => by
    have hw0 := hw w List.mem_cons_self
    have hd0 := hd d List.mem_cons_self
    show Doomed (wRound d :: uW ds)
      ((w.d - 1) * (bsRound .two d.entry d.kind).w, errR (ws.map (·.d)) ds) bad
    refine draw_cnt d (gOne _) hd0.inj hd0.logN (uW ds) _ (w.d - 1)
      (fun m x => (ansOf d m).length + 1 = w.d ∧
        PscF.polyAt (w.complete (ansOf d m) R) x = T [x]) (fun m => ?_) bad (fun m c a hc => ?_)
      fun m c hB => ?_
    · by_cases hs : (ansOf d m).length + 1 = w.d
      · exact le_trans (cnt_mono fun x hx => hx.2) (PscF.Tower.round_cnt hw0 hT hR _ hs)
      · rw [cnt_false fun x hx => hs hx.1]
        exact Nat.zero_le _
    · refine hp (m, c, a) fun h => ?_
      rw [((passT_cons d ds m c a).1 h).1] at hc
      cases hc
    · by_cases hs : (ansOf d m).length + 1 = w.d
      · exact rounds_doomed_end ws ds (Nat.succ.inj hlen)
          (fun v hv => hw v (List.mem_cons_of_mem _ hv))
          (fun v hv => hd v (List.mem_cons_of_mem _ hv))
          (fun p => T (gOne _ (valsOf d c) :: p)) (hT.2 _)
          (PscF.polyAt (w.complete (ansOf d m) R) (gOne _ (valsOf d c)))
          (fun h => hB ⟨hs, h⟩) (fun a => bad (m, c, a))
          (fun a h => hp (m, c, a) fun h' => h ((passT_cons d ds m c a).1 h').2)
          (fun a h => hl (m, c, a) fun h' => h ((lens_cons w ws _ _).1 h').2)
          fun a h1 => H (m, c, a) h1
      · exact doomed_of_all _ _ _ fun a =>
          hl (m, c, a) fun h' => hs ((lens_cons w ws _ _).1 h').1

section
variable (dEps : PQ.RD) (dXs : List PQ.RD)

/-- What is heard in the rounds: no shown values. -/
def heardN (τ : Tr (uW (dEps :: dXs))) : PscF.Heard where
  mu := (ansOf dEps τ.1).headD 0
  eps := gOne _ (valsOf dEps τ.2.1)
  rounds := heardR dXs τ.2.2
  values := []

/-- The error counts. dd: for each variable the number of coefficients of a round's polynomial. -/
def pscErrN (dd : List ℕ) : Err (uW (dEps :: dXs)) :=
  (1 * (bsRound .two dEps.entry dEps.kind).w, errR dd dXs)

variable {X : Type} (cl : X → PscF.Claim) (S : X → PscF.Summand) (fr : X → List Slot)

/-- The written sumcheck without a shown map, as a step. -/
def pscStepN (dd : List ℕ) : Step X (X × PscF.Out) where
  rds := dEps :: dXs
  err := pscErrN dEps dXs dd
  ok x τ := PscF.tests (cl x) (S x) (fr x) (heardN dEps dXs τ) = true
  nx x τ := (x, PscF.outOf (cl x) (S x) (fr x) (heardN dEps dXs τ))

/-- What is asked of the states: the claim's variables are as many as their rounds, their
polynomials have the listed numbers of coefficients, their weights meet Weight.OK; the summand shows
no map. -/
structure PscSideN (dd : List ℕ) (x : X) : Prop where
  len : (cl x).vars.length = dXs.length
  dims : (cl x).vars.map (·.d) = dd
  ok : ∀ w ∈ (cl x).vars, w.OK
  shown : (S x).shown = 0

end

/-- Soundness of the written sumcheck without a shown map. The letters are those of psc_sem. -/
theorem psc_sem_n (dEps : PQ.RD) (dXs : List PQ.RD) {X : Type} (cl : X → PscF.Claim)
    (S : X → PscF.Summand) (fr : X → List Slot) (dd : List ℕ) (hE : OneEl dEps)
    (hX : ∀ d ∈ dXs, OneEl d) (F : X → Prop) (hside : ∀ x, F x → PscSideN dXs cl S dd x)
    (W : PscF.World) (V Kp : X → ℕ → List GE → GE) (T : X → List GE → GE)
    (hT' : ∀ x, F x → PscF.Sums W (V x) (Kp x) (cl x) (S x) (fr x) (T x)) :
    (pscStepN dEps dXs cl S fr dd).Sem
      (fun x => F x → T x [] + W.form (cl x).masks = (cl x).target)
      fun p => p.2.Holds W (V p.1) (Kp p.1) (S p.1).kept := by
  intro x hx0
  obtain ⟨hF, hx⟩ := Classical.not_imp.1 hx0
  have hs := hside x hF
  have hT : PscF.Sums W (V x) (Kp x) (cl x) (S x) (fr x) (T x) := hT' x hF
  have hvars : PscF.varsOf (cl x) (S x) = (cl x).vars := by
    unfold PscF.varsOf
    rw [if_pos (by simp [hs.shown])]
  have hwAll : ∀ w ∈ PscF.varsOf (cl x) (S x), w.OK := by
    rw [hvars]
    exact hs.ok
  have htow : ∀ ε, PscF.Tower (cl x).vars (PscF.whole W (cl x) (S x) (fr x) (T x) ε) := by
    intro ε
    rw [← hvars]
    exact PscF.Tower.add (PscF.tower_hideT _ _ hwAll) (PscF.Tower.smul ε
      (PscF.Tower.add hT.tower (PscF.Tower.smul _ (PscF.tower_psiT _ hwAll))))
  show Doomed (wRound dEps :: uW dXs) (pscErrN dEps dXs dd) _
  refine draw_cnt dEps (gOne _) hE.inj hE.logN (uW dXs) _ 1
    (fun m ε => (ansOf dEps m).headD 0 + ε * (cl x).target =
      PscF.whole W (cl x) (S x) (fr x) (T x) ε []) (fun m => ?_) _ (fun m c τ hc hp => ?_)
    fun m c hB => ?_
  · refine cnt_le_one fun ε ε' h1 h2 => ?_
    unfold PscF.whole at h1 h2
    rw [PscF.psiT_nil, mul_one] at h1 h2
    have h3 : (ε - ε') * ((cl x).target - (T x [] + W.form (cl x).masks)) = 0 := by
      linear_combination h1 - h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact sub_eq_zero.1 h4
    · exact absurd (sub_eq_zero.1 h4).symm hx
  · rw [((passT_cons dEps _ m c τ).1 hp).1] at hc
    cases hc
  · rw [← hs.dims]
    refine rounds_doomed_end (cl x).vars dXs hs.len hs.ok hX _ (htow _) _ hB _
      (fun a h hp => ?_) (fun a h _ ht => ?_) fun a h1 _ ht ho => h1 ?_
    · exact absurd ((passT_cons dEps _ m c _).1 hp).2 h
    · have h2 := tests_lens ht
      rw [hvars] at h2
      exact absurd h2 h
    · have h3 := PscF.run_end W (V x) (Kp x) (cl x) (S x) (fr x) _ ht hwAll (T x) hT ho
      rw [hvars] at h3
      exact h3

end OnBytes.Slice
