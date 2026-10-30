-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/ProgramRPol.lean: the relation for a stretch of a reply under an acceptance policy,
without `Head3` (the request is well-formed). Definitions, and its corner cases spelt out.
Inst/Model/ProgramR.lean has `RinfR` := the program runs ∧ `Head3` (the request is well-formed:
r < e ≤ T; y = 0 if e < T) ∧ `PolOK` (the policy's clauses (a), (b), (c)). `Head3` is a public check
on the instance; no field relation of a segment (Inst/Model/FF/Trace.lean,
Inst/Model/Att/Trace.lean; the head's: Policy/Rel/LedgerHead.lean) says anything about it.
    `AcceptancePolicy.OK`, `AcceptancePolicy.exact_ok`  bounds on the policy's numbers under which nothing wraps around
                            and the honest numbers fit their bytes: C, θ < 2^40, cap < 2^16; exact
                            match meets them. Wider than what the implementation's verifier admits:
                            every admitted policy is covered; that verifier admits θ ≤ C, cap ≤ T,
                            numbers below 2^32, by a reading of docs/format/FORMAT.md, "12.5 The
                            acceptance policy", and docs/format/08-parameters.md, "8.6 The model's
                            lines", and of its source, and no theorem; in Lean:
                            `PolTests` (Inst/Model/ProgTests.lean), and the clause `pol` of valid
                            settings (`Lawful`, Inst/Model/Scales.lean); what Lean shows is that the
                            policy of all valid settings has `AcceptancePolicy.OK` (`LawfulBut.polOK`,
                            `Lawful.polOK` there).
    `ModelR`, `RinfR0`        the program runs, and the policy's three clauses hold. (Clause (c) has
                            the premise r < e in its own text: without a covered position nothing is
                            tested at position T − 1.)
    `RinfR_iff0`              `RinfR` ↔ `Head3` ∧ `RinfR0`
    `PolOK.congr`             if 0 < T, the policy's clauses read the logits at positions below T
                            only
    `polOK_of_le`             corner case 1: without a covered position (e ≤ r) the policy holds,
                            whatever the logits: `RinfR0` then says "the program runs" and nothing
                            else
    `polOK_y_unread`          corner case 2: for e < T the policy does not read y: `RinfR0` is then
                            true or false whatever y is. (`Head3` excludes the first and requires
                            y = 0 in the second; neither is excluded by `RinfR0`.)
    `RinfR_written_out`       `RinfR` written out: runs ∧ `Head3` ∧ (a) ∧ (b) ∧ (e = T → the gap of
                            y at T − 1 is 0)
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Inst.Model.ProgramR

set_option autoImplicit false

namespace Inst.Model

/-- bounds on the policy's numbers: C below 2^40 (c and k, which add up to C, have five bytes), θ
below 2^40, cap below 2^16 (z, which fills up to cap, has two bytes). c, k, z: `hidC`, `hidK`,
`hidZ` (Inst/Model/Head/Trace.lean). -/
structure AcceptancePolicy.OK (pol : AcceptancePolicy) : Prop where
  C : pol.C < 2 ^ 40
  theta : pol.theta < 2 ^ 40
  cap : pol.cap < 2 ^ 16

theorem AcceptancePolicy.exact_ok : AcceptancePolicy.exact.OK :=
  ⟨by norm_num [AcceptancePolicy.exact], by norm_num [AcceptancePolicy.exact], by norm_num [AcceptancePolicy.exact]⟩

/-- the program runs, and the policy holds -/
def ModelR (P : Params) (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables) (pol : AcceptancePolicy)
    (w : Weights) (x : Instance P) : Prop :=
  RunsK P κ nf tbs w x.prompt ∧ PolOK (lgK P κ nf tbs w x.prompt) pol x

def RinfR0 (P : Params) (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables) (pol : AcceptancePolicy)
    (i : Index P) (x : Instance P) : Prop :=
  ModelR P κ nf tbs pol i.val x

theorem RinfR_iff0 (P : Params) (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables) (pol : AcceptancePolicy)
    (i : Index P) (x : Instance P) :
    RinfR P κ nf tbs pol i x ↔ Head3 x ∧ RinfR0 P κ nf tbs pol i x :=
  ⟨fun h => ⟨h.2.1, h.1, h.2.2⟩, fun h => ⟨h.2.1, h.1, h.2.2⟩⟩

/-- If 0 < T: the policy's clauses read the logits at positions below T only. -/
theorem PolOK.congr {P : Params} {lg lg' : ℕ → ℕ → ℤ} {pol : AcceptancePolicy} {x : Instance P} (hT : 0 < P.T)
    (hl : ∀ t < P.T, lg t = lg' t) (h : PolOK lg pol x) : PolOK lg' pol x := by
  have hc : ∀ t ∈ x.cnt, costOf lg' x t = costOf lg x t := fun t ht => by
    have h1 := Finset.mem_Ico.1 ht
    unfold costOf
    rw [hl t (by omega)]
  refine ⟨?_, ?_, fun hre he => ?_⟩
  · rw [Finset.sum_congr rfl fun t ht => by rw [hc t ht]]
    exact h.a
  · rw [Finset.filter_congr fun t ht => by rw [hc t ht]]
    exact h.b
  · rw [← hl (P.T - 1) (by omega)]
    exact h.c hre he

/-- without a covered position the policy holds -/
theorem polOK_of_le {P : Params} (lg : ℕ → ℕ → ℤ) (pol : AcceptancePolicy) {x : Instance P} (h : x.e ≤ x.r) :
    PolOK lg pol x := by
  have hc : x.cnt = ∅ := Finset.Ico_eq_empty (by omega)
  have hN : x.NB = 0 := by rw [← x.card_cnt, hc]; rfl
  refine ⟨?_, ?_, fun hre => absurd hre (by omega)⟩
  · rw [hc, hN]; simp
  · rw [hc]; simp

/-- for e < T the policy does not read the announced token -/
theorem polOK_y_unread {P : Params} (lg : ℕ → ℕ → ℤ) (pol : AcceptancePolicy) (x : Instance P) (y' : Fin P.V)
    (he : x.e < P.T) (h : PolOK lg pol x) :
    PolOK lg pol { x with y := y' } := by
  have hw : ∀ t ∈ x.cnt, ({ x with y := y' } : Instance P).w t = x.w t := fun t ht => by
    have h1 := Finset.mem_Ico.1 ht
    unfold Instance.w Instance.tok
    rw [dif_pos (by omega), dif_pos (by omega)]
  have hc : ∀ t ∈ x.cnt, costOf lg ({ x with y := y' } : Instance P) t = costOf lg x t :=
    fun t ht => by unfold costOf; rw [hw t ht]
  refine ⟨?_, ?_, fun _ (e : x.e = P.T) => absurd e (by omega)⟩
  · show ∑ t ∈ x.cnt, min (costOf lg ({ x with y := y' } : Instance P) t) pol.C ≤ pol.theta * x.NB
    rw [Finset.sum_congr rfl fun t ht => by rw [hc t ht]]
    exact h.a
  · show (x.cnt.filter fun t => (pol.C : ℤ) < costOf lg ({ x with y := y' } : Instance P) t).card ≤
      pol.cap
    rw [Finset.filter_congr fun t ht => by rw [hc t ht]]
    exact h.b

/-- the relation with `Head3`, written out: the premise r < e inside (c) changes nothing in it -/
theorem RinfR_written_out (P : Params) (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables)
    (pol : AcceptancePolicy) (i : Index P) (x : Instance P) :
    RinfR P κ nf tbs pol i x ↔
    RunsK P κ nf tbs i.val x.prompt ∧
    Head3 x ∧
    (∑ t ∈ x.cnt, min (costOf (lgK P κ nf tbs i.val x.prompt) x t) pol.C ≤ pol.theta * x.NB) ∧
    ((x.cnt.filter fun t => (pol.C : ℤ) < costOf (lgK P κ nf tbs i.val x.prompt) x t).card ≤
      pol.cap) ∧
    (x.e = P.T → gapOf P.V (lgK P κ nf tbs i.val x.prompt (P.T - 1)) x.y.val = 0) :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2.a, h.2.2.b, h.2.2.c h.2.1.1⟩,
    fun h => ⟨h.1, h.2.1, ⟨h.2.2.1, h.2.2.2.1, fun _ => h.2.2.2.2⟩⟩⟩

end Inst.Model
