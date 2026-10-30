-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/StateFirstPriv.lean: the step that expands a long answer of a random oracle from a state
(Rom/StateFirst.lean), index privacy, part 5: index privacy carries over from A to
`stateFirstArg C A`, given `Spec.mixClose`. (not all hypotheses are named here: see
`privacy_stateFirst`)

Chain oracles, states, dr: `Link`, `stSpec` (Rom/StateFirst.lean); mixed programs, `real`, `ideal`,
`Book`: Rom/StateFirstMix.lean; the mixed experiment: `mixExp` (Rom/StateFirstPrivMix.lean); the
reduction, the replay: `downVSt`, `replaySt`, `stWorld` (Rom/StateFirstPrivReplay.lean),
`replayViewSt` (Rom/StateFirstPrivIdeal.lean); `consistent_replaySt` (Rom/StateFirstPrivCons.lean);
worlds: `GWorld`, `simWorld` (Rom/ExitPriv.lean); index privacy: `HasIndexPrivacyWith`
(ZKCP/Gen.lean).

`privacy_stateFirst`: if `Spec.mixClose` holds (a hypothesis of this theorem: Rom/StateFirstMix.lean
states it; Rom/StateFirstClose.lean proves it; it is not proved in this file), the scheme's
committer and prover (`A.C`, `A.P`) make at most nC and nP queries at chain oracles (P on batches of
at most B), the three algorithms do not read hid, the last block of a chain answer (`HidFree`), and
A has index privacy with Sim and ζ, then `stateFirstArg C A` has index privacy with `simSt C Sim`
and ζ t N + (t + h)² / 2^(2 lam) + t h / 2^lam, where h = nC + N nP. The budget in ζ does not
change: the reduction makes at most one query for each query of the adversary.

The proof. The real experiment over the second family is the real interpretation of the mixed
experiment (`real_mixExp`). That is close to the reduction's interpretation (`Spec.mixClose`, both
directions by complements), which has the distribution of the real experiment over the first family
with the reduction, after the replay (`Pr_ideal_mixExp`). That is ζ-close to the ideal experiment
with Sim after the replay (the hypothesis on A; images do not increase the distance), which is the
ideal experiment with `simSt C Sim` (`idealExp_simSt`, by `simWorld_simSt`: the world of the
simulator `simSt C Sim` is the world of Sim seen through the second family, `stWorld`). The second
half of index privacy (the simulator never answers a repeated query differently) comes from Sim's
own second half, applied to the reduction, and `consistent_replaySt`.

Notation:
  the first family, the second family: S, and `stSpec S lam C` (Rom/StateFirst.lean)
  chain oracle: an oracle o with `C o` of the form `Link.chain K e` (Rom/StateFirst.lean); the other
      oracles are unchanged (`Link.plain`)
  dr: the added oracle of the second family: `.inr ()` of `stSpec S lam C` (Rom/StateFirst.lean); a
      query to it is an expansion query (state, counter), of type `(Dg lam × Dg lam) × ℕ`; an answer
      is a hash block
  mixed program: an `OComp (mixSpec C) α` (Rom/StateFirstMix.lean): typed and raw queries; `.inl o`:
      a typed query, to the first family; `.inr (.inl o)`, `.inr (.inr ())`: raw queries, to the
      second family (the last to dr)
  `lam`: a natural number: a hash block has `lam` bits (`Dg lam`, Rom/NeedA.lean)
  B, ζ: in `HasIndexPrivacyWith R A B Sim ζ` (ZKCP/Gen.lean): a natural number B and a function ζ of
      two natural numbers
  t, N: natural numbers, the arguments of ζ; in `PrivacyFor` (ZKCP/Gen.lean) `ζ tV N`, with
      `(Vt ivk).QueryBound tV` (`AdvVerifier.QueryBound`, the same file; t is its tV); N counts
      batches
  `GWorld` (Rom/ExitPriv.lean): the challenger of an adversarial verifier: it answers oracle queries
      and serves batches

Limits: `Spec.mixClose` is assumed here, not proved (index privacy without this hypothesis:
Rom/StateFirstTop.lean). Completeness and index binding are not treated here. Nothing on one hash
function f.
-/
import Rom.StateFirstPrivCons

set_option autoImplicit false

open scoped ENNReal

namespace Rom
open ZKCP

variable {S : OSpec} {lam : ℕ} (C : ∀ o, Link lam (S.Rng o)) {I X W PP IVK ISK Pf : Type}

/-! ## The challenger made of the simulator -/

theorem ansInl_eq {T : Type} (ans : T → (o : S.ι) → S.Dom o → PMF (S.Rng o × T))
    (st : SimSt S lam T) (o : S.ι) (q : S.Dom o) :
    ansInl ans st o q (C o) = match st.book.kept C o q with
      | some r => PMF.pure ((C o).toAns r, st)
      | none =>
          (ans st.s o q).map fun out =>
              ((C o).toAns out.1, (st.book.note C o q out.1).withS out.2) := by
  unfold Book.kept Book.note
  generalize C o = c
  cases c with
  | plain => simp [ansInl, Link.isPlain, Link.toAns, SimSt.book, Book.withS]
  | chain K e =>
    cases hf : findMade st.made o q with
    | some r => simp [ansInl, Link.isPlain, Link.toAns, SimSt.book, hf]
    | none => simp [ansInl, Link.isPlain, Link.toAns, SimSt.book, Book.withS, hf]

theorem GWorld.mk_congr {σ : Type} {a a' : σ → (o : S.ι) → S.Dom o → PMF (S.Rng o × σ)}
    {s s' : σ → Gen.Batch X W → PMF (List (X × Pf) × σ)} (ha : a = a') (hs : s = s') :
    (⟨σ, a, s⟩ : GWorld S X W Pf) = ⟨σ, a', s'⟩ := by
  subst ha hs
  rfl

theorem simWorld_simSt (Sim : Gen.Simulator S PP IVK X Pf) :
    (simWorld (simSt C Sim) : GWorld (stSpec S lam C) X W Pf) = stWorld C (simWorld Sim) := by
  refine GWorld.mk_congr (σ := SimSt S lam Sim.St)
    (funext fun st => funext fun x => ?_) (funext fun st => funext fun b => ?_)
  · cases x with
    | inl o => exact funext fun q => ansInl_eq C Sim.answer st o q
    | inr u => rfl
  · show ((Sim.prove st.s b.ownX).map _).map _ = ((Sim.prove st.s b.ownX).map _).map _
    rw [PMF.map_comp, PMF.map_comp]
    rfl

/-- The ideal experiment with `simSt C Sim` is the image, under the replay, of the ideal experiment
with Sim, run with the reduction and with the environment applied to the replayed log. An equality
of distributions. -/
theorem idealExp_simSt (R : Gen.RelPair I X W PP) (Sim : Gen.Simulator S PP IVK X Pf)
    (Vt : IVK → Gen.AdvVerifier (stSpec S lam C) X Pf)
    (Z : Gen.ViewEnv (stSpec S lam C) IVK X W Pf) (i : I) (N : ℕ) :
    Gen.idealExp R (simSt C Sim) Vt Z i N =
      (Gen.idealExp R Sim (fun ivk => downVSt C (Vt ivk) ⟨[], []⟩)
          (fun v => Z (replayViewSt C Vt N v)) i N).map
        (replayViewSt C Vt N) := by
  have e1 : Gen.idealExp R (simSt C Sim) Vt Z i N =
      ((Sim.init (R.pp i) N).map fun out =>
        (out.1, (⟨out.2, [], []⟩ : SimSt S lam Sim.St))).bind fun out =>
      Gen.idealLoop (simSt C Sim) Z (Vt out.1) N
          ((Log.nil : Log (stSpec S lam C) X Pf).view out.1) out.2 := rfl
  have e2 : Gen.idealExp R Sim (fun ivk => downVSt C (Vt ivk) ⟨[], []⟩)
        (fun v => Z (replayViewSt C Vt N v)) i N =
      (Sim.init (R.pp i) N).bind fun out =>
        Gen.idealLoop Sim (fun v => Z (replayViewSt C Vt N v)) (downVSt C (Vt out.1) ⟨[], []⟩) N
            ((Log.nil : Log S X Pf).view out.1) out.2 := rfl
  rw [e1, e2, PMF.bind_map, PMF.map_bind]
  refine congrArg _ (funext fun out => ?_)
  simp only [Function.comp_def]
  rw [idealLoop_eq, idealLoop_eq, lLoop_congr (simWorld_simSt (W := W) C Sim)]
  have hl := loop_replaySt C (simWorld (W := W) Sim) (Vt out.1)
    (fun l => Z (Log.view out.1 l)) N ⟨[], []⟩ out.2
  refine (congrArg (PMF.map _) hl).trans ?_
  rw [PMF.map_comp, PMF.map_comp]
  rfl

/-! ## Index privacy -/

theorem Pr_add_compl {α : Type} (c : OComp S α) (E : Set α) :
    Pr c (fun _ => E) + Pr c (fun _ => Eᶜ) = 1 := by
  rw [Pr_eq_law, Pr_eq_law, Prob.pr_add_compl]

variable {C}

/-- As `privacy_stateFirst`, for any error term p nT nR that bounds, one-sidedly for every event,
the real against the reduction's interpretation of every mixed program under `MixBound` and
`HidFreeM` (hM): the privacy error is ζ t N + p (nC + N nP) t. -/
theorem privacy_stateFirst_of (p : ℕ → ℕ → ℝ≥0∞)
    (hM : ∀ (α : Type) (c : OComp (mixSpec C) α) (nT nR : ℕ), MixBound C c nT nR → HidFreeM C c →
      ∀ E : Set α, Pr (real C c) (fun _ => E) ≤
        Pr (ideal C false c ⟨[], []⟩) (fun _ => {x | x.1 ∈ E}) + p nT nR)
    (R : Gen.RelPair I X W PP) (A : Gen.Arg S I X W IVK ISK Pf) (B : ℕ)
    (Sim : Gen.Simulator S PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞) (nC nP : ℕ)
    (hC : ∀ i, (A.C i).CostBoundAt (wCh C) nC)
    (hP : ∀ k b, b.length ≤ B → (A.P k b).CostBoundAt (wCh C) nP) (hH : HidFree C A)
    (h : Gen.HasIndexPrivacyWith R A B Sim ζ) :
    Gen.HasIndexPrivacyWith R (stateFirstArg C A) B (simSt C Sim)
      (fun t N => ζ t N + p (nC + N * nP) t) := by
  intro i Z hZ tV Vt N hb
  obtain ⟨h1, h2⟩ := h i (fun v => Z (replayViewSt C Vt N v)) (fun v b hv => hZ _ b hv) tV
    (fun ivk => downVSt C (Vt ivk) ⟨[], []⟩) N
    fun ivk => queryBound_downVSt C (Vt ivk) _ tV (hb ivk)
  have hideal : ∀ T, Prob.pr (Gen.idealExp R (simSt C Sim) Vt Z i N) T =
      Prob.pr (Gen.idealExp R Sim (fun ivk => downVSt C (Vt ivk) ⟨[], []⟩)
          (fun v => Z (replayViewSt C Vt N v)) i N)
        (replayViewSt C Vt N ⁻¹' T) := by
    intro T
    rw [idealExp_simSt, Prob.pr_map]
  constructor
  · have hA : Prob.sd (fun T => Pr (Gen.realExp (stateFirstArg C A) Vt Z i N) (fun _ => T))
        (fun T =>
          Pr (Gen.realExp A (fun ivk => downVSt C (Vt ivk) ⟨[], []⟩)
              (fun v => Z (replayViewSt C Vt N v)) i N)
            (fun _ => replayViewSt C Vt N ⁻¹' T))
        ≤ p (nC + N * nP) tV := by
      refine Prob.sd_le_of_forall_le_add (fun E => Pr_add_compl _ E)
        (fun E => Pr_add_compl _ (replayViewSt C Vt N ⁻¹' E)) fun T => ?_
      have hm := hM _ (mixExp C A Vt Z i N) (nC + N * nP) tV
        (mixBound_mixExp C A Vt Z i N nC nP tV (hC i) (fun isk v b hv => hP isk _ (hZ v b hv).1) hb)
        (hidFreeM_mixExp C A hH Vt Z i N) T
      rw [real_mixExp, Pr_ideal_mixExp] at hm
      exact hm
    have hB : Prob.sd
          (fun T =>
            Pr (Gen.realExp A (fun ivk => downVSt C (Vt ivk) ⟨[], []⟩)
                (fun v => Z (replayViewSt C Vt N v)) i N)
              (fun _ => replayViewSt C Vt N ⁻¹' T))
          (fun T => Prob.pr (Gen.idealExp R (simSt C Sim) Vt Z i N) T) ≤ ζ tV N := by
      simp only [hideal]
      exact (Prob.sd_comap_le _ _ (replayViewSt C Vt N)).trans h1
    calc _ ≤ _ := Prob.sd_triangle _ _ _
      _ ≤ p (nC + N * nP) tV + ζ tV N := add_le_add hA hB
      _ = ζ tV N + p (nC + N * nP) tV := add_comm _ _
  · rw [hideal]
    refine le_antisymm (le_trans (Prob.pr_mono _ ?_) (le_of_eq h2)) (zero_le _)
    intro v hv hc
    exact hv (consistent_replaySt C (Vt v.ivk) N (Log.ofView v) hc)

/-- Index privacy carries over under the expansion step, given `Spec.mixClose`, under the bounds nC,
nP and `HidFree`. (The bound:
`ζ t N + collP lam (t + (nC + N * nP)) (t + (nC + N * nP)) + hitP lam t (nC + N * nP)`.) -/
theorem privacy_stateFirst (hM : Spec.mixClose) (R : Gen.RelPair I X W PP)
    (A : Gen.Arg S I X W IVK ISK Pf) (B : ℕ) (Sim : Gen.Simulator S PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞)
    (nC nP : ℕ) (hC : ∀ i, (A.C i).CostBoundAt (wCh C) nC)
    (hP : ∀ k b, b.length ≤ B → (A.P k b).CostBoundAt (wCh C) nP) (hH : HidFree C A)
    (h : Gen.HasIndexPrivacyWith R A B Sim ζ) :
    Gen.HasIndexPrivacyWith R (stateFirstArg C A) B (simSt C Sim) (fun t N =>
      ζ t N + collP lam (t + (nC + N * nP)) (t + (nC + N * nP)) + hitP lam t (nC + N * nP)) := by
  have e : (fun t N =>
        ζ t N + collP lam (t + (nC + N * nP)) (t + (nC + N * nP)) + hitP lam t (nC + N * nP)) =
      fun t N =>
        ζ t N + (fun nT nR => collP lam (nT + nR) (nT + nR) + hitP lam nR nT) (nC + N * nP) t := by
    funext t N
    simp only [Nat.add_comm t, add_assoc]
  rw [e]
  exact privacy_stateFirst_of _
    (fun α c nT nR hB hF E => by rw [← add_assoc]; exact hM S lam C α c nT nR hB hF E)
    R A B Sim ζ nC nP hC hP hH h

end Rom
