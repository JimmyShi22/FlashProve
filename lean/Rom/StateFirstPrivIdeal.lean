-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/StateFirstPrivIdeal.lean: the step that expands a long answer of a random oracle from a state
(Rom/StateFirst.lean), index privacy, part 3: the reduction's interpretation of the mixed
experiment, with the family fixed (`ideal_mixExp`), and for probabilities over the family
(`Pr_ideal_mixExp`).

Chain oracles, states, dr: `Link`, `stSpec` (Rom/StateFirst.lean); mixed programs, `real`:
Rom/StateFirstMix.lean.

The mixed experiment `mixExp` is in Rom/StateFirstPrivMix.lean, the reduction `downVSt` and the
replay `replaySt` in Rom/StateFirstPrivReplay.lean, the reduction's table `Book` and its
interpretation `ideal C false` in Rom/StateFirstMix.lean.

  `ideal_mixLoop`     With a family F fixed and a table that agrees with F (`Book.Agrees`): the
                      first component of `ideal C false` of `mixLoop` is the loop of the adversary
                      against `stWorld C` of `eagerWorld A isk F`, the challenger of the real
                      experiment over the first family.

Notation:
  family (of functions), F: `Fam S` (Rom/OSpec.lean): a whole family of functions
  the first family, the second family (of oracles): S, and `stSpec S lam C` (Rom/StateFirst.lean)
  mixed program: an `OComp (mixSpec C) α` (Rom/StateFirstMix.lean): typed and raw queries; `.inl o`:
      a typed query, to the first family; `.inr (.inl o)`, `.inr (.inr ())`: raw queries, to the
      second family (the last to dr)
  `ideal C false` (Rom/StateFirstMix.lean): the ideal interpretations: typed queries go to the first
      family; a raw query for a state becomes the typed query, of whose answer the state is
      returned; with `all` = false only the raw queries are entered in the table (what a reduction
      can do)
  `Book` (Rom/StateFirstMix.lean): the reduction's table: the chain answers seen, oldest first
      (`made`), and the answers that it has itself given for dr at other queries (`loose`)

Limits: `ideal_mixExp` is an equality of distributions for every fixed family, not of programs:
`ideal C false` queries the family again at a repeated raw query for a state, the reduction does
not. No bound is proved here.
-/
import Rom.StateFirstPrivMix
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Rom
open ZKCP

variable {S : OSpec} {lam : ℕ} (C : ∀ o, Link lam (S.Rng o))
  {I X W PP IVK ISK Pf : Type} {α β : Type}

/-! ## The table and the family -/

/-- every entered answer equals the family's answer at that query -/
def Book.Agrees (b : Book S lam) (F : Fam S) : Prop := ∀ e ∈ b.made, e.2.2 = F e.1 e.2.1

variable {C}

theorem kept_findMade {b : Book S lam} {o : S.ι} {q : S.Dom o}
    {r : S.Rng o} (h : b.kept C o q = some r) :
    (C o).isPlain = false ∧ findMade b.made o q = some r := by
  unfold Book.kept at h
  cases hp : (C o).isPlain with
  | true => simp [hp] at h
  | false => simpa [hp] using h

theorem kept_agrees {b : Book S lam} {F : Fam S} (hb : b.Agrees F) {o : S.ι} {q : S.Dom o}
    {r : S.Rng o} (h : b.kept C o q = some r) : r = F o q :=
  hb _ (findMade_mem (kept_findMade h).2)

theorem note_of_kept {b : Book S lam} {o : S.ι} {q : S.Dom o} {r : S.Rng o}
    (h : b.kept C o q = some r) (r' : S.Rng o) : b.note C o q r' = b := by
  obtain ⟨h1, h2⟩ := kept_findMade h
  simp [Book.note, h1, h2]

theorem note_agrees {b : Book S lam} {F : Fam S} (hb : b.Agrees F) (o : S.ι) (q : S.Dom o) :
    (b.note C o q (F o q)).Agrees F := by
  unfold Book.note
  split
  · exact hb
  · split
    · exact hb
    · intro e he
      rcases List.mem_append.1 he with he | he
      · exact hb e he
      · rw [List.mem_singleton.1 he]

variable (C)

/-! ## The reduction's interpretation, the family fixed -/

theorem ideal_mixLoop (A : Gen.Arg S I X W IVK ISK Pf) (Z : Gen.ViewEnv (stSpec S lam C) IVK X W Pf)
    (isk : ISK) (ivk : IVK) (F : Fam S) (V : Gen.AdvVerifier (stSpec S lam C) X Pf) :
    ∀ (n : ℕ) (l : Log (stSpec S lam C) X Pf) (b : Book S lam), b.Agrees F →
      ((ideal C false (mixLoop C A Z isk V n (l.view ivk)) b).runEager F).map Prod.fst =
        (lLoop (stWorld C (eagerWorld A isk F)) (fun l => Z (l.view ivk)) V n l (b.withS ())).map
          (Log.view ivk) := by
  induction V with
  | halt => intro n l b _; simp only [mixLoop, ideal, OComp.runEager, lLoop, PMF.pure_map]
  | sample m k ih =>
    intro n l b hb
    simp only [mixLoop, ideal, OComp.runEager, lLoop, PMF.map_bind]
    exact congrArg _ (funext fun r => ih r n { l with coins := l.coins ++ [r.val] } b hb)
  | request k ih =>
    intro n l b hb
    cases n with
    | zero => simp only [mixLoop, ideal, OComp.runEager, lLoop, PMF.pure_map]
    | succ n =>
      cases hz : Z (l.view ivk) with
      | none => simp only [mixLoop, hz, ideal, OComp.runEager, lLoop, PMF.pure_map]
      | some bt =>
        simp only [mixLoop, hz, lLoop, ideal_bind, ideal_liftT, OComp.bind_assoc, OComp.bind,
          OComp.runEager_bind, PMF.map_bind]
        show _ = ((((A.P isk bt.pairs).runEager F).map _).map _).bind _
        rw [PMF.map_comp, PMF.bind_map]
        exact congrArg _
          (funext fun πs => ih _ n { l with sessions := l.sessions ++ [bt.released πs.val] } b hb)
  | query x q k ih =>
    intro n l b hb
    match x, q, k, ih with
    | .inl o, q, k, ih =>
      simp only [mixLoop, ideal, OComp.runEager, lLoop, PMF.map_bind]
      cases hk : b.kept C o q with
      | some r =>
        rw [stWorld_inl_some C (eagerWorld A isk F) b () hk, PMF.pure_bind,
          note_of_kept hk, ← kept_agrees hb hk]
        exact ih _ n { l with trace := l.trace ++ [⟨.inl o, q, (C o).toAns r⟩] } b hb
      | none =>
        rw [stWorld_inl_none C (eagerWorld A isk F) b () hk]
        show _ = ((PMF.pure (F o q, ())).map _).bind _
        rw [PMF.pure_map, PMF.pure_bind]
        exact ih _ n { l with trace := l.trace ++ [⟨.inl o, q, (C o).toAns (F o q)⟩] } _
          (note_agrees hb o q)
    | .inr u, p, k, ih =>
      simp only [mixLoop, lLoop, PMF.map_bind]
      cases h1 : drVal C b p with
      | some r =>
        simp only [ideal, h1]
        rw [stWorld_dr_some C (eagerWorld A isk F) b () h1, PMF.pure_bind]
        exact ih _ n { l with trace := l.trace ++ [⟨.inr u, p, r⟩] } b hb
      | none =>
        simp only [ideal, h1]
        rw [stWorld_dr_none C (eagerWorld A isk F) b () h1, PMF.bind_map]
        simp only [OComp.runEager, PMF.map_bind]
        exact congrArg _
          (funext fun x => ih _ n { l with trace := l.trace ++ [⟨.inr u, p, digE lam x⟩] } _ hb)

/-- The view over the second family, recovered from the reduction's view. -/
def replayViewSt
    (Vt : IVK → Gen.AdvVerifier (stSpec S lam C) X Pf) (N : ℕ) (v : Gen.View S IVK X Pf) :
    Gen.View (stSpec S lam C) IVK X Pf :=
  (replaySt C (Vt v.ivk) N ⟨[], []⟩ (Log.ofView v)).view v.ivk

/-- With the family F fixed, the first component of the reduction's interpretation of the mixed
experiment has the distribution of the real experiment over the first family, `Gen.realExp A`, run
with the reduction and with the environment applied to the replayed log, mapped by the replay. -/
theorem ideal_mixExp (A : Gen.Arg S I X W IVK ISK Pf)
    (Vt : IVK → Gen.AdvVerifier (stSpec S lam C) X Pf) (Z : Gen.ViewEnv (stSpec S lam C) IVK X W Pf)
    (i : I) (N : ℕ) (F : Fam S) :
    ((ideal C false (mixExp C A Vt Z i N) ⟨[], []⟩).runEager F).map Prod.fst =
      ((Gen.realExp A (fun ivk => downVSt C (Vt ivk) ⟨[], []⟩)
          (fun v => Z (replayViewSt C Vt N v)) i N).runEager F).map
        (replayViewSt C Vt N) := by
  have e2 : Gen.realExp A (fun ivk => downVSt C (Vt ivk) ⟨[], []⟩) (fun v => Z (replayViewSt C Vt N v)) i N = (A.C i).bind fun key =>
      Gen.realLoop A (fun v => Z (replayViewSt C Vt N v)) key.2 (downVSt C (Vt key.1) ⟨[], []⟩)
          N ((Log.nil : Log S X Pf).view key.1) := rfl
  rw [e2]
  simp only [mixExp, ideal_bind, ideal_liftT, OComp.bind_assoc, OComp.bind,
    OComp.runEager_bind, PMF.map_bind]
  refine congrArg _ (funext fun key => ?_)
  have h1 :=
    ideal_mixLoop C A Z key.2 key.1 F (Vt key.1) N Log.nil ⟨[], []⟩ (fun e he => by cases he)
  refine h1.trans ?_
  rw [realLoop_eq, loop_replaySt, PMF.map_comp, PMF.map_comp]
  rfl

/-- `ideal_mixExp` for probabilities over the family. -/
theorem Pr_ideal_mixExp (A : Gen.Arg S I X W IVK ISK Pf)
    (Vt : IVK → Gen.AdvVerifier (stSpec S lam C) X Pf) (Z : Gen.ViewEnv (stSpec S lam C) IVK X W Pf)
    (i : I) (N : ℕ) (T : Set (Gen.View (stSpec S lam C) IVK X Pf)) :
    Pr (ideal C false (mixExp C A Vt Z i N) ⟨[], []⟩) (fun _ => {x | x.1 ∈ T}) =
      Pr (Gen.realExp A (fun ivk => downVSt C (Vt ivk) ⟨[], []⟩)
          (fun v => Z (replayViewSt C Vt N v)) i N)
        (fun _ => replayViewSt C Vt N ⁻¹' T) := by
  unfold Pr PrCoins
  refine MeasureTheory.lintegral_congr fun F => ?_
  have h := congrArg (fun p => Prob.pr p T) (ideal_mixExp C A Vt Z i N F)
  simp only [Prob.pr_map] at h
  exact h

end Rom
