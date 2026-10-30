-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/CutOf.lean: the honest side of the kind "lookup" (K3). The
rounds of a course are cut by stage: `Cut R x` (Honest/K3/Law/Walk.lean) holds wherever the course
stands at its place, its challenges can be sampled (`Fit R`) and its stages answer
(`R.rounds = some x`). For every face. Theorems, with one definition.

Terms. Honest/K3/GLOSSARY.md ("course", "fit", "stage").

What is shown.
  `cut_aloneFrom`: a part played alone shows one round for each move, with the challenges that it
    was given.
  `cut_stage`: the like of a stage of a course.
  `cut_run`: the like of stages in a row.
  `cut_step`, `cut_front`: the course's run, opened at the stage with a given number.
  `cut_plain` (helper: `cut_plain_sum`), `cut_fit_all`, `cut_fit_at`: what the frame's test on
    challenges says at the verifier's own entries: no position, no matrix entry; as many elements as
    the entry states.
  `cut_of_rounds`: the cut.

Hypotheses that remain. `Fit R` (`hF`) and `R.rounds = some x` (`h`), in `cut_of_rounds`. In the
steps: `h`: the stage, the run or the course returns; `hs`: s is the stage number n; `h2`: (in
`cut_plain`) the face has two planes at least. In `cut_run`, `cut_fit_all`, `cut_fit_at`,
`cut_aloneFrom`, `cut_front` the hypotheses stand without a name, in front of arrows: a return; a
number in range; no entry states a position or a matrix entry; the frame's test accepts; the entry
and the challenge stand at number i.

Users. This file is imported by Honest/K3/Law/LookHeardOne.lean and
Honest/K3/Law/Thread/OkRounds.lean.

Limits. Nothing is said of what is sent.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Walk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E zeroE)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.K3 (entriesV)
open VerifiableInference.Desc.First.ProdV (elementsAlone)
open ProofFile.Honest.SumLaw (alone aloneFrom)
open ProofFile.Honest.K3.Forward (Quiet)

variable {W : Type}

/-! ## A part, a stage, stages in a row -/

theorem cut_aloneFrom {Cn X : Type} (c : Cn) : ∀ (mvs : List (Move Cn W X)) (t : State W X)
    (seen : Seen) (ds : List Fmt.Drawn) (y : List Fmt.RoundView),
    aloneFrom c mvs t seen ds = some y → y.map (·.drawn) = ds ∧ y.length = mvs.length
  | [], _, _, [], y, h => by
    simp only [aloneFrom, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩
  | [], _, _, _ :: _, y, h => by simp [aloneFrom] at h
  | _ :: _, _, _, [], y, h => by simp [aloneFrom] at h
  | mv :: mvs, t, seen, d :: ds, y, h => by
    unfold aloneFrom at h
    split at h
    · dsimp only at h
      obtain ⟨y', hy', e⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨a, b⟩ := cut_aloneFrom c mvs _ _ _ _ hy'
      subst e
      simp [a, b]
    · cases h

theorem cut_stage (R : Course W) {s : Stage} {t : State W Unit} {seen : Seen}
    {d : List Fmt.Drawn} {y : List Fmt.RoundView} (h : R.stage s t seen d = some y) :
    y.map (·.drawn) = d ∧ y.length = s.rounds R.f ∧
      (s.call R.f = none → ∃ d0, d = [d0] ∧ y = [⟨[], d0⟩]) := by
  unfold Course.stage at h
  split at h
  · rename_i k hk
    obtain ⟨a, b⟩ := cut_aloneFrom _ _ _ _ _ _ h
    refine ⟨a, ?_, fun hc => by rw [hk] at hc; cases hc⟩
    rw [b, sumPart_moves]
    show VerifiableInference.Desc.K3.roundsOf (shapeAt R.a s) = _
    unfold shapeAt Stage.rounds
    rw [hk]
    rfl
  · rename_i hk
    split at h
    · rename_i d0
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨rfl, ?_, fun _ => ⟨d0, rfl, rfl⟩⟩
      unfold Stage.rounds
      rw [hk]
      rfl
    · cases h

theorem cut_run (R : Course W) : ∀ (l : List Stage) (t : State W Unit) (seen : Seen)
    (ds : List Fmt.Drawn) (x : List Fmt.RoundView), R.run l t seen ds = some x →
    x.map (·.drawn) = ds ∧ x.length = (l.map (Stage.rounds R.f)).sum
  | [], _, _, [], x, h => by
    simp only [Course.run, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩
  | [], _, _, _ :: _, x, h => by simp [Course.run] at h
  | s :: l, t, seen, ds, x, h => by
    unfold Course.run at h
    obtain ⟨y, hy, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨z, hz, e⟩ := Option.map_eq_some_iff.1 h2
    obtain ⟨a, b, _⟩ := cut_stage R hy
    obtain ⟨a', b'⟩ := cut_run R l _ _ _ _ hz
    subst e
    refine ⟨?_, by simp [b, b']⟩
    rw [List.map_append, a, a', List.take_append_drop]

/-! ## The run, opened at a stage's number -/

/-- The state in front of the stage number n. -/
def stN (R : Course W) (n : Nat) : State W Unit :=
  { R.t with heard := R.t.heard ++ R.ds.take (off R.f n) }

/-- What the run from stage number n on is made of. -/
theorem cut_step (R : Course W) {n : Nat} {s : Stage} (hs : (stages R.f)[n]? = some s)
    {seen : Seen} {xn : List Fmt.RoundView}
    (h : R.run ((stages R.f).drop n) (stN R n) seen (R.ds.drop (off R.f n)) = some xn) :
    ∃ y z, R.stage s (stN R n) seen ((R.ds.drop (off R.f n)).take (s.rounds R.f)) = some y ∧
      R.run ((stages R.f).drop (n + 1)) (stN R (n + 1)) (seen.plus y)
        (R.ds.drop (off R.f (n + 1))) = some z ∧ xn = y ++ z := by
  obtain ⟨hn, e⟩ := List.getElem?_eq_some_iff.1 hs
  rw [List.drop_eq_getElem_cons hn, e] at h
  unfold Course.run at h
  obtain ⟨y, hy, h2⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨z, hz, e2⟩ := Option.map_eq_some_iff.1 h2
  refine ⟨y, z, hy, ?_, e2.symm⟩
  have e3 : ({ stN R n with
      heard := (stN R n).heard ++ (R.ds.drop (off R.f n)).take (s.rounds R.f) } : State W Unit) =
      stN R (n + 1) := by
    unfold stN
    rw [off_succ hs, List.take_add]
    simp
  rw [e3, dd, ← off_succ hs] at hz
  exact hz

/-- Where the course's rounds return, the run from stage number n on returns the rest of them. seen
is bound by "∃" and held by what functions return at it alone: some value: the statement does not
say that it is the run's own. The seen that the proof lays is `R.seen` with rounds laid behind
(`Seen.plus`); `cut_of_rounds`, which alone takes it, does not read it. -/
theorem cut_front (R : Course W) {x : List Fmt.RoundView} (h : R.rounds = some x) :
    ∀ n, n ≤ (stages R.f).length → ∃ seen,
      R.run ((stages R.f).drop n) (stN R n) seen (R.ds.drop (off R.f n)) =
        some (x.drop (off R.f n)) := by
  intro n
  induction n with
  | zero =>
    intro _
    have e0 : off R.f 0 = 0 := rfl
    have es : stN R 0 = R.t := by
      unfold stN
      rw [e0]
      simp
    exact ⟨R.seen, by rw [es, e0]; exact h⟩
  | succ n ih =>
    intro hn
    obtain ⟨seen, e⟩ := ih (by omega)
    have hs : (stages R.f)[n]? = some (stages R.f)[n] := List.getElem?_eq_getElem (by omega)
    obtain ⟨y, z, hy, hz, e2⟩ := cut_step R hs e
    obtain ⟨_, b, _⟩ := cut_stage R hy
    refine ⟨seen.plus y, ?_⟩
    rw [hz, off_succ hs, ← dd, e2, ← b]
    simp

/-! ## The frame's test on challenges, at the verifier's entries -/

theorem cut_plain_sum (k : MaskedSum.Call) : ∀ e ∈ MaskedSum.entries k, e.poss = 0 ∧ e.trits = 0 :=
    by
  intro e he
  unfold MaskedSum.entries at he
  rcases List.mem_append.1 he with h | h
  · rcases List.mem_append.1 h with h | h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      subst h
      exact ⟨rfl, rfl⟩
    · obtain ⟨_, _, e2⟩ := List.mem_map.1 h
      subst e2
      exact ⟨rfl, rfl⟩
  · cases hk : k.ends with
    | none => simp [hk] at h
    | some e' =>
      simp only [hk, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h <;> subst h <;> exact ⟨rfl, rfl⟩

theorem cut_plain (f : LFace) (h2 : 2 ≤ f.planes) : ∀ e ∈ entriesV f, e.poss = 0 ∧ e.trits = 0 := by
  intro e he
  rw [← entries_stages f h2] at he
  obtain ⟨s, _, h⟩ := List.mem_flatMap.1 he
  unfold Stage.entries at h
  split at h
  · exact cut_plain_sum _ e h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    exact ⟨rfl, rfl⟩

theorem cut_fit_all : ∀ (es : List Fmt.Entry) (ds : List Fmt.Drawn),
    (∀ e ∈ es, e.poss = 0 ∧ e.trits = 0) → drawsFit (es.map declOf) ds = true →
    ∀ D ∈ ds, D.poss = [] ∧ D.trits = []
  | [], [], _, _ => by simp
  | [], _ :: _, _, h => by simp [drawsFit] at h
  | _ :: _, [], _, h => by simp [drawsFit] at h
  | e :: es, d :: ds, hp, h => by
    simp only [List.map_cons, drawsFit, Bool.and_eq_true] at h
    intro D hD
    rcases List.mem_cons.1 hD with hD | hD
    · subst hD
      have h1 := h.1
      simp only [drawFit, Bool.and_eq_true, beq_iff_eq] at h1
      obtain ⟨p0, t0⟩ := hp e (by simp)
      have a : D.poss.length = 0 := by
        have := h1.1.1.1.1.1.1.2
        rw [this]
        exact p0
      have b : D.trits.length = 0 := by
        have := h1.1.1.1.1.1.2
        rw [this]
        exact t0
      exact ⟨List.eq_nil_of_length_eq_zero a, List.eq_nil_of_length_eq_zero b⟩
    · exact cut_fit_all es ds (fun e' he' => hp e' (List.mem_cons_of_mem _ he')) h.2 D hD

theorem cut_fit_at : ∀ (es : List Fmt.Entry) (ds : List Fmt.Drawn) (i : Nat) (e : Fmt.Entry)
    (D : Fmt.Drawn), drawsFit (es.map declOf) ds = true → es[i]? = some e → ds[i]? = some D →
    D.elems.length = e.drawE
  | [], _, _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, h, _, _ => by simp [drawsFit] at h
  | e0 :: es, d :: ds, 0, e, D, h, he, hD => by
    simp only [List.map_cons, drawsFit, Bool.and_eq_true] at h
    simp only [List.getElem?_cons_zero, Option.some.injEq] at he hD
    subst he hD
    have h1 := h.1
    simp only [drawFit, Bool.and_eq_true, beq_iff_eq] at h1
    exact h1.1.1.1.1.1.1.1
  | e0 :: es, d :: ds, i + 1, e, D, h, he, hD => by
    simp only [List.map_cons, drawsFit, Bool.and_eq_true] at h
    simp only [List.getElem?_cons_succ] at he hD
    exact cut_fit_at es ds i e D h.2 he hD

/-! ## The cut -/

/-- **The rounds of a course are cut by stage.** -/
theorem cut_of_rounds (R : Course W) (x : List Fmt.RoundView) (hF : Fit R) (h : R.rounds = some x) :
    Cut R x := by
  have h2 := two_le_planes_of_ok R.f hF.ok
  obtain ⟨hd, hl⟩ := cut_run R _ _ _ _ _ h
  have hall := cut_fit_all _ _ (cut_plain R.f h2) hF.draws
  have key : ∀ s ∈ stages R.f, ∃ seen y, R.stage s (R.stateAt s) seen (R.draws s) = some y ∧
      sliceOf R.f x s = y := by
    intro s hs
    obtain ⟨n, hn, e⟩ := List.getElem_of_mem hs
    have hs' : (stages R.f)[n]? = some s := by rw [← e]; exact List.getElem?_eq_getElem hn
    obtain ⟨seen, e1⟩ := cut_front R h n (by omega)
    obtain ⟨y, z, hy, _, e2⟩ := cut_step R hs' e1
    obtain ⟨_, b, _⟩ := cut_stage R hy
    refine ⟨seen, y, ?_, ?_⟩
    · unfold Course.stateAt Course.draws
      rw [off_at hs']
      exact hy
    · unfold sliceOf
      rw [off_at hs', e2, ← b]
      simp
  refine ⟨hd, ?_, hl, ?_, ?_⟩
  · unfold elementsAlone
    rw [List.all_eq_true]
    intro r hr
    obtain ⟨a, b⟩ := hall r.drawn (by rw [← hd]; exact List.mem_map_of_mem hr)
    simp [a, b]
  · intro s hs
    obtain ⟨seen, y, hy, e⟩ := key s hs
    exact ⟨seen, by rw [e]; exact hy⟩
  · intro s hs hc
    obtain ⟨seen, y, hy, e⟩ := key s hs
    obtain ⟨_, _, q⟩ := cut_stage R hy
    obtain ⟨d0, hd0, hy0⟩ := q hc
    refine ⟨⟨[], d0⟩, by rw [e, hy0], rfl, ?_, ?_, ?_⟩
    · -- the entry at the stage's round states the stage's number of samples
      have hr : Stage.rounds R.f s = 1 := by
        unfold Stage.rounds
        rw [hc]
      have he := entries_at R.f h2 s hs
      have hen : Stage.entries R.f s =
          [VerifiableInference.Desc.K3.drawEntry s.name (s.draws R.f)] := by
        unfold Stage.entries
        rw [hc]
      rw [hr, hen] at he
      have g1 : (entriesV R.f)[firstRound R.f s]? =
          some (VerifiableInference.Desc.K3.drawEntry s.name (s.draws R.f)) := by
        have := congrArg (fun l => l[0]?) he
        simpa [List.getElem?_take, List.getElem?_drop] using this
      have g2 : R.ds[firstRound R.f s]? = some d0 := by
        have : (R.draws s)[0]? = some d0 := by rw [hd0]; rfl
        unfold Course.draws at this
        rw [hr] at this
        simpa [List.getElem?_take, List.getElem?_drop] using this
      exact cut_fit_at _ _ _ _ _ hF.draws g1 g2
    · have g2 : d0 ∈ R.ds := by
        have : d0 ∈ R.draws s := by rw [hd0]; simp
        unfold Course.draws at this
        exact List.mem_of_mem_drop (List.mem_of_mem_take this)
      exact (hall d0 g2).1
    · have g2 : d0 ∈ R.ds := by
        have : d0 ∈ R.draws s := by rw [hd0]; simp
        unfold Course.draws at this
        exact List.mem_of_mem_drop (List.mem_of_mem_take this)
      exact (hall d0 g2).2

#print axioms ProofFile.Honest.K3.Law.cut_aloneFrom
#print axioms ProofFile.Honest.K3.Law.cut_stage
#print axioms ProofFile.Honest.K3.Law.cut_run
#print axioms ProofFile.Honest.K3.Law.cut_step
#print axioms ProofFile.Honest.K3.Law.cut_front
#print axioms ProofFile.Honest.K3.Law.cut_plain_sum
#print axioms ProofFile.Honest.K3.Law.cut_plain
#print axioms ProofFile.Honest.K3.Law.cut_fit_all
#print axioms ProofFile.Honest.K3.Law.cut_fit_at
#print axioms ProofFile.Honest.K3.Law.cut_of_rounds

end ProofFile.Honest.K3.Law
