-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/WalkFold.lean: the walk's own verdict is the verifier's
`foldBlocks` on what the walk has produced. The honest prover of Honest/Walk.lean asks the
description's own step, one sub-protocol after another, on its own rounds as produced and its own
columns as filled. The main lemma, `walk_fold`: at a chain's end the verifier's state that the walk
holds is the result of `foldBlocks` (Johnson/Desc/Block.lean) over the chain's whole list, at all
rounds produced and all columns filled; it is `none` exactly where `foldBlocks` rejects, or where
the chain began as rejected. The lemma is general in the chain's list, its rounds, the challenges
and the state of the prover's run, and it holds for real rounds and substitutes alike.

  1  `foldBlocks_append`, `fold_exact`, `owed_nil`, `owed_snoc`, `fold_snoc`   on `foldBlocks`
  2  `ChainProgress.Tied`, `ChainProgress.Open`   the invariant of a walk between two rounds
  3  `settle_tied`, `heard_tied`, `walk_tied`, `start_tied`   it is preserved
  4  `walk_fold`   the end

Limits.
  * One chain.
  * Nothing is said on whether the walk goes through.
  * The lemmas on `ChainProgress.start` are general in its fifth argument `front`, the earlier chains'
    columns that this chain's parts are handed; no end reads it. `z.cols` are the chain's own
    columns.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Walk
import Johnson.Desc.ProofFile.Honest.Law.Causal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl W Y : Type}

/-! ## 1 On `foldBlocks` -/

theorem foldBlocks_append (ft : Nat) (l₂ : List (Block S Cl)) : ∀ (l₁ : List (Block S Cl)) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn),
    foldBlocks ft (l₁ ++ l₂) s rs cols =
      (foldBlocks ft l₁ s rs cols).bind fun z => foldBlocks ft l₂ z.1 z.2.1 z.2.2
  | [], _, _, _ => rfl
  | b :: l₁, s, rs, cols => by
    rw [List.cons_append, foldBlocks_eq, foldBlocks_eq]
    split
    · rfl
    · cases b.step ft s (rs.take b.rounds.length) cols with
      | error e => rfl
      | ok z => exact foldBlocks_append ft l₂ l₁ z.1 _ _

theorem owed_nil (ft : Nat) (rs : List Fmt.RoundView) : owed ft ([] : List (Block S Cl)) rs = 0 := by
  simp [owed, groupsOf]

/-- Over exactly its own rounds and the columns that it reads (`owed` counts them), `foldBlocks`
leaves nothing over. -/
theorem fold_exact (ft : Nat) : ∀ (l : List (Block S Cl)) (s : S) (R : List Fmt.RoundView)
    (C : List OpenedColumn) (z : S × List Fmt.RoundView × List OpenedColumn), foldBlocks ft l s R C = .ok z →
    R.length = (l.flatMap (·.rounds)).length → C.length = owed ft l R → z.2.1 = [] ∧ z.2.2 = []
  | [], s, R, C, z, h, hr, hc => by
    have e : (Except.ok (s, R, C) : Except String (S × List Fmt.RoundView × List OpenedColumn)) = .ok z := h
    cases e
    rw [owed_nil] at hc
    exact ⟨List.eq_nil_of_length_eq_zero hr, List.eq_nil_of_length_eq_zero hc⟩
  | b :: l, s, R, C, z, h, hr, hc => by
    obtain ⟨-, s', k, hs, h'⟩ := foldBlocks_cons_ok.1 h
    have hk := ((step_iff ft b s s' _ C k).1 hs).2.2
    subst hk
    rw [List.flatMap_cons, List.length_append] at hr
    rw [owed_cons] at hc
    exact fold_exact ft l s' _ _ z h' (by rw [List.length_drop]; omega)
      (by rw [List.length_drop]; omega)

theorem owed_snoc (ft : Nat) (b : Block S Cl) : ∀ (l : List (Block S Cl)) (R r : List Fmt.RoundView),
    R.length = (l.flatMap (·.rounds)).length →
    owed ft (l ++ [b]) (R ++ r) = owed ft l R + (b.want ft (r.take b.rounds.length)).length
  | [], R, r, h => by
    have hR : R = [] := List.eq_nil_of_length_eq_zero h
    rw [hR, List.nil_append, List.nil_append, owed_cons, owed_nil, owed_nil]
    omega
  | a :: l, R, r, h => by
    rw [List.flatMap_cons, List.length_append] at h
    have hn : a.rounds.length ≤ R.length := by omega
    rw [List.cons_append, owed_cons, owed_cons, List.take_append_of_le_length hn,
      List.drop_append_of_le_length hn,
      owed_snoc ft b l _ r (by rw [List.length_drop]; omega), Nat.add_assoc]

/-- **One sub-protocol more**: the result of `foldBlocks` over a list and one sub-protocol after it
is the step at the list's end. -/
theorem fold_snoc (ft : Nat) (l : List (Block S Cl)) (b : Block S Cl) (s : S) (R r : List Fmt.RoundView)
    (C c : List OpenedColumn) (hR : R.length = (l.flatMap (·.rounds)).length) (hC : C.length = owed ft l R)
    (hr : r.length = b.rounds.length) :
    (foldBlocks ft (l ++ [b]) s (R ++ r) (C ++ c)).toOption.map (·.1) =
      ((foldBlocks ft l s R C).toOption.map (·.1)).bind fun s' => judge ft b s' r c := by
  rw [foldBlocks_append, foldBlocks_more ft l s R r C c hR hC]
  cases h : foldBlocks ft l s R C with
  | error e => rfl
  | ok z =>
    obtain ⟨e1, e2⟩ := fold_exact ft l s R C z h hR hC
    show (foldBlocks ft [b] z.1 (z.2.1 ++ r) (z.2.2 ++ c)).toOption.map (·.1) = judge ft b z.1 r c
    rw [e1, e2, List.nil_append, List.nil_append, foldBlocks_eq, ← hr, List.take_length,
      if_neg (fun h' => h' rfl)]
    unfold judge
    cases b.step ft z.1 r c with
    | error e => rfl
    | ok y => rfl

/-! ## 2 The invariant of a walk between two rounds -/

/-- `bs`: the chain's whole list. `v₀`: the verifier's state at the chain's start, or `none`.
`todo`: the sub-protocols not yet asked. The sub-protocols asked so far, and the rounds produced for
them, account for what the walk holds: its columns are as many as they read (`owed`), and its
verifier's state is the result of `foldBlocks` over them. -/
def ChainProgress.Tied (L : Lay) (bs : List (Block S Cl)) (v₀ : Option S) (todo : List (Block S Cl))
    (z : ChainProgress S Cl W Y) : Prop :=
  ∃ (done : List (Block S Cl)) (front : List Played), bs = done ++ todo ∧
    z.laid = front ++ z.own ∧ front.length = (done.flatMap (·.rounds)).length ∧
    z.cols.length = owed L.firstTree done (roundsOf front) ∧
    z.ver = v₀.bind fun s =>
      (foldBlocks L.firstTree done s (roundsOf front) z.cols).toOption.map (·.1)

/-- The sub-protocol that is being played still lacks a round; or none is left. -/
def ChainProgress.Open (z : ChainProgress S Cl W Y) : Prop :=
  ∀ b t, z.todo = b :: t → z.own.length < b.rounds.length

/-! ## 3 It is preserved -/

theorem roundsOf_append (a b : List Played) : roundsOf (a ++ b) = roundsOf a ++ roundsOf b := by
  unfold roundsOf
  rw [List.map_append]

theorem roundsOf_length (a : List Played) : (roundsOf a).length = a.length := by
  unfold roundsOf
  rw [List.length_map]

theorem settle_tied (L : Lay) (bs : List (Block S Cl)) (v₀ : Option S) :
    ∀ (todo : List (Block S Cl)) (z z' : ChainProgress S Cl W Y), ChainProgress.Tied L bs v₀ todo z →
    (∀ b t, todo = b :: t → z.own.length ≤ b.rounds.length) → ChainProgress.settle L todo z = .ok z' →
    ChainProgress.Tied L bs v₀ z'.todo z' ∧ z'.Open ∧ z'.laid = z.laid
  | [], z, z', h, _, hs => by
    simp only [ChainProgress.settle] at hs
    cases hs
    exact ⟨h, fun b t e => (by cases e), rfl⟩
  | b :: t, z, z', h, ho, hs => by
    simp only [ChainProgress.settle] at hs
    by_cases hlt : z.own.length < b.rounds.length
    · rw [if_pos hlt] at hs
      cases hs
      refine ⟨h, fun b' t' e => ?_, rfl⟩
      have e' : b :: t = b' :: t' := e
      cases e'
      exact hlt
    · rw [if_neg hlt] at hs
      have hn : z.own.length = b.rounds.length :=
        Nat.le_antisymm (ho b t rfl) (Nat.le_of_not_lt hlt)
      obtain ⟨cols, hc, hs⟩ := exBind_ok hs
      have hc' : fillCols (readsOf L.chain L.firstTree L.stored (L.tree z.laid) b.rounds
          (z.own.map (·.drawn))) [] = .ok cols := by
        cases hf : fillCols (readsOf L.chain L.firstTree L.stored (L.tree z.laid) b.rounds
          (z.own.map (·.drawn))) [] with
        | error e =>
          rw [hf] at hc
          cases hc
        | ok c' =>
          rw [hf] at hc
          cases hc
          rfl
      obtain ⟨done, front, h1, h2, h3, h4, h5⟩ := h
      have hdr : (roundsOf z.own).map (·.drawn) = z.own.map (·.drawn) := by
        unfold roundsOf
        rw [List.map_map]
        rfl
      have hcl : cols.length = (b.want L.firstTree (roundsOf z.own)).length := by
        have e := congrArg List.length (fillCols_kept _ _ _ hc')
        rw [readsOf_wants, List.length_map] at e
        unfold Block.want
        rw [hdr]
        exact e
      have hro : (roundsOf z.own).length = b.rounds.length := by rw [roundsOf_length, hn]
      have hfr : (roundsOf front).length = (done.flatMap (·.rounds)).length := by
        rw [roundsOf_length, h3]
      have key := fun (z₁ : ChainProgress S Cl W Y) (g1 : ChainProgress.settle L t z₁ = .ok z')
          (g2 : ChainProgress.Tied L bs v₀ t z₁) (g3 : z₁.own = []) =>
        settle_tied L bs v₀ t z₁ z' g2 (fun _ _ _ => by rw [g3]; exact Nat.zero_le _) g1
      have g := key _ hs
      refine g ?_ rfl
      refine ⟨done ++ [b], front ++ z.own, ?_, ?_, ?_, ?_, ?_⟩
      · rw [h1, List.append_assoc]
        rfl
      · show z.laid = front ++ z.own ++ []
        rw [List.append_nil, h2]
      · rw [List.length_append, List.flatMap_append, List.length_append, h3, hn]
        simp
      · show (z.cols ++ cols).length = _
        rw [roundsOf_append, owed_snoc L.firstTree b done _ _ hfr, ← hro, List.take_length,
          List.length_append, h4, hcl]
      · show (z.ver.bind fun s => judge L.firstTree b s (roundsOf z.own) cols) = _
        rw [h5, roundsOf_append]
        cases v₀ with
        | none => rfl
        | some s₀ => exact (fold_snoc L.firstTree done b s₀ _ _ _ _ hfr h4 hro).symm

theorem heard_tied (L : Lay) (bs : List (Block S Cl)) (v₀ : Option S) {z z' : ChainProgress S Cl W Y}
    {s : Step W Y} {x : Told} {d : Fmt.Drawn} (h : ChainProgress.Tied L bs v₀ z.todo z) (ho : z.Open)
    (hz : z.heard L s x d = .ok z') :
    ChainProgress.Tied L bs v₀ z'.todo z' ∧ z'.Open ∧ z'.laid.length = z.laid.length + 1 := by
  unfold ChainProgress.heard at hz
  obtain ⟨m', -, hz⟩ := exBind_ok hz
  obtain ⟨done, front, h1, h2, h3, h4, h5⟩ := h
  have key : ChainProgress.Tied L bs v₀ z'.todo z' ∧ z'.Open ∧ z'.laid =
      z.laid ++ [⟨s.name, s.addr.place, s.addr.part, x.told, x.vals, x.tables, d⟩] := by
    refine settle_tied L bs v₀ z.todo _ z' ?_ ?_ hz
    · refine ⟨done, front, h1, ?_, h3, h4, h5⟩
      show z.laid ++ [_] = front ++ (z.own ++ [_])
      rw [h2, List.append_assoc]
    · intro b t e
      show (z.own ++ [_]).length ≤ b.rounds.length
      rw [List.length_append]
      exact ho b t e
  obtain ⟨g1, g2, g3⟩ := key
  refine ⟨g1, g2, ?_⟩
  rw [g3, List.length_append]
  rfl

theorem walk_tied (L : Lay) (bs : List (Block S Cl)) (v₀ : Option S) :
    ∀ (ss : List (Step W Y)) (ds : List Fmt.Drawn) (z z' : ChainProgress S Cl W Y),
    ChainProgress.Tied L bs v₀ z.todo z → z.Open → walk L ss ds z = .ok z' →
    ChainProgress.Tied L bs v₀ z'.todo z' ∧ z'.Open ∧ z'.laid.length = z.laid.length + ss.length
  | [], [], z, z', h, ho, hw => by
    simp only [walk] at hw
    cases hw
    exact ⟨h, ho, rfl⟩
  | [], _ :: _, _, _, _, _, hw => by simp [walk] at hw
  | _ :: _, [], _, _, _, _, hw => by simp [walk] at hw
  | s :: ss, d :: ds, z, z', h, ho, hw => by
    simp only [walk] at hw
    obtain ⟨x, -, hw⟩ := exBind_ok hw
    obtain ⟨z₁, hz₁, hw⟩ := exBind_ok hw
    obtain ⟨a1, a2, a3⟩ := heard_tied L bs v₀ h ho hz₁
    obtain ⟨b1, b2, b3⟩ := walk_tied L bs v₀ ss ds z₁ z' a1 a2 hw
    refine ⟨b1, b2, ?_⟩
    rw [b3, a3, List.length_cons]
    omega

theorem start_tied (L : Lay) (bs : List (Block S Cl)) (m : Option (Mid W Y)) (v : Option S)
    {a : ChainProgress S Cl W Y} {front : List OpenedColumn} (h : ChainProgress.start L bs m v front = .ok a) :
    ChainProgress.Tied L bs (if m.isSome then v else none) a.todo a ∧ a.Open ∧ a.laid = [] := by
  unfold ChainProgress.start at h
  refine settle_tied L bs _ bs _ a ?_ ?_ h
  · refine ⟨[], [], rfl, rfl, rfl, ?_, ?_⟩
    · show ([] : List OpenedColumn).length = _
      rw [owed_nil]
      rfl
    · show (if m.isSome then v else none) = _
      cases (if m.isSome then v else none) <;> rfl
  · intro _ _ _
    exact Nat.zero_le _

/-! ## 4 The end -/

/-- **The walk's own verdict is the verifier's `foldBlocks` on what the walk has produced.** At
the end of a chain's walk over as many rounds as the chain's sub-protocols have: every sub-protocol
has been asked; the columns are as many as the sub-protocols read; and the verifier's state that the
walk holds is the result of `foldBlocks` over the whole list at all rounds produced and all columns
filled. It is `none` exactly where `foldBlocks` rejects, or where the chain began as rejected. -/
theorem walk_fold (L : Lay) (bs : List (Block S Cl)) (m : Option (Mid W Y)) (v : Option S)
    {a z : ChainProgress S Cl W Y} {ss : List (Step W Y)} {ds : List Fmt.Drawn}
    {front : List OpenedColumn} (ha : ChainProgress.start L bs m v front = .ok a) (hz : walk L ss ds a = .ok z)
    (hl : ss.length = (bs.flatMap (·.rounds)).length) :
    z.todo = [] ∧ z.own = [] ∧ z.laid.length = ss.length ∧
      z.cols.length = owed L.firstTree bs (roundsOf z.laid) ∧
      z.ver = (if m.isSome then v else none).bind fun s =>
        (foldBlocks L.firstTree bs s (roundsOf z.laid) z.cols).toOption.map (·.1) := by
  obtain ⟨a1, a2, a3⟩ := start_tied L bs m v ha
  obtain ⟨⟨done, front, h1, h2, h3, h4, h5⟩, b2, b3⟩ := walk_tied L bs _ ss ds a z a1 a2 hz
  rw [a3] at b3
  have hlen : z.laid.length = ss.length := by
    rw [b3]
    exact Nat.zero_add _
  have hcount : front.length + z.own.length =
      (done.flatMap (·.rounds)).length + (z.todo.flatMap (·.rounds)).length := by
    rw [← List.length_append, ← h2, hlen, hl, h1, List.flatMap_append, List.length_append]
  have htodo : z.todo = [] := by
    cases ht : z.todo with
    | nil => rfl
    | cons b t =>
      have h6 := b2 b t ht
      rw [ht, List.flatMap_cons, List.length_append] at hcount
      omega
  rw [htodo] at hcount h1
  have hown : z.own = [] := List.eq_nil_of_length_eq_zero (by
    rw [List.flatMap_nil, List.length_nil] at hcount
    omega)
  rw [List.append_nil] at h1
  rw [hown, List.append_nil] at h2
  subst h1
  rw [← h2] at h4 h5
  exact ⟨htodo, hown, hlen, h4, h5⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.foldBlocks_append
#print axioms ProofFile.Honest.owed_nil
#print axioms ProofFile.Honest.fold_exact
#print axioms ProofFile.Honest.owed_snoc
#print axioms ProofFile.Honest.fold_snoc
#print axioms ProofFile.Honest.roundsOf_append
#print axioms ProofFile.Honest.roundsOf_length
#print axioms ProofFile.Honest.settle_tied
#print axioms ProofFile.Honest.heard_tied
#print axioms ProofFile.Honest.walk_tied
#print axioms ProofFile.Honest.start_tied
#print axioms ProofFile.Honest.walk_fold
#print axioms ProofFile.Honest.ChainProgress.Tied
#print axioms ProofFile.Honest.ChainProgress.Open
