-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/ChainEnd.lean: what a chain's course
(Honest/Law/Rule/Chain.lean: `Chained`) leaves behind. Where the prover's run still goes on at the
chain's end, the state at its end is written out from the state at its start: what the parts have
passed on, by `dryFold` (Honest/Law/Rule/Dry.lean); the challenges; the rounds shown. Its field
`opened` is not spoken of, nor what the added rounds hold. What the sub-protocols have read, apart
from the tables, is what the chain's declared rounds read. And every read that the chain has added
has words.

  0  `lays_drawn`, `chained_laid`   a sub-protocol's rounds carry its challenges; a chain's rounds
     at its end extend those at its start
  1  `chained_mid`   the prover's run goes on exactly where the verifier has not rejected, if that
     is so at the chain's start; at a chain at whose end it still goes on, the last state's `st`,
     `loc` and `seen`, from the first state's
  2  `fill_words`, `chained_reads`   each read has words; the reads, without what depends on a
     table, are those of `readsOf` over the sub-protocols' rounds, concatenated; each read is one of
     some sub-protocol's, at the tables of an initial segment of the chain's rounds

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.ChainModel
import Johnson.Desc.ProofFile.Honest.Law.Cut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place Oracle OpenedColumn)

variable {S Cl V W Y : Type}

/-! ## 0 Two small lemmas -/

theorem lays_drawn : ∀ (l : List (Step W Y)) (ds : List Fmt.Drawn) (m : Option (Mid W Y))
    (y : List Played × Option (Mid W Y)), lays l ds m = .ok y → y.1.map (·.drawn) = ds
  | [], [], m, y, h => by
    rw [lays] at h
    cases h
    rfl
  | [], _ :: _, _, _, h => by simp [lays] at h
  | _ :: _, [], _, _, h => by simp [lays] at h
  | s :: l, d :: ds, m, y, h => by
    rw [lays] at h
    obtain ⟨x, -, h⟩ := exBind_ok h
    obtain ⟨m', -, h⟩ := exBind_ok h
    obtain ⟨y', hy, e⟩ := exMap_ok h
    subst e
    exact congrArg (d :: ·) (lays_drawn l ds m' y' hy)

/-- A chain's rounds at its end extend those at its start. -/
theorem chained_laid {L : Lay} : ∀ (bs : List (Block S Cl)) (ss : List (Step W Y))
    (ds : List Fmt.Drawn) (c c' : Core S W Y), Chained L bs ss ds c c' →
    ∃ suf, c'.laid = c.laid ++ suf
  | [], ss, ds, c, c', hC => by
    rw [Chained] at hC
    obtain ⟨-, -, rfl⟩ := hC
    exact ⟨[], (List.append_nil _).symm⟩
  | b :: bs, ss, ds, c, c', hC => by
    rw [Chained] at hC
    obtain ⟨y, cols, -, -, hC'⟩ := hC
    obtain ⟨suf, h⟩ := chained_laid bs _ _ _ _ hC'
    refine ⟨y.1 ++ suf, ?_⟩
    rw [h]
    show c.laid ++ y.1 ++ suf = _
    rw [List.append_assoc]

/-! ## 1 The state of the prover's run -/

/-- **Where the prover's run still goes on at a chain's end**, three fields of the state at its end,
from the state at its start, the chain's `Step`s and challenges, and the rounds that the chain has
added. (Between two sub-protocols the walk lays the columns read into the field `opened`, which
`play` does not: so the end state is not said to be what `play` returns on the whole chain.)
Hypotheses: the `Step`s are those that `chainSteps` returns for the chain's sub-protocols; at the
chain's start the prover's run goes on exactly where the verifier has not rejected. -/
theorem chained_mid {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option V} {hs : List (Placed V W Y)} {L : Lay} :
    ∀ (bs : List (Block S Cl)) (ss : List (Step W Y)) (ds : List Fmt.Drawn) (c c' : Core S W Y),
    chainSteps B rows look v bs hs = .ok ss → Chained L bs ss ds c c' →
    c.mid.isSome = c.ver.isSome →
    c'.mid.isSome = c'.ver.isSome ∧ ∃ suf, c'.laid = c.laid ++ suf ∧
      ∀ m', c'.mid = some m' → ∃ m, c.mid = some m ∧
        m'.st = dryFold (ss.map Step.hand) ds m.st ∧ m'.loc = m.loc ++ ds ∧
        m'.seen = m.seen ++ roundsOf suf
  | [], ss, ds, c, c', _, hC, hb => by
    rw [Chained] at hC
    obtain ⟨rfl, rfl, rfl⟩ := hC
    exact ⟨hb, [], (List.append_nil _).symm, fun m' hm =>
      ⟨m', hm, rfl, (List.append_nil _).symm, (List.append_nil _).symm⟩⟩
  | b :: bs, ss, ds, c, c', hss, hC, hb => by
    obtain ⟨ho, l, hl, hcase⟩ := chainSteps_cons_ok hss
    rw [Chained] at hC
    obtain ⟨y, cols, hy, -, hC'⟩ := hC
    have hzl : (b.rounds.zip b.oracles).length = b.rounds.length := by
      rw [List.length_zip, ho, Nat.min_self]
    obtain ⟨sb, hsb, hstates, hpart⟩ : ∃ sb : List (Step W Y), ss = sb ++ l ∧
        (sb.map fun s => (s.decl, s.oracles)) = b.rounds.zip b.oracles ∧
        ∀ s ∈ sb, s.move.isSome = false → s.addr.part = 0 := by
      rcases hcase with ⟨-, h2⟩ | ⟨g, cc, -, h2, -, -, h5⟩
      · exact ⟨bareStepsR b, h2, bare_states b, fun s hs' _ => (bare_moves b s hs').2⟩
      · have hmv' : ∀ s ∈ g.steps b v cc, s.move.isSome = false → s.addr.part = 0 := by
          intro s hs' hf
          rw [row_moves g b v cc h2 ho s hs'] at hf
          cases hf
        exact ⟨g.steps b v cc, h5, row_states g b v cc h2 ho, hmv'⟩
    have hsbl : sb.length = b.rounds.length := by
      have e := congrArg List.length hstates
      rw [List.length_map, hzl] at e
      exact e
    have htake : ss.take b.rounds.length = sb := by rw [hsb]; exact List.take_left' hsbl
    have hdrop : ss.drop b.rounds.length = l := by rw [hsb]; exact List.drop_left' hsbl
    rw [htake] at hy
    rw [hdrop] at hC'
    have hown := lays_draws _ _ _ _ hy
    -- after the sub-protocol the two are both there, or neither is
    have hnext : (c.next L b y cols).mid.isSome = (c.next L b y cols).ver.isSome := by
      show (if (c.next L b y cols).ver.isSome then y.2.map (·.took cols) else none).isSome = _
      cases hvn : (c.next L b y cols).ver with
      | none => rfl
      | some s' =>
        have hcv : c.ver.isSome = true := by
          cases hcv : c.ver with
          | some _ => rfl
          | none =>
            have : (c.next L b y cols).ver = none := by
              show (c.ver.bind fun s => _) = none
              rw [hcv]
              rfl
            rw [this] at hvn
            cases hvn
        rw [← hb] at hcv
        obtain ⟨m, hmm⟩ := Option.isSome_iff_exists.1 hcv
        rw [hmm] at hy
        obtain ⟨m', e, -⟩ := lays_after hpart hy
        show (if (some s').isSome = true then y.2.map (·.took cols) else none).isSome = true
        have hsome : (some s').isSome = true := rfl
        rw [if_pos hsome, e]
        rfl
    obtain ⟨h1, suf, h2, h3⟩ := chained_mid bs l (ds.drop b.rounds.length) (c.next L b y cols) c'
      hl hC' hnext
    refine ⟨h1, y.1 ++ suf, ?_, ?_⟩
    · rw [h2]
      show c.laid ++ y.1 ++ suf = _
      rw [List.append_assoc]
    · intro m' hm'
      obtain ⟨m₁, hm₁, p1, p2, p3⟩ := h3 m' hm'
      have hm₁' : (if (c.next L b y cols).ver.isSome then y.2.map (·.took cols) else none) =
          some m₁ := hm₁
      have hy2 : y.2.map (·.took cols) = some m₁ := by
        by_cases hvs : (c.next L b y cols).ver.isSome = true
        · rw [if_pos hvs] at hm₁'
          exact hm₁'
        · rw [if_neg hvs] at hm₁'
          cases hm₁'
      cases hcm : c.mid with
      | none =>
        rw [hcm] at hy
        have e := lays_sub _ _ _ hy
        rw [e] at hy2
        simp at hy2
      | some m =>
        rw [hcm] at hy
        obtain ⟨m₂, e, -, a2, a3, a4⟩ := lays_after hpart hy
        rw [e] at hy2
        have em : m₂.took cols = m₁ := Option.some.inj hy2
        subst em
        have q1 : m'.st = dryFold (l.map Step.hand) (ds.drop b.rounds.length) m₂.st := p1
        have q2 : m'.loc = m₂.loc ++ ds.drop b.rounds.length := p2
        have q3 : m'.seen = m₂.seen ++ roundsOf suf := p3
        refine ⟨m, rfl, ?_, ?_, ?_⟩
        · conv_rhs => rw [hsb, ← List.take_append_drop b.rounds.length ds, List.map_append,
            dryFold_append _ _ _ _ _ (by rw [List.length_map, hown])]
          rw [q1, a3]
        · rw [q2, a4, List.append_assoc, List.take_append_drop]
        · rw [q3, a2, List.append_assoc]
          unfold roundsOf
          rw [List.map_append]

/-! ## 2 What has been read -/

/-- Columns that are filled with nothing to fall back on: each read has words. -/
theorem fill_words : ∀ (qs : List Read) (cols : List OpenedColumn), fillCols qs [] = .ok cols →
    ∀ q ∈ qs, q.words.isSome = true
  | [], _, _, q, hq => by cases hq
  | r :: qs, cols, h, q, hq => by
    cases hw : r.words with
    | none => simp [fillCols, hw] at h
    | some w =>
      simp only [fillCols, hw] at h
      split at h
      · cases h
      cases hrec : fillCols qs ([] : List OpenedColumn).tail with
      | error e =>
        rw [hrec] at h
        cases h
      | ok l =>
        rcases List.mem_cons.1 hq with e | e
        · rw [e, hw]
          rfl
        · exact fill_words qs l hrec q e

/-- **What a chain's sub-protocols have read**, where there are as many `Step`s as the sub-protocols
have rounds, and as many challenges. -/
theorem chained_reads {L : Lay} :
    ∀ (bs : List (Block S Cl)) (ss : List (Step W Y)) (ds : List Fmt.Drawn) (c c' : Core S W Y),
    Chained L bs ss ds c c' → ss.length = (bs.map (·.rounds.length)).sum → ds.length = ss.length →
    ∃ new, c'.reads = c.reads ++ new ∧
      new.map Read.bare = readsOf L.chain L.firstTree (fun _ _ => none) (fun _ => none)
        (bs.flatMap (·.rounds)) ds ∧
      ∀ q ∈ new, q.words.isSome = true ∧ ∃ l₁ l₂ b own, c'.laid = l₁ ++ l₂ ∧ b ∈ bs ∧
        q ∈ readsOf L.chain L.firstTree L.stored (L.tree l₁) b.rounds own
  | [], ss, ds, c, c', hC, _, _ => by
    rw [Chained] at hC
    obtain ⟨rfl, rfl, rfl⟩ := hC
    exact ⟨[], (List.append_nil _).symm, by simp [readsOf], fun q hq => by cases hq⟩
  | b :: bs, ss, ds, c, c', hC, hl, hd => by
    rw [Chained] at hC
    obtain ⟨y, cols, hy, hc, hC'⟩ := hC
    simp only [List.map_cons, List.sum_cons] at hl
    have hown := lays_draws _ _ _ _ hy
    have htl : (ss.take b.rounds.length).length = b.rounds.length := by
      rw [List.length_take]
      omega
    obtain ⟨new, h1, h2, h3⟩ := chained_reads bs (ss.drop b.rounds.length)
      (ds.drop b.rounds.length) (c.next L b y cols) c' hC' (by rw [List.length_drop]; omega)
      (by rw [List.length_drop, List.length_drop, hd])
    have hdr : y.1.map (·.drawn) = ds.take b.rounds.length := lays_drawn _ _ _ _ hy
    -- the chain's rounds at its end extend the sub-protocol's
    obtain ⟨suf, hsuf⟩ := chained_laid bs _ _ _ _ hC'
    refine ⟨readsOf L.chain L.firstTree L.stored (L.tree (c.laid ++ y.1)) b.rounds
      (y.1.map (·.drawn)) ++ new, ?_, ?_, ?_⟩
    · rw [h1]
      show c.reads ++ _ ++ new = _
      rw [List.append_assoc]
    · rw [List.map_append, readsOf_bare, h2, hdr, List.flatMap_cons]
      conv_rhs => rw [← List.take_append_drop b.rounds.length ds]
      rw [readsOf_append _ _ _ _ _ _ _ _ (by rw [hown, htl])]
    · intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · exact ⟨fill_words _ _ hc q hq, c.laid ++ y.1, suf, b, _, hsuf,
          List.mem_cons.2 (Or.inl rfl), hq⟩
      · obtain ⟨w1, l₁, l₂, b', own, e1, e2, e3⟩ := h3 q hq
        exact ⟨w1, l₁, l₂, b', own, e1, List.mem_cons_of_mem _ e2, e3⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.lays_drawn
#print axioms ProofFile.Honest.chained_laid
#print axioms ProofFile.Honest.chained_mid
#print axioms ProofFile.Honest.fill_words
#print axioms ProofFile.Honest.chained_reads
