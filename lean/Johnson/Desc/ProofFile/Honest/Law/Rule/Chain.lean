-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Chain.lean: a chain's walk (Honest/Walk.lean) that goes
through (returns without an error), sub-protocol by sub-protocol of the description's flat list. A
walk (`ChainProgress`, `walk`) takes a chain's rounds one at a time and carries both the state of the
prover's run and the verifier's state. The sub-protocol's rounds are produced (`lays`,
Honest/Law/Rule/WalkLaw.lean); its columns are filled from the tables produced so far; the
verifier's step is asked (`judge`); where it accepts, the state of the prover's run takes these
columns (`Mid.took`: none where no columns are handed); where it rejects, or has rejected before,
nothing more is played.

  1  `lays_lengthR`, `walk_length`   as many rounds as `Step`s; as many challenges as `Step`s
  2  `Core`, `ChainProgress.core`, `Core.next`, `Chained`   what of a walk the chain's course depends on;
     after one sub-protocol; the course as a proposition, by recursion on the sub-protocols
  3  `chained_of_walk`, `chained_of_start`   a walk that goes through, over as many `Step`s as the
     sub-protocols have rounds, has that course

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.WalkLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place Oracle OpenedColumn)

variable {S Cl W Y : Type}

/-! ## 1 Lengths -/

theorem lays_lengthR : ∀ (l : List (Step W Y)) (ds : List Fmt.Drawn) (m : Option (Mid W Y))
    (y : List Played × Option (Mid W Y)), lays l ds m = .ok y → y.1.length = l.length
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
    exact congrArg (· + 1) (lays_lengthR l ds m' y' hy)

theorem walk_length {L : Lay} : ∀ (ss : List (Step W Y)) (ds : List Fmt.Drawn)
    (z z' : ChainProgress S Cl W Y), walk L ss ds z = .ok z' → ds.length = ss.length
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp [walk] at h
  | _ :: _, [], _, _, h => by simp [walk] at h
  | s :: ss, d :: ds, z, z', h => by
    obtain ⟨x, z₁, -, -, h⟩ := walk_cons_ok h
    exact congrArg (· + 1) (walk_length ss ds z₁ z' h)

/-! ## 2 The course -/

/-- What of a walk the chain's course depends on. -/
structure Core (S W Y : Type) where
  mid : Option (Mid W Y)
  ver : Option S
  laid : List Played
  reads : List Read
  cols : List OpenedColumn

/- These five fields of a walk; `refused`, `todo` and `own` are dropped. -/
def ChainProgress.core (z : ChainProgress S Cl W Y) : Core S W Y := ⟨z.mid, z.ver, z.laid, z.reads, z.cols⟩

/-- After a sub-protocol. `y`: its rounds as produced, and the state of the prover's run after them.
`cols`: its columns. The verifier's step is asked; where it accepts, the state takes these columns
(`Mid.took`); where it rejects, nothing more is played. -/
def Core.next (L : Lay) (b : Block S Cl) (c : Core S W Y) (y : List Played × Option (Mid W Y))
    (cols : List OpenedColumn) : Core S W Y :=
  ⟨if (c.ver.bind fun s => judge L.firstTree b s (roundsOf y.1) cols).isSome
      then y.2.map (·.took cols) else none,
    c.ver.bind fun s => judge L.firstTree b s (roundsOf y.1) cols, c.laid ++ y.1,
    c.reads ++ readsOf L.chain L.firstTree L.stored (L.tree (c.laid ++ y.1)) b.rounds
      (y.1.map (·.drawn)), c.cols ++ cols⟩

/-- **A chain's course, sub-protocol by sub-protocol.** -/
def Chained (L : Lay) : List (Block S Cl) → List (Step W Y) → List Fmt.Drawn → Core S W Y →
    Core S W Y → Prop
  | [], ss, ds, c, c' => ss = [] ∧ ds = [] ∧ c' = c
  | b :: bs, ss, ds, c, c' =>
    ∃ y cols, lays (ss.take b.rounds.length) (ds.take b.rounds.length) c.mid = .ok y ∧
      fillCols (readsOf L.chain L.firstTree L.stored (L.tree (c.laid ++ y.1)) b.rounds
        (y.1.map (·.drawn))) [] = .ok cols ∧
      Chained L bs (ss.drop b.rounds.length) (ds.drop b.rounds.length) (c.next L b y cols) c'

/-! ## 3 A walk that goes through -/

theorem chained_of_walk {L : Lay} : ∀ (bs : List (Block S Cl)) (ss : List (Step W Y))
    (ds : List Fmt.Drawn) (z a z' : ChainProgress S Cl W Y), z.own = [] → ChainProgress.settle L bs z = .ok a →
    walk L ss ds a = .ok z' → ss.length = (bs.map (·.rounds.length)).sum →
    Chained L bs ss ds z.core z'.core
  | [], ss, ds, z, a, z', _, ha, hw, hl => by
    rw [ChainProgress.settle] at ha
    cases ha
    have hd := walk_length ss ds _ z' hw
    have hs : ss = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst hs
    have hd' : ds = [] := List.eq_nil_of_length_eq_zero (by simpa using hd)
    subst hd'
    have e := walk_nil_ok hw
    subst e
    rw [Chained]
    exact ⟨rfl, rfl, rfl⟩
  | b :: bs, ss, ds, z, a, z', hown, ha, hw, hl => by
    obtain ⟨mid, ver, refused, laid, reads, cols₀, todo, own⟩ := z
    have hown' : own = [] := hown
    subst hown'
    have hd := walk_length ss ds a z' hw
    simp only [List.map_cons, List.sum_cons] at hl
    by_cases hn : 0 < b.rounds.length
    · have hsw := settle_wait L b bs
        (⟨mid, ver, refused, laid, reads, cols₀, todo, []⟩ : ChainProgress S Cl W Y) hn
      rw [hsw] at ha
      cases ha
      have hw' : walk L (ss.take b.rounds.length ++ ss.drop b.rounds.length)
          (ds.take b.rounds.length ++ ds.drop b.rounds.length)
          (⟨mid, ver, refused, laid, reads, cols₀, b :: bs, []⟩ : ChainProgress S Cl W Y) = .ok z' := by
        rw [List.take_append_drop, List.take_append_drop]
        exact hw
      have hlen : (ss.take b.rounds.length).length = b.rounds.length := by
        rw [List.length_take]
        omega
      obtain ⟨z₁, h1, h2⟩ := walk_append_ok (ss.drop b.rounds.length) (ds.drop b.rounds.length)
        (ss.take b.rounds.length) (ds.take b.rounds.length) _ z'
        (by rw [List.length_take, List.length_take, hd]) hw'
      obtain ⟨y, hy, hs⟩ := member_ok (ss.take b.rounds.length) (ds.take b.rounds.length)
        (⟨mid, ver, refused, laid, reads, cols₀, b :: bs, []⟩ : ChainProgress S Cl W Y) z₁ rfl
        (by
          show ([] : List Played).length + (ss.take b.rounds.length).length = b.rounds.length
          rw [hlen]
          exact Nat.zero_add _)
        (by
          intro e
          have h0 : (ss.take b.rounds.length).length = 0 := by rw [e]; rfl
          omega) h1
      have hy1 := lays_lengthR _ _ _ _ hy
      obtain ⟨cols, hc, hs'⟩ := settle_ask_ok (by
        show ¬ ([] ++ y.1).length < b.rounds.length
        rw [List.nil_append, hy1, hlen]
        omega) hs
      have ih := chained_of_walk bs (ss.drop b.rounds.length) (ds.drop b.rounds.length) _ z₁ z' rfl
        hs' h2 (by
          rw [List.length_drop]
          omega)
      rw [Chained]
      exact ⟨y, cols, hy, hc, ih⟩
    · have hz : b.rounds.length = 0 := by omega
      obtain ⟨cols, hc, hs'⟩ := settle_ask_ok (by
        show ¬ ([] : List Played).length < b.rounds.length
        rw [hz]
        exact Nat.lt_irrefl 0) ha
      have ih := chained_of_walk bs ss ds _ a z' rfl hs' hw (by omega)
      rw [Chained]
      refine ⟨([], mid), cols, ?_, ?_, ?_⟩
      · rw [hz, List.take_zero, List.take_zero, lays]
        rfl
      · show fillCols (readsOf L.chain L.firstTree L.stored (L.tree (laid ++ [])) b.rounds []) [] =
          .ok cols
        rw [List.append_nil]
        exact hc
      · rw [hz, List.drop_zero, List.drop_zero]
        have e : (⟨mid, ver, laid, reads, cols₀⟩ : Core S W Y).next L b ([], mid) cols =
            ⟨if (ver.bind fun s => judge L.firstTree b s (roundsOf []) cols).isSome
              then mid.map (·.took cols)
              else none, ver.bind fun s => judge L.firstTree b s (roundsOf []) cols, laid,
              reads ++ readsOf L.chain L.firstTree L.stored (L.tree laid) b.rounds [],
              cols₀ ++ cols⟩ := by
          unfold Core.next
          simp only [List.append_nil, List.map_nil]
        show Chained L bs ss ds
          ((⟨mid, ver, laid, reads, cols₀⟩ : Core S W Y).next L b ([], mid) cols) z'.core
        rw [e]
        exact ih

/-- **From a chain's start.** `m`, `v`: the state of the prover's run and the verifier's state.
`front`: the columns of earlier chains that this chain's parts are handed; what `m` held in the
field `opened` is dropped. -/
theorem chained_of_start {L : Lay} {bs : List (Block S Cl)} {ss : List (Step W Y)}
    {ds : List Fmt.Drawn} {m : Option (Mid W Y)} {v : Option S} {a z' : ChainProgress S Cl W Y}
    {front : List OpenedColumn} (ha : ChainProgress.start L bs m v front = .ok a) (hw : walk L ss ds a = .ok z')
    (hl : ss.length = (bs.map (·.rounds.length)).sum) :
    Chained L bs ss ds
      ⟨if v.isSome then m.map ({ · with opened := some front }) else none,
        if m.isSome then v else none, [], [], []⟩
      z'.core :=
  chained_of_walk bs ss ds _ a z' rfl ha hw hl

end ProofFile.Honest

#print axioms ProofFile.Honest.lays_lengthR
#print axioms ProofFile.Honest.walk_length
#print axioms ProofFile.Honest.chained_of_walk
#print axioms ProofFile.Honest.chained_of_start
#print axioms ProofFile.Honest.Core
#print axioms ProofFile.Honest.ChainProgress.core
#print axioms ProofFile.Honest.Core.next
#print axioms ProofFile.Honest.Chained
