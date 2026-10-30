-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/OnFrom.lean: a side's hypothesis beside `Good`
(Honest/Side.lean): the list's condition at a part's entry follows from the invariant. `Good.exact`
takes a parameter On as a hypothesis: a condition on what the part carries, the state of the run
before it, and what has been shown before. Here is the form in which a kind's author has to prove
that condition: from the state of a run inside the sub-protocol (`Inside`, Honest/Thread/Pays.lean),
at every `front` that is true to that state. Four definitions, two of them (`TrueTo`, `OnFrom`)
meant as hypotheses; and what `Inside` gives an author, as lemmas. General in the `Thread`'s
parameters: no kind is named; no description, no list of challenges and no run occurs.

  1  `Side.off`, `treeSrc`, `TrueTo`   how many of the sub-protocol's rounds come before a part; a
     tree's name as a chain sees it; a `front` that is true to a state and the available tables
  2  `OnFrom`   the hypothesis
  3  `inside_front`, `inside_valid`, `inside_stored`   what `Inside` gives
  4  `trueTo_mono`   a greater len: a weaker condition

True to. The `front` shows the rounds that the prover's run has seen (`seen`: these rounds); it
lists every tree that is available; every column that it lists of such a tree is that table's own,
at a position below 2 ^ len c j; every stored column that it lists is the stored table's own. `len`:
for tree number j of chain number c, a bound on the depth at which the plan opens it: a parameter
here: no description occurs. The invariant's clause on the available tables speaks of a table's
columns below its length alone: so an author who uses that clause on a listed column proves, of its
own parameters: len c j is at most the logLength of its `Thread`'s table at that tree. A greater len
makes `TrueTo` weaker (`trueTo_mono`) and the hypothesis harder. It is proved of the `front` that
rounds as produced give, at one len: `depthAt F` (`trueTo_one`, `trueTo_two`, `trueTo_three`,
Honest/Law/Rule/TrueLaid.lean; the three as one: `trueLaid_depth`, Johnson/T3/OwedMixed.lean): so
that is where an author proves it.

What On may read of `front`, if it is to be proved through this form: the rounds seen; the columns
listed of trees that are available; the stored columns listed. Not: a round's chain number; how the
roots are grouped by rounds; how many trees are listed above the available ones; that a given
position is listed. `TrueTo` holds of values of `front` that no run gives, and says less than a
run's own `front` does: an On that asks one of these as a run's own `front` has it is true at every
run and still cannot be proved here.

Met trivially.
  (1) Where `Inside T b n` never holds: an invariant that cannot hold at the start; a list whose
      earlier parts never play.
  (2) On is a parameter that the side's author chooses: at On := True the hypothesis holds trivially
      and `Good.exact` has to hold at every state: that is the right choice where the part's
      simulator reads nothing of `front`; at On := the equation of `exact` itself `Good.exact` says
      nothing and all of it lies here: so `Good` and `OnFrom` count at one On, together, or not at
      all.
  (3) `TrueTo` is a hypothesis inside `OnFrom`: were no `front` true to a state, `OnFrom` would hold
      vacuously: that the `front` which rounds as produced give is true to these rounds is proved,
      chain by chain, in Honest/Law/Rule/TrueLaid.lean (`trueTo_one`, `trueTo_two`, `trueTo_three`).

What `Inside` does not give. That the tables which the list's earlier parts have sent are the
`Thread`'s functions: that clause has to be proved at the sub-protocol's end (`Plays`): inside a
list an author reads the definitions of its own earlier parts.

Limits.
  * It is not proved that the hypothesis can be met.
  * None is one of the library's goals.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.InsideLaw
import Johnson.Desc.ProofFile.Honest.Thread.PaysLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-! ## 1 The parameters -/

/-- How many of the sub-protocol's rounds come before its part number j: as `membersOf` cuts the
list: each part as many rounds as it has moves. -/
def Side.off (σ : Side S Cl V W X Pb) (j : Nat) : Nat :=
  ((σ.row.take j).map fun x => x.1.moves.length).sum

/-- Tree number j of chain number c, as chain number ch names it. -/
def treeSrc (ch c j : Nat) : Fmt.TreeSource := if c == ch then .own j else .taken c j

/-- **A `front` is true to a state and the available tables.** It is a definition, meant as a
hypothesis. Nothing is claimed of it, and it is none of the library's goals. -/
def TrueTo (ch : Nat) (len : Nat → Nat → Nat) (front : Before) (seen : List Fmt.RoundView) (E : Env) :
    Prop :=
  front.seen = seen ∧
    (∀ c j pt, E.tree (treeSrc ch c j) = some pt → ∃ cols, front.treeCols c j = some cols ∧
      ∀ q ∈ cols, q.1 < 2 ^ len c j ∧ q.2 = pt.2.col q.1) ∧
    ∀ q ∈ front.stored, E.stored q.1 q.2.1 = some q.2.2

/-! ## 2 The hypothesis -/

/-- **On follows from the invariant**, at sub-protocol number b, whose list is L: at each part u of
the list: at the state of the run after the rounds of the list's parts before u, at what the book
gives u as carried, at every `front` that is true to that state: the list's own condition at the
entry holds. It is a definition, meant as a hypothesis. Nothing is claimed of it, and it is none of
the library's goals. -/
def OnFrom (T : Thread Bk S Cl V W X Pb) (L : Lettered Bk S Cl V W X Pb) (b : Nat)
    (len : Nat → Nat → Nat) : Prop :=
  ∀ σ, L.side T.bs = some σ → ∀ u ∈ σ.members, ∀ k m E ca front,
    Inside T b (σ.off u.number) k m E →
    carriedAt Bk k T.chain ⟨L.place, u.number⟩ u.part = .ok ca →
    TrueTo T.chain len front m.seen E → L.On u ca m front

/-! ## 3 What `Inside` gives -/

variable (T : Thread Bk S Cl V W X Pb)

/-- **Inside a sub-protocol**: the whole invariant at a state before it; the input is that state's;
what was heard and seen is that state's and the rounds played since; the tables available there are
still available. -/
theorem inside_front {b n : Nat} {k : Coins Bk} {m : Mid W X} {E : Env}
    (h : Inside T b n k m E) :
    ∃ (s : S) (m₀ : Mid W X) (E₀ : Env) (ps : List Played) (ds : List Fmt.Drawn),
      Thr T b k s m₀ E₀ ∧ m.st.input = m₀.st.input ∧ m.st.heard = m₀.st.heard ++ ds ∧
        m.seen = m₀.seen ++ roundsOf ps ∧ E = E₀.add ps ∧
        ∀ σ pt, E₀.tree σ = some pt → E.tree σ = some pt := by
  unfold Inside at h
  obtain ⟨blk, s, m₀, E₀, l, ds, y, -, hA, -, -, hy, rfl, rfl⟩ := h
  obtain ⟨hi, -, hs⟩ := play_mid _ _ _ _ _ hy
  refine ⟨s, m₀, E₀, y.1, ds, hA, hi, play_heard _ _ _ _ _ hy, hs, rfl, fun σ pt hσ => ?_⟩
  have hA' := hA
  unfold Thr Thread.Made at hA'
  have hT : ∀ n, E₀.sent ≤ n → E₀.tree (.own n) = none := hA'.2.2.2.2.1.2.2.2.1
  cases σ with
  | own j =>
    show (if j < E₀.sent then E₀.tree (.own j) else _) = some pt
    by_cases hj : j < E₀.sent
    · rw [if_pos hj]
      exact hσ
    · rw [hT j (Nat.le_of_not_lt hj)] at hσ
      cases hσ
  | taken c j => exact hσ

/-- The input inside a sub-protocol is one of which something is to be stated. -/
theorem inside_valid {b n : Nat} {k : Coins Bk} {m : Mid W X} {E : Env}
    (h : Inside T b n k m E) : T.valid m.st.input := by
  obtain ⟨s, m₀, E₀, ps, ds, hA, hi, -, -, -, -⟩ := inside_front T h
  unfold Thr at hA
  rw [hi]
  exact hA.2.2.2.2.2.2

/-- The stored columns available inside a sub-protocol are the `Thread`'s, at the state's own input.
-/
theorem inside_stored {b n : Nat} {k : Coins Bk} {m : Mid W X} {E : Env}
    (h : Inside T b n k m E) : ∀ i x, E.stored i x = T.stored m.st.input i x := by
  obtain ⟨s, m₀, E₀, ps, ds, hA, hi, -, -, rfl, -⟩ := inside_front T h
  unfold Thr Thread.Hand at hA
  intro i x
  rw [hi]
  exact hA.1.1 i x

/-! ## 4 A greater len -/

theorem trueTo_mono {ch : Nat} {len len' : Nat → Nat → Nat} {front : Before} {seen : List Fmt.RoundView}
    {E : Env} (hl : ∀ c j, len c j ≤ len' c j) (h : TrueTo ch len front seen E) :
    TrueTo ch len' front seen E := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, fun c j pt hpt => ?_, h3⟩
  obtain ⟨cols, hc, hq⟩ := h2 c j pt hpt
  exact ⟨cols, hc, fun q hqm => ⟨Nat.lt_of_lt_of_le (hq q hqm).1
    (Nat.pow_le_pow_right (by decide) (hl c j)), (hq q hqm).2⟩⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.inside_front
#print axioms ProofFile.Honest.inside_valid
#print axioms ProofFile.Honest.inside_stored
#print axioms ProofFile.Honest.trueTo_mono
