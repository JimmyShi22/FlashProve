-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ChainEndLaw.lean: the chains' end's law, at the record and at the block. Theorems. THE
LAW IS OF untestedL, refuse AND chainEnd AS THEY STAND IN Johnson/Desc/ChainEnd.lean.

  refuse_ok_iff         a list of named clauses is not refused just where every clause holds.
  NothingLeft T         every group of the statement T has its mark inRun, and every sampled oracle
                        message of T names a group that is there and has that mark.
  untested_spec         refuse (untestedL T) = ok → NothingLeft T.
  programs_of_untested  refuse (untestedL T) = ok → the Boolean expression that the verifier program
                        asks at a chain's end is true at T (every group's test has begun, and every
                        sampled message's list of groups is not empty). The converse fails: a
                        sampled message that names only a group which is not there.
  Asks st ask           the clauses "ask" hold those of untestedL, read by st, among them.
  untested_of_chainEnd  a last block whose clauses hold untestedL's among them says yes only at a
                        state that passes untestedL, and returns that state.
WHAT OF `verify-on-bytes` IS USED: its plain records Statement, Group and Oracle
(OnBytes/Iop/Ground.lean). No routine in a context is reached from a statement or a proof here.
What is not claimed. "Its test has begun" is the mark inRun: nothing on whether the test was carried
through: that is the kind K12's own law. Nothing of a claim that was never laid on a group. Nothing
of the tests on the plan. Nothing on soundness as such, on an honest prover or on hiding.

-/
import Johnson.Desc.ChainEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.ChainEnd
open OnBytes

/-- A list of named clauses is not refused just where every clause holds. -/
theorem refuse_ok_iff (l : Clauses) : refuse l = .ok () ↔ ∀ c ∈ l, c.2 = true := by
  unfold refuse
  split
  · rename_i c h
    constructor
    · intro h'; cases h'
    · intro h'
      have hm := List.mem_of_find?_eq_some h
      have hp := List.find?_some h
      have := h' c hm
      simp [this] at hp
  · rename_i h
    constructor
    · intro _ c hc
      have := List.find?_eq_none.1 h c hc
      simpa using this
    · intro _; rfl

/-- Nothing is left untested at a statement. -/
def NothingLeft (T : Statement) : Prop :=
  (∀ i (hi : i < T.groups.size), (T.groups[i]).inRun = true) ∧
  ∀ i (hi : i < T.oracles.size), (T.oracles[i]).sampled = true →
    ∃ g ∈ (T.oracles[i]).groups, ∃ G, T.groups[g]? = some G ∧ G.inRun = true

/-- The two clauses, out of the list. -/
theorem untested_two (T : Statement) (h : refuse (untestedL T) = .ok ()) :
    T.groups.all (·.inRun) = true ∧
    (T.oracles.all fun x =>
      !x.sampled || x.groups.any fun g => (T.groups[g]?).any (·.inRun)) = true := by
  have h' := (refuse_ok_iff _).1 h
  exact ⟨h' ("end: a proximity test has begun on every group", T.groups.all (·.inRun))
      (show _ ∈ untestedL T from List.Mem.head _),
    h' ("end: every sampled message is in a tested group", T.oracles.all fun x =>
      !x.sampled || x.groups.any fun g => (T.groups[g]?).any (·.inRun))
      (show _ ∈ untestedL T from List.Mem.tail _ (List.Mem.head _))⟩

/-- Where the end's two clauses pass, nothing is left untested. -/
theorem untested_spec (T : Statement) (h : refuse (untestedL T) = .ok ()) : NothingLeft T := by
  obtain ⟨h1, h2⟩ := untested_two T h
  rw [Array.all_eq_true] at h1 h2
  refine ⟨h1, ?_⟩
  intro i hi hs
  have h3 := h2 i hi
  simp only [hs, Bool.not_true, Bool.false_or, List.any_eq_true] at h3
  obtain ⟨g, hg, hG⟩ := h3
  refine ⟨g, hg, ?_⟩
  cases hx : T.groups[g]? with
  | none => simp [hx] at hG
  | some G => exact ⟨G, rfl, by simpa [hx] using hG⟩

/-- Where the end's two clauses pass, the program's own expression at a chain's end is true. -/
theorem programs_of_untested (T : Statement) (h : refuse (untestedL T) = .ok ()) :
    (T.groups.all (·.inRun) && T.oracles.all fun x => !x.sampled || !x.groups.isEmpty) = true := by
  obtain ⟨h1, h2⟩ := untested_two T h
  rw [Bool.and_eq_true]
  refine ⟨h1, ?_⟩
  rw [Array.all_eq_true] at h2 ⊢
  intro i hi
  have h3 := h2 i hi
  cases hs : (T.oracles[i]).sampled
  · simp
  · cases hg : (T.oracles[i]).groups
    · simp [hs, hg] at h3
    · simp

/-- The clauses "ask" hold those of untestedL, read by st, among them. -/
def Asks {S : Type} (st : S → Statement) (ask : S → Clauses) : Prop :=
  ∀ x, ∀ c ∈ untestedL (st x), c ∈ ask x

/-- The end's own clauses hold themselves among them. -/
theorem asks_self {S : Type} (st : S → Statement) : Asks st fun x => untestedL (st x) :=
  fun _ _ hc => hc

/-- Further clauses behind them do not take the end's clauses away. -/
theorem asks_append {S : Type} (st : S → Statement) (more : S → Clauses) :
    Asks st fun x => untestedL (st x) ++ more x :=
  fun _ _ hc => List.mem_append_left _ hc

/-- The last block says yes only at a state that passes the end's clauses, and returns it. -/
theorem untested_of_chainEnd {S Cl : Type} (chain piece : Nat) (sealed : Bool)
    (inFront : List Fmt.DeclaredRound) (st : S → Statement) (ask : S → Clauses) (ha : Asks st ask)
    (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (chainEnd (Cl := Cl) chain piece sealed inFront ask).decide s rs gs = .ok s') :
    s' = s ∧ refuse (untestedL (st s)) = .ok () := by
  simp only [chainEnd] at h
  cases hr : refuse (ask s) with
  | error e => simp [hr, Except.map] at h
  | ok u =>
    simp [hr, Except.map] at h
    refine ⟨h.symm, ?_⟩
    rw [refuse_ok_iff] at hr ⊢
    exact fun c hc => hr c (ha s c hc)

end VerifiableInference.Desc.ChainEnd
