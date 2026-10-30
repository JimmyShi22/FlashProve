-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/LinkOf.lean: a code of the link's chain queries from a code of its first query and a
code of its later rounds' queries.

OnBytes/TypedOracleCompiler/Run/SeedPage.lean takes any `LinkCode`. Here one is made of two parts, told apart by the
typed round: a code f0 of first queries, whose strings have the form of a call 160 under the link's
label, written at the block of the chain value; and a code pR of later queries with a block, whose
strings have the form of a call 162 under that label.

Main definitions: `linkOf`; `roundsAlong` (a code of later queries over one interface, carried to
another along a pair of OnBytes/TypedOracleCompiler/Run/LinkAlong.lean).
Main theorems.
 `linkOf_first`   at a query of round 0, at the last block: what f0 writes.
 `linkOf_round`   at a query of another round: what pR writes.
 `roundsAlong_put`, `roundsAlong_is`.

Not claimed. No code is given here. The blocks of a first query's answer other than the chain value
have no string. Nothing on soundness.


-/
import OnBytes.TypedOracleCompiler.Run.LinkAlong

set_option autoImplicit false

namespace TypedOracleCompiler.Run.LinkOf
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Run.Apart TypedOracleCompiler.Run.SeamAt TypedOracleCompiler.Run.PutSome
open TypedOracleCompiler.Run.SeedPage TypedOracleCompiler.Run.LinkAlong
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ} (l : ℕ) (hlt : l < 2 ^ 48)
  (hne : l ≠ _root_.Fmt.recordLabel) (f0 : PCode (FbIn 256 L .link))
  (h0 : ∀ q s, f0.put q = some s → Is160 l s) (pR : PCode (FbIn 256 L .link × Fin (K + 1)))
  (hR : ∀ x s, pR.put x = some s → Is162 l s)

/-- **The link's chain queries, by the typed round.** -/
def linkOf : LinkCode L K where
  pL := split (tailP f0 K) pR (fun x => decide (x.1.round = 0)) (fun a b s h1 h2 =>
    no_160_162 _ _ hlt s (h0 _ s (tailP_put _ K a s h1).1) (hR b s h2))
  l := l
  hlt := hlt
  hne := hne
  his := fun x s h => by
    rcases split_put _ _ _ _ x s h with h1 | h1
    · exact Or.inl (h0 _ s (tailP_put _ K x s h1).1)
    · exact Or.inr (hR x s h1)

/-- At a query of round 0, at the block of the chain value. -/
theorem linkOf_first (q : FbIn 256 L .link) (hq : q.round = 0) (s : List Bool)
    (h : f0.put q = some s) : (linkOf l hlt hne f0 h0 pR hR).pL.put (q, Fin.last K) = some s := by
  show (split _ _ _ _).put _ = _
  rw [split_true _ _ (fun x : FbIn 256 L .link × Fin (K + 1) => decide (x.1.round = 0)) _
    (q, Fin.last K) (decide_eq_true hq)]
  exact tailP_some _ K _ _ h

/-- At a query of another round. -/
theorem linkOf_round (q : FbIn 256 L .link) (hq : q.round ≠ 0) (j : Fin (K + 1)) :
    (linkOf l hlt hne f0 h0 pR hR).pL.put (q, j) = pR.put (q, j) := by
  show (split _ _ _ _).put _ = _
  rw [split_false _ _ (fun x : FbIn 256 L .link × Fin (K + 1) => decide (x.1.round = 0)) _
    (q, j) (decide_eq_false hq)]

variable {I1 X1 : Type} {L1 : BatchProtocolWithLeafBody I1 X1}

/-- A code of later queries over L1, carried to L along a pair. -/
def roundsAlong (F : FbPair L1 L) (p1 : PCode (FbIn 256 L1 .link × Fin (K + 1))) :
    PCode (FbIn 256 L .link × Fin (K + 1)) :=
  p1.pull F.selB F.mkB F.mkB_selB F.selB_mkB

/-- What it writes at a query that is read as q1. -/
theorem roundsAlong_put (F : FbPair L1 L) (p1 : PCode (FbIn 256 L1 .link × Fin (K + 1)))
    (q2 : FbIn 256 L .link) (q1 : FbIn 256 L1 .link) (h : F.sel q2 = some q1) (j : Fin (K + 1)) :
    (roundsAlong F p1).put (q2, j) = p1.put (q1, j) := by
  show (F.selB (q2, j)).bind _ = _
  have e : F.selB (q2, j) = some (q1, j) := by
    show (F.sel q2).map _ = _
    rw [h]
    rfl
  rw [e]
  rfl

/-- Its strings have the form that the given code's have. -/
theorem roundsAlong_is (F : FbPair L1 L) (p1 : PCode (FbIn 256 L1 .link × Fin (K + 1)))
    (h1 : ∀ x s, p1.put x = some s → Is162 l s) (x : FbIn 256 L .link × Fin (K + 1))
    (s : List Bool) (h : (roundsAlong F p1).put x = some s) : Is162 l s := by
  obtain ⟨y, -, hy⟩ := PCode.pull_put _ _ _ _ _ x s h
  exact h1 y s hy

end TypedOracleCompiler.Run.LinkOf
