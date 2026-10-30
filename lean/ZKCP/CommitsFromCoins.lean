-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/CommitsFromCoins.lean: the form of a committer that samples one number and then computes.

`Arg.CommitsFromCoins A commit` says of a scheme A (ZKCP/Defs.lean) that its committer samples one
number, computes the verifier's key (`IVK`) from the index and that number without sampling again,
and returns the index with that number as the prover's key (`ISK`).
Beside the definition:
  `Arg.eq_of_parts`                          two schemes with the same three algorithms are equal
  `OComp.QueryBound.of_mapO`                 a bound on an algorithm followed by a function holds
                                             for the algorithm
and, for a scheme of this form:
  `Arg.CommitsFromCoins.queryBound_commit`   a bound on the committer's queries holds at each number
  `Arg.CommitsFromCoins.queryBound_C`        and the other way round
The file does not say that any scheme has this form.
-/
import ZKCP.KeyTag

set_option autoImplicit false

namespace ZKCP

variable {lam : ℕ} {I X W IVK ISK Pf : Type}

/-! ## 1. The form -/

/-- The form of a committer that samples first. It samples one number from 0, …, `bound`; from the
index and that number it computes the verifier's key by `commit`, which samples nothing; the
prover's key is the index with that number. -/
structure Arg.CommitsFromCoins {bound : ℕ} (A : Arg lam I X W IVK (I × Fin (bound + 1)) Pf)
    (commit : I → Fin (bound + 1) → OComp lam IVK) : Prop where
  committer : ∀ i, A.C i = .sample bound fun coins =>
    (commit i coins).mapO fun key => (key, (i, coins))
  noCoin : ∀ i coins, (commit i coins).DrawsNoCoin

/-! ## 2. Two general facts -/

/-- Two schemes with the same committer, the same prover and the same verifier are equal. -/
theorem Arg.eq_of_parts {A B : Arg lam I X W IVK ISK Pf} (hC : A.C = B.C) (hP : A.P = B.P)
    (hV : A.V = B.V) : A = B :=
  calc A = ⟨A.C, A.P, A.V⟩ := rfl
    _ = ⟨B.C, B.P, B.V⟩ := by rw [hC, hP, hV]
    _ = B := rfl

/-- If an algorithm followed by a function of its result makes at most t queries, so does the
algorithm. The converse is `OComp.QueryBound.mapO` (ZKCP/KeyTag.lean). -/
theorem OComp.QueryBound.of_mapO {α β : Type} (h : α → β) :
    ∀ (c : OComp lam α) (t : ℕ), (c.mapO h).QueryBound t → c.QueryBound t
  | .pure _, _, _ => trivial
  | .query _ _, 0, hc => False.elim hc
  | .query _ k, t + 1, hc => fun r => OComp.QueryBound.of_mapO h (k r) t
      ((show ∀ r, ((k r).mapO h).QueryBound t from hc) r)
  | .sample _ k, t, hc => fun r => OComp.QueryBound.of_mapO h (k r) t
      ((show ∀ r, ((k r).mapO h).QueryBound t from hc) r)

/-! ## 3. The committer's queries -/

namespace Arg.CommitsFromCoins

variable {bound : ℕ} {A : Arg lam I X W IVK (I × Fin (bound + 1)) Pf}
  {commit : I → Fin (bound + 1) → OComp lam IVK}

/-- For a scheme of this form (`h`): if the committer makes at most t queries at the index i, then
`commit i coins` makes at most t queries at every number `coins`. -/
theorem queryBound_commit (h : A.CommitsFromCoins commit) (i : I) (t : ℕ)
    (hC : (A.C i).QueryBound t) (coins : Fin (bound + 1)) : (commit i coins).QueryBound t := by
  rw [h.committer i] at hC
  exact OComp.QueryBound.of_mapO _ (commit i coins) t
    ((show ∀ coins, ((commit i coins).mapO fun key => (key, (i, coins))).QueryBound t from hC)
      coins)

/-- For a scheme of this form (`h`): if `commit i coins` makes at most t queries at every number
`coins`, then the committer makes at most t queries at the index i. -/
theorem queryBound_C (h : A.CommitsFromCoins commit) (i : I) (t : ℕ)
    (hc : ∀ coins, (commit i coins).QueryBound t) : (A.C i).QueryBound t := by
  rw [h.committer i]
  exact show ∀ coins, ((commit i coins).mapO fun key => (key, (i, coins))).QueryBound t from
    fun coins => OComp.QueryBound.mapO _ (commit i coins) t (hc coins)

end Arg.CommitsFromCoins

end ZKCP
