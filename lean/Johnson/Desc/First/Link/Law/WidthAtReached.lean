-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/WidthAtReached.lean: THE CLOSED TEST `okWidthB` (PosLater.lean: the
lengths of
the vectors U1 and U3 are at most their arrays' columns) CARRIED FROM THE PLANNED ARRAYS' COLUMNS,
at
which it can be run, TO THE LEDGER OF A REACHED STATE AND OF A LATER STATE, at which `pos_later`
asks
it. Statements and proofs: calls.

  `colsU_of_looks`: two ledgers whose arrays have the same looks have the same numbers of columns.
  `okWidth_congr`: the test reads the ledger through its numbers of columns alone.
  `okWidth_of_inv`: **`LooksInv (shOfBuilt built) s` (LooksWalk.lean, LooksSeated.lean: where a
ledger and
    a link are open, the ledger has the looks of that link's planned arrays) · s.fork? = some G ·
    s.link? = some L · built[L.link]? = some X · okWidthB nU U (colsU X.Fp) ⊢ okWidthB nU U (colsU
    G).**
  `okWidth_goes`: **`GoesOn v b` (Johnson/Desc/First/Batch/Law/FitsAtS.lean) · okWidthB nU U (colsU
v.F) ⊢
    okWidthB nU U (colsU b.F)**: from the snapshot to every state that goes on from it.
`LooksInv` along "reached" is `looks_at_reached` (Johnson/LPFK9R/LooksSeat.lean: no
premise
but that the IOP is made).
Limits. That the snapshot's ledger is the reached state's own is the caller's. At the planned arrays
the test was EVALUATED true at the 25 links of one stored full-size set of public files: a run, no
theorem. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.PosLater
import Johnson.Desc.First.Link.Law.LooksSeated
import Johnson.Desc.First.Link.Law.FullEq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Tie.Pv.Tail.Port (colsU)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9L

/-- The looks give the numbers of columns, array by array. -/
theorem colsU_of_looks {F G : Fork} (h : G.trees.map look = F.trees.map look) (t : ℕ) :
    colsU G t = colsU F t := by
  have e := congrArg (fun a => (a[t]?).getD 0) (widths_of_looks _ _ h)
  simpa [colsU, Array.getElem?_map] using e

/-- The test reads the ledger through its numbers of columns alone. -/
theorem okWidth_congr (nU : Array ℕ) (U : Array (Option ℕ)) {c c' : ℕ → ℕ} (h : ∀ t, c' t = c t)
    (T : okWidthB nU U c = true) : okWidthB nU U c' = true := by
  have e : c' = c := funext h
  rw [e]
  exact T

/-- **FROM THE PLANNED ARRAYS TO THE LEDGER OF A STATE THAT HAS THE PLAN's LOOKS.** -/
theorem okWidth_of_inv {built : Array Stages.LinkH} {s : S} (hI : LooksInv (shOfBuilt built) s)
    {G : Fork} {L : LinkCtx} (hG : s.fork? = some G) (hL : s.link? = some L) {X : Stages.LinkH}
    (hX : built[L.link]? = some X) (nU : Array ℕ) (U : Array (Option ℕ))
    (T : okWidthB nU U (colsU X.Fp) = true) : okWidthB nU U (colsU G) = true := by
  have h1 : G.trees.toList.map look = X.Fp.trees.toList.map look := by
    have := hI G L hG hL
    unfold LooksAre at this
    rw [this, shOfBuilt_at hX]
  have h2 : G.trees.map look = X.Fp.trees.map look := by
    apply Array.toList_inj.1
    rw [Array.toList_map, Array.toList_map]
    exact h1
  exact okWidth_congr nU U (colsU_of_looks h2) T

/-- **FROM THE SNAPSHOT TO EVERY STATE THAT GOES ON FROM IT.** -/
theorem okWidth_goes {v : Pub9} {b : K9.Part} (h : GoesOn v b) (nU : Array ℕ)
    (U : Array (Option ℕ)) (T : okWidthB nU U (colsU v.F) = true) :
    okWidthB nU U (colsU b.F) = true :=
  okWidth_congr nU U (colsU_goes h) T

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.colsU_of_looks
#print axioms VerifiableInference.Desc.LinkJoin.okWidth_congr
#print axioms VerifiableInference.Desc.LinkJoin.okWidth_of_inv
#print axioms VerifiableInference.Desc.LinkJoin.okWidth_goes
