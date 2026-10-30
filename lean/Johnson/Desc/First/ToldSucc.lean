-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/ToldSucc.lean: THEOREMS: THE NUMBERS' TWO COUNTS GO ON BY WHAT THE SUB-PROTOCOL
AT THE PLACE TELLS. Kind-free; small; no Mathlib of its own. A JOINING OF WHAT LIES: the numbers
closed over the description's own sub-protocols (Numbers.atBlocks, NumbersAtBlocks.lean: its two
counts are treesTold | msgsTold at borderOf, by rfl) · borderOf at the k-th place of a list without
a place twice is k (borderOf_getElem, BookFitTold.lean) · NEW: told_succ_at.
  told_succ_at    what the first k + 1 tell is what the first k tell and the k-th: trees and
                  tenants. (told_succ_nil, BookFit.lean, is its case "tells nothing".)
  told_succ       **THE STATEMENT**: no place twice; the k-th sub-protocol is b: the count of trees
                  at border k + 1 is that at border k and b.oracles.flatten.length; the count of
                  messages: and the sum of these oracles' tenants. At the last sub-protocol border
                  k + 1 is the chain's end (none): covered.
  told_succ_ps    the same along a written list ps, where the sub-protocols' places are ps.
  told_succ_zero  a sub-protocol that declares no oracle: both counts stay.
  told_twice      WITHOUT "no place twice" IT FAILS: two sub-protocols at one place, each telling
                  one tree: at k = 0 the count of trees does not go on.
What is not claimed. That a description's places are pairwise different: a closed test on the
written list. Nothing on the verifier's state. Nothing on soundness.

-/
import Johnson.Desc.First.NumbersAtBlocks
import Johnson.Desc.First.BookFitTold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc OnBytes OnBytes.Model

/-- What the first k + 1 tell is what the first k tell and the k-th. -/
theorem told_succ_at (told : List (List Oracle)) (k : Nat) (os : List Oracle)
    (h : told[k]? = some os) :
    treesTold told (k + 1) = treesTold told k + os.length ∧
      msgsTold told (k + 1) = msgsTold told k + (os.map fun o => o.tenants.length).sum := by
  unfold treesTold msgsTold
  rw [List.take_add_one, h]
  simp

section
variable {St Cl : Type} (N : Numbers) (s : Params.ReqShape) (links : List ModelPart)
  (bs : List (Block St Cl))

/-- **The two counts go on by what the sub-protocol at the place tells.** -/
theorem told_succ (hn : (blockPlaces bs).Nodup) (k : Nat) (b : Block St Cl)
    (hb : bs[k]? = some b) :
    (N.atBlocks s links bs).treesAt (blockPlaces bs)[k + 1]? =
        (N.atBlocks s links bs).treesAt (blockPlaces bs)[k]? + b.oracles.flatten.length ∧
      (N.atBlocks s links bs).msgsAt (blockPlaces bs)[k + 1]? =
        (N.atBlocks s links bs).msgsAt (blockPlaces bs)[k]? +
          (b.oracles.flatten.map fun o => o.tenants.length).sum := by
  have hk : k < bs.length := (List.getElem?_eq_some_iff.1 hb).1
  have hl : (blockPlaces bs).length = bs.length := List.length_map _
  have ht : (toldOf bs)[k]? = some b.oracles.flatten := by
    unfold toldOf
    rw [List.getElem?_map, hb]
    rfl
  rw [atBlocks_treesAt, atBlocks_treesAt, atBlocks_msgsAt, atBlocks_msgsAt,
    borderOf_getElem _ hn (k + 1) (by omega), borderOf_getElem _ hn k (by omega)]
  exact told_succ_at (toldOf bs) k _ ht

/-- The same along a written list of places. -/
theorem told_succ_ps (ps : List Place) (hps : blockPlaces bs = ps) (hn : ps.Nodup) (k : Nat)
    (b : Block St Cl) (hb : bs[k]? = some b) :
    (N.atBlocks s links bs).treesAt ps[k + 1]? =
        (N.atBlocks s links bs).treesAt ps[k]? + b.oracles.flatten.length ∧
      (N.atBlocks s links bs).msgsAt ps[k + 1]? =
        (N.atBlocks s links bs).msgsAt ps[k]? +
          (b.oracles.flatten.map fun o => o.tenants.length).sum := by
  subst hps
  exact told_succ N s links bs hn k b hb

/-- A sub-protocol that declares no oracle: both counts stay. -/
theorem told_succ_zero (hn : (blockPlaces bs).Nodup) (k : Nat) (b : Block St Cl)
    (hb : bs[k]? = some b) (h0 : b.oracles.flatten = []) :
    (N.atBlocks s links bs).treesAt (blockPlaces bs)[k + 1]? =
        (N.atBlocks s links bs).treesAt (blockPlaces bs)[k]? ∧
      (N.atBlocks s links bs).msgsAt (blockPlaces bs)[k + 1]? =
        (N.atBlocks s links bs).msgsAt (blockPlaces bs)[k]? := by
  have h := told_succ N s links bs hn k b hb
  rw [h0] at h
  exact h

end

/-- A sub-protocol without a round that tells one tree. -/
def oneTree (o : Oracle) : Block Unit Unit :=
  { (roundlessBlock "tells one tree" 1 none 0 .ok : Block Unit Unit) with oracles := [[o]] }

/-- **Without "no place twice" it fails.** -/
theorem told_twice (N : Numbers) (s : Params.ReqShape) (links : List ModelPart) (o : Oracle) :
    ¬ ((N.atBlocks s links [oneTree o, oneTree o]).treesAt
          (blockPlaces [oneTree o, oneTree o])[0 + 1]? =
        (N.atBlocks s links [oneTree o, oneTree o]).treesAt
          (blockPlaces [oneTree o, oneTree o])[0]? + (oneTree o).oracles.flatten.length) := by
  intro h
  have h' : (0 : Nat) = 0 + 1 := h
  omega

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.told_succ_at
#print axioms VerifiableInference.Desc.First.told_succ
#print axioms VerifiableInference.Desc.First.told_succ_ps
#print axioms VerifiableInference.Desc.First.told_succ_zero
#print axioms VerifiableInference.Desc.First.told_twice
