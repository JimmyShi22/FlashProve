-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/Full/Rows.lean: three ways to a lot's row (`RowAt`, Full/Ask.lean),
one for each form in which a lot's own module may have stated what its lot's skeleton is.
Statements and proofs.
  `rowAt_of_lotSk`    from `lotSk G L = k` and the closed fact `lotW asW lsW k = w`
  `lotW_cut`          the plain data at the numbers ls does not see the cut to ls
  `rowAt_of_cut`      from `(lotSk G L).cut lsW = k.cut lsW` and the same closed fact
  `rowAt_of_blocks`   from the sub-protocols' skeletons alone, for a lot that supplies no batching,
                      no `each` and no `tests`: the row's name, `letters` and `still` are the lot's
                      own
  `plainK n rows`     the skeleton of a lot of the name n with these sub-protocols' skeletons that
                      supplies none of the three, does not depend on the request and runs no older
                      step
  `lotW_plain`, `rowAt_plain`: its plain data; the first way, for such a lot
Limits. Nothing is paid here. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Law.Skel.Full.Ask

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk.Full
open ProofFile ProofFile.Sk

theorem rowAt_of_lotSk {G : Ground} {L : Lot} {k : LotSk} {w : LotW} (h : lotSk G L = k)
    (c : lotW asW lsW k = w) : RowAt G L w := by
  unfold RowAt
  rw [h, c]

theorem lotW_cut (as : List VerifiableInference.Desc.Place) (ls : List Nat) (k : LotSk) :
    lotW as ls (k.cut ls) = lotW as ls k := by
  have e : ∀ p : Nat → Bool, (ls.filter fun l => ls.contains l && p l) = ls.filter p := fun p =>
    List.filter_congr fun l hl => by
      rw [show ls.contains l = true from List.elem_iff.2 hl, Bool.true_and]
  show LotW.mk k.name k.letters k.still k.blocks _ (ls.filter fun l => ls.contains l && k.each l)
      (ls.filter fun l => ls.contains l && k.tests l) = LotW.mk k.name k.letters k.still k.blocks _
      (ls.filter k.each) (ls.filter k.tests)
  rw [e, e]
  rfl

theorem rowAt_of_cut {G : Ground} {L : Lot} {k : LotSk} {w : LotW}
    (h : (lotSk G L).cut lsW = k.cut lsW) (c : lotW asW lsW k = w) : RowAt G L w := by
  unfold RowAt
  rw [← lotW_cut, h, lotW_cut, c]

theorem rowAt_of_blocks {G : Ground} {L : Lot} {rows : List Skel}
    (hb : (L.blocks G).map skel = rows) (h1 : ∀ a, L.batch G a = none)
    (h2 : ∀ l, L.each G l = none) (h3 : ∀ l, L.tests G l = none) :
    RowAt G L ⟨L.name, L.letters, L.still, rows, [], [], []⟩ := by
  unfold RowAt lotW lotSk
  simp [hb, h1, h2, h3]

/-- The skeleton of a plain lot. -/
def plainK (n : String) (rows : List Skel) : LotSk :=
  { name := n, letters := false, still := [], blocks := rows, batch := fun _ => none
    each := fun _ => false, tests := fun _ => false }

theorem lotW_plain (as : List VerifiableInference.Desc.Place) (ls : List Nat) (n : String)
    (rows : List Skel) : lotW as ls (plainK n rows) = ⟨n, false, [], rows, [], [], []⟩ := by
  simp [lotW, plainK]

theorem rowAt_plain {G : Ground} {L : Lot} {n : String} {rows : List Skel} {w : LotW}
    (h : lotSk G L = plainK n rows) (c : (⟨n, false, [], rows, [], [], []⟩ : LotW) = w) :
    RowAt G L w :=
  rowAt_of_lotSk h ((lotW_plain asW lsW n rows).trans c)

end ProofFile.Sk.Full

#print axioms ProofFile.Sk.Full.rowAt_of_lotSk
#print axioms ProofFile.Sk.Full.lotW_cut
#print axioms ProofFile.Sk.Full.rowAt_of_cut
#print axioms ProofFile.Sk.Full.rowAt_of_blocks
#print axioms ProofFile.Sk.Full.lotW_plain
#print axioms ProofFile.Sk.Full.rowAt_plain
