-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/LinkLook.lean: WHAT THE VIEW's LOOK-UP FINDS AT linkNext. The chain's walk
(Johnson/Prover/Link/ChainDefs.lean) reads each declared group by key and position through lookV;
here that look-up is said in linkAll's own terms (Johnson/Prover/Link/LinkAll.lean). Statements and
proofs.

  look_tree     under an own tree's number, whose seat is tree 0 of round r: at a position below the
                tree's length the look-up finds the column that linkAll's round r writes there
  look_stored   under a stored table's key: at a position below the tables' length it finds that
                table's stored column
  readG_groupAt a declared group of one tree, read by a look-up that finds col at every position
                below the tree's length, is groupAt (BodyAll.lean)

By: colOf_at (LinkFrame.lean) · linkNext_at (LinkCausal.lean) · lookY's text.
Not shown here. Which trees a plan declares. Nothing on a decision, on soundness or on what any
written value discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.LinkView
import Johnson.Prover.Link.ChainDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.Plain.One (readG lookY)
open _root_.Desc.K15 (P15)
open TypedOracleCompiler.Run.PQ (RD)
open _root_.Run.PQ (SgX storedKey xPos)
open _root_.Iop (twoExternalStrings)

theorem readG_groupAt (L : ℕ → ℕ → Option (List UInt64)) (κ a W : ℕ) (poss : List ℕ)
    (col : ℕ → List UInt64) (h : ∀ x, x < 2 ^ a → L κ x = some (col x)) :
    readG L ((Fmt.listOf (poss.map (· % 2 ^ a))).map fun x => (κ, x, W)) = groupAt a poss col := by
  unfold readG groupAt
  rw [List.map_map]
  refine List.map_congr_left fun x hx => ?_
  obtain ⟨y, _, rfl⟩ := List.mem_map.1 ((Fmt.listOf_mem _ _).1 hx)
  show (y % 2 ^ a, (L κ (y % 2 ^ a)).getD []) = _
  rw [h _ (Nat.mod_lt _ (Nat.pos_of_ne_zero (by positivity)))]
  rfl

variable (P : P15) (S : Sz) (t : ℕ) (X : LIn S) (C : LCoins)

theorem look_tree (ds : List RD) (a : ℕ) (y : (twoExternalStrings (2 ^ a) SgX).Str) (Ds : List Fmt.Drawn)
    (n r x : ℕ) (d : RD) (s : Fmt.Shape) (hn : n < 2 ^ 16) (hseat : seatOf ds n = some (r, 0))
    (hd : ds[r]? = some d) (ht : d.trees[0]? = some s) (hx : x < 2 ^ s.a) (hr : r < Ds.length)
    (hw : ((linkNext P S t X C r (Ds.take r)).col 0 x).length = s.W) :
    lookV ds a (linkNext P S t X C) y Ds n x =
      some ((((linkAll P S t X C (drawsOf Ds)).tr[r]?).getD fun _ => []) x) := by
  have k0 : n ≠ storedKey false := fun e => by
    have : 2 ^ 16 ≤ storedKey false := Nat.le_add_right _ _
    omega
  have k1 : n ≠ storedKey true := fun e => by
    have : 2 ^ 16 ≤ storedKey true := Nat.le_add_right _ _
    omega
  unfold lookV lookY
  rw [if_neg k0, if_neg k1,
    colOf_at (linkNext P S t X C) ds 0 [] Ds n x r 0 d s hseat hd ht hx hr
      (by rw [Nat.zero_add, List.nil_append]; exact hw),
    Nat.zero_add, List.nil_append, (linkNext_at P S t X C Ds r).2]
  rfl

theorem look_stored (ds : List RD) (a : ℕ) (next : ℕ → List Fmt.Drawn → MsgV)
    (y : (twoExternalStrings (2 ^ a) SgX).Str) (Ds : List Fmt.Drawn) (w : Bool) (x : ℕ) (hx : x < 2 ^ a) :
    lookV ds a next y Ds (storedKey w) x =
      some ((twoExternalStrings (2 ^ a) SgX).rd y (if w then .inr ⟨x, hx⟩ else .inl ⟨x, hx⟩)).2 := by
  unfold lookV lookY xPos
  cases w
  · rw [if_pos rfl, dif_pos hx]
    rfl
  · have ne : storedKey true ≠ storedKey false := by decide
    rw [if_neg ne, if_pos rfl, dif_pos hx]
    rfl

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.readG_groupAt
#print axioms Johnson.Prover.Link.look_tree
#print axioms Johnson.Prover.Link.look_stored
