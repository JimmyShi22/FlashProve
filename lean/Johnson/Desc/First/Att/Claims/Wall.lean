-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/Wall.lean: kind K5: one sum cut in two: the weight of all the pieces
of a softmax-table call (wall, in the padding's term of its key form) is the two units' weights
together (sumW of each unit's pieces). KeyPub.pad (Johnson/Road/Rows/AttKeyAll.lean) wants this, and
more.

Main names: `pcW`, `wall_val`, `sumW_pieces` (sorting the pieces turns no sum), `wall_two`.
Premise: every piece of the call belongs to the list fm or to the list fd. Not shown in this file or
in what it imports.
Limit: that the call's padding key reads as the library's number is not said here.
Used of OnBytes: the field's type and Reading.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.Any

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo CallG Pc Keys W1)

variable {Kf : Type} [CommRing Kf] (ρ : Reading Kf)

theorem foldl_addE_val {α : Type} (f : α → E) : ∀ (l : List α) (s : E),
    ρ.val (l.foldl (fun s x => addE s (f x)) s) = ρ.val s + (l.map fun x => ρ.val (f x)).sum
  | [], s => by simp
  | a :: l, s => by
    rw [List.foldl_cons, foldl_addE_val f l, ρ.add, List.map_cons, List.sum_cons]
    ring

theorem sum_two {α : Type} (f : α → Kf) (p q : α → Bool) : ∀ (l : List α),
    (∀ x ∈ l, (p x = true ∧ q x = false) ∨ (p x = false ∧ q x = true)) →
    (l.map f).sum = ((l.filter p).map f).sum + ((l.filter q).map f).sum
  | [], _ => by simp
  | a :: l, h => by
    have ih := sum_two f p q l fun x hx => h x (List.mem_cons_of_mem _ hx)
    rcases h a List.mem_cons_self with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [List.filter_cons_of_pos h1, List.filter_cons_of_neg (by rw [h2]; decide), List.map_cons,
        List.map_cons, List.sum_cons, List.sum_cons, ih]
      ring
    · rw [List.filter_cons_of_neg (by rw [h1]; decide), List.filter_cons_of_pos h2, List.map_cons,
        List.map_cons, List.sum_cons, List.sum_cons, ih]
      ring

/-- A piece's weight at the call's key point. -/
def pcW (n : ℕ) (zk : Array E) (pc : Pc) : E := P.eqAt (zk.extract 0 (n - pc.b)) (pc.off >>> pc.b)

theorem wall_val (c : CallG) (zk : Array E) :
    ρ.val (P.Runs.wall c zk) = (c.pcs.map fun pc => ρ.val (pcW c.n zk pc)).sum := by
  unfold P.Runs.wall
  have e := foldl_addE_val ρ (pcW c.n zk) c.pcs zeroE
  rw [ρ.zero, zero_add] at e
  exact e

theorem sumW_pieces (u : P.UnitG) (zk : Array E) :
    ρ.val (P.Runs.sumW (P.piecesOf u zk)) = (u.pcs.map fun pc => ρ.val (pcW u.n zk pc)).sum := by
  unfold P.Runs.sumW P.piecesOf
  rw [← Array.foldl_toList, foldl_addE_val ρ (fun x : W1 => x.wp), ρ.zero, zero_add]
  have hp := List.mergeSort_perm (u.pcs.map fun pc => W1.mk pc.lam pc.a (pcW u.n zk pc))
    (fun x y => x.lam < y.lam || (x.lam == y.lam && x.a ≤ y.a))
  have e := (hp.map fun x : W1 => ρ.val x.wp).sum_eq
  rw [List.map_map] at e
  exact e

/-- **One sum cut in two**: the weight of all a softmax-table call's pieces is the two units' weights together. -/
theorem wall_two (g : Geo) (q : ℕ) (c : CallG) (zk : Array E)
    (hk : ∀ pc ∈ c.pcs, pc.keys = Keys.fm ∨ pc.keys = Keys.fd) :
    ρ.val (P.Runs.wall c zk) = ρ.val (P.Runs.sumW (P.piecesOf (g.unitAt q c .fm) zk)) +
      ρ.val (P.Runs.sumW (P.piecesOf (g.unitAt q c .fd) zk)) := by
  rw [wall_val, sumW_pieces, sumW_pieces]
  exact sum_two (fun pc => ρ.val (pcW c.n zk pc)) (fun pc => pc.keys == Keys.fm)
    (fun pc => pc.keys == Keys.fd) c.pcs fun pc hpc => by
    rcases hk pc hpc with e | e
    · exact .inl (by dsimp only; rw [e]; exact ⟨rfl, rfl⟩)
    · exact .inr (by dsimp only; rw [e]; exact ⟨rfl, rfl⟩)

end K5Law
