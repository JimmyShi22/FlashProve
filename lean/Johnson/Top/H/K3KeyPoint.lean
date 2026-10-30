-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3KeyPoint.lean: the kind "lookup" (K3): A SMALL LAW ON WHAT THE HEARING LAYS: key
point number c has as many coordinates as call c's key numbers have bits. Statements and proofs.

Why. A calling kind reads key point number c of the carried record and tests its size against its
own layout (at the output head: the number of bits of a column, plus the positions' lt). That this
size is the n of the lookup's own call c is said here, so that the two numbers meet at every run
that both blocks pass, without a further test in either.

Main names:
  `zk_size_of_point`: from the sentence on the shape of what was heard (zx has dT coordinates, zy
    has rK, call c's key point is the last iota_c coordinates of zy, then all of zx) and the public
    tests (ShapeOf): the key point's size is FoNums.nOf g.shape c.
  `k3_keyPoint_calls`, `k3_keyPoint_digits`: so at K3.block's own decide at the two seats that run,
    with no premise.

It stands on Johnson/Desc/First/Look/K3PointAtSeats.lean (block_point_calls, block_point_digits)
and on two lemmas of the library on plain records: Fo.Pay.shapeOf_ok, Cb.Fo.ok_parts.

Limits. A sentence on sizes; nothing on what the coordinates are. A tie: no error term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3PointAtSeats
import OnBytes.Tie.Pv.Lookup.Peel.FoPayCaller
import OnBytes.Tie.Pv.Lookup.Forest.FoHole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model

/-- The key point's size, from the shape of what was heard. -/
theorem zk_size_of_point {calls : Array Call} {pub : Array Nat} {lid : ℕ} (g : Forest.Heard)
    (hS : _root_.Fo.ShapeOf calls pub lid g.shape) (hx : g.zx.size = g.shape.dT)
    (hy : g.zy.size = g.shape.rK) (c : ℕ) (hc : c < g.shape.NC)
    (hio : g.shape.iota.getD c 0 ≤ g.shape.rK)
    (hz : g.zk.getD c #[] =
      g.zy.extract (g.shape.rK - g.shape.iota.getD c 0) g.zy.size ++ g.zx) :
    (g.zk.getD c #[]).size = FoNums.nOf g.shape c := by
  have H : FoNums.ok g.shape = true := _root_.Fo.Pay.shapeOf_ok hS
  have hn : FoNums.nOf g.shape c = FoNums.io g.shape c + g.shape.dT :=
    ((Cb.Fo.ok_parts H).2.2.1 c hc).2.2.1
  have hi : FoNums.io g.shape c = g.shape.iota.getD c 0 := rfl
  rw [hz, Array.size_append, Array.size_extract, hx, hy, hn, hi, Nat.min_self]
  omega

/-- At the lookup on a link's calls. -/
theorem k3_keyPoint_calls {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
    {s s' : Desc.First.S} {rs : List Fmt.RoundView} {cols : List (List (ℕ × List UInt64))}
    (H : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') :
    ∃ g, (Desc.K3.seatCalls claim).heard s' = some g ∧
      ∀ c, c < g.shape.NC → (g.zk.getD c #[]).size = FoNums.nOf g.shape c := by
  obtain ⟨g, hg, hS, hx, hy, -, hz⟩ :=
    Desc.K3.block_point_calls claim piece laid before p guests H
  exact ⟨g, hg, fun c hc => zk_size_of_point g hS hx hy c hc (hz c hc).1 (hz c hc).2⟩

/-- At the lookup on the smallness test's digits. -/
theorem k3_keyPoint_digits {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
    {s s' : Desc.First.S} {rs : List Fmt.RoundView} {cols : List (List (ℕ × List UInt64))}
    (H : (Desc.K3.block (Desc.K3.seatDigits claim) piece laid before p guests).decide s rs cols =
      .ok s') :
    ∃ g, (Desc.K3.seatDigits claim).heard s' = some g ∧
      ∀ c, c < g.shape.NC → (g.zk.getD c #[]).size = FoNums.nOf g.shape c := by
  obtain ⟨g, hg, hS, hx, hy, -, hz⟩ :=
    Desc.K3.block_point_digits claim piece laid before p guests H
  exact ⟨g, hg, fun c hc => zk_size_of_point g hS hx hy c hc (hz c hc).1 (hz c hc).2⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.zk_size_of_point
#print axioms VerifiableInference.OnPublicFiles.k3_keyPoint_calls
#print axioms VerifiableInference.OnPublicFiles.k3_keyPoint_digits
