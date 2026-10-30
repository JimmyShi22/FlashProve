-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/WireOf.lean: generic parts of a wire record.

`WireR.ofPoint` is the record of a round whose oracle is a string and whose challenges come from
the universal sampler (Iop/Univ.lean): its tree has depth ⌈log₂ (number of positions)⌉, and a
position is at the leaf of its number. Its inputs are data, none of them obtained from a statement
of existence. `WireE.one`, `WireE.two`: one and two external strings. `Enum.ofNum`: the enumeration
that belongs to a numbering. `OpenNums`: bounds on the numbers of opened positions.
-/
import Iop.Univ
import Iop.ShapeKit

namespace Iop
open Prob

/-- The enumeration that belongs to a numbering. -/
def Enum.ofNum (β : Type) [Fintype β] [Nonempty β] (nb : β ≃ Fin (Fintype.card β)) : Enum β where
  n := Fintype.card β - 1
  e := fun r => nb.symm ⟨r.val % Fintype.card β, Nat.mod_lt _ Fintype.card_pos⟩

def WireR.ofPoint (lam K : ℕ) (r : Round) (pt : r.IsPoint) (nc : Num r.Chal)
    (np : r.Pos ≃ Fin (@Fintype.card r.Pos pt.finPos)) :
    WireR lam K (r.pull (Sampler.univ lam r nc)) :=
  letI := pt.finPos
  { pt :=
    { finPos := pt.finPos, decPos := pt.decPos, ofSyms := pt.ofSyms, rd_ofSyms := pt.rd_ofSyms,
            ofSyms_rd := pt.ofSyms_rd, zero := pt.zero }
    depth := Nat.clog 2 (Fintype.card r.Pos)
    place := fun p => (np p).val
    posAt := fun j => if h : j < Fintype.card r.Pos then some (np.symm ⟨j, h⟩) else none
    chal := fun b i => if h : i.val < K then b ⟨i.val, h⟩ else fun _ => false }

def WireE.one (n : ℕ) (Sg : Type) (z : Sg) : WireE (oneExternalString n Sg) where
  all := List.finRange n
  which := fun _ => 0
  leaf := fun p => p.val
  depth := Nat.clog 2 n
  build := fun f p => (f p).getD z
  dec := inferInstanceAs (DecidableEq (Fin n))

def WireE.two (n : ℕ) (Sg : Type) (z : Sg) : WireE (twoExternalStrings n Sg) where
  all := (List.finRange n).map Sum.inl ++ (List.finRange n).map Sum.inr
  which := fun p => p.elim (fun _ => 0) (fun _ => 1)
  leaf := fun p => p.elim (fun q => q.val) (fun q => q.val)
  depth := Nat.clog 2 n
  build := fun f => (fun p => (f (.inl p)).getD z, fun p => (f (.inr p)).getD z)
  dec := inferInstanceAs (DecidableEq (Fin n ⊕ Fin n))

/-- bounds on the numbers of positions that the three verifiers open, external ones included -/
structure OpenNums where
  T : ℕ
  L : ℕ
  O : ℕ

end Iop
