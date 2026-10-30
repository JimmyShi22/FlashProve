-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoKeys.lean.
What a caller of a sub-proof's lookup owes for its key forms, and the law of the reads.

The join of a lookup takes from its caller one form for each call. The lookup's claims say what they
are meant to say only if, in the world at hand, the value of call k's form is the extension of call
k's key vector at call k's point. This file gives that condition a name, and it names two further
conditions from which a caller can reach it: that two worlds agree on a form, and the law of the
reads.

Defines:
  KeysAt ρ W NC KF Kv zk: for each call k below NC the value of KF[k] in the world W is the
    extension of Kv k at zk k. It is a condition on the world.
  AgreeOn a W W': the two worlds agree on every slot and every entry that the form a names.
  FunRead, ReadsAll: the law of the reads. A sub-proof keeps tables of reads in a vector; each entry
    of a table is meant to be the sum, over a block of rows of a committed matrix, of a public
    weight times the matrix's cell in one column (OnBytes.Model.HFun). FunRead says this of one
    table's entries in a world and of given cells; ReadsAll of all tables of a list that lie in the
    vector U3. It is no identity: it is what the claims on the reads are to enforce.
States:
  value_agree: a form has one value in two worlds that agree on what it names.
  KeysAt.agree: so KeysAt passes between such worlds.
  ReadsAll.filter: the law at all tables gives the law at some of them.
  keysAt_of_ext: KeysAt from the library's extension (Blocks.ext) at the points read as functions.
Not claimed: anything on soundness, completeness or hiding. Nor is it claimed that KeysAt or
ReadsAll holds of any world.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoKfDig
import OnBytes.Tie.Pv.Lookup.Port.FoReads

set_option autoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- In the world W each call's form has the value of the call's key vector's extension at the call's
point. -/
def KeysAt (W : World K) (NC : ℕ) (KF : Array Aff) (Kv : ℕ → ℕ → K) (zk : ℕ → List K) : Prop :=
  ∀ k < NC, (KF.getD k (Aff.ofConst zeroE)).value ρ W = extL (Kv k) (zk k)

/-- The two worlds agree on all that the form names. -/
def AgreeOn (a : Aff) (W W' : World K) : Prop :=
  (∀ x ∈ a.ents.toList, W.entry x.tree x.row x.idx = W'.entry x.tree x.row x.idx) ∧
    ∀ x ∈ a.slots.toList, W.slot x.1 = W'.slot x.1

theorem value_agree {a : Aff} {W W' : World K} (h : AgreeOn a W W') :
    a.value ρ W = a.value ρ W' := by
  unfold Aff.value
  rw [List.map_congr_left fun x hx => show Ent.value ρ W x = Ent.value ρ W' x by
      unfold Ent.value; rw [h.1 x hx],
    List.map_congr_left fun x hx => show slotValue ρ W x = slotValue ρ W' x by
      unfold slotValue; rw [h.2 x hx]]

theorem KeysAt.agree {W W' : World K} {NC : ℕ} {KF : Array Aff} {Kv : ℕ → ℕ → K}
    {zk : ℕ → List K} (h : KeysAt ρ W' NC KF Kv zk)
    (ha : ∀ k < NC, AgreeOn (KF.getD k (Aff.ofConst zeroE)) W W') : KeysAt ρ W NC KF Kv zk :=
  fun k hk => (value_agree ρ (ha k hk)).trans (h k hk)

/-- The law of the reads at one table: entry c * nsg + sg of the table is the sum over block sg of
the rows of column c of the table's matrix, under the table's weights. Here nsg is the number of
blocks: the matrix's rows divided by the rows of a block (f.len). cellM m r c: the cell (r, c) of
matrix number m. -/
def FunRead (mats : Array TMat) (entry : ℕ → ℕ → ℕ → K) (iU3 K3 : ℕ) (cellM : ℕ → ℕ → ℕ → K)
    (f : HFun) : Prop :=
  ReadAt entry iU3 K3 f.start (fun j => ρ.val (f.phi.getD j zeroE))
    (fun row col => cellM f.mat
      (col % ((mats.getD f.mat {}).m / f.len) * f.len + row)
      (col / ((mats.getD f.mat {}).m / f.len)))
    f.len ((mats.getD f.mat {}).k * ((mats.getD f.mat {}).m / f.len))

/-- The law of the reads at all tables of a list that lie in the vector U3. -/
def ReadsAll (mats : Array TMat) (funs : Array HFun) (entry : ℕ → ℕ → ℕ → K) (iU3 K3 : ℕ)
    (cellM : ℕ → ℕ → ℕ → K) : Prop :=
  ∀ f ∈ funs.toList, f.tree = 2 → FunRead ρ mats entry iU3 K3 cellM f

/-- The law at all tables gives the law at some of them. -/
theorem ReadsAll.filter {mats : Array TMat} {funs : Array HFun} {entry : ℕ → ℕ → ℕ → K}
    {iU3 K3 : ℕ} {cellM : ℕ → ℕ → ℕ → K} (h : ReadsAll ρ mats funs entry iU3 K3 cellM)
    (p : HFun → Bool) : ReadsAll ρ mats (funs.filter p) entry iU3 K3 cellM := by
  intro f hf
  rw [Array.toList_filter] at hf
  exact h f (List.mem_filter.mp hf).1

end

/-- KeysAt from the library's extension. -/
theorem keysAt_of_ext {E : Type} [Field E] (ρ : Reading E) (W : World E) (NC : ℕ) (KF : Array Aff)
    (Kv : ℕ → ℕ → E) (zk : ℕ → List E)
    (h : ∀ k < NC, (KF.getD k (Aff.ofConst zeroE)).value ρ W =
      Blocks.ext (zk k).length (Kv k) (Blocks.ofList (zk k))) : KeysAt ρ W NC KF Kv zk :=
  fun k hk => (h k hk).trans (extL_ofList (Kv k) (zk k)).symm

end Fo
