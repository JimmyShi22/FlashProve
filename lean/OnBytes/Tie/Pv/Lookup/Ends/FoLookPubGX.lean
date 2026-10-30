-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLookPubGX.lean.
The calls' lookup of a group of layers: its share of the link's public record, with the keys
written.

Fo.Pub2.lookPubG (OnBytes/Tie/Pv/Lookup/Ends/FoLookPubG.lean) leaves the keys an argument and has
cells of the group's matrices and slots as its entries. OnBytes/Tie/Pv/Lookup/Ends/G.lean writes the
calls' key vectors at a group of layers as G.kvG, a term on the names G.NameG; that these terms are
the byte-level verifier's is no theorem of that file. The names hold the cells of the committed
matrix of weights beside the cells of the group's own matrices. So the entries here are two boxes of
cells and the slots, as at the head.

Main names:
  `IxGw`: what the sub-proof's committed messages hold, by names: G.NameG, and the mask row's slots.
  `cellOfG`: the cells by their names, read in the entries.
  `lookPubGX rdG X g hp .. St`: the record, over any base reading M₀ that is read at the names IxGw
    by rdG: h := X.layers.y.fo; the keys are G.kvG X.layers g at the cells; the mask entries are the
    slots from hp.Fp.next on; the bits of the counts lie in the matrix number
    (Layer.matIx X.layers.y).iB, of 2^lmb rows.
  `lookPubGX_ok`: where Verify.publicOf returns X: Fo.Pub2.LookPubOK of it, at the calls, numbers of
    padding keys and cap of the layers' layout. No further premise.
  `iB_eq`: the number under which G.placeG names the matrix of the counts' bits is the byte-level
    verifier's (Layer.matIx y).iB.
Limits: the boxes' bounds are free. hp is free: no clause reads it but through hp.Fp.next and hp.ns;
nothing here ties g to hp. Fo.Pub2.LookPubOK has no clause on the keys: it holds whatever the keys
are. That the first slot of the lookup in a run is hp.Fp.next is Fo.slots_next
(OnBytes/Tie/Pv/Lookup/Ends/FoDoors.lean). The keys read neither the caller's state nor the request.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoLookPubH
import OnBytes.Tie.Pv.Lookup.Ends.FoLookPubG
import OnBytes.Tie.Pv.Lookup.Ends.G

set_option autoImplicit false

namespace Fo.Pub2
open Cb Cb.Fo OnBytes OnBytes.Model OnBytes.Ends OnBytes.Ends.G

/-- The names at a group of layers: the cells of its matrices and of the weights, and the mask row's
slots. -/
abbrev IxGw : Type := NameG ⊕ ℕ

variable {nM nR nC wR wC nS : ℕ}

/-- The cells by their names, read in the entries. -/
def cellOfG (μ : JH nM nR nC wR wC nS → Cb.Gl.E) : NameG → Cb.Gl.E
  | .cell M r c => μ (cellH M r c)
  | .w r c => μ (wH r c)

/-- The calls' lookup's share of the public record of a group of layers. -/
def lookPubGX {M₀ : Type} (rdG : M₀ → IxGw → Cb.Gl.E) (X : Verify.Public) (g : ℕ)
    (hp : Layer.HPlan2) (nM nR nC wR wC : ℕ) (St : Type) : LookPub M₀ St where
  h := X.layers.y.fo
  J₀ := JH nM nR nC wR wC hp.ns
  L :=
    { K := fun _ μ q i => kvG X.layers g (cellOfG μ) q i
      bc := fun t c j => cellH (Layer.matIx X.layers.y).iB
        (FoNums.cellRC X.layers.y.fo X.layers.y.h.lmb (t, c, j)).1
        (FoNums.cellRC X.layers.y.fo X.layers.y.h.lmb (t, c, j)).2
      mkS := fun s => maskH (hp.Fp.next + s) }
  rd₀ := fun b => Sum.elim (fun n => rdG b (.inl (.cell n.1.val n.2.1.val n.2.2.val)))
    (Sum.elim (fun n => rdG b (.inl (.w n.1.val n.2.val))) fun s => rdG b (.inr s.val))

theorem lookPubGX_ok {M₀ : Type} (rdG : M₀ → IxGw → Cb.Gl.E) {pol KL : ByteArray}
    {layout : Option ByteArray} {X : Verify.Public} (h : Verify.publicOf pol KL layout = .ok X)
    (g : ℕ) (hp : Layer.HPlan2) (nM nR nC wR wC : ℕ) (St : Type) :
    LookPubOK (lookPubGX rdG X g hp nM nR nC wR wC St) X.layers.y.cl X.layers.y.fo.pub
      X.layers.y.h.lidb X.layers.y.h.lmb hp.Fp.next maskH
      (cellH (Layer.matIx X.layers.y).iB) :=
  ⟨Fo.public_shape h, (public_lm h).1, (public_lm h).2, fun _ => rfl, fun _ _ _ _ => rfl⟩

theorem iB_eq (y : Layer.Lay) : G.iB y = (Layer.matIx y).iB := rfl

end Fo.Pub2
