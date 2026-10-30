-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ent/ColRound.lean: a round whose oracle is one string of columns: a position is a leaf of one
tree, and the symbol at a leaf is the whole column: all symbols of a given round's oracle that lie
in the leaf, and all symbols of a rider (an oracle that a later round of the typed protocol would
send) that lie in it. And the maps of messages (`Carry`, Iop/Carry.lean) from that round to the
given round: the column is cut into the round's own symbols.

Definitions and statements; the proofs are in Cb/Ent/ColRoundProofs.lean.
General: any round r whose oracle is a string (`Round.IsPoint`, Iop/Shape.lean), any rider given by
its symbols, any assignment of positions to leaves.
Compare `Round.deco` (Iop/Deco.lean): the same positions, one further value at each.

Main names:
  `ColLay r W`: the layout: the leaves `Pt`; in which leaf a position of r's oracle lies (`lf`); the
    rider's positions and symbols, their leaves (`lfW`), the rider from its symbols (`ofW`).
  `L.Col p`: the column at the leaf p. `L.round`: the round: `Pos := L.Pt`, `Sym := L.Col`; plain
    part and verifier message are r's.
  `L.main pt o`, `L.rider o`: r's oracle and the rider, cut out of a string of columns.
  `L.join o w`: the string of columns that holds r's oracle o and the rider's symbols w.
  `L.point`: the oracle of `L.round` is a string, if the leaves are finitely many, with decidable
    equality.
  `L.car pt t`, `L.up pt τ`: the maps from `L.round :: t` to `r :: t` (the later rounds unchanged);
    the image of a transcript.
  `C.colLay Cw Pt lf lfW ..`: the layout for a native word of the code C sent as an oracle
    (`LdCode.sendRound`, Cb/Ld/LdRelKit.lean) with a native word of the code Cw as the rider.
  `Spec.ldEnt_col_tr`, `Spec.ldEnt_col_fib`, `Spec.ldEnt_col_chal`: every transcript has the image
    `L.up pt τ`; one verifier message goes to one; as many verifier messages as r has.
  `Spec.ldEnt_col_read`: a symbol of the oracle cut out is read in one column, that of its leaf.
  `Spec.ldEnt_col_join`: nothing is lost: every oracle of r, with the rider of any symbols, is cut
    out of some string of columns.
  `Spec.ldEnt_col_whole`: a string of columns holds nothing but the two: joined again, what is cut
    out gives it back.
  `Spec.ldEnt_col_riderAt`: at `C.colLay`, a symbol of the rider is read in the column of its leaf.

Limits: no tree, no hash, no path occurs here: how a string of columns is committed to is the
compiler's matter. Nothing on what a verifier reads, beyond `Spec.ldEnt_col_read` and
`Spec.ldEnt_col_riderAt`: no count of leaves. Nothing on an honest prover.

Terms: lean/GLOSSARY.md.

-/
import Iop.Carry
import Ior.KnowCollRulesChainErr
import Cb.Ld.LdRelKit

set_option autoImplicit false

namespace Cb
open Iop Prob

/-- How the symbols of the oracle of the round r and of a rider of the type W lie in the leaves of
one tree. -/
structure ColLay (r : Round) (W : Type) where
  /-- the leaves -/
  Pt   : Type
  /-- the leaf of a position of r's oracle -/
  lf   : r.Pos → Pt
  /-- the rider's positions -/
  PosW : Type
  /-- the rider's symbols -/
  SymW : PosW → Type
  /-- the leaf of a position of the rider -/
  lfW  : PosW → Pt
  /-- the rider from its symbols -/
  ofW  : (∀ q, SymW q) → W
  /-- fixed symbols of the rider -/
  dW   : ∀ q, SymW q

namespace ColLay
variable {r : Round} {W : Type} (L : ColLay r W)

/-- The column at a leaf: the symbols of r's oracle, and of the rider, that lie in it. -/
def Col (p : L.Pt) : Type :=
  (∀ q : {q : r.Pos // L.lf q = p}, r.Sym q.1) × (∀ q : {q : L.PosW // L.lfW q = p}, L.SymW q.1)

/-- The string of columns that holds the oracle o and the rider's symbols w. -/
def join (o : r.Orc) (w : ∀ q, L.SymW q) : ∀ p, L.Col p := fun _ =>
  (fun q => r.rd o q.1, fun q => w q.1)

/-- The round: a string of columns; plain part and verifier message as in r. -/
@[reducible] def round : Round where
  Orc := ∀ p, L.Col p
  Pos := L.Pt
  Sym := L.Col
  rd := fun o p => o p
  Plain := r.Plain
  Chal := r.Chal
  dOrc := L.join r.dOrc L.dW
  dPlain := r.dPlain

/-- The oracle of the round of columns is a string. -/
def point [Fintype L.Pt] [DecidableEq L.Pt] : L.round.IsPoint where
  finPos := ‹Fintype L.Pt›
  decPos := ‹DecidableEq L.Pt›
  ofSyms := fun f => f
  rd_ofSyms := fun _ _ => rfl
  ofSyms_rd := fun _ => rfl
  zero := L.join r.dOrc L.dW

/-- r's oracle, cut out of a string of columns. -/
def main (pt : r.IsPoint) (o : ∀ p, L.Col p) : r.Orc := pt.ofSyms fun q => (o (L.lf q)).1 ⟨q, rfl⟩

/-- The rider, cut out of a string of columns. -/
def rider (o : ∀ p, L.Col p) : W := L.ofW fun q => (o (L.lfW q)).2 ⟨q, rfl⟩

/-- The maps: the column is cut; all else is unchanged. -/
def car (pt : r.IsPoint) (t : Shape) : Carry (L.round :: t) (r :: t) :=
  (fun m => (L.main pt m.1, m.2), fun _ c => some c, fun _ _ => Carry.id t)

/-- The image of a transcript. -/
def up (pt : r.IsPoint) {t : Shape} (τ : Tr (L.round :: t)) : Tr (r :: t) :=
  ((L.main pt τ.1.1, τ.1.2), τ.2.1, τ.2.2)

end ColLay

/-- The layout for a native word of C, sent as an oracle, with a native word of Cw as the rider. -/
def LdCode.colLay {E P Pw : Type} [Zero E] (C : LdCode E P) (Cw : LdCode E Pw) (Pt : Type)
    (lf : C.NP → Pt) (lfW : Cw.NP → Pt) (Plain Chal : Type) [Fintype Chal] [Nonempty Chal]
    (dPlain : Plain) : ColLay (C.sendRound Plain Chal dPlain) Cw.Word where
  Pt := Pt
  lf := lf
  PosW := Cw.NP
  SymW := fun p => Cw.NS p → E
  lfW := lfW
  ofW := fun f => f
  dW := fun _ _ => 0

namespace Spec

/-- Every transcript has an image. -/
def ldEnt_col_tr : Prop :=
  ∀ (r : Round) (W : Type) (L : ColLay r W) (pt : r.IsPoint) (t : Shape) (τ : Tr (L.round :: t)),
    (L.car pt t).tr τ = some (L.up pt τ)

/-- One verifier message goes to one. -/
def ldEnt_col_fib : Prop :=
  ∀ (r : Round) (W : Type) (L : ColLay r W) (pt : r.IsPoint) (t : Shape),
    (L.car pt t).Fib (Err.ones (L.round :: t))

/-- The round of columns has as many verifier messages as r. -/
def ldEnt_col_chal : Prop :=
  ∀ (r : Round) (W : Type) (L : ColLay r W) (t : Shape),
    Shape.chalList (L.round :: t) = Shape.chalList (r :: t)

/-- A symbol of the oracle cut out is read in the column of its leaf. -/
def ldEnt_col_read : Prop :=
  ∀ (r : Round) (W : Type) (L : ColLay r W) (pt : r.IsPoint) (o : ∀ p, L.Col p) (q : r.Pos),
    r.rd (L.main pt o) q = (o (L.lf q)).1 ⟨q, rfl⟩

/-- Every oracle of r, with the rider of any symbols, is cut out of some string of columns. -/
def ldEnt_col_join : Prop :=
  ∀ (r : Round) (W : Type) (L : ColLay r W) (pt : r.IsPoint) (o : r.Orc) (w : ∀ q, L.SymW q),
    L.main pt (L.join o w) = o ∧ L.rider (L.join o w) = L.ofW w

/-- A string of columns is the join of r's oracle and of the rider's symbols that are cut out of it.
-/
def ldEnt_col_whole : Prop :=
  ∀ (r : Round) (W : Type) (L : ColLay r W) (pt : r.IsPoint) (o : ∀ p, L.Col p),
    L.join (L.main pt o) (fun q => (o (L.lfW q)).2 ⟨q, rfl⟩) = o

/-- At the layout of two native words, a symbol of the rider is read in the column of its leaf. -/
def ldEnt_col_riderAt : Prop :=
  ∀ (E P Pw : Type) [Zero E] (C : LdCode E P) (Cw : LdCode E Pw) (Pt : Type) (lf : C.NP → Pt)
      (lfW : Cw.NP → Pt) (Plain Chal : Type) [Fintype Chal] [Nonempty Chal] (dPlain : Plain)
      (o : ∀ p, (C.colLay Cw Pt lf lfW Plain Chal dPlain).Col p) (q : Cw.NP),
    (C.colLay Cw Pt lf lfW Plain Chal dPlain).rider o q = (o (lfW q)).2 ⟨q, rfl⟩

end Spec
end Cb
