-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartCf.lean: the configuration over which a request is built from a partition: the witness
is (the data of all segments as they will be sent, the integer cells); the relation pair is written
out in the segments' terms.

The indexed relation pair of which a built request's theorems speak, and how it stands to the
model's pair: one map of witnesses forth (`Spec.ldPartCf_yes`), one back (`Spec.ldPartCf_no`), and
the languages. Definitions and statements (`Cb.Spec.ldPartCf_yes` to `Cb.Spec.ldPartCf_langs`); the
proofs are in Cb/Part/LdPartCfProofs.lean.
A configuration is an `LdCf` (Cb/Obj/LdObjectConf.lean), a partition P an `LdPartD Cf`
(Cb/Part/LdPartDef.lean). The data w : `LdPartW E`, the ghost g : `LdPartGh` (the integer cells) and
the public parameters of packing K : `LdPartPk` (in the formulas below ϱ is K.rdx and a bare P is
K.P; B, D are P.B, P.D) are in Cb/Part/LdPartRide.lean. The relation pair of a configuration is Ryes
(the honest side's relation) and Rno (the relaxed relation); Ryes ⊆ Rno is a clause of
`LdCf.ModelOK`, not of `LdCf`.

Why: a sending takes data out of the witness and its relation afterwards
reads them back off the messages (Cb/Req1/LdSegKit.lean: the relation after a sending is the one
before it at bk (new messages) (rest)). So what goes out must be a part of the witness as it goes
out: field elements. A model's own cells (say functions on names) are not. Hence a configuration of
the builder's own, with the model's side of Cf replaced; code, format, index set, instances and the
index's side (body, heldB) are Cf's.

Main names:
  `LdPartBits P`: parameters for the bits of the front lookups' multiplicities: ok j x W g b: "b are
    honest bits of segment j's lookup at the cells g"; hon j x W g: the honest bits.
  `P.RyesB K Bt`: of i, x, (w, g): the request has the form; g is below B in absolute value in all
    shapes; every layer of w is the packing of g's matrix; every layer's bits are honest; all
    segments' conditions at (x, the matrix of i, g).
  `P.RnoB K`: of i, x, (w, g): the request has the form; every layer of w is a packing of cells
    below 2 D in absolute value; all segments' conditions at (x, the matrix of i, the cells unpacked
    from w). The ghost is not read.
  `P.packW K Bt x W g`: the data of integer matrices g: entry (j, i, c) := Σ_l ϱ^l · g j (i P + l) c
    (rows below the last and columns beyond the last are 0); the honest bits.
  `P.cfB K Bt`: the configuration: Cf with Cells := LdPartW E × LdPartGh, the pair above,
    trace i x := (packW of the model's honest matrices, these matrices).
  The five statements are made for `P.Props p`, `P.Wide K` and unique packing (`Uniq` (2 D) ϱ P p,
  Cb/Ld/LdRngAlg.lean), CharP E p, honest bits honest (`P.BitsOK Bt`). This is the union of what the
  five ask: _yes asks `P.Props p` and the honest bits alone; _no `P.Props p` and 0 < K.P alone;
  0 < K.P stands in all but _yes; _model asks moreover `Cf.ModelOK`.
  `Spec.ldPartCf_yes`: a witness c of the model's relation gives the witness
    (packW (toMat c), toMat c) of `RyesB`.
  `Spec.ldPartCf_no`: a witness (w, g) of `RnoB` gives the witness ofMat (the integers unpacked from
    w) of the model's relaxed relation.
  `Spec.ldPartCf_sub`: RyesB ⊆ RnoB.
  `Spec.ldPartCf_model`: if moreover "a witness of the model's relaxed relation makes the model's
    honest trace a witness of its relation": `(P.cfB K Bt).ModelOK`.
  `Spec.ldPartCf_langs`: under the same, without `Cf.ModelOK`: the two languages of the new pair
    agree, and they are the language of the model's relaxed relation (∃ c, Cf.Rno i x c).

Limits:
What this means for a theorem on the built request: its relation pair is (RyesB, RnoB). By
`ldPartCf_langs`, under its hypotheses, the languages are that of the model's relaxed relation; by
`ldPartCf_yes`, `ldPartCf_no`, each under its hypotheses, an honest prover that holds the model's
witness has the new one by a map, and an extracted witness gives the model's relaxed witness by a
public map. For a relation whose witness is idle ("the request is true") nothing else is read.
Declared: in this protocol's technical report (lean/CREDITS.md) the witness holds integer cells, and
packing is the protocol's;
here the packings stand in the witness too (the same content under unique packing). This file says
nothing on protocols. This file gives no instance that meets its hypotheses, so as far as this file
shows its theorems may hold of nothing.



Terms: lean/GLOSSARY.md.
-/
import Cb.Part.LdPartRide
import Cb.Obj.LdObjectConfMore
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb

open Iop Prob Hiop Blocks Finset Cb.RngPk

/-- parameters for the bits of the front lookups' multiplicities -/
structure LdPartBits {F E : Type} [Field F] [Field E] [Algebra F E]
    {Cf : LdCf F E} (P : LdPartD Cf) where
  ok  : ℕ → Cf.Xm → (ℕ → ℕ → F) → LdPartGh → (ℕ → E) → Prop
  hon : ℕ → Cf.Xm → (ℕ → ℕ → F) → LdPartGh → ℕ → E

namespace LdPartD
variable {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E] {Cf : LdCf F E} (P : LdPartD Cf)
  (K : LdPartPk) (Bt : LdPartBits P)

/-- the relation, in the segments' terms -/
def RyesB (i : Cf.I) (x : Cf.Xm) (t : LdPartW E × LdPartGh) : Prop :=
  P.form x ∧ P.Below P.B t.2 ∧
  (∀ j < P.n, PackBy P.B K.rdx (P.layX K t.2 j) (P.layW K t.1 j)) ∧
  (∀ j < P.n, Bt.ok j x (P.matI i) t.2 (t.1.bit j)) ∧
  P.Cond x (P.matI i) (castM (E := E) t.2)

/-- its relaxation -/
def RnoB (i : Cf.I) (x : Cf.Xm) (t : LdPartW E × LdPartGh) : Prop :=
  P.form x ∧
  (∀ j < P.n, Packed K.P (2 * P.D) K.rdx (P.layW K t.1 j)) ∧
  P.Cond x (P.matI i) (fun s => P.cellsW K t.1 s)

/-- the data of integer matrices -/
def packW (x : Cf.Xm) (W : ℕ → ℕ → F) (g : LdPartGh) : LdPartW E where
  pk  := fun j i c =>
    ∑ l ∈ range K.P, ((K.rdx : ℤ) : E) ^ l *
      (((if i * K.P + l < 2 ^ (P.seg j).rowsLog ∧ c < (P.seg j).cols then g j (i * K.P + l) c
        else 0 : ℤ)) : E)
  bit := fun j => Bt.hon j x W g

/-- the integers unpacked from the data -/
def unpackW (w : LdPartW E) : LdPartGh := fun j r c =>
  if h : (r / K.P < P.rp K j ∧ r % K.P < K.P) ∧ c < K.Cw then
    (if r < 2 ^ (P.seg j).rowsLog ∧ c < (P.seg j).cols then
        cells K.P (2 * P.D) K.rdx (P.layW K w j) (⟨r / K.P, h.1.1⟩, ⟨r % K.P, h.1.2⟩) ⟨c, h.2⟩
      else 0)
  else 0

/-- The configuration over which the request is built. -/
def cfB : LdCf F E :=
  { Cf with
    Cells := LdPartW E × LdPartGh
    Ryes := P.RyesB K Bt
    Rno := P.RnoB K
    trace := fun i x => (P.packW K Bt x (P.matI i) (P.toMat (Cf.trace i x)), P.toMat (Cf.trace i x))
    cells0 := (⟨fun _ _ _ => 0, fun _ _ => 0⟩, fun _ _ _ => 0) }

/-- every segment's matrix fits the public width -/
def Wide : Prop := ∀ j < P.n, (P.seg j).cols ≤ K.Cw

/-- honest bits are honest, where segment j's conditions hold (`SegSpec.Holds`: identities vanish,
keys lie in their tables) -/
def BitsOK : Prop :=
  ∀ j < P.n, ∀ x W g, (P.seg j).Holds P.fmt x W (castM (E := E) g) → Bt.ok j x W g (Bt.hon j x W g)

end LdPartD

namespace Spec

def ldPartCf_yes : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E) (P : LdPartD Cf)
      (K : LdPartPk) (Bt : LdPartBits P) (p : ℕ),
    P.Props p → P.BitsOK Bt →
    ∀ i x c, Cf.Ryes i x c → P.RyesB K Bt i x (P.packW K Bt x (P.matI i) (P.toMat c), P.toMat c)

def ldPartCf_no : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E)
      (P : LdPartD Cf) (K : LdPartPk) (p : ℕ),
    P.Props p → 0 < K.P → ∀ i x t, P.RnoB K i x t → Cf.Rno i x (P.ofMat (P.unpackW K t.1))

def ldPartCf_sub : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E) (P : LdPartD Cf)
      (K : LdPartPk) (Bt : LdPartBits P) (p : ℕ) [CharP E p],
    P.Props p → P.Wide K → 0 < K.P → Uniq (2 * P.D) K.rdx K.P p →
    ∀ i x t, P.RyesB K Bt i x t → P.RnoB K i x t

def ldPartCf_model : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E) (P : LdPartD Cf)
      (K : LdPartPk) (Bt : LdPartBits P) (p : ℕ) [CharP E p],
    P.Props p → P.Wide K → P.BitsOK Bt → 0 < K.P → Uniq (2 * P.D) K.rdx K.P p → Cf.ModelOK →
    (∀ i x c, Cf.Rno i x c → Cf.Ryes i x (Cf.trace i x)) → (P.cfB K Bt).ModelOK

def ldPartCf_langs : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E) (P : LdPartD Cf)
      (K : LdPartPk) (Bt : LdPartBits P) (p : ℕ) [CharP E p],
    P.Props p → P.Wide K → P.BitsOK Bt → 0 < K.P → Uniq (2 * P.D) K.rdx K.P p →
    (∀ i x c, Cf.Rno i x c → Cf.Ryes i x (Cf.trace i x)) →
    ∀ i x,
      ((∃ t, P.RnoB K i x t) ↔ ∃ c, Cf.Rno i x c) ∧ ((∃ t, P.RyesB K Bt i x t) ↔ ∃ c, Cf.Rno i x c)

end Spec

end Cb
