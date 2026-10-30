-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartLkpFam.lean: the key families of a segment of a partition, with their tables, as the
key functions of the shift and the assembled lookup after it; the joint shifted key as one family.

Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Part/LdPartLkpFamProofs.lean. No
protocol.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).
E is an algebra over the field F.
The file is between Cb/Req/ReqSpec.lean (`Fam`, `Tab`, `SegSpec`: a segment's conditions),
Cb/Part/LdPart.lean (a family as a polynomial; one reading of a block's entries) and
Cb/Part/LdPartLkp.lean (from key functions of any sizes to the data of shift and lookup).

Main names:
  K : `LdPartKeys X F E`: nk key families "fam f", each with its table "tb f".
  `K.lk h k R xs : LdPartLk E St J`: the key number b of the function f, at the state st and the
    entries m, is the family's polynomial at the vertex b, at the instance xs st, at the index
    matrix (over E, h rows, 2^k columns) and the matrices of cells that the reading R reads off m.
    The tables read neither state nor entries.
  `K.sz`, `K.g`, `K.v`: the sizes (`LdPartSz`) and the numbers of Cb/Part/LdPartLkp.lean, which
    read the sizes alone.
  `K.keyFam : Fam (X × E) E`: one family on g + v variables, over instances (instance, shift θ):
    Σ_{f < nk} (the table that is 1 where the first g bits of the vertex write f) · (fam f, read at
    the low bits of the vertex) + (a term without atoms with the public table b ↦ (the number that
    the first g bits write) · θ). It is made with the steps of Cb/Req/ReqGlue.lean (more variables,
    a public factor, a public table, side by side) and Cb/Req/ReqFamTuple.lean (another type of
    instances).
  `Spec.ldPartKeys_holds`: K is the keys of a list l (`LdPartKeys.ofList l`), its key functions
    taken at a format Φ's sizes (`K.lk Φ.h (Φ.hi + Φ.lo) R xs`). If the families are well formed at
    Φ (`Fam.WF`) and the entries' index matrix (`R.W m`) is the image of a matrix W over F, then the
    claim before the shift, `(K.lk ..).P.inC st m`, holds ⇔ every key of every family lies in its
    table, in the words of `SegSpec.Holds` (its second clause).
  `Spec.ldPartKeyFam_vtx`: see its docstring. So, for well-formed families, what the lookup claims
    at its end, of the joint keys extended multilinearly, is claimed of one family's values at the
    vertices, extended, its public part tag · θ included: nothing is moved into a target.
  `Spec.ldPartKeyFam_v`: `K.keyFam` has g + v variables. `Spec.ldPartKeyFam_wf`,
    `Spec.ldPartKeyFam_places`: for well-formed families it is well formed, and it reads the places
    that the families read.
  `Spec.ldPartKeyFam_deg`: every d with `(K.fam f).DegLe d` for all f < nk has `K.keyFam.DegLe d`
    (`Fam.DegLe`, Cb/Req/ReqNumsGlue.lean; inner sums too): the selector is a factor of the term's
    one public coefficient table, not a further map; the public part is a term without atoms.

Notation:
  `K.g`: `Nat.clog 2 K.nk`;
  `K.v`: `vm + 1`, vm the largest kv, less 1 (0 if that is 0);
  `kv f`: the function f has 2^(kv f) keys (`LdPartSz`, Cb/Part/LdPartLkp.lean);
  `P`: the shift's data (`LdPartLk.P`, there);
  `P.inC`: the claim before the shift: `AllIn` of the shift's keys and tables
    (Cb/Ld/LdLkpShift.lean);
  `P.tag f`: `(f : E)`;
  `shKey`: the joint keys at θ (there).

Limits: this file says nothing on degrees variable by variable. The polynomial of K.keyFam off the
vertices is not the multilinear extension of the joint keys (a product of extensions is not
multilinear): the claim on that extension is a sum claim on the family under equality weights, for
the sumcheck that follows. The padding (repeats; idle functions) and how it differs from this
protocol's technical report (lean/CREDITS.md): head of Cb/Part/LdPartLkp.lean. The reading R is a
letter without a law.
This file gives no instance that meets its hypotheses.

Terms: lean/GLOSSARY.md.
-/
import Cb.Part.LdPartLkp
import Cb.Part.LdPart
import Cb.Req.ReqFamTuple

set_option autoImplicit false

namespace Cb
open Blocks Hiop Finset Cb.LdLkp Cb.Lkp

/-- The key families of a segment with their tables, numbered. -/
structure LdPartKeys (X F E : Type) where
  nk : ℕ
  fam : ℕ → Fam X E
  tb : ℕ → Tab F

namespace LdPartKeys
variable {X F E : Type}

/-- those of a list, in its order; beyond its end: a family without terms, a table of zeros -/
def ofList [Zero F] [Zero E] (l : List (Fam X E × Tab F)) : LdPartKeys X F E :=
  ⟨l.length,
    fun f => (l.getD f (⟨0, 0, fun _ => .base (.cell fun _ => ⟨0, []⟩), []⟩, ⟨0, fun _ => 0⟩)).1,
    fun f => (l.getD f (⟨0, 0, fun _ => .base (.cell fun _ => ⟨0, []⟩), []⟩, ⟨0, fun _ => 0⟩)).2⟩

/-- the sizes -/
def sz (K : LdPartKeys X F E) : LdPartSz := ⟨K.nk, fun f => (K.fam f).v, fun f => (K.tb f).T⟩

variable [Field F] [Field E] [Algebra F E] (K : LdPartKeys X F E)

/-- The key functions. -/
def lk {St J : Type} (h k : ℕ) (R : LdPartRd E J) (xs : St → X) : LdPartLk E St J where
  toLdPartSz := K.sz
  key := fun st m f b => (K.fam f).ext h k (xs st) (R.W m) (R.A m) (vtx (K.fam f).v b)
  tab := fun _ f u => algebraMap F E ((K.tb f).t u)

abbrev g : ℕ := K.sz.g
abbrev v : ℕ := K.sz.v

/-- the public part, and the families below number i, each at its selector value -/
def keyUpTo : ℕ → Fam (X × E) E
  | 0 => Fam.pub (K.g + K.v) fun x b => ((b / 2 ^ K.v : ℕ) : E) * x.2
  | i + 1 =>
    Fam.add (Fam.mask (fun _ b => if b / 2 ^ K.v = i then 1 else 0)
        (((K.fam i).reX Prod.fst).to (K.g + K.v))) (keyUpTo i)

/-- The joint shifted key as one family. -/
def keyFam : Fam (X × E) E := K.keyUpTo K.nk

end LdPartKeys

namespace Spec

/-- States: under the two premises below, the claim before the shift is the segment's condition on
keys. -/
def ldPartKeys_holds : Prop :=
  ∀ (X F E St J : Type) [Field F] [Field E] [Algebra F E] (l : List (Fam X E × Tab F))
      (Φ : IdxFmt F) (R : LdPartRd E J) (xs : St → X) (st : St) (m : J → E) (W : ℕ → ℕ → F),
    (∀ q ∈ l, q.1.WF Φ) → (R.W m = fun y c => algebraMap F E (W y c)) →
    (((LdPartKeys.ofList l).lk Φ.h (Φ.hi + Φ.lo) R xs).P.inC st m ↔
      ∀ q ∈ l, ∀ b < 2 ^ q.1.v, ∃ u ∈ q.2.set, q.1.val Φ (xs st) W (R.A m) b = algebraMap F E u)

def ldPartKeyFam_v : Prop :=
  ∀ (X F E St J : Type) [Field F] [Field E] [Algebra F E] (K : LdPartKeys X F E) (h k : ℕ)
      (R : LdPartRd E J) (xs : St → X),
    K.keyFam.v = K.g + K.v ∧ (K.lk h k R xs).g = K.g ∧ (K.lk h k R xs).v = K.v

/-- States: for well-formed families, the joint family has the joint shifted keys (`shKey`,
Cb/Ld/LdLkpShift.lean) as its values at the vertices. -/
def ldPartKeyFam_vtx : Prop :=
  ∀ (X F E St J : Type) [Field F] [Field E] [Algebra F E] (K : LdPartKeys X F E) (Φ : IdxFmt F)
      (h k : ℕ) (R : LdPartRd E J) (xs : St → X) (st : St) (m : J → E) (θ : E),
    (∀ f < K.nk, (K.fam f).WF Φ) →
    ∀ b < 2 ^ (K.g + K.v), K.keyFam.ext h k (xs st, θ) (R.W m) (R.A m) (vtx (K.g + K.v) b) =
      shKey (K.lk h k R xs).P.v ((K.lk h k R xs).P.key st m) (K.lk h k R xs).P.tag θ b

def ldPartKeyFam_wf : Prop :=
  ∀ (X F E : Type) [Field F] [Field E] [Algebra F E] (K : LdPartKeys X F E) (Φ : IdxFmt F),
    (∀ f < K.nk, (K.fam f).WF Φ) → K.keyFam.WF Φ

/-- States: a number d that bounds, in every family, the atoms of a term and of a term of an inner
sum (`Fam.DegLe d`) bounds them in the joint family. -/
def ldPartKeyFam_deg : Prop :=
  ∀ (X F E : Type) [Field F] [Field E] [Algebra F E] (K : LdPartKeys X F E) (d : ℕ),
    (∀ f < K.nk, (K.fam f).DegLe d) → K.keyFam.DegLe d

def ldPartKeyFam_places : Prop :=
  ∀ (X F E : Type) [Field F] [Field E] [Algebra F E] (K : LdPartKeys X F E) (Φ : IdxFmt F),
    (∀ f < K.nk, (K.fam f).WF Φ) → ∀ p, p ∈ K.keyFam.places ↔ ∃ f < K.nk, p ∈ (K.fam f).places

end Spec
end Cb
