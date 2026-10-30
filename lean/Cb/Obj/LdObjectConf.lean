-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectConf.lean: how the index is encoded and decoded: row by row under a linear code, so
that a word is an interleaved word, with a sample taken of the message; and the properties of this
encoding that the holographic IOP requires of a configuration (`ConfigurationWithOutOfDomainSample.Props`), each from named
conditions.

Definitions and statements (each a `Prop` in `Cb.Spec`); the proofs are in
Cb/Obj/LdObjectConfProofs.lean. The sub-protocols of the object (`LdObj`, Cb/Obj/LdObject.lean) are
stated over this configuration.

A configuration (`ConfigurationWithOutOfDomainSample`, Hiop/RecConf.lean) fixes an index set with a relation and its relaxation,
a randomised encoder of messages into words of n symbols, which message holds which index, and a
record phase. A record (`ConfigurationWithOutOfDomainSample.Rec`) is a seed with answers.
The list of a word has the tables of full messages whose codewords are within eM columns of it. The
word has a collision at a seed (`LdIx.Coll`, Cb/Ld/LdFoldEq.lean) if two members of the list have
different message parts and the same answers there; it decodes with a record (`LdIx.dec`) to the
message part of the nearest member of the list that has the record's answers (among equally near
ones one of least `rank`), or to none if there is no such member.

The data (`LdCf F E`):
  the code: `C₀`, a code with encoder over the small field F (Code/Iface.lean), read over E where it
    is tested.
  the format: v row variables (the rows are the vertices of a cube). The message part of a row has
    coordinates J₀ ⊕ Pd: J₀ all entries but the pads, Pd the pads. `lay` names, among J₀, the
    layout: the places where the index proper is (there may be further places off it: what `body i`
    has there for the honest committer, anything in a relaxed relation). Z is the sample map of one
    row, eM the radius of decoding, `rank` the decoder's fixed order (it is a total order if `rank`
    is injective; no clause of this file asks that).
  the model: index set I, instances, cells, the relation pair, the trace; `body i`: the entries of
    the index i at J₀, in F; `heldB`: the index that such entries hold, if any. `Cf.OK` asks that
    heldB read the layout only: this is what turns "agree on the layout" into "the same index"
    (`Spec.ldCf_held_same`).

The configuration (`Cf.conf`):
  `Msg`: the message parts of all rows, pads included, with entries in F. (So every message has an
    encoding in the format, and "decoding undoes encoding" can hold of every message.)
  `Rnd`, `Pad`: the rows' encoding randomness; one pad for each row; all over F.
  `hold i η`: body i at J₀, η on the pads. `held` does not read the pads (by definition), and of J₀
    the layout only (`Cf.OK`).
  `Seed`, `Ans`: those of a record of the format: `Cf.conf.Rec` is `Cf.X.Rec` (by definition).
  `dcd`: `Cf.X.dec` of the word read as a table over E (`Cf.tab`), brought down to F (`downF`). (For
    eM below the distance every member of the list of a table over F is over F: `Cb.ldFc_overF`;
    so nothing is lost: `Spec.ldCf_dcd_iff`.)

Main names: the clauses of `ConfigurationWithOutOfDomainSample.Props`, each from named conditions:
  `Spec.ldCf_dcd_enc`, `Spec.ldCf_free_enc`: from the distance, and eM below it.
  `Spec.ldCf_held_hold`: from heldB (body i) = some i.
  `Spec.ldCf_rcd`: the record binds: (L choose 2)·err seeds at most, for every word, under `Cf.OK L`
    (among its clauses: lists of at most L, Z a zero-evader on the vectors whose pad part is in F;
    `Cb.ldFc_binds`).
  `Spec.ldCf_strong`: the encoding is strong at b ≤ the code's own number: from `Enc.Core`
    (Cb/Gen/CodeList.lean).
  `Spec.ldCf_rows`: the pads mask the answers: Hiop's `Rows.Laws` from `Cf.PadBij`: at every seed
    and for all other entries of the row, pad ↦ answers of the row is a bijection.
  `Spec.ldCf_hides`: under `Cf.C₀.Core`, b ≤ C₀.b and `Cf.PadBij`: so the record hides
    (`Hiop.rec_hides_of_rows`).
  `Spec.ldCf_props`: `ConfigurationWithOutOfDomainSample.Props b ((L choose 2)·err)` from `Cf.OK L` and `Cf.PadBij` and b ≤ C₀.b.
  `Spec.ldCf_padBij_pad`: for a non-empty set B (a seed is a point with a β in B; the pad's
    coefficient is b β): for the row with a pad (`Sample.pad`): PadBij from: the pad's weights are a
    basis of E over F, and no seed has β = 0 (in Lean: b β ≠ 0 for every β).



Why `hp` (a proof among the data): the code's message places are among its k coordinates (C₀.msg ≤
C₀.k). It is needed to write the format down; `Enc.Core` implies it.

Limits: (1) `Msg` is over F and `dcd` brings down: the format's decoder returns vectors over E. (2)
The positions are Fin C₀.n. (3) `plE` is an equivalence: message part and pads fill the message
places of the code. (4) Exact laws only.
No bound on L is proved here. `Cb.ldFc_list_johnson` gives one below the Johnson radius. On the
model this file has its data, nine fields of `LdCf` (`I`, `Xm`, `Cells`, `Ryes`, `Rno`, `trace`,
`cells0`, `body`, `heldB`), and three statements that name them or `hold`, `held`:
`Spec.ldCf_held_hold`, `Spec.ldCf_held_same`, `Spec.ldCf_D`; `Cf.conf` and `Cf.rows`, on which other
statements of the file are, take the fields over. This file gives no value for any of the nine
fields. What it asks of the model's fields: the clauses `sub`, `admits`, `held`, `reads` of `Cf.OK`.
One record for each encoded index. Hiop/RecRows.lean says why. This file says nothing on the value
of any number.
`Cb.ldFc_overF`, `Cb.ldFc_binds`, `Cb.ldFc_list_johnson` are in Cb/Ld/LdFoldEqCodeProofs.lean.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdFoldEqCode
import Hiop.RecRows
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood

/-- The configuration: the data. -/
structure LdCf (F E : Type) [Field F] [Field E] [Algebra F E] where
  /-- the code -/
  C₀ : Code.Enc F
  hp : C₀.msg ≤ C₀.k
  /-- the format -/
  v  : ℕ
  J₀ : Type
  Pd : Type
  [finJ : Fintype J₀]
  [finP : Fintype Pd]
  [decP : DecidableEq Pd]
  /-- the layout, among the entries that are no pads -/
  Lay : Type
  [finL : Fintype Lay]
  lay : Lay → J₀
  plE : J₀ ⊕ Pd ≃ Fin C₀.msg
  Z  : Sample E (J₀ ⊕ Pd)
  eM : ℕ
  rank : ((Fin v → Bool) → Fin C₀.k → E) → ℕ
  /-- the model -/
  I     : Type
  Xm    : Type
  Cells : Type
  Ryes  : I → Xm → Cells → Prop
  Rno   : I → Xm → Cells → Prop
  trace : I → Xm → Cells
  cells0 : Cells
  body  : I → (Fin v → Bool) × J₀ → F
  heldB : ((Fin v → Bool) × J₀ → F) → Option I

attribute [instance] LdCf.finJ LdCf.finP LdCf.decP LdCf.finL

/-- a fixed F-linear map from E to F that is the identity on F -/
def downF (F E : Type) [Field F] [Field E] [Algebra F E] : E →ₗ[F] F :=
  (Code.exists_form_algebraMap F E).choose

namespace LdCf
variable {F E : Type} [Field F] [Field E] [Algebra F E] (Cf : LdCf F E)

abbrev Row : Type := Fin Cf.v → Bool
abbrev J : Type := Cf.J₀ ⊕ Cf.Pd

/-- The format of the encoded index. -/
def X : LdIx E (Fin Cf.C₀.n) (Fin Cf.C₀.k) Cf.J :=
  LdIx.ofEnc E Cf.C₀ Cf.hp Cf.plE Cf.v Cf.Z Cf.eM Cf.rank

/-- a column as sent; messages, encoding randomness, pads: all over F -/
abbrev Sg : Type := Cf.Row → F
abbrev Msg : Type := Cf.Row × Cf.J → F
abbrev Rnd : Type := Cf.Row → Fin Cf.C₀.r → F
abbrev Pad : Type := Cf.Row → Cf.Pd → F

/-- a word as a table over E -/
def tab (y : Fin Cf.C₀.n → Cf.Sg) : Cf.Row → Fin Cf.C₀.n → E := fun r j => algebraMap F E (y j r)
/-- the same over F -/
def tabF (y : Fin Cf.C₀.n → Cf.Sg) : Cf.Row → Fin Cf.C₀.n → F := fun r j => y j r

/-- the message of the row r, on the message places of the code -/
def mrow (m : Cf.Msg) (r : Cf.Row) : Fin Cf.C₀.msg → F := fun s => m (r, Cf.plE.symm s)
/-- the full messages of the rows -/
def full (m : Cf.Msg) (ρ : Cf.Rnd) : Cf.Row → Fin Cf.C₀.k → F := fun r =>
  Cf.C₀.fm (Cf.mrow m r) (ρ r)

/-- The encoder: row by row. -/
def enc (m : Cf.Msg) (ρ : Cf.Rnd) : Fin Cf.C₀.n → Cf.Sg := fun j r =>
  Cf.C₀.enc (Cf.mrow m r) (ρ r) j

/-- a message over F, read over E; a vector over E, brought down -/
def upM (m : Cf.Msg) : Cf.Row × Cf.J → E := fun n => algebraMap F E (m n)
def dnM (U : Cf.Row × Cf.J → E) : Cf.Msg := fun n => downF F E (U n)

/-- The message that holds an index, with these pads; the index that a message holds. -/
def hold (i : Cf.I) (η : Cf.Pad) : Cf.Msg := fun n => match n.2 with
  | .inl j => Cf.body i (n.1, j)
  | .inr p => η n.1 p
def held (m : Cf.Msg) : Option Cf.I := Cf.heldB fun n => m (n.1, .inl n.2)

variable [Fintype F]

/-- The configuration. -/
def conf : ConfigurationWithOutOfDomainSample where
  I := Cf.I
  X := Cf.Xm
  Cells := Cf.Cells
  Ryes := Cf.Ryes
  Rno := Cf.Rno
  n := Cf.C₀.n
  Sg := Cf.Sg
  Msg := Cf.Msg
  Rnd := Cf.Rnd
  enc := Cf.enc
  Pad := Cf.Pad
  hold := Cf.hold
  held := Cf.held
  Seed := Cf.Z.D
  Ans := Cf.Row × Cf.Z.S → E
  smp := fun s m => Cf.X.ZR.val s (Cf.upM m)
  coll := fun y s => Cf.X.Coll (Cf.tab y) s
  dcd := fun y rec => (Cf.X.dec (Cf.tab y) rec).map Cf.dnM
  trace := Cf.trace
  cells0 := Cf.cells0

/-- The named conditions on code, format and model; L bounds the lists at the radius of decoding. -/
structure OK (L : ℕ) : Prop where
  core   : Cf.C₀.Core
  rad    : Cf.eM < Cf.C₀.d
  list   : ∀ f₀ : Cf.Row → Fin Cf.C₀.n → F,
    ListLE (DecodesTo (Cf.C₀.GE E) Cf.eM fun a => Code.liftWord E (f₀ a)) L
  evades : Cf.Z.OKOn (PadInF F)
  sub    : ∀ i x w, Cf.Ryes i x w → Cf.Rno i x w
  admits : ∀ i x w, Cf.Ryes i x w → Cf.Ryes i x (Cf.trace i x)
  held   : ∀ i, Cf.heldB (Cf.body i) = some i
  reads  : ∀ a a' : Cf.Row × Cf.J₀ → F,
    (∀ r l, a (r, Cf.lay l) = a' (r, Cf.lay l)) → Cf.heldB a = Cf.heldB a'

omit [Fintype F] in
/-- The pad of a row masks the answers of the row: at every seed, whatever the other entries of the
row. -/
def PadBij : Prop :=
  ∀ (ρ : Cf.Z.D) (a : Cf.J₀ → E), Function.Bijective fun c : Cf.Pd → F => Cf.Z.val ρ (withPad a c)

open Classical in
/-- The index in rows (Hiop/RecRows.lean). -/
def rows [Fintype E] : Cf.conf.Rows where
  K := Cf.Row
  Row := Cf.J₀ → F
  PadR := Cf.Pd → F
  A := Cf.Z.S → E
  finA := Fintype.ofFinite _
  lay := fun i k j => Cf.body i (k, j)
  pads := Equiv.refl _
  answers := Equiv.curry _ _ _
  ansRow := fun s row pad => Cf.Z.val s (withPad (fun j => algebraMap F E (row j)) pad)

end LdCf

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def ldCf_dcd_enc : Prop :=
  ∀ (Cf : LdCf F E), HasDist Cf.C₀.G Cf.C₀.d → Cf.eM < Cf.C₀.d →
    ∀ m r s, Cf.conf.dcd (Cf.conf.enc m r) (s, Cf.conf.smp s m) = some m

def ldCf_free_enc : Prop :=
  ∀ (Cf : LdCf F E),
    HasDist Cf.C₀.G Cf.C₀.d → Cf.eM < Cf.C₀.d → ∀ m r s, ¬ Cf.conf.coll (Cf.conf.enc m r) s

def ldCf_held_hold : Prop :=
  ∀ (Cf : LdCf F E),
    (∀ i, Cf.heldB (Cf.body i) = some i) → ∀ i η, Cf.conf.held (Cf.conf.hold i η) = some i

/-- Under `Cf.OK L`, the record binds. -/
def ldCf_rcd : Prop :=
  ∀ (Cf : LdCf F E) (L : ℕ), Cf.OK L → ∀ y, cnt (fun s => Cf.conf.coll y s) ≤ L.choose 2 * Cf.Z.err

/-- Under the hypotheses below, the encoding is strong. -/
def ldCf_strong : Prop := ∀ (Cf : LdCf F E) (b : ℕ), Cf.C₀.Core → b ≤ Cf.C₀.b → Cf.conf.Strong b

def ldCf_rows : Prop := ∀ (Cf : LdCf F E), Cf.PadBij → Cf.rows.Laws

/-- Under the hypotheses below, the record hides. -/
def ldCf_hides : Prop :=
  ∀ (Cf : LdCf F E) (b : ℕ), Cf.C₀.Core → b ≤ Cf.C₀.b → Cf.PadBij → Cf.conf.Hides b

/-- The configuration has its properties, under the hypotheses below. -/
def ldCf_props : Prop :=
  ∀ (Cf : LdCf F E) (L b : ℕ),
    Cf.OK L → Cf.PadBij → b ≤ Cf.C₀.b → Cf.conf.Props b (L.choose 2 * Cf.Z.err)

/-- Under the hypotheses below, the row with a pad: its pad masks its answer, if the weights are a
basis and no seed has β = 0. -/
def ldCf_padBij_pad : Prop :=
  ∀ (μ J₀ P B : Type) [Fintype μ] [DecidableEq μ] [Fintype B] [Nonempty B] [Fintype J₀] [Fintype P]
      (plc : J₀ → μ → Bool) (w : P → E) (b : B → E),
    PadBasis F w → (∀ β, b β ≠ 0) →
    ∀ (ρ : (Sample.pad E μ J₀ P B plc w b).D) (a : J₀ → E),
      Function.Bijective fun c : P → F => (Sample.pad E μ J₀ P B plc w b).val ρ (withPad a c)

/-- Under the hypotheses below, the configuration's decoder loses nothing: what the format decodes
to is over F. -/
def ldCf_dcd_iff : Prop :=
  ∀ (Cf : LdCf F E), HasDist Cf.C₀.G Cf.C₀.d → Cf.eM < Cf.C₀.d →
    ∀ (y : Fin Cf.C₀.n → Cf.Sg) (rec : Cf.X.Rec) (m : Cf.Msg),
      Cf.conf.dcd y rec = some m ↔ Cf.X.dec (Cf.tab y) rec = some (Cf.upM m)

/-- Under `Cf.OK L`, agreement on the layout is "the same index". -/
def ldCf_held_same : Prop :=
  ∀ (Cf : LdCf F E) (L : ℕ), Cf.OK L →
    ∀ U U' : Cf.Row × Cf.J → E, (∀ r l, U (r, .inl (Cf.lay l)) = U' (r, .inl (Cf.lay l))) →
      Cf.held (Cf.dnM U) = Cf.held (Cf.dnM U')

/-- The index decoder, by the format's `Coll` and `dec`. -/
def ldCf_D : Prop :=
  ∀ (Cf : LdCf F E) (y : Fin Cf.C₀.n → Cf.Sg) (rec : Cf.X.Rec) (i : Cf.I),
    Cf.conf.D y rec = some i ↔
    ¬ Cf.X.Coll (Cf.tab y) rec.1 ∧
      ∃ U, Cf.X.dec (Cf.tab y) rec = some U ∧ Cf.held (Cf.dnM U) = some i

end
end Spec
end Cb
