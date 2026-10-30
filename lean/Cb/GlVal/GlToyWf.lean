-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/GlVal/GlToyWf.lean: the data of a small test instance of the preamble of weights-formedness, the
sub-protocol for the claim that an encoded index decodes to a message that holds an index, where
lookups describe the index set. Here: one lookup with two keys and the table (5, 7), over the field
with p = 2^64 - 2^32 + 1 elements and its cubic extension.

Definitions. The laws: Cb/GlVal/GlToyWfProofs.lean. A guard against empty theorems; no parameter of
a protocol.
The data of a preamble are a value of the structure `LdWfP` (Cb/Ld/LdWf.lean); with the data of the
test that follows, of `LdOWf` (Cb/Obj/LdObjectWf.lean). A forest is a family of keys with its table.
The named entries (`LdWfP.N`) are the entries of the messages that rows and mask forms may read.
The analogue, over two different fields, of Cb/Ld/LdWfToy.lean (one field with 101 elements). What
is new: F ≠ E. The entries of an index message, and the index set, are over F (the integers modulo
p); the matrix of the index, keys, table, bits, masks, codes as read, challenges are over
E = F[x] / (x^3 - 2). An entry reaches a key through the embedding of F in E (`Cf.upM`).

The claim. At the toy configuration over the code on the subgroup of order 8 with the proper index
set (`Cf` := `toyCf8 ToyMo8.two`, Cb/GlVal/GlToyConf.lean): the message of an encoded index has two
rows with one entry each; it holds an index if and only if both entries are 5 or 7 (in F)
(`held_iff`, Cb/GlVal/GlToyWfProofs.lean).

Main names; the data of the names below are as at the toy over 101 elements, but for the family's
code, radius and pad coefficient:
  `key`, `tab`: one forest, two keys: the two entries of the matrix (offsets 0, coefficients 1);
    table (5, 7) in E.
  `Kl`: the lookup's numbers and 35 own masks: those of Cb/Ld/LdLkpToyE.lean at E (`LkpToyE.Mk E`:
    the masks' names); and where bits and masks are among the named entries. Its fields
    (`LdWfP.Lks`, Cb/Ld/LdWfBlocks.lean): the number of keys as 2^(v' + 1); 2^w bit positions of
    which the first n + 1 count; `bAt`: where the bits stand; the other eleven: where the own masks
    stand (`LkAsm2.plN`, Cb/Ld/LdLkpMaskPlaces2.lean).
  `Fm`: the family sent (`fam8`, Cb/GlVal/GlToyFam.lean): a named member with the 4 bits of the
    multiplicities (`Ix`), a mask-only member with 39 entries (`Im`: 35 + the batching's 3 + one
    idle, which the levels that are never played name); each with a pad; radius 1.
  `Nm`: the named entries; `mkAt`, `btAt`, `idle` name the lookup's, the batching's and the idle one
    among them.
  `P`: the data of the preamble. Public supports: of the mask form: the lookup's own masks; of a
    row: all named entries but the batching's three. The batching: one claim, degree 2.
Notation (fields of `LdWfP`, Cb/Ld/LdWf.lean): `n`: the forests are 0, .., n; `v`, `d`: numbers of
variables of keys and tables; `nR`: the number of rows that the lookup on a forest files; `off`,
`gOf`, `cOf`: of a key map: constant, row factor and point of the column factor.
Names: those of Cb/Ld/LdWfToy.lean, but for the family, which is `Fm` here (F is the field).
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdWfEnd
import Cb.Ld.LdLkpToyE
import Cb.GlVal.GlToyFam
import Cb.GlVal.GlToyConf

set_option autoImplicit false

namespace Cb.Gl
namespace Wf8
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.LdLkp Cb.Lkp

noncomputable section

/-- The configuration. -/
abbrev Cf : LdCf F E := toyCf8 ToyMo8.two

/-- The names of the coefficients of the batching's hiding polynomial. -/
abbrev WBt : Type := PIdx (List.replicate 1 (pfCube E 2))
/-- `Ix`: the names of the bits of the multiplicities: (table entry, bit position). `Im`, below: the
names of the mask entries: the lookup's, the batching's, an idle one. -/
abbrev Ix : Type := Bool × Bool
abbrev Im : Type := LkpToyE.Mk E ⊕ (WBt ⊕ Unit)

instance decIm : DecidableEq Im := Classical.decEq _

/-- The family sent. -/
abbrev Fm : StdFam E := fam8 Ix Im Ix Im (fun i j => decide (j = i)) (fun i j => decide (j = i))

/-- The named entries. -/
abbrev Nm : Type := Ix ⊕ Im
def mkAt (i : LkpToyE.Mk E) : Nm := .inr (.inl i)
def btAt (i : WBt) : Nm := .inr (.inr (.inl i))
def idle : Nm := .inr (.inr (.inr ()))

/-- The matrix of the index: the entries over F, embedded in E. -/
def mat (U : Cf.conf.Msg) (a : Unit × (Fin 1 → Bool)) : E := Cf.upM U (a.2, Sum.inl ())
/-- The keys; `tab`, below: the table. -/
def key (U : Cf.conf.Msg) (b : ℕ) : E := 0 + ∑ r : Unit, 1 * mat U (r, Alg.bits 1 (b % 2 ^ 1))
def tab (u : ℕ) : E := if u = 0 then 5 else 7
/-- Bits as the lookup reads them. -/
def bitOf (bd : Ix → E) : ℕ → ℕ → E := fun u j => bd (decide (u = 1), decide (j = 1))
open Classical in
/-- How often x is a key. -/
def cntK (U : Cf.conf.Msg) (x : E) : ℕ :=
  (if key U 0 = x then 1 else 0) + (if key U 1 = x then 1 else 0)
/-- The honest bits. -/
def bodyOf (U : Cf.conf.Msg) : Ix → E := fun ub =>
  if (cntK U (if ub.1 then 7 else 5)).testBit (if ub.2 then 1 else 0) then 1 else 0

/-- The data of the preamble. -/
@[reducible] def P : LdWfP E Cf.conf where
  S := Fm.sig
  Sd := Sig.Seeds.indep Fm.sig
  Body := Ix → E
  body := Fm.vec
  bodyOf := bodyOf
  N := Nm
  ent := fun m => Sum.elim (Fm.vec m) (Fm.msk m)
  n := 0
  v := fun _ => 1
  d := fun _ => 1
  key := fun _ => key
  tab := fun _ => tab
  mult := fun _ U bd => Valid 1 1 1 2 (key U) tab (bitOf bd)
  nR := fun _ => 8
  gC := fun _ n => ∃ i, n = mkAt i
  gR := fun _ _ n => ∀ i, n ≠ btAt i
  Rw := Unit
  k := 1
  mat := mat
  off := fun _ z => ext 0 (fun _ => 0) z
  gOf := fun _ z _ => ext 0 (fun _ => 1) z
  cOf := fun _ z i => z (0 + (i : ℕ))
  Z := Evader.powers E (0 + 1)
  deg := 2
  wAt := btAt

/-- The places and numbers of the lookup. -/
@[reducible] def Kl : P.Lks where
  v' := fun _ => 0
  w := fun _ => 1
  n := fun _ => 1
  bAt := fun _ u j => .inl (decide (u = 1), decide (j = 1))
  wS := fun _ i => mkAt (.inl (.inl (.inl i)))
  cS := fun _ b => mkAt (.inl (.inl (.inr b)))
  wAt := fun _ l => match l with
    | 0 => fun i => mkAt (.inl (.inr (.inl i)))
    | _ + 1 => fun _ => idle
  cAt := fun _ l => match l with
    | 0 => fun b => mkAt (.inl (.inr (.inr b)))
    | _ + 1 => fun _ => idle
  wK := fun _ l => match l with
    | 0 => fun i => mkAt (.inr (.inl (.inl (.inl i))))
    | _ + 1 => fun _ => idle
  cK := fun _ l => match l with
    | 0 => fun b => mkAt (.inr (.inl (.inl (.inr b))))
    | _ + 1 => fun _ => idle
  wT := fun _ l => match l with
    | 0 => fun i => mkAt (.inr (.inl (.inr (.inl i))))
    | _ + 1 => fun _ => idle
  cT := fun _ l => match l with
    | 0 => fun b => mkAt (.inr (.inl (.inr (.inr b))))
    | _ + 1 => fun _ => idle
  wE := fun _ i => mkAt (.inr (.inr (.inl i)))
  wB := fun _ i => mkAt (.inr (.inr (.inr (.inl i))))
  cB := fun _ => mkAt (.inr (.inr (.inr (.inr ()))))

/-- What the test that follows needs beside: a parameter. -/
structure ToyLn : Type 1 where
  l   : ℕ
  py  : Unit → Fin l → Bool
  e' : ℕ
  t  : ℕ
  NW  : Sig E
  SdW : NW.Seeds
  iW  : NW.O
  lW  : ((Fin Cf.X.v ⊕ Fin 0) → Bool) → (NW.om iW).C.J
  NU  : Sig E
  SdU : NU.Seeds
  iU  : NU.O
  lU  : Fin Cf.C₀.k → (NU.om iU).C.J
  NO  : Sig E
  SdO : NO.Seeds
  iO  : NO.O
  lO  : Unit → (NO.om iO).C.J

/-- The data of the preamble and of the test. -/
@[reducible] def W (Ln : ToyLn) : LdOWf F E where
  Cf := Cf
  P := P
  klo := 0
  e := (Equiv.sumEmpty (Fin 1) (Fin 0)).symm
  l := Ln.l
  lay := fun _ => ()
  py := Ln.py
  e' := Ln.e'
  t := Ln.t
  NW := Ln.NW
  SdW := Ln.SdW
  iW := Ln.iW
  lW := Ln.lW
  NU := Ln.NU
  SdU := Ln.SdU
  iU := Ln.iU
  lU := Ln.lU
  NO := Ln.NO
  SdO := Ln.SdO
  iO := Ln.iO
  lO := Ln.lO

/-- A fixed prover encoded index. -/
def p0 : Cf.conf.PIdx := ((fun _ => 0, fun _ _ => 0), ((), fun a => a.2.elim))

end
end Wf8
end Cb.Gl
