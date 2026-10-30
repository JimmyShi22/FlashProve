-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
In this library the records through which a count for agreement is claimed (`IsGlJ`, `IsGlS`:
Cb/Gl/GlLdJ.lean; `IsGlCpJ`: Cb/Gl/GlCopy.lean) do not ask a
radius within half the distance, and the fact on agreement, `Gl.AgreeJ`, is stated nowhere as a
separate theorem: it follows, by one application that is written down nowhere, from `Cb.BCHKS46At`
(`Cb.Gl.glAg_ofAt`, Cb/Gl/GlFinalAg.lean), which this library proves in Cb/Bridge (bchks46At), from
files adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15), and applies in second forms of some of its theorems (files named `…Codes.lean` under
Johnson/; a bound on the entry file's closed check); this file
does not apply that proof.
So read the Lean text, not the words below, to see
what is a hypothesis here: neither "the statement on codes" nor "the fact on agreement" in these
words tells whether it is one.
A theorem with no premise rests on nothing unproved beyond Lean's three axioms (a theorem's premises
are the hypotheses in its statement; how the axioms are checked: lean/CHECKING.md). A theorem that
has the premise Gl.AgreeJ takes it as a hypothesis: this library states it nowhere as a separate
theorem (only its conclusion within half the distance: agreeHalf, Cb/Gl/GlAgreeHalf.lean). A
statement that has the premise Cb.BCHKS46, BCHKS46F or BCHKS46At takes it as a hypothesis; this file
does not prove it. Cb/Bridge/ proves BCHKS46 and BCHKS46At from the files under ThirdParty/,
which are adapted from ArkLib and Mathlib, and BCHKS46F follows from the first by one
line
(Cb.bchks46F_of_wide). Its
source: Theorem 4.6 of the full version (ePrint 2025/2055) of a paper published at STOC 2026; the
theorem is not in the proceedings, which state the plain form (their Theorem 1.5). Of a statement
with any other premise these lines say nothing: it rests on what that premise asks. (More on the
source, of which no full proof was checked for this library: the head of
Cb/Gen/CodeListRS.lean.) Cb/GlVal/GlJ3SegRefToyMd.lean: a small example of an indexed relation with
its relaxed form, for the small example instances of the interactive proof for a request. It is the
relation pair of the toy reference request (`Cc`,
Cb/GlVal/GlJ3SegRefToyAll.lean, stands on `Md`): a relation that says something, of the cells and of
the index.

Definitions, statement (`Cb.GlJ3.Spec.ldSegRef_toyMd`) and proof. A guard against empty theorems; no
parameter of a protocol.
A relation pair (`ToyMd`, Cb/GlVal/GlToyConfM.lean) is the exact relation `Ryes` and the relaxed
relation `Rno` of a toy configuration, with a trace. Here the relation pair is the entry claim of
the toy reference segment: the packing, the front's entry claim (`FrontToy.EntryP`,
`FrontToy.EntryR`, Cb/GlVal/GlJ3SegFrontToy.lean) and the tensor row, read at the data that are no
masks.
Why: here the two fields meet in a relation: the index's entries lie in F, the cells in E: `tenI`
and `dat01` read the entries through `algebraMap F E`; the last clause of the statement is 5 ≠ 7 in
F.

Main names:
  `RDn`: the names of the data that are no masks: the packed entry; the four bits of the
    multiplicities; a₀, a₁; the incoming mask of the tensor row (a mask of an earlier block: a datum
    here); three idle entries.
  The cells: (a value for each name in `RDn`, the ghost: the matrix of two integer cells).
  `cellK c b`, `rVec c`: the two virtual cells, read off the packed entry; the vector of all entries
    of the front: the keys 5 + 2 · cell, the bits, a₀, a₁; all masks 0.
  `tenI i μ`: the tensor row: (the table of the index i at the first corner) + μ = 0.
  `Md`: instances: Unit. `Ryes i _ c`: the ghost is below 2 in absolute value and is packed in the
    packed entry; both keys are in the table (5, 7), a₀ and a₁ are bits, the bits are the
    multiplicities; the tensor row at i. `Rno`: the packed entry is a packing of cells below 4 in
    absolute value; keys in the table, a₀ and a₁ bits; the tensor row at i. `trace i`: the cells
    (0, 1), so the keys (5, 7); each table entry once; a₀ = a₁ = 0; μ = minus the table of i at the
    first corner.
  `Spec.ldSegRef_toyMd` states: `Md.OK` (`ToyMd.OK`, Cb/GlVal/GlToyConfM.lean: `Ryes` implies `Rno`;
    where some cells meet `Ryes`, the trace does); at every index the trace meets `Ryes`; the trace
    with μ := 0 does not even meet `Rno`; the relation depends on the index: cells that meet `Rno`
    at i and at i' force the tables of i and i' to agree at the first corner, and there are two
    indices whose tables differ there (`ix5`, `ix7`).

Conventions of this namespace's toys, said of the toys' own oracle messages and groups, not of what
a statement takes as a parameter (of the names declared in Cb/GlVal/ and Cb/Gl/GlField.lean this
file uses only the fields F and E with `up_inj`, `up_ofNat`, `n57F`, Cb/GlVal/GlToyBase.lean,
`RefToy.p` with `uniq`, Cb/GlVal/GlJ3SegRefToy.lean, `FrontToy.JJ`, `ent`, `EntryP`, `EntryR`,
Cb/GlVal/GlJ3SegFrontToy.lean, with `ldSegFront_toy`, Cb/GlVal/GlJ3SegFrontToyProofs.lean, `wit`,
`w57`, Cb/GlVal/GlToyLkpNames.lean, `ToyMd`, Cb/GlVal/GlToyConfM.lean, `ToyMo8.two`,
Cb/GlVal/GlToyConf.lean, and `pK`, `natK_ne`, Cb/GlVal/GlToyNum.lean; it has no oracle message): the
fields are F, the integers modulo 2^64 - 2^32 + 1, and E = F[x] / (x^3 - 2) (Cb/Gl/GlField.lean).
The toys' code is that of Cb/GlVal/GlToyBase4.lean: eight points, dimension 4, distance 5, hides 3.
The radius, the bounds on lists, the counts for agreement and the pad's coefficient of these toys
are told in the head of Cb/GlVal/GlJ3Base.lean: read it before quoting.
This is not said of the offline side (configuration, index, lookup tables, weights-formedness).

Limits: instances are trivial. The toy front's first explicit part is Unit: nothing could read an
instance. This file says nothing on real parameters. Degenerate; whoever quotes a guard that stands
on this file quotes this with it: the relation pair is not "true" (not the constant True, as in
`ToyMd.triv`, Cb/GlVal/GlToyConfM.lean) but it is tautological: `Ryes` and `Rno` are the exact and
the relaxed form of the toy request's own entry claim, so the entry step (its statement is not in
this library) holds by construction; no model of a computation stands behind it. One instance. Pads
in the subfield F are not exercised.

Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyNum
import Cb.GlVal.GlToyLkpNames
import Cb.GlVal.GlJ3Send
import Cb.GlVal.GlToyConfM
import Cb.GlVal.GlJ3PackNames
import Cb.GlVal.GlJ3SegRefToy
import Cb.GlVal.GlJ3SegFrontToyProofs
import Cb.Ld.LdRngAlgProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb.GlJ3
open Cb.Gl hiding p
namespace RefToy
open Iop Prob Hiop Cb.Gl.LkpToy Cb.Rng Cb.RngPk

/-- The names of the data that are no masks. -/
abbrev RDn : Type := Unit ⊕ ((Bool × Bool) ⊕ (Bool ⊕ (Unit ⊕ (Unit ⊕ (Unit ⊕ Unit)))))
def dPk : RDn := .inl ()
def dBit (ub : Bool × Bool) : RDn := .inr (.inl ub)
def dA (b : Bool) : RDn := .inr (.inr (.inl b))
def dMk : RDn := .inr (.inr (.inr (.inl ())))

/-- the virtual cells -/
def cellK (c : RDn → E) (b : Bool) : E :=
  ((cells p.P (2 * p.D) p.rdx (fun (_ : p.Rp) (_ : p.C) => c dPk)
    ((), if b then 1 else 0) () : ℤ) : E)

/-- The vector of all entries of the front. -/
def rVec (c : RDn → E) : FrontToy.JJ → E :=
  FrontToy.ent (wit (fun b => 5 + 2 * cellK c b) fun ub => c (dBit ub)) fun b => c (dA b)

/-- The tensor row. -/
def tenI (i : ToyMo8.two.I) (μ : E) : Prop :=
  Alg.mle (fun cc => ∑ _r : Unit, (1 : E) * algebraMap F E (i.1 (cc, ()))) (fun _ : Fin 1 => 0) +
      1 * μ = 0

/-- the honest ghost: the cells (0, 1) -/
def gh01 : p.Cells := fun r _ => if r.2 = 1 then 1 else 0

/-- the honest data at the index i -/
def dat01 (i : ToyMo8.two.I) : RDn → E
  | .inl _ => 7
  | .inr (.inl ub) => if ub.2 then 0 else 1
  | .inr (.inr (.inl _)) => 0
  | .inr (.inr (.inr (.inl _))) => - algebraMap F E (i.1 (fun _ => false, ()))
  | .inr (.inr (.inr (.inr _))) => 0

/-- The relation pair. -/
def Md : ToyMd ToyMo8.two.I where
  Xm := Unit
  Cells := (RDn → E) × p.Cells
  Ryes := fun i _ c =>
    PackBy p.B p.rdx c.2 (fun (_ : p.Rp) (_ : p.C) => c.1 dPk) ∧
    FrontToy.EntryP (rVec c.1) ∧
    tenI i (c.1 dMk)
  Rno := fun i _ c =>
    Packed p.P (2 * p.D) p.rdx (fun (_ : p.Rp) (_ : p.C) => c.1 dPk) ∧
    FrontToy.EntryR (rVec c.1) ∧
    tenI i (c.1 dMk)
  trace := fun i _ => (dat01 i, gh01)
  cells0 := (fun _ => 0, fun _ _ => 0)

theorem tenI_iff (i : ToyMo8.two.I) (μ : E) :
    tenI i μ ↔ algebraMap F E (i.1 (fun _ => false, ())) + μ = 0 := by
  have e : (fun _ : Fin 1 => (0 : E)) = Alg.corner (fun _ => false) :=
    funext fun _ => by simp [Alg.corner]
  unfold tenI
  rw [e, Alg.mle_corner]
  simp

theorem pack01 (i : ToyMo8.two.I) :
    PackBy p.B p.rdx gh01 (fun (_ : p.Rp) (_ : p.C) => dat01 i dPk) := by
  refine ⟨fun r c => ?_, fun _ _ => ?_⟩
  · unfold gh01
    split <;> decide
  · show (7 : E) = pack 7 (fun r => ((gh01 r () : ℤ) : E)) ()
    simp [pack, gh01]

theorem cell01 (i : ToyMo8.two.I) (b : Bool) : cellK (dat01 i) b = if b then 1 else 0 := by
  unfold cellK
  rw [rngPk_cells E pK p.Rp p.C p.P (2 * p.D) p.B p.rdx gh01 _ uniq (by decide) (pack01 i)]
  cases b <;> simp [gh01]

theorem rVec01 (i : ToyMo8.two.I) : rVec (dat01 i) = FrontToy.ent w57 fun _ => 0 := by
  unfold rVec w57
  congr 2
  funext b
  rw [cell01]
  cases b <;> norm_num

theorem ryes_trace (i : ToyMo8.two.I) (x : Md.Xm) : Md.Ryes i x (Md.trace i x) :=
  ⟨pack01 i,
    by rw [show (Md.trace i x).1 = dat01 i from rfl, rVec01]; exact ldSegFront_toy.2.2.1,
    (tenI_iff i _).2 (add_neg_cancel _)⟩

theorem mdOK : Md.OK where
  sub := fun _ _ c h =>
    ⟨⟨c.2, fun r cc => lt_of_lt_of_le (h.1.1 r cc) (by decide), h.1.2⟩, ⟨h.2.1.1, h.2.1.2.1⟩, h.2.2⟩
  admits := fun i x _ _ => ryes_trace i x

/-- the trace with the tensor row's mask set to 0 does not even meet the relaxed relation -/
theorem not_rno0 (i : ToyMo8.two.I) (x : Md.Xm) :
    ¬ Md.Rno i x (Function.update (dat01 i) dMk 0, gh01) := by
  rintro ⟨-, -, h⟩
  have h' : algebraMap F E (i.1 (fun _ => false, ())) + Function.update (dat01 i) dMk 0 dMk = 0 :=
    (tenI_iff i _).1 h
  rw [Function.update_self] at h'
  rw [add_zero] at h'
  rcases i.2 (fun _ => false, ()) with e | e <;> rw [e, up_ofNat] at h'
  · exact absurd h'
      (by simpa using natK_ne (m := 5) (n := 0) (by norm_num) (by norm_num) (by norm_num))
  · exact absurd h'
      (by simpa using natK_ne (m := 7) (n := 0) (by norm_num) (by norm_num) (by norm_num))

/-- The relation depends on the index: cells that meet `Rno` at i and at i' force the tables of i
and i' to agree at the first corner. -/
theorem rno_index (i i' : ToyMo8.two.I) (x : Md.Xm) (c : Md.Cells)
    (h : Md.Rno i x c) (h' : Md.Rno i' x c) :
    i.1 (fun _ => false, ()) = i'.1 (fun _ => false, ()) :=
  up_inj (add_right_cancel (((tenI_iff i _).1 h.2.2).trans ((tenI_iff i' _).1 h'.2.2).symm))

def ix5 : ToyMo8.two.I := ⟨fun _ => 5, fun _ => Or.inl rfl⟩
def ix7 : ToyMo8.two.I := ⟨fun _ => 7, fun _ => Or.inr rfl⟩

end RefToy

namespace Spec
open RefToy

def ldSegRef_toyMd : Prop :=
  Md.OK ∧ (∀ i x, Md.Ryes i x (Md.trace i x)) ∧
  (∀ i x, ¬ Md.Rno i x (Function.update (dat01 i) dMk 0, gh01)) ∧
  (∀ i i' x c,
    Md.Rno i x c → Md.Rno i' x c → i.1 (fun _ => false, ()) = i'.1 (fun _ => false, ())) ∧
  ix5.1 (fun _ => false, ()) ≠ ix7.1 (fun _ => false, ())

end Spec

open RefToy in
theorem ldSegRef_toyMd : Spec.ldSegRef_toyMd := ⟨mdOK, ryes_trace, not_rno0, rno_index, n57F⟩

end Cb.GlJ3
