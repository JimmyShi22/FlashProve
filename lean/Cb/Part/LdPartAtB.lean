-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartAtB.lean: a partition, read over the configuration over which its request is built.

Book-keeping: a partition is typed anew over the configuration that is built from it; under the
hypotheses of `Spec.ldPartAtB_props` it keeps its laws. Three definitions and five statements
(`Cb.Spec.ldPartAtB_idem` to `Cb.Spec.ldPartAtB_rel`); the proofs are in
Cb/Part/LdPartAtBProofs.lean. Glue on Lean's own records; nothing of this protocol's technical
report (lean/CREDITS.md) is rendered here.

Why: a request from a partition P : `LdPartD Cf` is built over the configuration `P.cfB K Bt`
(Cb/Part/LdPartCf.lean: the witness holds the data as they go out, and a ghost): the request's
start, its lists and its end stand over that configuration.
But one parameter Cf types both the partition and the
request's lists. The stages fit by definition; the records do not: a list over ⟨Cf.conf, ..⟩ is no
list over ⟨(P.cfB K Bt).conf, ..⟩. The cure: use the configuration `P.cfB K Bt`
and the partition Q := `P.atB K Bt`.


Why `ofMat` has its form: it has neither instance nor index at hand, so it cannot lay honest bits;
the relaxed relation `P.RnoB` does not read the bits, and "force" speaks of that relation alone.
Both parts read the cut matrix, because the law ofMat_congr asks that matrices which agree inside
the shapes give one value; "inside the shapes" includes "of a segment below P.n", and the packing's
own condition (row and column within segment j's matrix) does not bound j: packing M itself would
break the law at a layer beyond P.n (by reading).
In `ldPartAtB_rel` the relaxed relation, the condition and the core agree by definition; the exact
relation does not unify as it stands (it names the message that holds an index, a definition by
cases).

Main names:
  `P.atB K Bt : LdPartD (P.cfB K Bt)`: all structural fields are P's own (h, klo, lay, n, seg, form,
    Xr, req, matI, kept, B, D: they are typed by what `P.cfB` keeps of Cf); only the dictionary
    between cells and matrices differs: toMat t := the ghost t.2; ofMat M := (the packing of
    `P.cut M`, bits 0; `P.cut M`).
  `Spec.ldPartAtB_idem`: Q.cfB K (Bt.atB P K) = P.cfB K Bt (by definition).

  `Spec.ldPartAtB_props`: `P.Props p`, `P.Wide K`, 0 < K.P, unique packing, E of characteristic p
    (an instance argument) ⇒ `Q.Props p` (all sixteen clauses).
  `Spec.ldPartAtB_side`: Q.Wide K ⇔ P.Wide K; Q.BitsOK (Bt.atB P K) ⇔ P.BitsOK Bt.
  `Spec.ldPartAtB_bits`: the lookup's own parameters on bits at Q are P's: Q.bitsV.ok = P.bitsV.ok,
    Q.bitsV.hon = P.bitsV.hon.
  `Spec.ldPartAtB_rel`: what rides, and the entry relations, at Q are P's: equations of relations
    (the types agree by definition).

Limits: this file does not say `(P.cfB K Bt).ModelOK` (Cb/Part/LdPartCf.lean: `ldPartCf_model`). It
does not say that the ties, bodies, closings have values at Q. Are admit, force, ofMat_congr of Q
used by a step of a request? By design not (the model's steps unfold the built relation). By a
search of names in the texts, no proof: among the files Cb/Part/LdPart*.lean
these three clauses and the letters toMat, ofMat are named only in this file
with its proofs, in Cb/Part/LdPartDef.lean (their definition), Cb/Part/LdPartCf.lean with its proofs
(the tie of the built configuration to Cf); in comments alone also in Cb/Part/LdPartHead.lean;
a proof that takes the record apart without names would escape that search.

They are shown here because the theorems of the files that build segments from a partition take the
record `Props` whole. This file gives no instance that meets its hypotheses, so as far as this file
shows its theorems may hold of nothing.



Terms: lean/GLOSSARY.md.
-/
import Cb.Part.LdPartCf
import Cb.Part.LdPartNext
import Cb.Part.LdPartLkpBits
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks IOR Finset Cb.RngPk

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E] {Cf : LdCf F E} (P : LdPartD Cf)
  (K : LdPartPk) (Bt : LdPartBits P)

open Classical in
/-- an integer matrix, 0 outside the shapes -/
def LdPartD.cut (M : ℕ → ℕ → ℕ → ℤ) : ℕ → ℕ → ℕ → ℤ := fun s r c =>
  if P.InShape (s, r, c) then M s r c else 0

/-- the partition, read over the built configuration -/
def LdPartD.atB : LdPartD (P.cfB K Bt) where
  h := P.h
  klo := P.klo
  lay := P.lay
  n := P.n
  seg := P.seg
  form := P.form
  Xr := P.Xr
  req := P.req
  matI := P.matI
  toMat := fun t => t.2
  ofMat := fun M =>
    (⟨fun j i c =>
          ∑ l ∈ range K.P, ((K.rdx : ℤ) : E) ^ l *
            (((if i * K.P + l < 2 ^ (P.seg j).rowsLog ∧ c < (P.seg j).cols then
                P.cut M j (i * K.P + l) c
              else 0 : ℤ)) : E),
        fun _ _ => 0⟩,
      P.cut M)
  kept := P.kept
  B := P.B
  D := P.D

/-- the parameters on bits, read over `P.atB K Bt` -/
def LdPartBits.atB : LdPartBits (P.atB K Bt) := ⟨Bt.ok, Bt.hon⟩

end

namespace Spec

/-- the built configuration of Q := `P.atB K Bt` is the built configuration of P -/
def ldPartAtB_idem : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E) (P : LdPartD Cf)
      (K : LdPartPk) (Bt : LdPartBits P),
    (P.atB K Bt).cfB K (Bt.atB P K) = P.cfB K Bt

/-- the laws of Q := `P.atB K Bt` -/
def ldPartAtB_props : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E) (P : LdPartD Cf)
      (K : LdPartPk) (Bt : LdPartBits P) (p : ℕ) [CharP E p],
    P.Props p → P.Wide K → 0 < K.P → Uniq (2 * P.D) K.rdx K.P p → (P.atB K Bt).Props p

def ldPartAtB_side : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E) (P : LdPartD Cf)
      (K : LdPartPk) (Bt : LdPartBits P),
    ((P.atB K Bt).Wide K ↔ P.Wide K) ∧ ((P.atB K Bt).BitsOK (Bt.atB P K) ↔ P.BitsOK Bt)

def ldPartAtB_bits : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E) (P : LdPartD Cf)
      (K : LdPartPk) (Bt : LdPartBits P),
    (P.atB K Bt).bitsV.ok = P.bitsV.ok ∧ (P.atB K Bt).bitsV.hon = P.bitsV.hon

def ldPartAtB_rel : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E) (P : LdPartD Cf)
      (K : LdPartPk) (Bt : LdPartBits P) (S : Sig E) (O : LdPartOut E S) (St : Type)
      (x : St → Cf.Xm) (rc : St → Cf.conf.Rec)
      (bitX : ℕ → Cf.Xm → (ℕ → ℕ → F) → LdPartGh → (ℕ → E) → Prop)
      (vld : St → Cf.conf.Msg × S.Msg → Prop) (k : ℕ),
    (P.atB K Bt).ride K k O x rc bitX = P.ride K k O x rc bitX ∧
    (P.atB K Bt).rideB K k O x rc bitX = P.rideB K k O x rc bitX ∧
    (P.atB K Bt).entry K k O x rc bitX vld = P.entry K k O x rc bitX vld

end Spec

end Cb
