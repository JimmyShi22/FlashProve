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
Cb/Gen/CodeListRS.lean.) Cb/GlVal/GlJ3SegFrontToySeamS.lean: the toy front ends at the stage at
which the toy body's step "read" begins, over any open oracle messages. (not all hypotheses are
named here: see
`Spec.ldSegFront_toySeamS`)

A sanity check of hypotheses. The row of sub-protocols of Cb/GlVal/GlJ3SegFrontToy.lean (a shift, a
lookup argument, a zerocheck, two sumchecks) is joined to the sub-protocols that follow it in a
segment's body, over any family of oracles that is open at the start; the statement says that, under
the hypotheses below, the claims which the first leaves open hold exactly when the input claims of
the second hold, and that the conditions which the library names for the whole, listed under Main
names, hold at this instance.
Definitions and the statement. Proof: Cb/GlVal/GlJ3SegFrontToySeamSProofs.lean. A part of a guard;
no parameter of a protocol.
In Cb/GlVal/GlJ3SegFrontToySeam.lean the open oracle messages are one family with one datum a
member. Here they are any signature S, with an injective naming at' : RefToy.So Nr → S.Ent of the
entries that front and body read or name.
Front, stage: see the head of Cb/GlVal/GlJ3SegFrontToySeam.lean.

Main names:
  `Spec.ldSegFront_toySeamS` states, for all S and all injective at': `sMeets S at'`;
    `(sV ..).OK pK`; `(RefToyS.A (sP ..) (sV ..)).OK pK`; the hypotheses of the list of moves of the
    whole body.

Conventions of this namespace's toys, said of the toys' own oracle messages and groups, not of what
a statement takes as a parameter (of the names declared in Cb/GlVal/ and Cb/Gl/GlField.lean this
file uses only the field E, the front's data of Cb/GlVal/GlJ3SegFrontToy.lean, `Nr`, `SJc`, `allOf`,
`sCl`, `sW`, `SSt`, `SWp`, `xL`, Cb/GlVal/GlJ3SegFrontToySeam.lean, `RefToy.p`, `RefToy.So`,
Cb/GlVal/GlJ3SegRefToy.lean, `RefToy.Cc`, `RefToy.Gh`, Cb/GlVal/GlJ3SegRefToyAll.lean, `RefToyS.D`,
Cb/GlVal/GlJ3SegRefToyS.lean, `RefToyS.APar`, `RefToyS.R`, `RefToyS.A`,
Cb/GlVal/GlJ3SegRefToyAllS.lean, `Cb.Gl.Wf8.p0`, `Cb.Gl.Wf8.mat`, Cb/GlVal/GlToyWf.lean, and `pK`,
Cb/GlVal/GlToyNum.lean; S, `at'` are parameters):
the fields are F, the integers modulo 2^64 - 2^32 + 1, and E = F[x] / (x^3 - 2)
(Cb/Gl/GlField.lean). The toys' code is that of Cb/GlVal/GlToyBase4.lean: eight points, dimension 4,
distance 5, hides 3.
The radius, the bounds on lists, the counts for agreement and the pad's coefficient of these toys
are told in the head of Cb/GlVal/GlJ3Base.lean: read it before quoting.
This is not said of the offline side (configuration, index, lookup tables, weights-formedness).

Limits: what the head of Cb/GlVal/GlJ3SegFrontToySeam.lean lists as not said is not said here either
(among them: one further sumcheck: m = 0; one read; one packed entry: the clauses that speak of
several hold for want of cases). This file is superseded by Cb/GlVal/GlJ3SegFrontToySeamX.lean (a
state that rides, a further part of the further witness, a further claim), of which this file's
front is the case Sx := Unit, W₁ := Unit, w₁0 := (), rc := fun _ => Cb.Gl.Wf8.p0.2, rel0 := True,
relR0 := True, on0 := True, at the same S, at', hat (by reading of the two definitions; no statement
says it). Of this file only `sPk`, `sCell`, `sAll` are used above it; `sP`, `sRx`, `sV` and the
statement have no user but the proof file.

Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyNum
import Cb.GlVal.GlToyLkpNames
import Cb.GlVal.GlJ3Send
import Cb.GlVal.GlToyConfM
import Cb.GlVal.GlJ3PackNames
import Cb.GlVal.GlJ3SegFrontToySeamProofs
import Cb.GlVal.GlJ3SegRefToyAllS

set_option autoImplicit false

namespace Cb.GlJ3
open Cb.Gl hiding p
namespace FrontToyS
open Iop Prob Hiop IOR Cb.Gl.LkpToy Cb.LdLkp Cb.Lkp Cb.Rng Cb.RngPk FrontToy

noncomputable
section
variable (S : Sig E) (at' : RefToy.So Nr → S.Ent)

/-- the packed entry; the cells; the reading of all entries -/
def sPk (ms : S.Msg) : RefToy.p.Rp → RefToy.p.C → E := fun _ _ => S.ents ms (at' (.inl ()))
def sCell (ms : S.Msg) (b : Bool) : E :=
  ((cells RefToy.p.P (2 * RefToy.p.D) RefToy.p.rdx (sPk S at' ms)
    ((), if b then 1 else 0) () : ℤ) : E)
def sAll : S.Msg → JJ → E := fun ms =>
  allOf (sCell S at' ms) fun n => S.ents ms (at' (.inr (.inl n)))

variable (hat : Function.Injective at')

/-- What the front hands over. -/
@[reducible] def sP : RefToyS.APar where
  W₁ := Unit
  w₁0 := ()
  Xn := Nr
  S := S
  at' := at'
  inj := hat
  St := SSt
  W := sW
  cl := FrontToy.sCl
  finJc := inferInstanceAs (Fintype SJc)
  rc := fun _ => Cb.Gl.Wf8.p0.2
  tg := fun _ => 0
  pt := fun _ _ => 0
  mf := fun _ => 1
  rel0 := fun _ _ _ => True
  relR0 := fun _ _ => True
  on0 := fun _ => True

/-- the riding joint of the toy body, over the trivial state -/
def sIx : Rels RefToy.Gh Unit RefToy.Cc.E0 (S.Msg × SWp) :=
  idxAt RefToy.Cc (fun _ : Unit => Cb.Gl.Wf8.p0.2) ⟨fun _ _ w =>
      True ∧ Alg.mle (fun c => ∑ r : Unit, (1 : E) * Cb.Gl.Wf8.mat w.1.1 (r, c))
            (fun _ : Fin 1 => 0) +
          1 * S.ents w.1.2 (at' (.inr (.inr (.inr (.inr (.inl ())))))) = 0,
    fun _ w =>
      True ∧ Alg.mle (fun c => ∑ r : Unit, (1 : E) * Cb.Gl.Wf8.mat w.1.1 (r, c))
            (fun _ : Fin 1 => 0) +
          1 * S.ents w.1.2 (at' (.inr (.inr (.inr (.inr (.inl ())))))) = 0,
    fun _ => True, fun w => w.2.2⟩

/-- What rides along: packing, and that joint. -/
def sRx : Rels RefToy.Gh Unit RefToy.Cc.E0 (S.Msg × SWp) where
  rel := fun _ y w =>
    PackBy RefToy.p.B RefToy.p.rdx w.2.2.2 (sPk S at' w.1) ∧ (sIx S at').rel () y w
  relR := fun a w =>
    Packed RefToy.p.P (2 * RefToy.p.D) RefToy.p.rdx (sPk S at' w.1) ∧ (sIx S at').relR a w
  on := fun a => ¬ RefToy.Cc.coll a.2 Cb.Gl.Wf8.p0.2.1 ∧ True
  core := fun w => w.2.2.2

/-- The front, ending at the stage at which the toy body's step "read" begins. -/
def sV : LdFrontRef E RefToy.Gh (RefToyS.D (RefToyS.R (sP S at' hat))).s0 :=
  { Fp := tF RefToy.Gh S RefToy.Cc.E0 SWp (sAll S at') (sRx S at'), m := 0, T := fun _ => tEnd.psc,
    A0 := fun _ => tA00 RefToy.Gh S RefToy.Cc.E0 SWp (sAll S at') (sRx S at'),
    msg := fun _ => sAll S at', g0 := fun o => (o.vals () + 1, o), g := fun _ o => (0, o.st),
    gz := id }

/-- States: the claims `sCl` say what the front leaves open. -/
def sMeets : Prop :=
  ∀ (o : SSt) (ms : S.Msg),
    FrontToy.sCl.OnCells sW o (cells RefToy.p.P (2 * RefToy.p.D) RefToy.p.rdx (sPk S at' ms))
      (fun j => S.ents ms (at' (.inr j))) ↔
    tA.lk.outF id (tA.entN tι) (xL o) (sAll S at' ms) ∧
    tBit.zc.next.par.UHolds o.st (sAll S at' ms) ∧
    tEnd.psc.par.OutHolds o (sAll S at' ms)

end
end FrontToyS

namespace Spec
open FrontToy FrontToyS

def ldSegFront_toySeamS : Prop :=
  ∀ (S : Sig E) (at' : RefToy.So Nr → S.Ent) (hat : Function.Injective at'),
    sMeets S at' ∧
    (sV S at' hat).OK pK ∧
    (RefToyS.A (sP S at' hat) (sV S at' hat)).OK pK ∧
    ((RefToyS.A (sP S at' hat) (sV S at' hat)).body
      (RefToyS.A (sP S at' hat) (sV S at' hat)).X.bt.par.Mid id
      (RefToyS.A (sP S at' hat) (sV S at' hat)).X.m1.A).Hyp

end Spec
end Cb.GlJ3
