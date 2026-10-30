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
Cb/Gen/CodeListRS.lean.) Cb/GlVal/GlJ3SegFrontToySeam.lean: the toy front ends at the stage at which
the toy body's step "read" begins.

A sanity check of hypotheses. The row of sub-protocols of Cb/GlVal/GlJ3SegFrontToy.lean (a shift, a
lookup argument, a zerocheck, two sumchecks) is joined to the sub-protocols that follow it in a
segment's body; `Spec.ldSegFront_toySeam` says that the claims which the first leaves open hold
exactly when the input claims of the second hold, and that the conditions which the library names
for the whole, listed under Main names, hold at this instance.
Definitions and two statements. Proof: Cb/GlVal/GlJ3SegFrontToySeamProofs.lean. A guard against
empty theorems; no parameter of a protocol.
The front (`LdFrontRef`, Cb/Req1/LdSegFrontRef.lean) of a segment's body (`LdBodyD`,
Cb/Req1/LdSegRefBody.lean) is the list of moves before the step "read". A stage is an `LdStage`
(Cb/Req1/LdSegKit.lean). Here the toy front of Cb/GlVal/GlJ3SegFrontToy.lean is taken over the toy
body's oracle messages.

Main names:
  The two keys of the lookup are virtual: key_b := 5 + 2 · cell_b (`allOf`) (so "the keys are in the
    table (5, 7)" says that the cells are 0 or 1).
  `SSt`, `xL`, `th`: the last explicit part of the front; the lookup's explicit part and the shift
    in it.
  `SJc`, `sCo`, `sTg`, `sCl`: what the front leaves open, as claims of the form that the step "read"
    takes (`ReadCl`, Cb/Ld/LdRead.lean): their names, forms on all entries, targets.
  `SS`, `SWp`: the oracle messages (one packed entry, which holds two cells, and one datum for each
    name in `RefToy.Jn Nr`); the further witness.
  `Spec.ldSegFront_toySeam` states: `sMeets`; `sV.OK pK`; `(RefToy.A sP sV).OK pK`; the hypotheses
    of the list of moves of the whole body.
  `Spec.ldSegFront_toyRide` states: every form `sCo o j` has the coefficient 0 at each entry
    `rAt r`.

Conventions of this namespace's toys, said of the toys' own oracle messages and groups, not of what
a statement takes as a parameter (of the names declared in Cb/GlVal/ and Cb/Gl/GlField.lean this
file uses only the field E, the front's data of Cb/GlVal/GlJ3SegFrontToy.lean, `datSig`, `datAt`,
Cb/GlVal/GlJ3RefKit.lean, the toy body's `RefToy.p`, `RefToy.Jn`, `RefToy.So`, `RefToy.D`,
Cb/GlVal/GlJ3SegRefToy.lean, and `RefToy.APar`, `RefToy.R`, `RefToy.A`, `RefToy.Cc`, `RefToy.Gh`,
`RefToy.mkN`, Cb/GlVal/GlJ3SegRefToyAll.lean, `Mk`, Cb/GlVal/GlToyLkpNames.lean, `Cb.Gl.Wf8.p0`,
`Cb.Gl.Wf8.mat`, Cb/GlVal/GlToyWf.lean, and `pK`, Cb/GlVal/GlToyNum.lean):
the fields are F, the integers modulo 2^64 - 2^32 + 1, and E = F[x] / (x^3 - 2)
(Cb/Gl/GlField.lean). The toys' code is that of Cb/GlVal/GlToyBase4.lean: eight points, dimension 4,
distance 5, hides 3.
The radius, the bounds on lists, the counts for agreement and the pad's coefficient of these toys
are told in the head of Cb/GlVal/GlJ3Base.lean: read it before quoting.
This is not said of the offline side (configuration, index, lookup tables, weights-formedness).

Limits: one further sumcheck (m = 0), one read, one packed entry: the clauses that speak of several
hold for want of cases. Pads in the subfield F are not exercised. The bounds that the toys write
(one hidden position) are kept, though this code hides 3 (said of `RefToy.D`,
Cb/GlVal/GlJ3SegRefToy.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyNum
import Cb.GlVal.GlToyLkpNames
import Cb.GlVal.GlJ3Send
import Cb.GlVal.GlToyConfM
import Cb.GlVal.GlJ3PackNames
import Cb.GlVal.GlJ3SegFrontToyProofs
import Cb.GlVal.GlJ3SegRefToyAll

set_option autoImplicit false

namespace Cb.GlJ3
open Cb.Gl hiding p
namespace FrontToy
open Iop Prob Hiop IOR Cb.Gl.LkpToy Cb.LdLkp Cb.Lkp Cb.Rng Cb.RngPk

noncomputable
section

/-- The real entries: all entries but the two keys. -/
abbrev Nr : Type := (((Bool × Bool) ⊕ (Mk ⊕ Unit)) ⊕ Unit) ⊕ X
instance decNr : DecidableEq Nr := Classical.decEq _

def nr : Nr → JJ
  | .inl (.inl (.inl ub)) => .inl (.inl (.inl (.inr ub)))
  | .inl (.inl (.inr x)) => .inl (.inl (.inr x))
  | .inl (.inr u) => .inl (.inr u)
  | .inr x => .inr x

/-- All entries, from the two cells and the real entries. -/
def allOf (cell : Bool → E) (e : Nr → E) : JJ → E
  | .inl (.inl (.inl (.inl b))) => 5 + 2 * cell b
  | .inl (.inl (.inl (.inr ub))) => e (.inl (.inl (.inl ub)))
  | .inl (.inl (.inr x)) => e (.inl (.inl (.inr x)))
  | .inl (.inr u) => e (.inl (.inr u))
  | .inr x => e (.inr x)

/-- the last explicit part of the front, and what is read off it -/
abbrev SSt : Type := tEnd.psc.par.Out
def xL (o : SSt) : FXt := o.st.st.1
def th (o : SSt) : E := (xL o).1.2

/-- the names of the claims -/
abbrev SJc : Type := Unit ⊕ (Fin tA0.nRows ⊕ (Unit ⊕ (Unit ⊕ Unit)))

/-- mask forms, on all entries; targets -/
def sCo (o : SSt) : SJc → JJ → E
  | .inl _ => pushJ tι (xL o).2.1.mf
  | .inr (.inl i) => pushJ tι ((xL o).2.2 i).cf
  | .inr (.inr (.inl _)) => tBit.zc.next.par.slU (fun _ b => b.elim) o.st
  | .inr (.inr (.inr (.inl _))) => tEnd.psc.par.slU (fun _ b => b.elim) o
  | .inr (.inr (.inr (.inr _))) => tEnd.psc.par.slE tEnd.rowA () o
def sTg (o : SSt) : SJc → E
  | .inl _ => (xL o).2.1.tg
  | .inr (.inl i) => ((xL o).2.2 i).tg
  | .inr (.inr (.inl _)) => tBit.zc.next.par.tU o.st
  | .inr (.inr (.inr (.inl _))) => tEnd.psc.par.tU o
  | .inr (.inr (.inr (.inr _))) => o.vals ()

/-- The claims. -/
def sCl : ReadCl RefToy.p E SSt (RefToy.Jn Nr) where
  Jc := SJc
  k0 := fun o j => match j with
    | .inl _ => Blocks.ext 1 (fun _ => 5 + 1 * th o) (xL o).2.1.pt
    | .inr _ => 0
  cw := fun _ j _ _ => match j with
    | .inl _ => 2
    | .inr _ => 0
  ms := fun o j n => match n with
    | .inl n' => sCo o j (nr n')
    | .inr _ => 0
  v := sTg

/-- the weight vector of the one read: the equality weights at the lookup's end point -/
def sW : SSt → RefToy.p.Rd → RefToy.p.Row → E := fun o _ r => Blocks.eqN 1 0 (xL o).2.1.pt r.2.val

/-- What the front hands over. -/
@[reducible] def sP : RefToy.APar where
  W₁ := Unit
  w₁0 := ()
  Xn := Nr
  St := SSt
  W := sW
  cl := sCl
  finJc := inferInstanceAs (Fintype SJc)
  rc := fun _ => Cb.Gl.Wf8.p0.2
  tg := fun _ => 0
  pt := fun _ _ => 0
  mf := fun _ => 1
  rel0 := fun _ _ _ => True
  relR0 := fun _ _ => True
  on0 := fun _ => True

/-- the oracle messages, the further witness -/
abbrev SS : Sig E := datSig (RefToy.So Nr)
abbrev SWp : Type := RefToy.Cc.PIdx × (Unit × RefToy.Gh)

/-- the packed entry; the cells; the reading of all entries -/
def sPk (ms : SS.Msg) : RefToy.p.Rp → RefToy.p.C → E := fun _ _ => datAt ms (.inl ())
def sCell (ms : SS.Msg) (b : Bool) : E :=
  ((cells RefToy.p.P (2 * RefToy.p.D) RefToy.p.rdx (sPk ms) ((), if b then 1 else 0) () : ℤ) : E)
def sAll : SS.Msg → JJ → E := fun ms => allOf (sCell ms) fun n => datAt ms (.inr (.inl n))

/-- What rides along: packing, and the toy body's riding joint, over the trivial state. -/
def sRx : Rels RefToy.Gh Unit RefToy.Cc.E0 (SS.Msg × SWp) where
  rel := fun _ y w =>
    PackBy RefToy.p.B RefToy.p.rdx w.2.2.2 (sPk w.1) ∧
    (idxAt RefToy.Cc (fun _ : Unit => Cb.Gl.Wf8.p0.2) ⟨fun _ _ w =>
          True ∧ Alg.mle (fun c => ∑ r : Unit, (1 : E) * Cb.Gl.Wf8.mat w.1.1 (r, c))
                (fun _ : Fin 1 => 0) +
              1 * datAt w.1.2 (RefToy.mkN sP) = 0,
        fun _ w =>
          True ∧ Alg.mle (fun c => ∑ r : Unit, (1 : E) * Cb.Gl.Wf8.mat w.1.1 (r, c))
                (fun _ : Fin 1 => 0) +
              1 * datAt w.1.2 (RefToy.mkN sP) = 0,
        fun _ => True, fun w => w.2.2⟩).rel
      () y w
  relR := fun a w =>
    Packed RefToy.p.P (2 * RefToy.p.D) RefToy.p.rdx (sPk w.1) ∧
    (idxAt RefToy.Cc (fun _ : Unit => Cb.Gl.Wf8.p0.2) ⟨fun _ _ w =>
          True ∧ Alg.mle (fun c => ∑ r : Unit, (1 : E) * Cb.Gl.Wf8.mat w.1.1 (r, c))
                (fun _ : Fin 1 => 0) +
              1 * datAt w.1.2 (RefToy.mkN sP) = 0,
        fun _ w =>
          True ∧ Alg.mle (fun c => ∑ r : Unit, (1 : E) * Cb.Gl.Wf8.mat w.1.1 (r, c))
                (fun _ : Fin 1 => 0) +
              1 * datAt w.1.2 (RefToy.mkN sP) = 0,
        fun _ => True,
        fun w => w.2.2⟩).relR
      a w
  on := fun a => ¬ RefToy.Cc.coll a.2 Cb.Gl.Wf8.p0.2.1 ∧ True
  core := fun w => w.2.2.2

/-- The front, ending at the stage at which the toy body's step "read" begins. -/
def sV : LdFrontRef E RefToy.Gh (RefToy.D (RefToy.R sP)).s0 :=
  { Fp := tF RefToy.Gh SS RefToy.Cc.E0 SWp sAll sRx, m := 0, T := fun _ => tEnd.psc,
    A0 := fun _ => tA00 RefToy.Gh SS RefToy.Cc.E0 SWp sAll sRx, msg := fun _ => sAll,
    g0 := fun o => (o.vals () + 1, o), g := fun _ o => (0, o.st), gz := id }

/-- States: the claims `sCl` say what the front leaves open. -/
def sMeets : Prop :=
  ∀ (o : SSt) (ms : SS.Msg),
    sCl.OnCells sW o (cells RefToy.p.P (2 * RefToy.p.D) RefToy.p.rdx (sPk ms))
      (fun j => datAt ms (.inr j)) ↔
    tA.lk.outF id (tA.entN tι) (xL o) (sAll ms) ∧
    tBit.zc.next.par.UHolds o.st (sAll ms) ∧
    tEnd.psc.par.OutHolds o (sAll ms)

end
end FrontToy

namespace Spec
open FrontToy

def ldSegFront_toySeam : Prop :=
  sMeets ∧ sV.OK pK ∧
  (RefToy.A sP sV).OK pK ∧
  ((RefToy.A sP sV).body (RefToy.A sP sV).X.bt.par.Mid id (RefToy.A sP sV).X.m1.A).Hyp

/-- States: no claim reads an entry that rides. -/
def ldSegFront_toyRide : Prop := ∀ o j r, sCo o j (rAt r) = 0

end Spec
end Cb.GlJ3
