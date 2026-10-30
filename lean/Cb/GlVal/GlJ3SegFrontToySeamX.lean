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
Cb/Gen/CodeListRS.lean.) Cb/GlVal/GlJ3SegFrontToySeamX.lean: one seam for every segment of a toy
request: the toy front with a state that rides ends at the stage at which the toy body's step "read"
begins, over any open oracle messages, any further part of the further witness, any further claim.
(not all hypotheses are named here: see `Spec.ldSegFront_toySeamX`)

A sanity check of hypotheses. The row of sub-protocols of Cb/GlVal/GlJ3SegFrontToyX.lean (a shift, a
lookup argument, a zerocheck, two sumchecks) is joined to the sub-protocols that follow it in a
segment's body, over any family of oracles that is open at the start, with a state, a further part
of the further witness and a further claim carried along; the statement says that, under the
hypotheses below, the claims which the first leaves open hold exactly when the input claims of the
second hold, and that the conditions which the library names for the whole, listed under Main names,
hold at this instance.
Definitions and the statement. Proof: Cb/GlVal/GlJ3SegFrontToySeamXProofs.lean. A part of a guard;
no parameter of a protocol.
Front, stage: see the head of Cb/GlVal/GlJ3SegFrontToySeam.lean.

Main names:
  The parameters: Sx, the state that rides (Cb/GlVal/GlJ3SegFrontToyX.lean); S, at', hat: the open
    oracle messages and the injective naming of the entries that front and body read or name; W₁,
    w₁0: a further part of the further witness; rc : Sx → the record (`RefToy.Cc.Rec`,
    Cb/GlVal/GlJ3SegRefToyAll.lean), read off the state; rel0, relR0, on0: what else is claimed, at
    a state in Sx.
  `SSt Sx`, `xL`, `th`, `sx`: the front's last explicit part; the lookup's explicit part, the shift
    and the state in it.
  `sCo`, `sTg`, `sClX Sx`, `sW`: the claims, as in Cb/GlVal/GlJ3SegFrontToySeam.lean.
  `Spec.ldSegFront_toySeamX` states, for all these parameters: `sMeets Sx S at'`; every form
    `sCo o j` has the coefficient 0 at each entry `rAt r`; `(sV ..).OK pK`;
    `(RefToyS.A (sP ..) (sV ..)).OK pK`; the hypotheses of the list of moves of the whole body.

Conventions of this namespace's toys, said of the toys' own oracle messages and groups, not of what
a statement takes as a parameter (of the names declared in Cb/GlVal/ and Cb/Gl/GlField.lean this
file uses only the field E, the entries, the sets, `tA0` and `tι` of Cb/GlVal/GlJ3SegFrontToy.lean,
the front's data of Cb/GlVal/GlJ3SegFrontToyX.lean, `Nr`, `nr`, `allOf`, `SJc`,
Cb/GlVal/GlJ3SegFrontToySeam.lean, `sPk`, `sCell`, `sAll`, Cb/GlVal/GlJ3SegFrontToySeamS.lean,
`RefToy.p`, `RefToy.Jn`, `RefToy.So`, Cb/GlVal/GlJ3SegRefToy.lean, `RefToy.Cc`, `RefToy.Gh`,
Cb/GlVal/GlJ3SegRefToyAll.lean, `RefToyS.D`, Cb/GlVal/GlJ3SegRefToyS.lean, `RefToyS.APar`,
`RefToyS.R`, `RefToyS.A`, Cb/GlVal/GlJ3SegRefToyAllS.lean, `Cb.Gl.Wf8.mat`, Cb/GlVal/GlToyWf.lean,
and `pK`, Cb/GlVal/GlToyNum.lean; Sx, S, `at'`, W₁, `w₁0`, `rc`, `rel0`, `relR0`, `on0` are
parameters):
the fields are F, the integers modulo 2^64 - 2^32 + 1, and E = F[x] / (x^3 - 2)
(Cb/Gl/GlField.lean). The toys' code is that of Cb/GlVal/GlToyBase4.lean: eight points, dimension 4,
distance 5, hides 3.
The radius, the bounds on lists, the counts for agreement and the pad's coefficient of these toys
are told in the head of Cb/GlVal/GlJ3Base.lean: read it before quoting.
This is not said of the offline side (configuration, index, lookup tables, weights-formedness).

Limits: what the head of Cb/GlVal/GlJ3SegFrontToySeam.lean lists as not said is not said here either
(among them: one further sumcheck: m = 0; one read; one packed entry: the clauses that speak of
several hold for want of cases).

Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyNum
import Cb.GlVal.GlToyLkpNames
import Cb.GlVal.GlJ3Send
import Cb.GlVal.GlToyConfM
import Cb.GlVal.GlJ3PackNames
import Cb.GlVal.GlJ3SegFrontToyXProofs
import Cb.GlVal.GlJ3SegFrontToySeamSProofs

set_option autoImplicit false

namespace Cb.GlJ3
open Cb.Gl hiding p
namespace FrontToyX
open Iop Prob Hiop IOR Cb.Gl.LkpToy Cb.LdLkp Cb.Lkp Cb.Rng Cb.RngPk
open FrontToy (WZ WC Ride X JJ eL aAt zAt cAt rAt tA0 tι tDt tRdK tRd0 tRd1 Nr nr allOf SJc)
open FrontToyS (sPk sCell sAll)

noncomputable
section
variable (Sx : Type)

/-- the last explicit part of the front, and what is read off it -/
abbrev SSt : Type := (tEnd Sx).psc.par.Out
variable {Sx}
def xL (o : SSt Sx) : FXt Sx := o.st.st.1
def th (o : SSt Sx) : E := (xL o).1.2
/-- the state that rode -/
def sx (o : SSt Sx) : Sx := (xL o).1.1

def sCo (o : SSt Sx) : SJc → JJ → E
  | .inl _ => pushJ tι (xL o).2.1.mf
  | .inr (.inl i) => pushJ tι ((xL o).2.2 i).cf
  | .inr (.inr (.inl _)) => (tBit Sx).zc.next.par.slU (fun _ b => b.elim) o.st
  | .inr (.inr (.inr (.inl _))) => (tEnd Sx).psc.par.slU (fun _ b => b.elim) o
  | .inr (.inr (.inr (.inr _))) => (tEnd Sx).psc.par.slE (tEnd Sx).rowA () o
def sTg (o : SSt Sx) : SJc → E
  | .inl _ => (xL o).2.1.tg
  | .inr (.inl i) => ((xL o).2.2 i).tg
  | .inr (.inr (.inl _)) => (tBit Sx).zc.next.par.tU o.st
  | .inr (.inr (.inr (.inl _))) => (tEnd Sx).psc.par.tU o
  | .inr (.inr (.inr (.inr _))) => o.vals ()
variable (Sx)

/-- The claims. -/
def sClX : ReadCl RefToy.p E (SSt Sx) (RefToy.Jn Nr) where
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

def sW : SSt Sx → RefToy.p.Rd → RefToy.p.Row → E := fun o _ r =>
  Blocks.eqN 1 0 (xL o).2.1.pt r.2.val

variable (S : Sig E) (at' : RefToy.So Nr → S.Ent) (hat : Function.Injective at') (W₁ : Type)
  (w₁0 : W₁) (rc : Sx → RefToy.Cc.Rec)
  (rel0 : Sx → RefToy.Cc.E0.Str → (RefToy.Cc.Msg × S.Msg) × (W₁ × RefToy.Gh) → Prop)
  (relR0 : Sx × RefToy.Cc.E0.Str → (RefToy.Cc.Msg × S.Msg) × (W₁ × RefToy.Gh) → Prop)
  (on0 : Sx × RefToy.Cc.E0.Str → Prop)

/-- the further witness -/
abbrev SWp : Type := RefToy.Cc.PIdx × (W₁ × RefToy.Gh)

/-- What the front hands over. -/
@[reducible] def sP : RefToyS.APar where
  W₁ := W₁
  w₁0 := w₁0
  Xn := Nr
  S := S
  at' := at'
  inj := hat
  St := SSt Sx
  W := sW Sx
  cl := sClX Sx
  finJc := inferInstanceAs (Fintype SJc)
  rc := fun o => rc (sx o)
  tg := fun _ => 0
  pt := fun _ _ => 0
  mf := fun _ => 1
  rel0 := fun o => rel0 (sx o)
  relR0 := fun a => relR0 (sx a.1, a.2)
  on0 := fun a => on0 (sx a.1, a.2)

/-- the riding joint of the toy body, at a state in Sx -/
def sIx : Rels RefToy.Gh Sx RefToy.Cc.E0 (S.Msg × SWp W₁) :=
  idxAt RefToy.Cc rc ⟨fun x y w =>
      rel0 x y w ∧
      Alg.mle (fun c => ∑ r : Unit, (1 : E) * Cb.Gl.Wf8.mat w.1.1 (r, c)) (fun _ : Fin 1 => 0) +
          1 * S.ents w.1.2 (at' (.inr (.inr (.inr (.inr (.inl ())))))) = 0,
    fun a w =>
      relR0 a w ∧
      Alg.mle (fun c => ∑ r : Unit, (1 : E) * Cb.Gl.Wf8.mat w.1.1 (r, c)) (fun _ : Fin 1 => 0) +
          1 * S.ents w.1.2 (at' (.inr (.inr (.inr (.inr (.inl ())))))) = 0,
    on0, fun w => w.2.2⟩

/-- What rides along: packing, and that joint. -/
def sRx : Rels RefToy.Gh Sx RefToy.Cc.E0 (S.Msg × SWp W₁) where
  rel := fun x y w =>
    PackBy RefToy.p.B RefToy.p.rdx w.2.2.2 (sPk S at' w.1) ∧
    (sIx Sx S at' W₁ rc rel0 relR0 on0).rel x y w
  relR := fun a w =>
    Packed RefToy.p.P (2 * RefToy.p.D) RefToy.p.rdx (sPk S at' w.1) ∧
    (sIx Sx S at' W₁ rc rel0 relR0 on0).relR a w
  on := (sIx Sx S at' W₁ rc rel0 relR0 on0).on
  core := fun w => w.2.2.2

/-- The front, ending at the stage at which the toy body's step "read" begins. -/
def sV :
    LdFrontRef E RefToy.Gh (RefToyS.D (RefToyS.R (sP Sx S at' hat W₁ w₁0 rc rel0 relR0 on0))).s0 :=
  { Fp := tF Sx RefToy.Gh S RefToy.Cc.E0 (SWp W₁) (sAll S at') (sRx Sx S at' W₁ rc rel0 relR0 on0),
    m := 0, T := fun _ => (tEnd Sx).psc,
    A0 := fun _ =>
        tA00 Sx RefToy.Gh S RefToy.Cc.E0 (SWp W₁) (sAll S at') (sRx Sx S at' W₁ rc rel0 relR0 on0),
    msg := fun _ => sAll S at', g0 := fun o => (o.vals () + 1, o),
    g := fun _ o => (0, o.st), gz := id }

/-- States: the claims `sClX Sx` say what the front leaves open. -/
def sMeets : Prop :=
  ∀ (o : SSt Sx) (ms : S.Msg),
    (sClX Sx).OnCells (sW Sx) o (cells RefToy.p.P (2 * RefToy.p.D) RefToy.p.rdx (sPk S at' ms))
      (fun j => S.ents ms (at' (.inr j))) ↔
    (tA Sx).lk.outF id ((tA Sx).entN tι) (xL o) (sAll S at' ms) ∧
    (tBit Sx).zc.next.par.UHolds o.st (sAll S at' ms) ∧
    (tEnd Sx).psc.par.OutHolds o (sAll S at' ms)

end
end FrontToyX

namespace Spec
open FrontToyX
open FrontToy (Nr rAt)

def ldSegFront_toySeamX : Prop :=
  ∀ (Sx : Type) (S : Sig E) (at' : RefToy.So Nr → S.Ent) (hat : Function.Injective at') (W₁ : Type)
      (w₁0 : W₁) (rc : Sx → RefToy.Cc.Rec)
      (rel0 : Sx → RefToy.Cc.E0.Str → (RefToy.Cc.Msg × S.Msg) × (W₁ × RefToy.Gh) → Prop)
      (relR0 : Sx × RefToy.Cc.E0.Str → (RefToy.Cc.Msg × S.Msg) × (W₁ × RefToy.Gh) → Prop)
      (on0 : Sx × RefToy.Cc.E0.Str → Prop),
    sMeets Sx S at' ∧
    (∀ (o : SSt Sx) j r, sCo o j (rAt r) = 0) ∧
    (sV Sx S at' hat W₁ w₁0 rc rel0 relR0 on0).OK pK ∧
    (RefToyS.A (sP Sx S at' hat W₁ w₁0 rc rel0 relR0 on0)
      (sV Sx S at' hat W₁ w₁0 rc rel0 relR0 on0)).OK pK ∧
    ((RefToyS.A (sP Sx S at' hat W₁ w₁0 rc rel0 relR0 on0)
        (sV Sx S at' hat W₁ w₁0 rc rel0 relR0 on0)).body
      (RefToyS.A (sP Sx S at' hat W₁ w₁0 rc rel0 relR0 on0)
        (sV Sx S at' hat W₁ w₁0 rc rel0 relR0 on0)).X.bt.par.Mid
      id (RefToyS.A (sP Sx S at' hat W₁ w₁0 rc rel0 relR0 on0)
        (sV Sx S at' hat W₁ w₁0 rc rel0 relR0 on0)).X.m1.A).Hyp

end Spec
end Cb.GlJ3
