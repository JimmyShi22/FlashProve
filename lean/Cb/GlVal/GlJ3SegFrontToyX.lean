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
Cb/Gen/CodeListRS.lean.) Cb/GlVal/GlJ3SegFrontToyX.lean: the toy front with a state that rides: all
named conditions met together, nothing assumed beyond the hypotheses of the statements, for every
type of states.

A sanity check of hypotheses. A shift (`tP`), a lookup argument, a zerocheck and two sumchecks are
run in a row on one small vector of field elements, with a state carried along; the statement says
that, under the hypotheses below, the conditions which the library names for such a row of
sub-protocols, listed under Main names, hold together at this instance.
Definitions and the statement. Proof: Cb/GlVal/GlJ3SegFrontToyXProofs.lean. A guard against empty
theorems; no parameter of a protocol.
The front (`LdFrontRef`, Cb/Req1/LdSegFrontRef.lean) of a segment's body (`LdBodyD`,
Cb/Req1/LdSegRefBody.lean) is the list of moves before the step "read". In
Cb/GlVal/GlJ3SegFrontToy.lean the toy front starts at the trivial state; here it starts at a state
in any type Sx, which none of these sub-protocols reads or changes.

Main names:
  Rx: a joint on Sx that rides along (any). `tV` is the front.
  `Spec.ldSegFront_toyX` states, for all Sx, Kc, S, E₀ having a string (`E₀.Str` nonempty), Wp,
    every reading all : S.Msg → JJ → E and every joint Rx on Sx: `(tV ..).OK pK` (the list "shift,
    lookup", `(tF ..).OK pK`; the zerocheck's three conditions; the conditions of both sumchecks;
    the steps between); `(tV ..).prog.Hyp` (the hypotheses of its list of moves); the number of
    rounds `(tV ..).prog.nAll` is 36 (the count for every front: `Spec.ldSegFrontRef_nums`,
    Cb/Req1/LdSegFrontRef.lean); and the clauses `ZkOK` (Cb/Req1/LdSegRefLkpPreZk.lean), `OwnOur`
    (twice; Cb/Ld/LdPscZk.lean), `ldQuiet` (three times; Cb/Req1/LdSegFrontTabZk.lean) and
    `(tV ..).prog.Zk (tBase ..)` (Cb/Req1/LdReq.lean): for these see the statement.

Conventions of this namespace's toys, said of the toys' own oracle messages and groups, not of what
a statement takes as a parameter (of the names declared in Cb/GlVal/ and Cb/Gl/GlField.lean this
file uses only the field E, the data of Cb/GlVal/GlJ3SegFrontToy.lean, `kAt`, `toyA`, `Nm`,
Cb/GlVal/GlToyLkpNames.lean, and `pK`, Cb/GlVal/GlToyNum.lean; Sx, Kc, S, E₀, Wp, `all`, `Rx` are
parameters):
the fields are F, the integers modulo 2^64 - 2^32 + 1, and E = F[x] / (x^3 - 2)
(Cb/Gl/GlField.lean). The toys' code is that of Cb/GlVal/GlToyBase4.lean: eight points, dimension 4,
distance 5, hides 3.
The radius, the bounds on lists, the counts for agreement and the pad's coefficient of these toys
are told in the head of Cb/GlVal/GlJ3Base.lean: read it before quoting.
This is not said of the offline side (configuration, index, lookup tables, weights-formedness).

Notation: `tBase ..`: the facts `((tF ..).dm tRdK (tC Sx)).fact`, `(tV ..).tab.f0 tRd0` and
`(tV ..).tab.f i tRd1`, i ≤ 0.

Limits: what the head of Cb/GlVal/GlJ3SegFrontToy.lean lists as not said is not said here either
(among them: one further sumcheck: m = 0). `(tV ..).prog.Zk (tBase ..)` is conditional on the three
facts being fresh at the entry: that is the matter of the sending before the front.

Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyNum
import Cb.GlVal.GlToyLkpNames
import Cb.GlVal.GlJ3Send
import Cb.GlVal.GlToyConfM
import Cb.GlVal.GlJ3PackNames
import Cb.GlVal.GlJ3SegFrontToyProofs

set_option autoImplicit false

namespace Cb.GlJ3
open Cb.Gl hiding p
namespace FrontToyX
open Iop Prob Hiop IOR Cb.Gl.LkpToy Cb.LdLkp Cb.Lkp
open FrontToy (WZ WC Ride X JJ eL aAt zAt cAt rAt tA0 tι ValidU tDt tRdK tRd0 tRd1)

noncomputable
section
variable (Sx : Type)

def tP : ShiftP E Sx (JJ → E) :=
  ⟨0, 1, 1, fun _ m _ i => m (eL (kAt (decide (i = 1)))),
    fun _ _ u => if u = 0 then 5 else 7, fun _ => 1⟩
def tA : LkAsm2 E :=
  toyA.re (Sx × E) JJ eL (fun x m => shKey 1 ((tP Sx).key x.1 m) (tP Sx).tag x.2)
    fun x => shTab 1 ((tP Sx).tab x.1) (tP Sx).tag x.2
abbrev FXt : Type := FX (Sx × E) E Nm tA0.nRows
def tBit : LkBit E :=
  { St := FXt Sx, J := JJ, k := 1, tAt := aAt, wAt := fun i => zAt (.inl i), cAt := zAt (.inr ()) }
def gam (o : (tBit Sx).zc.next.par.Out) : Fin 1 → E :=
  (tBit Sx).zc.fn o.st.2.2 ((tBit Sx).zc.next.ini o.st ((tBit Sx).zc.next.par.hp o.st o.pt))
def bet (o : (tBit Sx).zc.next.par.Out) : E :=
  (tBit Sx).zc.next.lst o.st ((tBit Sx).zc.next.par.hp o.st o.pt)

open Classical in
def tEnd : LkEnd E :=
  { X := (tBit Sx).zc.next.par.Out, J := JJ, k := 1, tAt := aAt, z := gam Sx,
    cp := fun _ _ => 1, inc := fun o j => if j = zAt (.inr ()) then bet Sx o else 0,
    wAt := fun i => cAt (.inl i), cAt := cAt (.inr ()) }

def tC : Sx × E → (JJ → E) → Prop := (tA Sx).lk.inP (tA Sx).ValidMu

section
variable (Kc : Type) (S : Sig E) (E₀ : ExtSpec) (Wp : Type)
  (all : S.Msg → JJ → E) (Rx : Rels Kc Sx E₀ (S.Msg × Wp))

def tRr : Rels Kc Sx E₀ (S.Msg × Wp) :=
  ⟨fun st y w => Rx.rel st y w ∧ (tBit Sx).AllBits (all w.1) ∧ ValidU (all w.1),
    fun a w => Rx.relR a w ∧ (tBit Sx).AllBits (all w.1),
    Rx.on, Rx.core⟩
def tJT : Rels Kc (FXt Sx) E₀ (S.Msg × Wp) :=
  cj (⟨fun x y w => Rx.rel x.1 y w,
      fun a w => Rx.relR (a.1.1, a.2) w,
      fun a => Rx.on (a.1.1, a.2),
      Rx.core⟩ : Rels Kc (Sx × E) E₀ (S.Msg × Wp))
    all Prod.fst ((tA Sx).lk.outF id ((tA Sx).entN tι)) ((tA Sx).lk.outF id ((tA Sx).entN tι))

def tF : LdPreD E Kc S E₀ Wp :=
  { St := Sx, A0 := tA0, msg := all, P := tP Sx, Rr := tRr Sx Kc S E₀ Wp all Rx, N := Nm,
    ι := tι, Mu := (tA Sx).ValidMu, Z := (tBit Sx).zc.toIn,
    R0z := tJT Sx Kc S E₀ Wp all Rx, msg0 := all, e := id }

def tA00 : Rels Kc (tEnd Sx).X E₀ (S.Msg × Wp) :=
  ⟨fun o y w =>
      ((tBit Sx).zc.toIn.ride (tJT Sx Kc S E₀ Wp all Rx)).rel o.st y w ∧
      (tBit Sx).zc.next.par.UHolds o (all w.1),
    fun a w =>
      ((tBit Sx).zc.toIn.ride (tJT Sx Kc S E₀ Wp all Rx)).relR (a.1.st, a.2) w ∧
      (tBit Sx).zc.next.par.UHolds a.1 (all w.1),
    fun a => ((tBit Sx).zc.toIn.ride (tJT Sx Kc S E₀ Wp all Rx)).on (a.1.st, a.2),
    ((tBit Sx).zc.toIn.ride (tJT Sx Kc S E₀ Wp all Rx)).core⟩

@[reducible] def tz : LdStage E Kc :=
  ⟨S, (tEnd Sx).psc.par.Out, E₀, Wp,
    (tEnd Sx).psc.par.baseOut (tA00 Sx Kc S E₀ Wp all Rx) fun w => all w.1⟩

/-- The front. -/
def tV : LdFrontRef E Kc (tz Sx Kc S E₀ Wp all Rx) :=
  { Fp := tF Sx Kc S E₀ Wp all Rx, m := 0, T := fun _ => (tEnd Sx).psc,
    A0 := fun _ => tA00 Sx Kc S E₀ Wp all Rx, msg := fun _ => all,
    g0 := fun o => (o.vals () + 1, o), g := fun _ o => (0, o.st), gz := id }

def tBase : MaskFact (S.Wit × Wp) → Prop := fun f =>
  f = ((tF Sx Kc S E₀ Wp all Rx).dm tRdK (tC Sx)).fact ∨
  f = (tV Sx Kc S E₀ Wp all Rx).tab.f0 tRd0 ∨
  ∃ i ≤ 0, f = (tV Sx Kc S E₀ Wp all Rx).tab.f i tRd1

end
end
end FrontToyX

namespace Spec
open Iop IOR Cb.Gl.LkpToy FrontToyX Cb.LdLkp
open FrontToy (JJ tDt tRdK tRd0 tRd1)

def ldSegFront_toyX : Prop :=
  ∀ (Sx Kc : Type) (S : Sig E) (E₀ : ExtSpec) [Nonempty E₀.Str] (Wp : Type)
      (all : S.Msg → JJ → E) (Rx : Rels Kc Sx E₀ (S.Msg × Wp)),
    (tV Sx Kc S E₀ Wp all Rx).OK pK ∧
    (tF Sx Kc S E₀ Wp all Rx).ZkOK pK tDt tRdK (tC Sx) ∧
    (tBit Sx).zc.next.OwnOur tRd0 ∧
    (tEnd Sx).psc.OwnOur tRd1 ∧
    ldQuiet S ((tV Sx Kc S E₀ Wp all Rx).tab.f0 tRd0) all ((tA Sx).srAll tDt) ∧
    ldQuiet S ((tV Sx Kc S E₀ Wp all Rx).tab.f 0 tRd1) all ((tA Sx).srAll tDt) ∧
    ldQuiet S ((tV Sx Kc S E₀ Wp all Rx).tab.f 0 tRd1) all tRd0 ∧
    (tV Sx Kc S E₀ Wp all Rx).prog.Hyp ∧
    (tV Sx Kc S E₀ Wp all Rx).prog.Zk (tBase Sx Kc S E₀ Wp all Rx) ∧
    (tV Sx Kc S E₀ Wp all Rx).prog.nAll = 36

end Spec
end Cb.GlJ3
