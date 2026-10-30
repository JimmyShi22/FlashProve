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
Cb/Gen/CodeListRS.lean.) Cb/GlVal/GlJ3SegFrontToy.lean: a toy front of a segment's body: shift,
lookup, zerocheck, two sumchecks; all named conditions met together, nothing assumed beyond the
hypotheses of the statements and whatever the arguments hold as proofs.

A sanity check of hypotheses. A shift, a lookup argument, a zerocheck and two sumchecks are run in a
row on one small vector of field elements; the statement says that, under the hypotheses below, the
conditions which the library names for such a row of sub-protocols, listed under Main names, hold
together at this instance.
Definitions and the statement. Proof: Cb/GlVal/GlJ3SegFrontToyProofs.lean. A guard against empty
theorems; no parameter of a protocol.
The front of a segment's body (`LdBodyD`, Cb/Req1/LdSegRefBody.lean) is the list of moves before the
step "read": the record `LdFrontRef` (Cb/Req1/LdSegFrontRef.lean), with its list of moves `V.prog`
and its conditions `V.OK p`. This file fills that record at small data.

Main names:
  The claims: two keys are entries of the table (5, 7) (`tP`); two further entries a₀, a₁ are bits
    (`tBit`).
  The blocks, in the order of the front: (1) the shift θ (one function, tag 1: `tP`); (2) the
    assembled lookup on the keys + θ and the table (5 + θ, 7 + θ) (`tA`); (3) the zerocheck's point
    and the sumcheck of the bit test on (a₀, a₁) (`tBit`; `LkBit`, Cb/Ld/LdLkpBit.lean; one
    variable); (4) one further sumcheck (`tEnd`; `LkEnd`, Cb/Ld/LdLkpEnd.lean; one variable, public
    vector 1), which takes up the value row of the one before, with the target value + 1.
  Generic in: the core's type Kc; the oracle messages S; the further oracles E₀; the further witness
    Wp; the reading all : S.Msg → JJ → E of the entries off the messages (any function); a joint Rx
    that rides along (any).
  `tDt`: the lookup's data (keys, bits) among all entries.
  `Spec.ldSegFront_toy` states, for all these parameters, E₀ having a string (`E₀.Str` nonempty):
    `(tV ..).OK pK` (the list "shift, lookup", `(tF ..).OK pK`; the zerocheck's three conditions;
    the conditions of both sumchecks; the steps between); `(tV ..).prog.Hyp` (the hypotheses of its
    list of moves); the number of rounds `(tV ..).prog.nAll` is 36 (the count for every front:
    `Spec.ldSegFrontRef_nums`, Cb/Req1/LdSegFrontRef.lean); and the clauses
    `(tF ..).ZkOK pK tDt tRdK tC` (Cb/Req1/LdSegRefLkpPreZk.lean), `OwnOur` of both sumchecks
    (Cb/Ld/LdPscZk.lean), `ldQuiet` three times (Cb/Req1/LdSegFrontTabZk.lean) and
    `(tV ..).prog.Zk (tBase ..)` (Cb/Req1/LdReq.lean): for these see the statement. Further:
    `eL idle` and `eL (.inr ())` are not in `tRd1`; no `zAt i` is in `tRdK`, no `cAt i` in `tRd0`,
    no `rAt r` in `tRd1`. The entry claims can hold and can fail: `EntryP` holds of two vectors of
    entries with different keys (`w57`, `w55`); `EntryR` fails of one with a key outside the table
    (`w56`) and of one with a₀ = a₁ = 2.

Conventions of this namespace's toys, said of the toys' own oracle messages and groups, not of what
a statement takes as a parameter (of the names declared in Cb/GlVal/ and Cb/Gl/GlField.lean this
file uses only the field E, the toy lookup's names `Rw`, `Nm`, `kAt`, `idle`, `iN`, `toyA`, `mkDt`,
`mkRd`, `w55`, `w56`, `w57`, Cb/GlVal/GlToyLkpNames.lean, and `pK`, Cb/GlVal/GlToyNum.lean; Kc, S,
E₀, Wp, `all`, `Rx` are parameters):
the fields are F, the integers modulo 2^64 - 2^32 + 1, and E = F[x] / (x^3 - 2)
(Cb/Gl/GlField.lean). The toys' code is that of Cb/GlVal/GlToyBase4.lean: eight points, dimension 4,
distance 5, hides 3.
The radius, the bounds on lists, the counts for agreement and the pad's coefficient of these toys
are told in the head of Cb/GlVal/GlJ3Base.lean: read it before quoting.
This is not said of the offline side (configuration, index, lookup tables, weights-formedness).
The names of codes, messages and their facts: Cb/GlVal/GlJ3Send.lean, Cb/GlVal/GlJ3StdNames.lean,
Cb/GlVal/GlJ3PackNames.lean.

Notation: `JJ`: all entries; `eL`: the toy lookup's entries (`Rw`) among them; `zAt i`, `cAt i`,
`rAt r`: the entries named by `WZ ⊕ Unit`, `WC ⊕ Unit`, `Ride`; `tRdK`: the entries `eL j0` with
`mkRd j0`; `tRd0`: `tRdK`, a₀, a₁ and every `zAt i`; `tRd1`: `tRd0` and every `cAt i`; `tBase ..`:
the facts `((tF ..).dm tRdK tC).fact`, `(tV ..).tab.f0 tRd0` and `(tV ..).tab.f i tRd1`, i ≤ 0.

Limits: `(tV ..).prog.Zk (tBase ..)` is conditional on the three facts being fresh at the entry:
that is the matter of the sending before the front. This file says nothing on real parameters. The
front ends at the further sumcheck's own output stage; a last step into the stage of the step "read"
is in Cb/GlVal/GlJ3SegFrontToySeam.lean. With one further sumcheck (m = 0) two groups of clauses
hold for want of cases and are not tested here: "step i, i < m" of `V.OK`, and "quiet for the
further sumchecks before it". Pads in the subfield F are not exercised. The bounds that the toys
write (one hidden position) are kept, though this code hides 3 (said of `RefToy.D`,
Cb/GlVal/GlJ3SegRefToy.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyNum
import Cb.GlVal.GlToyLkpNames
import Cb.GlVal.GlJ3Send
import Cb.GlVal.GlToyConfM
import Cb.GlVal.GlJ3PackNames
import Cb.Req1.LdSegFrontToyKit
import Cb.Ld.LdLkpRe2
import Cb.Req1.LdSegFrontRefZk

set_option autoImplicit false

namespace Cb.GlJ3
open Cb.Gl hiding p
namespace FrontToy
open Iop Prob Hiop IOR Cb.Gl.LkpToy Cb.LdLkp Cb.Lkp

noncomputable
section

/-- the names of the coefficients of the two further hiding polynomials -/
abbrev WZ : Type := PIdx (List.replicate 1 (pfCube E 2) ++ [pDummy E 2])
abbrev WC : Type := PIdx (List.replicate 1 (pfCube E 2) ++ [pDummy E 1])
/-- names that no block of the front reads: room for the own masks of a block behind the segment
(the coefficients of the hiding polynomial of a batching of tensor rows in one variable) -/
abbrev Ride : Type := PIdx (List.replicate 1 (pfCube E 2))
/-- the further entries: a₀, a₁; the own masks of the bit test; those of the further sumcheck;
entries that ride -/
abbrev X : Type := Bool ⊕ ((WZ ⊕ Unit) ⊕ ((WC ⊕ Unit) ⊕ Ride))
/-- All entries. -/
abbrev JJ : Type := Rw ⊕ X

def eL : Rw → JJ := Sum.inl
def aAt (b : Fin 1 → Bool) : JJ := .inr (.inl (b 0))
def zAt (i : WZ ⊕ Unit) : JJ := .inr (.inr (.inl i))
def cAt (i : WC ⊕ Unit) : JJ := .inr (.inr (.inr (.inl i)))
def rAt (r : Ride) : JJ := .inr (.inr (.inr (.inr r)))

/-- one function: the two keys, the table (5, 7), the tag 1 -/
def tP : ShiftP E Unit (JJ → E) :=
  ⟨0, 1, 1, fun _ m _ i => m (eL (kAt (decide (i = 1)))),
    fun _ _ u => if u = 0 then 5 else 7, fun _ => 1⟩

/-- numbers and places of the toy lookup, among all entries;  the lookup that runs -/
def tA0 : LkAsm2 E := toyA.re Unit JJ eL (fun _ m i => m (eL (kAt (decide (i = 1))))) toyA.tab
def tA : LkAsm2 E :=
  toyA.re (Unit × E) JJ eL (fun x m => shKey 1 (tP.key x.1 m) tP.tag x.2) fun x =>
    shTab 1 (tP.tab x.1) tP.tag x.2
def tι : Nm → JJ := fun n => eL (iN n)

/-- the explicit part after the lookup -/
abbrev FXt : Type := FX (Unit × E) E Nm tA0.nRows

/-- The bit test on (a₀, a₁). -/
def tBit : LkBit E :=
  { St := FXt, J := JJ, k := 1, tAt := aAt, wAt := fun i => zAt (.inl i), cAt := zAt (.inr ()) }

/-- the point at which its sumcheck ends, and its last challenge -/
def gam (o : tBit.zc.next.par.Out) : Fin 1 → E :=
  tBit.zc.fn o.st.2.2 (tBit.zc.next.ini o.st (tBit.zc.next.par.hp o.st o.pt))
def bet (o : tBit.zc.next.par.Out) : E := tBit.zc.next.lst o.st (tBit.zc.next.par.hp o.st o.pt)

open Classical in
/-- The further sumcheck. -/
def tEnd : LkEnd E :=
  { X := tBit.zc.next.par.Out, J := JJ, k := 1, tAt := aAt, z := gam, cp := fun _ _ => 1,
    inc := fun o j => if j = zAt (.inr ()) then bet o else 0,
    wAt := fun i => cAt (.inl i), cAt := cAt (.inr ()) }

/-- the multiplicities are valid, function by function -/
def ValidU (m : JJ → E) : Prop :=
  ∀ f < 2 ^ tP.g, Valid tP.v tP.d tA0.w (tA0.n + 1) (tP.key () m f) (tP.tab () f)
    fun u j => m (tA0.bAt (f * 2 ^ tP.d + u) j)

/-- The sets. -/
def tDt : JJ → Prop := fun j => ∃ j0, j = eL j0 ∧ mkDt j0
def tRdK : JJ → Prop := fun j => ∃ j0, j = eL j0 ∧ mkRd j0
def tRd0 : JJ → Prop := fun j => tRdK j ∨ (∃ b, j = .inr (.inl b)) ∨ ∃ i, j = zAt i
def tRd1 : JJ → Prop := fun j => tRd0 j ∨ ∃ i, j = cAt i
/-- the claim with which the lookup's item is started -/
def tC : Unit × E → (JJ → E) → Prop := tA.lk.inP tA.ValidMu

section
variable (Kc : Type) (S : Sig E) (E₀ : ExtSpec) (Wp : Type)
  (all : S.Msg → JJ → E) (Rx : Rels Kc Unit E₀ (S.Msg × Wp))

/-- what rides along from the entry: Rx; a₀, a₁ are bits; on the honest side: the multiplicities are
valid -/
def tRr : Rels Kc Unit E₀ (S.Msg × Wp) :=
  ⟨fun st y w => Rx.rel st y w ∧ tBit.AllBits (all w.1) ∧ ValidU (all w.1),
    fun a w => Rx.relR a w ∧ tBit.AllBits (all w.1),
    Rx.on, Rx.core⟩
def tR1 : Rels Kc (Unit × E) E₀ (S.Msg × Wp) :=
  ⟨fun x y w => (tRr Kc S E₀ Wp all Rx).rel x.1 y w,
    fun a w => (tRr Kc S E₀ Wp all Rx).relR (a.1.1, a.2) w,
    fun a => (tRr Kc S E₀ Wp all Rx).on (a.1.1, a.2),
    (tRr Kc S E₀ Wp all Rx).core⟩
/-- what rides beside the zerocheck: Rx and the lookup's output claim. "a₀, a₁ are bits" is the
zerocheck's own claim from here on and rides no further; the clause on the multiplicities is dropped
-/
def tJT : Rels Kc FXt E₀ (S.Msg × Wp) :=
  cj (⟨fun _ y w => Rx.rel () y w,
      fun a w => Rx.relR ((), a.2) w,
      fun a => Rx.on ((), a.2),
      Rx.core⟩ : Rels Kc (Unit × E) E₀ (S.Msg × Wp))
    all Prod.fst (tA.lk.outF id (tA.entN tι)) (tA.lk.outF id (tA.entN tι))

/-- The list "shift, lookup". -/
def tF : LdPreD E Kc S E₀ Wp :=
  { St := Unit, A0 := tA0, msg := all, P := tP, Rr := tRr Kc S E₀ Wp all Rx, N := Nm, ι := tι,
    Mu := tA.ValidMu, Z := tBit.zc.toIn, R0z := tJT Kc S E₀ Wp all Rx, msg0 := all, e := id }

/-- what rides beside the further sumcheck: what rode before, and the bit test's row on its hiding
coefficients -/
def tA00 : Rels Kc tEnd.X E₀ (S.Msg × Wp) :=
  ⟨fun o y w =>
      (tBit.zc.toIn.ride (tJT Kc S E₀ Wp all Rx)).rel o.st y w ∧
      tBit.zc.next.par.UHolds o (all w.1),
    fun a w =>
      (tBit.zc.toIn.ride (tJT Kc S E₀ Wp all Rx)).relR (a.1.st, a.2) w ∧
      tBit.zc.next.par.UHolds a.1 (all w.1),
    fun a => (tBit.zc.toIn.ride (tJT Kc S E₀ Wp all Rx)).on (a.1.st, a.2),
    (tBit.zc.toIn.ride (tJT Kc S E₀ Wp all Rx)).core⟩

/-- the stage at which the front ends -/
@[reducible] def tz : LdStage E Kc :=
  ⟨S, tEnd.psc.par.Out, E₀, Wp, tEnd.psc.par.baseOut (tA00 Kc S E₀ Wp all Rx) fun w => all w.1⟩

/-- The front. -/
def tV : LdFrontRef E Kc (tz Kc S E₀ Wp all Rx) :=
  { Fp := tF Kc S E₀ Wp all Rx, m := 0, T := fun _ => tEnd.psc,
    A0 := fun _ => tA00 Kc S E₀ Wp all Rx, msg := fun _ => all, g0 := fun o => (o.vals () + 1, o),
    g := fun _ o => (0, o.st), gz := id }

/-- exactly the facts that are used -/
def tBase : MaskFact (S.Wit × Wp) → Prop := fun f =>
  f = ((tF Kc S E₀ Wp all Rx).dm tRdK tC).fact ∨
  f = (tV Kc S E₀ Wp all Rx).tab.f0 tRd0 ∨
  ∃ i ≤ 0, f = (tV Kc S E₀ Wp all Rx).tab.f i tRd1

end

/-- vectors of entries: those of the toy lookup; a₀, a₁; all further masks 0 -/
def ent (r : Rw → E) (a : Bool → E) : JJ → E
  | .inl j => r j
  | .inr (.inl b) => a b
  | .inr (.inr _) => 0

/-- The entry claims, on a vector of entries. -/
def EntryP (m : JJ → E) : Prop :=
  AllIn tP.g tP.v tP.d (tP.key () m) (tP.tab ()) ∧ tBit.AllBits m ∧ ValidU m
def EntryR (m : JJ → E) : Prop := AllIn tP.g tP.v tP.d (tP.key () m) (tP.tab ()) ∧ tBit.AllBits m

end
end FrontToy

namespace Spec
open Iop IOR Cb.Gl.LkpToy FrontToy Cb.LdLkp

def ldSegFront_toy : Prop :=
  (∀ (Kc : Type) (S : Sig E) (E₀ : ExtSpec) [Nonempty E₀.Str] (Wp : Type)
        (all : S.Msg → JJ → E) (Rx : Rels Kc Unit E₀ (S.Msg × Wp)),
      (tV Kc S E₀ Wp all Rx).OK pK ∧
      (tF Kc S E₀ Wp all Rx).ZkOK pK tDt tRdK tC ∧
      tBit.zc.next.OwnOur tRd0 ∧
      tEnd.psc.OwnOur tRd1 ∧
      ldQuiet S ((tV Kc S E₀ Wp all Rx).tab.f0 tRd0) all (tA.srAll tDt) ∧
      ldQuiet S ((tV Kc S E₀ Wp all Rx).tab.f 0 tRd1) all (tA.srAll tDt) ∧
      ldQuiet S ((tV Kc S E₀ Wp all Rx).tab.f 0 tRd1) all tRd0 ∧
      (tV Kc S E₀ Wp all Rx).prog.Hyp ∧
      (tV Kc S E₀ Wp all Rx).prog.Zk (tBase Kc S E₀ Wp all Rx) ∧
      (tV Kc S E₀ Wp all Rx).prog.nAll = 36) ∧
  (¬ tRd1 (eL idle) ∧ ¬ tRd1 (eL (.inr ())) ∧ (∀ i, ¬ tRdK (zAt i)) ∧
    (∀ i, ¬ tRd0 (FrontToy.cAt i)) ∧ ∀ r, ¬ tRd1 (rAt r)) ∧
  EntryP (ent w57 fun _ => 0) ∧
  EntryP (ent w55 fun b => if b then 1 else 0) ∧
  ¬ EntryR (ent w56 fun _ => 0) ∧
  ¬ EntryR (ent w57 fun _ => 2)

end Spec
end Cb.GlJ3
