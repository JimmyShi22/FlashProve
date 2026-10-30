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
Cb/Gen/CodeListRS.lean.) Cb/GlVal/GlJ3SegRefToyAllS.lean: a small example instance of one part of
the interactive proof for a request: the sub-protocols of one piece of the request (among them a
read, a range check, a lookup on the digits, a batching of linear claims on the encoded index), put
together as one term, here over arbitrary oracle messages that are already open.

Definitions, statement (`Cb.GlJ3.Spec.ldSegRef_toyAllS`) and proof. A guard against empty theorems;
no parameter of a protocol. Before it: Cb/GlVal/GlJ3SegRefToyS.lean,
Cb/GlVal/GlJ3SegRefToyDigS.lean. The same over the fixed family: Cb/GlVal/GlJ3SegRefToyAll.lean (the
record `LdRefD`, the front, the ghost and the configuration are told there).

Main names:
  `APar`: what the front hands over, as parameters: those of `RefToy.APar`, and: the open oracle
    messages S with an injective naming `at'` of the entries that the body's own clauses read or
    name; the two families that the body sends (`k1`, `k3`).
  `A P V`: the closed data (`LdRefD`), for any front V.
  `reads_named`, `entry_named`: on what the body's own clauses read of S.
  `Spec.ldSegRef_toyAllS` states, for all P and V: the batching's conditions on its own entries
    (`(A P V).X.Own`); what is left goes over into what follows (`X.Ends`, with Az := all that is
    left, `X.m1.A`); the core is the ghost (`(A P V).Ghost id`); and, given the front's own
    conditions (if `V.OK pK`): `(A P V).OK pK`, and the whole body has all that a list of moves asks
    (`((A P V).body ..).Hyp`: `LdProg.Hyp`, Cb/Req1/LdSeg.lean; by `Spec.ldSegRefAll_body`,
    Cb/Req1/LdSegRefAll.lean, whose hypotheses, beside `[CharP E pp]`, are this `OK` and this
    `Ends`).

Conventions of this namespace's toys, said of the toys' own oracle messages and groups, not of what
a statement takes as a parameter (of the names declared in Cb/GlVal/ and Cb/Gl/GlField.lean this
file uses only the field E, `StdKit`, with `oneKit` as the default value of `k1` and `k3`,
Cb/GlVal/GlJ3SegRefToyStdKit.lean, the data and facts of Cb/GlVal/GlJ3SegRefToyS.lean (`RPar`, `D`,
`send1`, `send3`), of Cb/GlVal/GlJ3SegRefToyDigS.lean (`T`, `X`, `sAt`, `rAt` and its theorems), of
Cb/GlVal/GlJ3SegRefToy.lean (`p`, `pOK`, `uniq`, the types of names) and of
Cb/GlVal/GlJ3SegRefToyAll.lean (`Cc`, `Gh`, `tIx`, `mask_sumJ3`), `Wf8.mat`, `Wf8.p0`,
Cb/GlVal/GlToyWf.lean, and `pK`, Cb/GlVal/GlToyNum.lean; S, `k1`, `k3`, the front V and what it
hands over are parameters): the fields are F, the integers modulo 2^64 - 2^32 + 1, and
E = F[x] / (x^3 - 2) (Cb/Gl/GlField.lean). The toys' code is that of Cb/GlVal/GlToyBase4.lean: eight
points, dimension 4, distance 5, hides 3.
The radius, the bounds on lists, the counts for agreement and the pad's coefficient of these toys
are told in the head of Cb/GlVal/GlJ3Base.lean: read it before quoting.
This is not said of the offline side (configuration, index, lookup tables, weights-formedness).

Limits: this file does not say that a front with `V.OK pK` ends at this stage (`(D (R P)).s0`; at
values `FrontToyS.sP ..`, `FrontToyX.sP ..` of P, each for an injective `at'`, such fronts are
given: `FrontToyS.sV`, `Spec.ldSegFront_toySeamS`, Cb/GlVal/GlJ3SegFrontToySeamS.lean;
`FrontToyX.sV`, `Spec.ldSegFront_toySeamX`, Cb/GlVal/GlJ3SegFrontToySeamX.lean). This file says
nothing on the closing, on zero knowledge of the whole, on real parameters. Pads in the subfield F
are not exercised. "What else is claimed" (`rel0`, `relR0`) is the front's parameter and may read
more.

Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyNum
import Cb.GlVal.GlToyLkpNames
import Cb.GlVal.GlJ3Send
import Cb.GlVal.GlToyConfM
import Cb.GlVal.GlJ3PackNames
import Cb.GlVal.GlJ3SegRefToyDigS
import Cb.GlVal.GlJ3SegRefToyAll
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb.GlJ3
open Cb.Gl hiding p

namespace RefToyS
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp
open RefToy (p LN WBt Jn So Bt No' Cc Gh tIx pOK uniq)


/-- What the front hands over. -/
structure APar : Type 1 where
  W₁  : Type
  w₁0 : W₁
  Xn  : Type
  [finX : Fintype Xn]
  [decX : DecidableEq Xn]
  /-- the open oracle messages; the entries that the body reads or names -/
  S   : Sig E
  at' : So Xn → S.Ent
  inj : Function.Injective at'
  St  : Type
  W   : St → p.Rd → p.Row → E
  cl  : ReadCl p E St (Jn Xn)
  [finJc : Fintype cl.Jc]
  /-- the record; the tensor row: target, point, coefficient of its mask -/
  rc  : St → Cc.Rec
  tg  : St → E
  pt  : St → Fin 1 → E
  mf  : St → E
  /-- what else is claimed -/
  rel0  : St → Cc.E0.Str → (Cc.Msg × S.Msg) × (W₁ × Gh) → Prop
  relR0 : St × Cc.E0.Str → (Cc.Msg × S.Msg) × (W₁ × Gh) → Prop
  on0   : St × Cc.E0.Str → Prop
  /-- the two families that the body sends, with their standard layouts -/
  k1  : StdKit (Unit × Unit) := oneKit _
  k3  : StdKit No' := oneKit _

attribute [instance] APar.finX APar.decX APar.finJc

variable (P : APar)

/-- the name of the tensor row's mask -/
def mkN : So P.Xn := .inr (.inr (.inr (.inr (.inl ()))))

/-- The tensor row, on the messages of S. -/
def tenS (st : P.St) (U : Cc.Msg) (ms : P.S.Msg) : Prop :=
  Alg.mle (fun c => ∑ r : Unit, (1 : E) * Cb.Gl.Wf8.mat U (r, c)) (P.pt st) +
      P.mf st * P.S.ents ms (P.at' (mkN P)) = P.tg st

/-- what the front hands over, as the `RPar` of Cb/GlVal/GlJ3SegRefToyS.lean -/
@[reducible] def R : RPar Gh Cc.E0 (Cc.PIdx × (P.W₁ × Gh)) where
  Xn := P.Xn
  S := P.S
  at' := P.at'
  inj := P.inj
  St := P.St
  W := P.W
  yz := id
  cl := P.cl
  A₀ := idxAt Cc P.rc ⟨fun st y w => P.rel0 st y w ∧ tenS P st w.1.1 w.1.2,
    fun a w => P.relR0 a w ∧ tenS P a.1 w.1.1 w.1.2,
    P.on0, fun w => w.2.2⟩
  wp0 := (Cb.Gl.Wf8.p0, (P.w₁0, fun _ _ => 0))
  k1 := P.k1
  k3 := P.k3

/-- the messages of S among all messages -/
def prS (m : (T (R P)).Msg) : P.S.Msg := fun i => m (.inl (.inl i))

/-- The closed data. -/
@[reducible] def A (V : LdFrontRef E Gh (D (R P)).s0) : LdRefD E Gh tIx where
  W₁ := P.W₁
  Gh := Gh
  Xa := X (R P)
  finJc := P.finJc
  pkAt := fun _ _ => sAt (R P) (.inl ())
  rdAt := fun k c => rAt (R P) (k, c)
  jAt := fun j => sAt (R P) (.inr j)
  Stt := P.St
  rc := P.rc
  Qt := Fin (0 + 1)
  g := fun _ _ _ => 1
  pt := fun st _ => P.pt st
  Nm := Unit
  mf := fun st _ _ => P.mf st
  μAt := fun _ => sAt (R P) (mkN P)
  Zt := Evader.powers E (0 + 1)
  nt := 2
  wAt := fun i => sAt (R P) (.inr (.inr (.inr (.inl i))))
  A0t := ⟨fun st y w => P.rel0 st y ((w.1.1, prS P w.1.2), w.2),
    fun a w => P.relR0 a ((w.1.1, prS P w.1.2), w.2),
    P.on0, fun w => w.2.2⟩
  Rdt := fun j => (∃ i, j = sAt (R P) (.inr (.inr (.inr (.inl i))))) ∨ j = sAt (R P) (mkN P)
  g₀ := fun st => (fun _ => P.tg st, st)
  V := V


variable (P : APar) (V : LdFrontRef E Gh (D (R P)).s0)

/-- The tensor row on the messages of S is the batching's claim on all messages. -/
theorem ten_iff (st : P.St) (U : Cc.Msg) (m : (T (R P)).Msg) :
    (A P V).X.TenOK ((A P V).g₀ st) (U, m) ↔ tenS P st U (prS P m) := by
  have hs := (A P V).X.mask_sumJ3 ((A P V).X.mf st 0) (U, m)
  have h1 : ∑ a, (A P V).X.mf st 0 a * (A P V).X.S.ents (U, m).2 ((A P V).X.μAt a) =
      P.mf st * P.S.ents (prS P m) (P.at' (mkN P)) := by
    show ∑ _a : Unit, P.mf st * P.S.ents (prS P m) (P.at' (mkN P)) = _
    simp
  rw [h1] at hs
  constructor
  · intro h
    unfold tenS
    rw [← hs]
    exact h 0
  · intro h (q : Fin 1)
    obtain rfl : q = 0 := Subsingleton.elim _ _
    unfold tenS at h
    rw [← hs] at h
    exact h

theorem reads : (A P V).Gr.Reads := ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- What else was claimed goes over. -/
theorem rest : (A P V).Gr.Rest (A P V).Y.St₀ (A P V).Y.g₀ (A P V).Y.Ar where
  fw := fun st _ m _ h => ⟨h.1, h.2.1, (ten_iff P V st _ m).2 h.2.2⟩
  bw := fun st _ m _ _ ⟨U, hU, h1, h2⟩ => ⟨U, hU, h1, (ten_iff P V st U m).1 h2⟩
  on := fun _ _ h => h
  core := fun _ _ => rfl

theorem ok (hV : V.OK pK) : (A P V).OK pK where
  front := hV
  ok := pOK
  places := places (R P)
  uniq := uniq
  send1 := send1 (R P)
  send3 := send3 (R P)
  tabQ := show 2 ≤ 2 ^ 1 by decide
  tabH := show 2 ≤ 2 ^ 1 by decide
  keys := show 2 ≤ 2 ^ 1 by decide
  tags := zero_ne_one
  inj := iota_inj (R P)
  named := named (R P)
  adm := adm (R P)
  bits := bits (R P)
  reads := reads P V
  rest := rest P V
  deg := le_refl 2
  ev := ok_powers E (0 + 1)

theorem own : (A P V).X.Own where
  inj := fun _ _ h =>
    Sum.inl_injective (Sum.inr_injective (Sum.inr_injective (Sum.inr_injective (sAt_inj (R P) h))))
  own := fun i => Or.inl ⟨i, rfl⟩
  rdM := fun _ => Or.inr rfl
  wM := fun _ _ h =>
    Sum.inl_ne_inr (Sum.inr_injective (Sum.inr_injective (Sum.inr_injective (sAt_inj (R P) h))))

theorem ends : (A P V).X.Ends (A P V).X.bt.par.Mid id (A P V).X.m1.A :=
  ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h, fun _ _ h => h, fun _ => rfl⟩

theorem ghost : (A P V).Ghost id := fun _ => rfl

/-- The named entries are all that the body's own clauses read of S, in this form: messages of S
that agree at the named entries (`h`) give the same `pk`, the same `ent` and the same `tenS`. -/
theorem reads_named (m m' : P.S.Msg) (h : ∀ i, P.S.ents m (P.at' i) = P.S.ents m' (P.at' i)) :
    (D (R P)).c.pk m = (D (R P)).c.pk m' ∧
    (D (R P)).c.ent m = (D (R P)).c.ent m' ∧
    ∀ st U, tenS P st U m ↔ tenS P st U m' :=
  ⟨funext fun _ => funext fun _ => h _, funext fun _ => h _, fun st U => by unfold tenS; rw [h]⟩

/-- so the exact claim at the first stage of "read" (`(D (R P)).s0.A.rel`) is the same at messages
that agree at the named entries, if "what else is claimed" is -/
theorem entry_named (m m' : P.S.Msg) (h : ∀ i, P.S.ents m (P.at' i) = P.S.ents m' (P.at' i))
    (st : P.St) (y : Cc.E0.Str) (wp : Cc.PIdx × (P.W₁ × Gh))
    (h0 : P.rel0 st y ((wp.1.1.1, m), wp.2) ↔ P.rel0 st y ((wp.1.1.1, m'), wp.2)) :
    (D (R P)).s0.A.rel st y (m, wp) ↔ (D (R P)).s0.A.rel st y (m', wp) := by
  obtain ⟨e1, e2, e3⟩ := reads_named P m m' h
  show (PackBy p.B p.rdx wp.2.2 ((D (R P)).c.pk m) ∧
      P.cl.OnCells P.W st (cells p.P (2 * p.D) p.rdx ((D (R P)).c.pk m)) ((D (R P)).c.ent m) ∧
      Cc.Enc (P.rc st) y wp.1 ∧
      P.rel0 st y ((wp.1.1.1, m), wp.2) ∧
      tenS P st wp.1.1.1 m) ↔
    (PackBy p.B p.rdx wp.2.2 ((D (R P)).c.pk m') ∧
      P.cl.OnCells P.W st (cells p.P (2 * p.D) p.rdx ((D (R P)).c.pk m')) ((D (R P)).c.ent m') ∧
      Cc.Enc (P.rc st) y wp.1 ∧
      P.rel0 st y ((wp.1.1.1, m'), wp.2) ∧
      tenS P st wp.1.1.1 m')
  rw [e1, e2, h0, e3 st wp.1.1.1]

end RefToyS

namespace Spec
open Iop Prob Hiop IOR RefToyS
open RefToy (Gh)

def ldSegRef_toyAllS : Prop :=
  ∀ (P : APar) (V : LdFrontRef E Gh (D (R P)).s0),
    (A P V).X.Own ∧ (A P V).X.Ends (A P V).X.bt.par.Mid id (A P V).X.m1.A ∧ (A P V).Ghost id ∧
    (V.OK pK → (A P V).OK pK ∧ ((A P V).body (A P V).X.bt.par.Mid id (A P V).X.m1.A).Hyp)

end Spec

open RefToyS in
theorem ldSegRef_toyAllS : Spec.ldSegRef_toyAllS := fun P V =>
  ⟨own P V, ends P V, ghost P V,
    fun hV => ⟨ok P V hV, ldSegRefAll_body E RefToy.Gh pK _ (A P V) _ id _ (ok P V hV) (ends P V)⟩⟩

end Cb.GlJ3
