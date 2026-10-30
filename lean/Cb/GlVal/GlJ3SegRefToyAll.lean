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
Cb/Gen/CodeListRS.lean.) Cb/GlVal/GlJ3SegRefToyAll.lean: a small example instance of one part of the
interactive proof for a request: the sub-protocols of one piece of the request (among them a read, a
range check, a lookup on the digits, a batching of linear claims on the encoded index), put together
as one term.

Definitions, statement (`Cb.GlJ3.Spec.ldSegRef_toyAll`) and proof. A guard against empty theorems;
no parameter of a protocol. Before it: Cb/GlVal/GlJ3SegRefToy.lean (read, range check),
Cb/GlVal/GlJ3SegRefToyDig.lean (shift, digits' lookup).
`LdRefD` (Cb/Req1/LdSegRefAll.lean) is the data of the reference segment's body, closed;
`LdRefD.body` is the body as a list of moves, and `LdRefD.OK` is asked of it by
`Spec.ldSegRefAll_body`, whose hypotheses, beside `[CharP E pp]`, are `OK` and `X.Ends`. This file
fills that record (`A P V`). The front, the list of moves before the read, stays a parameter V.

Main names:
  `Cc`, `Gh`: the configuration `(toyCf8M ToyMo8.two Md).conf` (Cb/GlVal/GlToyConfM.lean, at the
    relation pair `Md` of Cb/GlVal/GlJ3SegRefToyMd.lean); the ghost: the matrix of integer cells.
  `APar`: what the front hands over, as parameters: W₁; the entries Xn; the states; the weights of
    the read; the claims on cell maps; the record; the tensor row (target, point, coefficient of its
    mask); what else is claimed (`rel0`, `relR0`, `on0`).
  `Spec.ldSegRef_toyAll` states, for all P and V: the batching's conditions on its own entries
    (`(A P V).X.Own`); what is left goes over into what follows (`X.Ends`, with Az := all that is
    left, `X.m1.A`); the core is the ghost (`(A P V).Ghost id`); and, given the front's own
    conditions (if `V.OK pK`): `(A P V).OK pK`, and the whole body has all that a list of moves asks
    (`((A P V).body ..).Hyp`: `LdProg.Hyp`, Cb/Req1/LdSeg.lean; by `Spec.ldSegRefAll_body`,
    Cb/Req1/LdSegRefAll.lean, whose hypotheses, beside `[CharP E pp]`, are this `OK` and this
    `Ends`).

Conventions of this namespace's toys, said of the toys' own oracle messages and groups, not of what
a statement takes as a parameter (of the names declared in Cb/GlVal/ and Cb/Gl/GlField.lean this
file uses only the field E, `datSig`, `datAt`, Cb/GlVal/GlJ3RefKit.lean, the data and facts
of Cb/GlVal/GlJ3SegRefToy.lean (`RPar`, `D`, `p`, `pOK`, `uniq`, `send1`, `send3`, the types of
names) and of Cb/GlVal/GlJ3SegRefToyDig.lean (`T`, `X`, `sAt`, `rAt` and its theorems), `Md`,
Cb/GlVal/GlJ3SegRefToyMd.lean, `toyCf8M`, Cb/GlVal/GlToyConfM.lean, `ToyMo8.two`,
Cb/GlVal/GlToyConf.lean, `Wf8.mat`, `Wf8.p0`, Cb/GlVal/GlToyWf.lean, and `pK`, `ne01`,
Cb/GlVal/GlToyNum.lean; the front V and what it hands over are parameters): the fields are F, the
integers modulo 2^64 - 2^32 + 1, and E = F[x] / (x^3 - 2) (Cb/Gl/GlField.lean). The toys' code is
that of Cb/GlVal/GlToyBase4.lean: eight points, dimension 4, distance 5, hides 3.
The radius, the bounds on lists, the counts for agreement and the pad's coefficient of these toys
are told in the head of Cb/GlVal/GlJ3Base.lean: read it before quoting.
This is not said of the offline side (configuration, index, lookup tables, weights-formedness).

Limits: this file does not say that a front with `V.OK pK` ends at this stage (`(D (R P)).s0`; at
one value of P, `FrontToy.sP`, such a front is given: `FrontToy.sV`, `Spec.ldSegFront_toySeam`,
Cb/GlVal/GlJ3SegFrontToySeam.lean). This file says nothing on the closing, on zero knowledge of the
whole, on real parameters. Pads in the subfield F are not exercised. The bound that the toys write
(one hidden position: `(D (R P)).t`, `(D (R P)).t'`, Cb/GlVal/GlJ3SegRefToy.lean) is kept, though
this code hides 3.

Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyNum
import Cb.GlVal.GlToyLkpNames
import Cb.GlVal.GlJ3Send
import Cb.GlVal.GlToyConfM
import Cb.GlVal.GlJ3PackNames
import Cb.GlVal.GlJ3SegRefToyDig
import Cb.Req1.LdSegRefAllProofs
import Cb.GlVal.GlToyWf
import Cb.GlVal.GlJ3SegRefToyMd

set_option autoImplicit false

namespace Cb.GlJ3
open Cb.Gl hiding p

/-- the value of an incoming mask form of the batching of tensor rows -/
theorem _root_.Cb.LdTenD.mask_sumJ3
    {E Kc : Type} [Field E] [Fintype E] (X : LdTenD E Kc) (c : X.Nm → E) (um : X.C.Msg × X.S.Msg) :
    ∑ j, (Sum.elim (fun _ => 0) (RngPk.placed X.μAt c) : X.bt.J → E) j * X.msg um j =
      ∑ a, c a * X.S.ents um.2 (X.μAt a) := by
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, zero_mul, Finset.sum_const_zero, zero_add, Sum.elim_inr]
  unfold RngPk.placed
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rfl

namespace RefToy
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp

noncomputable
section

/-- the configuration; the ghost -/
abbrev Cc : ConfigurationWithOutOfDomainSample := (toyCf8M ToyMo8.two Md).conf
abbrev Gh : Type := p.Cells

/-- What the front hands over. -/
structure APar : Type 1 where
  W₁  : Type
  w₁0 : W₁
  Xn  : Type
  [finX : Fintype Xn]
  [decX : DecidableEq Xn]
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
  rel0  : St → Cc.E0.Str → (Cc.Msg × (datSig (So Xn)).Msg) × (W₁ × Gh) → Prop
  relR0 : St × Cc.E0.Str → (Cc.Msg × (datSig (So Xn)).Msg) × (W₁ × Gh) → Prop
  on0   : St × Cc.E0.Str → Prop

attribute [instance] APar.finX APar.decX APar.finJc

variable (P : APar)

/-- the name of the tensor row's mask -/
def mkN : So P.Xn := .inr (.inr (.inr (.inr (.inl ()))))

/-- The tensor row, on the messages of S := `datSig (So P.Xn)`. -/
def tenS (st : P.St) (U : Cc.Msg) (ms : (datSig (So P.Xn)).Msg) : Prop :=
  Alg.mle (fun c => ∑ r : Unit, (1 : E) * Cb.Gl.Wf8.mat U (r, c)) (P.pt st) +
      P.mf st * datAt ms (mkN P) = P.tg st

/-- what the front hands over, as the `RPar` of Cb/GlVal/GlJ3SegRefToy.lean -/
@[reducible] def R : RPar Gh Cc.E0 (Cc.PIdx × (P.W₁ × Gh)) where
  Xn := P.Xn
  St := P.St
  W := P.W
  yz := id
  cl := P.cl
  A₀ := idxAt Cc P.rc ⟨fun st y w => P.rel0 st y w ∧ tenS P st w.1.1 w.1.2,
    fun a w => P.relR0 a w ∧ tenS P a.1 w.1.1 w.1.2,
    P.on0, fun w => w.2.2⟩
  wp0 := (Cb.Gl.Wf8.p0, (P.w₁0, fun _ _ => 0))

/-- the messages of S among all messages -/
def prS (m : (T (R P)).Msg) : (datSig (So P.Xn)).Msg := fun i => m (.inl (.inl i))

/-- the encoded index of the toy: its configuration, one row, one column variable -/
@[reducible] def tIx : LdRefIx E := ⟨Cc, Unit, 1, Cb.Gl.Wf8.mat⟩

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

end

variable (P : APar) (V : LdFrontRef E Gh (D (R P)).s0)

/-- The tensor row on the messages of S is the batching's claim on all messages. -/
theorem ten_iff (st : P.St) (U : Cc.Msg) (m : (T (R P)).Msg) :
    (A P V).X.TenOK ((A P V).g₀ st) (U, m) ↔ tenS P st U (prS P m) := by
  have hs := (A P V).X.mask_sumJ3 ((A P V).X.mf st 0) (U, m)
  have h1 : ∑ a, (A P V).X.mf st 0 a * (A P V).X.S.ents (U, m).2 ((A P V).X.μAt a) =
      P.mf st * datAt (prS P m) (mkN P) := by
    show ∑ _a : Unit, P.mf st * datAt (prS P m) (mkN P) = _
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
  tags := ne01
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

end RefToy

namespace Spec
open Iop Prob Hiop IOR RefToy

def ldSegRef_toyAll : Prop :=
  ∀ (P : APar) (V : LdFrontRef E Gh (D (R P)).s0),
    (A P V).X.Own ∧ (A P V).X.Ends (A P V).X.bt.par.Mid id (A P V).X.m1.A ∧ (A P V).Ghost id ∧
    (V.OK pK → (A P V).OK pK ∧ ((A P V).body (A P V).X.bt.par.Mid id (A P V).X.m1.A).Hyp)

end Spec

open RefToy in
theorem ldSegRef_toyAll : Spec.ldSegRef_toyAll := fun P V =>
  ⟨own P V, ends P V, ghost P V,
    fun hV => ⟨ok P V hV, ldSegRefAll_body E Gh pK _ (A P V) _ id _ (ok P V hV) (ends P V)⟩⟩

end Cb.GlJ3
