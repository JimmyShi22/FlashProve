-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectSendersLin.lean: the object with standard senders in its two tests for linear
constraints and in its link: the four clauses on these senders become a theorem, from `Y.Hyp`.

In standard terms: the honest prover's algorithms for sending encoded messages (senders:
`Sig.Sender`, Cb/Ld/LdSendFam.lean) inside three sub-protocols. In the data of the record of
sub-protocols they are values with assumed properties; here they are one fixed construction, the
standard sender, and these properties are derived from `Y.Hyp`.

Definitions, statements (`Cb.Spec.ldObjS_snd`, `Cb.Spec.ldObjS_hypD`) and proofs (an assembly).
Cb/Obj/LdObjectTerms.lean's data `LdObjD` hold seven honest senders as values (Sn: three, offline;
Sl: one, the link; SnB: three, at N instances), and its hypotheses have four clauses on them
(`LdObjD.HypSnd`: `Sn.OK`, `Sl.OK`, `SnB.OK`, `SnB.Apart`). A standard sender is made from a layout
(`Sig.StdL`, Cb/Ld/LdSendStdL.lean) of the messages into data, free entries and pads.

Main names:
  `LdLinP.Std.Hyp`, `LdLkP.StdHyp`: the hypotheses of `Spec.ldLinStd_ok`, `Spec.ldLk_std` as records
    (their fields: see the records). No clause speaks of a sender.
  `Y : D.StdS`: the data beside `D : LdObjD`: the pads' field `Y.Fp`; the tests' two `Std` and the
    link's layout, with their numbers (bounds for lists, positions that the encodings bear), the
    link's seeds (`SdK`), `ixK` and `wK`.
  `D.std Y`: D with the fields Sn, Sl, SnB (the seven senders with their numbers and the link's
    seeds) replaced. All other fields are D's; no field's type reads a sender.
  `Y.Hyp`: the three records.
  `Spec.ldObjS_snd`: `Y.Hyp` ⇒ `(D.std Y).HypSnd`.
  `Spec.ldObjS_hypD`: `(D.std Y).HypRest L`, `Y.Hyp` ⇒ `(D.std Y).HypD L`.

Why: the pads' field is a field of the record, not the configuration's base field (`Y.Fp` with E an
algebra over it). This protocol's technical report (lean/CREDITS.md) gives each oracle message a
field of its own: the base field if all its rows are over it, E otherwise; the pad of one answer has
as many entries of that
field as E has dimension over it. All oracle messages that the two tests and the link send are over
E: there the pad is one entry of E an answer: Y.Fp := E. (Pads in a proper subfield at places of a
message over E: private answers can be had, but then an answer has two or more pad places, and some
vector over E, not 0, has the answer 0 at every seed (Cb/Gl/GlSendersToyJ.lean [not in this library]: pad_two_kills,
stated of `Sample.pad` with a pad weight that is not 0): "evades" (`OMsg.Evades`, Cb/Ld/LdSig.lean)
fails as soon as two messages that differ by it lie in one list (where the sample's `err` is below
the number of its seeds: not so with one coefficient alone, card B = 1 in `Sample.pad`,
Cb/Gen/OodDecPad.lean); within unique decoding that cannot be.)
One field stands here for all seven layouts.

Limits: on the senders inside the preamble of weights-formedness and inside a request: the record
`HypRest L` (Cb/Obj/LdObjectTerms.lean), which `Spec.ldObjS_hypD` assumes and hands on unchanged,
has, nested under its fields `wfHyp`, `rHyp`, among others `sender`, `sBlind`, `hides` (`Blk.Hyp`,
Cb/Ld/LdWf.lean) and `sender`, `blind`, `hides` (`LdSendD.Hyp`, Cb/Req1/LdSegKit.lean); on these
senders as standard senders this file says nothing: Cb/Obj/LdObjectSenders.lean. That `Y.Hyp` can be
met together with `HypRest L` is not said here.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectPlan
import Cb.Ld.LdLinStd
import Cb.Ld.LdSendStdVec
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- What is asked for the three standard senders of the test. -/
structure LdLinP.Std.Hyp {F E ι κ J Y : Type} [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] {P : LdLinP E ι κ J Y} (T : P.Std F) (LW : P.NW.O → ℕ) (LU : P.NU.O → ℕ)
    (LO : P.NO.O → ℕ) (tW : P.NW.O → ℕ) (tU : P.NU.O → ℕ) (tO : P.NO.O → ℕ) : Prop where
  places : T.Places
  okW   : T.YW.OK tW
  okU   : T.YU.OK tU
  okO   : T.YO.OK tO
  lawsW : ∀ a, (P.NW.om a).C.Laws
  fairW : P.SdW.Fair
  listW : ∀ a, (P.NW.om a).ListLE (LW a)
  evW   : ∀ a, (P.NW.om a).Evades
  lawsU : ∀ a, (P.NU.om a).C.Laws
  fairU : P.SdU.Fair
  listU : ∀ a, (P.NU.om a).ListLE (LU a)
  evU   : ∀ a, (P.NU.om a).Evades
  lawsO : ∀ a, (P.NO.om a).C.Laws
  fairO : P.SdO.Fair
  listO : ∀ a, (P.NO.om a).ListLE (LO a)
  evO   : ∀ a, (P.NO.om a).Evades

/-- What is asked for the standard sender of the link. -/
structure LdLkP.StdHyp {F E ι κ J Λ : Type} [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] (P : LdLkP E ι κ J Λ) (Sd : P.N.Seeds) (L t : P.N.O → ℕ)
    (Y : P.N.StdL F) (ix : ∀ a, Y.Dt a → Option (κ ⊕ κ)) : Prop where
  ok    : Y.OK t
  reads : Y.Reads ix fun m => Sum.elim (P.uv₀ m) (P.uv₁ m)
  laws  : ∀ a, (P.N.om a).C.Laws
  fair  : Sd.Fair
  list  : ∀ a, (P.N.om a).ListLE (L a)
  ev    : ∀ a, (P.N.om a).Evades

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- Standard senders for the object: the data. -/
structure LdObjD.StdS (D : LdObjD F E) where
  /-- the pads' field -/
  Fp : Type
  [fldFp : Field Fp]
  [finFp : Fintype Fp]
  [algFp : Algebra Fp E]
  /-- offline -/
  TS : D.W.O.toC.P.Std Fp
  LW : D.W.O.toC.P.NW.O → ℕ
  LU : D.W.O.toC.P.NU.O → ℕ
  LO : D.W.O.toC.P.NO.O → ℕ
  tW : D.W.O.toC.P.NW.O → ℕ
  tU : D.W.O.toC.P.NU.O → ℕ
  tO : D.W.O.toC.P.NO.O → ℕ
  /-- the link -/
  YK  : D.K.P.N.StdL Fp
  ixK : ∀ a, YK.Dt a → Option (Fin D.W.Cf.C₀.k ⊕ Fin D.W.Cf.C₀.k)
  wK  : D.K.P.W1
  SdK : D.K.P.N.Seeds
  LK : D.K.P.N.O → ℕ
  tK : D.K.P.N.O → ℕ
  /-- at N instances -/
  TB  : D.on.ol.toC.P.Std Fp
  LWB : D.on.ol.toC.P.NW.O → ℕ
  LUB : D.on.ol.toC.P.NU.O → ℕ
  LOB : D.on.ol.toC.P.NO.O → ℕ
  tWB : D.on.ol.toC.P.NW.O → ℕ
  tUB : D.on.ol.toC.P.NU.O → ℕ
  tOB : D.on.ol.toC.P.NO.O → ℕ

attribute [instance] LdObjD.StdS.fldFp LdObjD.StdS.finFp LdObjD.StdS.algFp

/-- What is asked: no clause speaks of a sender. -/
structure LdObjD.StdS.Hyp {D : LdObjD F E} (Y : D.StdS) : Prop where
  off  : Y.TS.Hyp Y.LW Y.LU Y.LO Y.tW Y.tU Y.tO
  link : D.K.P.StdHyp Y.SdK Y.LK Y.tK Y.YK Y.ixK
  on   : Y.TB.Hyp Y.LWB Y.LUB Y.LOB Y.tWB Y.tUB Y.tOB

/-- The data with the seven senders replaced. -/
@[reducible] def LdObjD.std (D : LdObjD F E) (Y : D.StdS) : LdObjD F E :=
  { D with
    Sn := Y.TS.snd Y.LW Y.LU Y.LO Y.tW Y.tU Y.tO, Sl := D.K.P.stdS Y.SdK Y.LK Y.tK Y.YK Y.ixK Y.wK,
    SnB := Y.TB.snd Y.LWB Y.LUB Y.LOB Y.tWB Y.tUB Y.tOB }

/-- the same for the object with both closings at the plan -/
@[reducible] def LdObjP.std (P : LdObjP F E) (Y : P.toLdObjD.StdS) : LdObjP F E :=
  { P with toLdObjD := P.toLdObjD.std Y }

end

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The four clauses on the senders. -/
def ldObjS_snd : Prop := ∀ (D : LdObjD F E) (Y : D.StdS), Y.Hyp → (D.std Y).HypSnd

def ldObjS_hypD : Prop :=
  ∀ (D : LdObjD F E) (Y : D.StdS) (L : ℕ), (D.std Y).HypRest L → Y.Hyp → (D.std Y).HypD L

end
end Spec

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem LdLinP.Std.Hyp.ok {ι κ J Y : Type} {P : LdLinP E ι κ J Y} {T : P.Std F}
    {LW : P.NW.O → ℕ} {LU : P.NU.O → ℕ} {LO : P.NO.O → ℕ} {tW : P.NW.O → ℕ} {tU : P.NU.O → ℕ}
    {tO : P.NO.O → ℕ} (h : T.Hyp LW LU LO tW tU tO) : (T.snd LW LU LO tW tU tO).OK :=
  ldLinStd_ok P T LW LU LO tW tU tO h.places h.okW h.okU h.okO h.lawsW h.fairW h.listW h.evW h.lawsU
    h.fairU h.listU h.evU h.lawsO h.fairO h.listO h.evO

theorem ldObjS_snd : Spec.ldObjS_snd F E := fun D Y h =>
  ⟨h.off.ok,
    ldLk_std Y.Fp E _ _ _ _ D.K.P Y.SdK Y.LK Y.tK Y.YK Y.ixK Y.wK h.link.ok h.link.reads h.link.laws
      h.link.fair h.link.list h.link.ev,
    h.on.ok,
    ldLinStd_apart D.on.ol.toC.P Y.TB Y.LWB Y.LUB Y.LOB Y.tWB Y.tUB Y.tOB⟩

theorem ldObjS_hypD : Spec.ldObjS_hypD F E := fun D Y _ hr h => ⟨hr, ldObjS_snd D Y h⟩

end
end Cb
