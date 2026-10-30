-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
In this library the records through which a count for agreement is claimed (`IsGlJ`, `IsGlS`:
Cb/Gl/GlLdJ.lean; `IsGlCpJ`: Cb/Gl/GlCopy.lean) do not ask a
radius within half the distance, and the fact on agreement, `Gl.AgreeJ`, is stated nowhere as a
separate theorem: it follows, by one application that is written down nowhere, from `Cb.BCHKS46At`
(`Cb.Gl.glAg_ofAt`, Cb/Gl/GlFinalAg.lean), which this library proves in Cb/Bridge (bchks46At), from
files adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15), and applies in forms of some of its theorems (files named `…Codes.lean` under
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
Cb/Gen/CodeListRS.lean.) Cb/Gl/GlObjMixStd.lean: in the hypotheses on the protocol object over p =
2^64 - 2^32 + 1, clauses on the codes of weights-formedness, of the seven sendings and of the seven
tests follow from conditions on its Reed-Solomon codes and radii, under the hypothesis
`Cb.BCHKS46F F` on mutual correlated agreement, but for three things:
  one kind ("evades" for the session's three sendings);
  what the request's own hypotheses hold (`own`: `Own3.rHyp`, asked whole: the request is a
  parameter);
  what Limits lists as asked.
Here the honest sender of weights-formedness is the standard one, and the six clauses on it in
`Zw.Rest0 p` are derived from conditions on places, the data map, format, sample and codes (the
fields wfStd to wfCt below); the other clauses are asked as they stand.

Definitions, statements and proofs: an assembly.

Why: Cb/Gl/GlObjMix.lean (`ObjGlM`) asks `Zw.Rest0 p`, which holds six clauses on the sender of
weights-formedness, a term of the data; one of them, "what its encodings hide", touches the codes.
For the standard sender of a layout all six are theorems under the hypotheses of `ldWfE_std`
(Cb/Ld/LdWfEndStd.lean). Here they are put in.

Main names:
  `WfStdD Zw Fp`: data: the layout YS of the family of weights-formedness (pads in a subfield Fp of
    E), its data map datS, a map bd (asked to undo it: wfBd), a default witness; nAt, RdW, atL, pl
    (injective: hpl): where the named entries stand, what the wide reading shows, the places of the
    lookups' own masks as named entries, the free entries at which all masks stand.
  `ObjGlMS Z S a k msg r e mca`: `ObjGlM` with its two fields "wfC (GlC at t = 0)" and "wfRest
    (Zw.Rest0 p)" replaced by: wfStd: sender and mask places are the standard ones (one equation);
    wfAtL, wfAtB, wfNoPad, wfBody, wfBd: five clauses on places and on the data map; wfFmt: the
    format's three clauses; wfPriv: the sample's answers are private over the pads; wfCt: GlC at
    (dS, Zw.t): t uniform coefficients; wfRest2: `Zw.Rest2 p` (the conditions that speak neither of
    a code of an oracle message, nor of a list, nor of the sender, but for: its seeds are fair; the
    vectors that it computes are the multiplicities).
  `Spec.glMS_to`: ObjGlMS Z S .. → ObjGlM Z ..
  `Spec.glMS_hyp`: BCHKS46F F → ObjGlMS Z S .. → `Z.Hyp p`.

So of `Z.Hyp p`'s clauses that touch a code, outside the request's own hypotheses (`Own3.rHyp`) and
what Limits lists as asked: laws, distances, lists, what the sent encodings hide (all eight
sendings), agreement: all derived: from `GlC` / `GlJ`, inequalities, the format's clause zk
(Y.Fmt.zk, Cb/Gl/GlSenders.lean), and, for `T.John` of the session's three towers alone, BCHKS46F F.

Notation: `F`: the integers modulo p (Cb/Gl/GlField.lean); `E`: the challenge field
(Cb/Gl/GlField.lean); `rs a k msg r e mca`: the plain Reed-Solomon code of length 2^a and dimension
k + 1 (Cb/Gl/GlCodes.lean).

Limits: one kind is asked as it stands: "evades" for the session's three sendings: a clause on
the code's lists and the sample together (two members of one list agree at few seeds): beyond unique
decoding it does not follow from GlC. Asked as they stand beside it: the list in the head of
Cb/Gl/GlObjMix.lean without the six clauses: equations, places, seeds, formats, private samples,
radii, bounds, Own3, HypPl, Rest2; also the configuration's sample map and model (smp, model), Fits
of each group, the bridges' and the switches' evaders, and of a shaped tower `Sh.view.Laws`.
`Own3` (Cb/Obj/LdObjectDataThird.lean) holds the request's own hypotheses whole: rHyp : T.r.Hyp,
whose first clause is `LdSendD.Hyp` (Cb/Req1/LdSegKit.lean: laws, fair, list, evades, sender, blind,
hides) of the request's first sending, and rZk : T.r.ZkS.
Asked as they stand too: in each format, Y.Fmt.zk (Cb/Gl/GlSenders.lean); at each switch of a tower:
`Sample.PrivateSim` of the switch's sample.
This file does not say that `ObjGlMS` can be met: no instance of `ObjGlMS`. No instance that meets
the hypotheses of `glMS_hyp` is part of this library; as far as the library shows, this theorem may
hold of nothing. What the head of Cb/Gl/GlObjMix.lean lists as not said is not said here either (the
pads' field of the seven other sendings; the request is a parameter; the plan of the linear test).

Terms: lean/GLOSSARY.md.
-/
import Cb.Gl.GlObjMix
import Cb.Ld.LdWfEndStd

set_option autoImplicit false

namespace Cb.Gl
open Code Prob Blocks Iop Hiop IOR

/-- The standard sender of weights-formedness: the data. -/
structure WfStdD (Zw : LdWfE F E) (Fp : Type) [Field Fp] [Fintype Fp] [Algebra Fp E] where
  YS   : Zw.W.P.S.StdL Fp
  datS : Zw.W.P.Body → ∀ a, YS.Dt a → E
  wS   : Zw.W.P.Body × Zw.W.P.Wp
  bd   : (∀ a, YS.Dt a → E) → Zw.W.P.Body
  nAt  : Zw.W.P.N → Zw.W.P.S.Ent
  RdW  : Zw.W.P.S.Ent → Prop
  atL  : ∀ l : Fin (Zw.W.P.n + 1), (Zw.K.pl Zw.Rl l).I → Zw.W.P.N
  pl   : ∀ b, Zw.K.wfI Zw.Rl b → Σ a, YS.Fr a
  hpl  : Function.Injective fun x : Σ b, Zw.K.wfI Zw.Rl b => pl x.1 x.2

/-- The object at this field, weights-formedness' sender the standard one: the conditions. -/
structure ObjGlMS (Z : LdObjZM F E) {Fp : Type} [Field Fp] [Fintype Fp] [Algebra Fp E]
    [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] (S : WfStdD Z.Zw Fp) (a k msg r e mca : ℕ) :
    Prop where
  /-- the sender of weights-formedness -/
  wfStd   : (⟨Z.Zw.D, Z.Zw.X⟩ : Σ D, Z.Zw.K.MaskPl D Z.Zw.Rl) =
    ⟨Z.Zw.W.P.stdD S.YS S.datS S.wS,
      Z.Zw.K.stdX Z.Zw.Rl S.YS S.datS S.wS S.nAt S.RdW S.atL S.pl S.hpl⟩
  wfAtL   : ∀ l i, S.nAt (S.atL l i) = S.YS.entF (S.pl (some l) i)
  wfAtB   : ∀ i, S.nAt (Z.Zw.W.P.wAt i) = S.YS.entF (S.pl none i)
  wfNoPad : ∀ n, S.RdW n → S.YS.NoPad n
  wfBody  : ∀ m, Z.Zw.W.P.body m = S.bd (S.YS.dataOf m)
  wfBd    : ∀ b, S.bd (S.datS b) = b
  wfFmt   : S.YS.Fmt
  wfPriv  : ∀ o, ((Z.Zw.W.P.S.om o).Z.comap (S.YS.ν o).symm).Private Fp fun _ => True
  wfCt    : ∀ o, GlC (Z.Zw.W.P.S.om o).C (Z.dS o) (Z.Zw.t o)
  wfRest2 : Z.Zw.Rest2 p
  wfIs  : (⟨Z.R.W, Z.R.Bw⟩ : Σ W : LdOWf F E, W.P.Blk) = ⟨Z.Zw.W, Z.Zw.G.B⟩
  sndIs : Z.R.toLdObjD = Z.R.toLdObjD.std Z.Y
  /-- the code of the encoded index: within a third -/
  code  : Z.Zw.W.Cf.C₀ = rs a k msg r e mca
  ha    : a ≤ 32
  hk    : k < 2 ^ a
  hp    : msg + r ≤ k + 1
  h3    : 3 * Z.Zw.W.Cf.eM < 2 ^ a - k
  smp   : Z.Zw.W.Cf.Z.OKOn (Ood.PadInF F)
  model : Z.Zw.W.Cf.ModelOK
  /-- weights-formedness: within a third -/
  wfLt  : ∀ o, 3 * (Z.Zw.W.P.S.om o).e < Z.dS o
  wfOne : ∀ o, Z.Zw.L o = 1
  /-- the offline test's three sendings -/
  plS : Z.Y.TS.Places
  sW  : SndGl3 Z.R.W.O.toC.P.NW Z.Y.TS.YW Z.R.W.O.toC.P.SdW Z.Y.LW Z.Y.tW Z.dW
  sU  : SndGl3 Z.R.W.O.toC.P.NU Z.Y.TS.YU Z.R.W.O.toC.P.SdU Z.Y.LU Z.Y.tU Z.dU
  sO  : SndGl3 Z.R.W.O.toC.P.NO Z.Y.TS.YO Z.R.W.O.toC.P.SdO Z.Y.LO Z.Y.tO Z.dO
  /-- the link's sending -/
  rdK : Z.Y.YK.Reads Z.Y.ixK fun m => Sum.elim (Z.R.K.P.uv₀ m) (Z.R.K.P.uv₁ m)
  sK  : SndGl3 Z.R.K.P.N Z.Y.YK Z.Y.SdK Z.Y.LK Z.Y.tK Z.dN
  /-- the session's three sendings: below the Johnson radius -/
  plB : Z.Y.TB.Places
  sWB : SndGlJ Z.R.on.ol.toC.P.NW Z.Y.TB.YW Z.R.on.ol.toC.P.SdW Z.Y.LWB Z.Y.tWB Z.dWB
  sUB : SndGlJ Z.R.on.ol.toC.P.NU Z.Y.TB.YU Z.R.on.ol.toC.P.SdU Z.Y.LUB Z.Y.tUB Z.dUB
  sOB : SndGlJ Z.R.on.ol.toC.P.NO Z.Y.TB.YO Z.R.on.ol.toC.P.SdO Z.Y.LOB Z.Y.tOB Z.dOB
  /-- clauses as they stand in Z.Hyp p -/
  own : Z.R.toLdObjD.Own3
  pl  : Z.R.HypPl
  /-- the link's test and the offline test's three: within a third -/
  tK  : RunGlAt Z.R.Kc.run Z.twK Z.dK
  t₁  : RunGlAt Z.R.TP₀.D₁ Z.tw₁ Z.d₁
  t₂  : RunGlAt Z.R.TP₀.D₂ Z.tw₂ Z.d₂
  t₃  : RunGlAt Z.R.X.run Z.tw₃ Z.d₃
  /-- the session's three tests: below the Johnson radius -/
  t₁B : RunGlJAt Z.R.TB₀.D₁ Z.tw₁B Z.d₁B
  t₂B : RunGlJAt Z.R.TB₀.D₂ Z.tw₂B Z.d₂B
  t₃B : RunGlJAt Z.R.XB.run Z.tw₃B Z.d₃B

namespace Spec

def glMS_to : Prop :=
  ∀ (Z : LdObjZM F E) (Fp : Type) [Field Fp] [Fintype Fp] [Algebra Fp E]
      [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] (S : WfStdD Z.Zw Fp) (a k msg r e mca : ℕ),
    ObjGlMS Z S a k msg r e mca → ObjGlM Z a k msg r e mca

def glMS_hyp : Prop :=
  Cb.BCHKS46F F →
  ∀ (Z : LdObjZM F E) (Fp : Type) [Field Fp] [Fintype Fp] [Algebra Fp E]
      [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] (S : WfStdD Z.Zw Fp) (a k msg r e mca : ℕ),
    ObjGlMS Z S a k msg r e mca → Z.Hyp p

end Spec

theorem glMS_to : Spec.glMS_to := by
  intro Z Fp _ _ _ _ S a k msg r e mca h
  have hY : S.YS.OK Z.Zw.t :=
    ⟨h.wfFmt.enc, h.wfFmt.lay, h.wfPriv,
      fun o => h.wfFmt.zk o _ (glC_code _ _ _ _ (h.wfCt o)).2.2.2.2⟩
  obtain ⟨sS, bS, hS, pS, oS, fS⟩ :=
    ldWfE_std F E Fp Z.Zw S.YS S.datS S.wS S.bd S.nAt S.RdW S.atL S.pl S.hpl h.wfStd hY h.wfBody
      h.wfBd h.wfAtL h.wfAtB h.wfNoPad
  exact {
    wfIs := h.wfIs
    sndIs := h.sndIs
    code := h.code
    ha := h.ha
    hk := h.hk
    hp := h.hp
    h3 := h.h3
    smp := h.smp
    model := h.model
    wfC := fun o => glC_mono _ _ _ _ _ _ (h.wfCt o) (le_refl _) (Nat.zero_le _)
    wfLt := h.wfLt
    wfOne := h.wfOne
    wfRest := { toRest2 := h.wfRest2, pad := pS, sOwn := oS, sOff := fS, sender := sS,
                sBlind := bS, hides := hS }
    plS := h.plS
    sW := h.sW
    sU := h.sU
    sO := h.sO
    rdK := h.rdK
    sK := h.sK
    plB := h.plB
    sWB := h.sWB
    sUB := h.sUB
    sOB := h.sOB
    own := h.own
    pl := h.pl
    tK := h.tK
    t₁ := h.t₁
    t₂ := h.t₂
    t₃ := h.t₃
    t₁B := h.t₁B
    t₂B := h.t₂B
    t₃B := h.t₃B }

-- Limit: the statement has the premise `Cb.BCHKS46F F`, a hypothesis; this file does not prove it.
theorem glMS_hyp : Spec.glMS_hyp := fun H Z Fp _ _ _ _ S a k msg r e mca h =>
  glM_hyp H Z a k msg r e mca (glMS_to Z Fp S a k msg r e mca h)

end Cb.Gl
