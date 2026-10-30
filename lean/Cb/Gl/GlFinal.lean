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
Cb/Gen/CodeListRS.lean.) Cb/Gl/GlFinal.lean: the conditions over p = 2^64 - 2^32 + 1 (on codes,
radii, layouts, maps of coefficients, the configuration's model (`LdCf.ModelOK`), and those listed
under Limits, the model's duty among them), as one structure, from which the generic hypotheses on
the protocol object follow under a named hypothesis on mutual correlated agreement.

Exactly: a record of conditions over p: the object at the
reference request with plain Reed-Solomon codes, both reductions of hypotheses at once (told in the
next paragraph).

Definitions, statements and proofs: applications.
Both reductions at once: no bound on a list, no agreement, no bound on a fold's bad points, no
clause "two members of one list agree at few seeds" (Cb/Gl/GlFinJ.lean); and the three clauses on
masks replaced by the record on places, layouts and data maps (Cb/Ld/LdLayD.lean). Under the one
hypothesis BCHKS46F F, by name, it gives the generic record `Z.HypRefJU`.

Main names:
  `ReqRefGlU pp R core first b L T qφ q κ`: Cb/Gl/GlFinJ.lean's record `ReqRefGl`, field for field,
    but without lay, layT, layB; in their place layD : LdReqRefLayD LayGl pp R first b L T.
    Its clauses: the model's duty (duty); std : IsStdGl first ∧ ProtoGlL pp L ∧ ProtoGlA T.A pp
    (Cb/GlVal/GlReqJohn.lean); degree, evader and tie of the final batching (deg, ev, tie); own;
    layD; formats (fmt); numbers (bFirst, bSegs, bTail, bLast).
  `LayGl`: what the record on masks asks of each layout that it names, at this field (the parameter
    Q of Cb/Ld/LdLayDKit.lean): the format's three clauses; every member's sample is the row with a
    pad, the weights a basis of E over the pads' field, the factor never 0; every member's code is
    `GlC` at (some distance, t). `layGl_sound`: it gives the layout's laws `Y.OK t`, "private over
    the pads" and "the encodings hide t positions" among them: nothing assumed beside
    `LayGl N t Fp Y` itself (its clause `Y.Fmt.zk` on hiding among it).
  `Final X V p₀ plR a k msg r e mca`: Cb/Gl/GlFinJ.lean's record `FinJ`, field for field, with "req"
    at `ReqRefGlU`. What each field asks: the head of Cb/Gl/GlFinJ.lean.
    Its fields, by groups (the doc comments at the structure): which terms stand in the object; the
    code of the encoded index: within a third; weights-formedness, its sender the standard one; the
    offline test's three sendings; the link's sending; the batch test's three sendings; the index's
    folds; the request; the link's test and the offline test's three: within a third; the session's
    three tests: below the Johnson radius.
  `Spec.glFinal_req`: BCHKS46F F → ReqRefGlU .. → LdReqRefDJU LayGl ..
    (Cb/Obj/LdObjectDataRefJU.lean).
  `Spec.glFinal_hyp`: BCHKS46F F → Final X V p₀ plR a k msg r e mca → X.Z.HypRefJU LayGl p X.R
    X.core X.first X.c X.Ls X.T X.qφ X.q X.κ V p₀ plR.



  `Spec.glFinal_of`: how a guard can meet `Final`, nothing assumed beyond the hypotheses of its
    statement: FinJ X .. and LdReqRefLayD .. ⇒ Final X .. (the three clauses on masks of `FinJ` are
    dropped).

Why the name: not "Fin": inside this namespace that word would hide Lean's own type of numbers below
n.

Where BCHKS46F F enters: as in Cb/Gl/GlFinJ.lean: `T.John` of the batch test's three towers, and the
agreement of the three codes of each closing of the request. It is a hypothesis by name, no axiom;
its source (named at the head of this comment) gives an outline of a proof; nobody of us has checked
a proof. (The source of the statement on codes: the head of Cb/Gen/CodeListRS.lean.)
`Cb.BCHKS46F F` (Cb/Gen/CodeListRSF.lean): mutual correlated agreement of Reed-Solomon codes below
the Johnson radius, for two words, for the finite extensions of F and points in F.

Notation: `X`: the data (`LdFinJ F E`, Cb/Obj/LdObjectDataRefJFin.lean); `V`: of type
`X.Z.Zw.StdW Fp`: the standard sender of weights-formedness: the data beside Zw (`LdWfE.StdW`,
Cb/Obj/LdObjectDataSnd.lean); `p₀`: the plan without a splitting (`LdLinPl`,
Cb/Ld/LdLinClosePlan.lean); `a`, `k`, `msg`, `r`, `e`, `mca`: numbers; the field `code` asks that
the code of the encoded index be `rs a k msg r e mca` (Cb/Gl/GlCodes.lean), which is
`Code.RS.code (pts a) (k + 1) msg r e mca` (Code/RS.lean); `msg`, `r`, `e`, `mca` are handed on to
the fields of these names of `Code.Enc` (Code/Iface.lean): `e`: proximity parameter in positions;
`mca`: count of bad θ.

Limits: what is still asked and is not "families, places and numbers":
  (1) The model's duty (req.duty), the configuration's model (`model` : `LdCf.ModelOK`), and beside
      it the conditions `LdPend.StepD` inside req.layD: the model's entry and exit steps' honest
      maps neither read a pending mask nor drop it.
  (2) That each public map of coefficients is a zero-evader with its stated error: `Evader.OK` of
      every bridge, batching and switch; `Sample.OK` of each switch's sample; the configuration's
      sample map. They speak of no code, no list: properties of public data, no bound on what a
      prover sent. These forms have a theorem in this library: equality weights (`Cb.ok_eqPt`,
      `ok_eqNum`), independent coefficients (`ok_indep`), powers (`ok_powers`), the line
      (`ldBat_ok_line`), the one coefficient (`ldZero_ok_one`), Lagrange weights (`ldZero_ok_lag`).
      Whether these are all the forms that stand at these places has not been examined.
  (3) Clauses that speak of the codes' words, though of no list and no agreement: Fits of each
      group, the held messages' laws, the laws of each shape's view.
  (4) "fmt": formats along the request, each closing's link's format among them; the numbers'
      clauses (idle at κ = ⊤).
  (5) Inside req.layD: "the data map does not look" (`DatBlind`): a condition on data maps. req.layD
      names layouts of its own under "there is", which need not be those of req.std; what the
      messages' encodings and samples hide is asked outright of neither: of both the form is asked,
      `LayGl` in req.layD, `MsgsGl` in req.std, and the laws follow.
Two clauses that name hiding are still asked as they stand: in each format, `Y.Fmt.zk`: if the
code's encoder hides t long positions, so does the format's encoder of the words as sent; at each
switch of a tower: `Sample.PrivateSim` of the switch's sample.
All declared differences of Cb/Gl/GlFinJ.lean's head hold here:
  (a) the hypothesis is wider than the write-up's restatement;
  (b) not below half the distance: every message is over E;
  (c) mask rows of both forms, native and copied, are admitted since the leaf "copy" stands in GlC
      and GlJ (the constructor `copy`: families of copied plain Reed-Solomon codes,
      Cb/Gl/GlCopy.lean).
So do these limits of Cb/Ld/LdLayD.lean's head, which speak of the record in req.layD:
  (d) no splitting: nothing is said on a step that turns one row on two groups into a row on each
      (`LdSplD`, Cb/Req1/LdSegKit.lean);
  (e) a body's own sendings lay no masks;
  (f) a block that crosses a closing lies in messages that are no members of its group;
  (g) one statement at a time: no form for sets of instances;
and the declared differences of that head, among them:
  (h) hiding is exact.
This file does not say that `Final` can be met: no instance in this file. It does not say that the
counts are small against the field. No bound is evaluated.


Terms: lean/GLOSSARY.md: bridge, closing, code switch, evader, group, guard, layout, link,
object, record, reference request, sample, the model's duty, tower.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Gl.GlFinJProofs
import Cb.Obj.LdObjectDataRefJU

set_option autoImplicit false

namespace Cb.Gl
open Code Prob Blocks Iop Hiop IOR IOR.Chain Cb.Ood
open scoped ENNReal

/-- What the record on masks asks of a layout, at this field: the format's three clauses; every
member's sample is the row with a pad; every member's code is built from plain Reed-Solomon families
with at least t uniform coefficients. -/
def LayGl : LdLayQ E := fun N t _ _ _ _ Y =>
  Y.Fmt ∧ Y.PadSmp ∧ ∃ d : N.O → ℕ, ∀ a, GlC (N.om a).C (d a) (t a)

/-- it gives the layout's laws -/
theorem layGl_sound : LayGl.Sound := fun N t Fp _ _ _ Y h =>
  let ⟨d, hd⟩ := h.2.2
  gl_stdL_ok Fp N Y d t h.1 h.2.1 hd

/-- The record of the reference request, at this field: the hypotheses of `LdReqRefLayD LayGl ..`
(Cb/Ld/LdLayD.lean) on its masks. -/
structure ReqRefGlU {Kc : Type} (pp : ℕ) (R : LdORE F E Kc)
    (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
    (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
    (L : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
    (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
    (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) : Prop where
  duty   : LdModelDuty R L T
  std    : IsStdGl first ∧ ProtoGlL pp L ∧ ProtoGlA T.A pp
  deg    : 2 ≤ R.n
  ev     : R.Z.OK
  tie    : R.Tie
  own    : R.X.Own
  layD   : LdReqRefLayD LayGl pp R first b L T
  fmt    : ∃ (px' : first.Wp' → R.Cf.conf.PIdx)
        (φb : JFmt Kc R.Cf.conf.E0 R.Cf.conf.Rec R.Cf.conf.PIdx b.J),
      (∀ w, px' (first.D.rest w).2 = w.2.1) ∧
      L.FmtP (first.tgt.fmt (⟨id, id⟩ : IxAt R.Cf.conf.E0 R.Cf.conf.E0) Prod.snd px'
          ((LdStage.start E Kc (R.O.jReq core)).S.qSum first.N qφ first.t)) φb ∧
      T.FmtAt φb q
  bFirst : (ldSendFamErr first.N first.Sd first.L : ℝ≥0∞) ≤ κ * (Fintype.card first.Sd.D : ℝ≥0∞)
  bSegs  : L.Nums κ
  bTail  : T.A.Nums κ
  bLast  : Err.Below (R.X.bt.nums R.Cf.conf.E0 Kc).err κ

/-- The object at the reference request, at this field. -/
structure Final (X : LdFinJ F E) [∀ b, Fintype (X.Z.Zw.K.wfI X.Z.Zw.Rl b → E)] {Fp : Type}
    [Field Fp] [Fintype Fp] [Algebra Fp E] (V : X.Z.Zw.StdW Fp) (p₀ : LdLinPl X.R.O.d.ol.toC)
    (plR : X.R.Bn → X.R.S.Ent → Prop) (a k msg r e mca : ℕ) : Prop where
  /-- which terms stand in the object -/
  wfIs    : (⟨X.Z.R.W, X.Z.R.Bw⟩ : Σ W : LdOWf F E, W.P.Blk) = ⟨X.Z.Zw.W, X.Z.Zw.G.B⟩
  sndIs   : X.Z.R.toLdObjD = X.Z.R.toLdObjD.std X.Z.Y
  reqIs   : X.Z.R.toLdObjD.pack = ldRefPack X.R X.core X.first X.first.tgt (.nil X.first.tgt) (LdProg.all_nilK _ _) X.c X.Ls X.T X.qφ X.q
  onIs    : X.Z.R.onPack = ldRefOn X.R p₀
  /-- the code of the encoded index: within a third -/
  code    : X.Z.Zw.W.Cf.C₀ = rs a k msg r e mca
  ha      : a ≤ 32
  hk      : k < 2 ^ a
  hp      : msg + r ≤ k + 1
  h3      : 3 * X.Z.Zw.W.Cf.eM < 2 ^ a - k
  smp     : X.Z.Zw.W.Cf.Z.OKOn (Ood.PadInF F)
  model   : X.Z.Zw.W.Cf.ModelOK
  /-- weights-formedness, its sender the standard one -/
  wfStd   : (⟨X.Z.Zw.D, X.Z.Zw.X⟩ : Σ D, X.Z.Zw.K.MaskPl D X.Z.Zw.Rl) = ⟨X.Z.Zw.W.P.stdD V.Y V.dat V.w0, X.Z.Zw.K.stdX X.Z.Zw.Rl V.Y V.dat V.w0 V.nAt V.RdW V.atL V.pl V.hpl⟩
  wfBody  : ∀ m, X.Z.Zw.W.P.body m = V.bd (V.Y.dataOf m)
  wfBd    : ∀ b, V.bd (V.dat b) = b
  wfAtL   : ∀ l i, V.nAt (V.atL l i) = V.Y.entF (V.pl (some l) i)
  wfAtB   : ∀ i, V.nAt (X.Z.Zw.W.P.wAt i) = V.Y.entF (V.pl none i)
  wfNoPad : ∀ n, V.RdW n → V.Y.NoPad n
  wfRest2 : X.Z.Zw.Rest2 p
  wfM     : MsgsGl X.Z.Zw.W.P.S V.Y X.Z.Zw.L X.Z.Zw.t X.Z.dS
  /-- the offline test's three sendings -/
  plS     : X.Z.Y.TS.Places
  fW      : X.Z.R.W.O.toC.P.SdW.Fair
  fU      : X.Z.R.W.O.toC.P.SdU.Fair
  fO      : X.Z.R.W.O.toC.P.SdO.Fair
  sW      : MsgsGl X.Z.R.W.O.toC.P.NW X.Z.Y.TS.YW X.Z.Y.LW X.Z.Y.tW X.Z.dW
  sU      : MsgsGl X.Z.R.W.O.toC.P.NU X.Z.Y.TS.YU X.Z.Y.LU X.Z.Y.tU X.Z.dU
  sO      : MsgsGl X.Z.R.W.O.toC.P.NO X.Z.Y.TS.YO X.Z.Y.LO X.Z.Y.tO X.Z.dO
  /-- the link's sending -/
  rdK     : X.Z.Y.YK.Reads X.Z.Y.ixK fun m => Sum.elim (X.Z.R.K.P.uv₀ m) (X.Z.R.K.P.uv₁ m)
  fK      : X.Z.Y.SdK.Fair
  sK      : MsgsGl X.Z.R.K.P.N X.Z.Y.YK X.Z.Y.LK X.Z.Y.tK X.Z.dN
  /-- the batch test's three sendings -/
  plB     : X.Z.Y.TB.Places
  fWB     : X.Z.R.on.ol.toC.P.SdW.Fair
  fUB     : X.Z.R.on.ol.toC.P.SdU.Fair
  fOB     : X.Z.R.on.ol.toC.P.SdO.Fair
  sWB     : MsgsGl X.Z.R.on.ol.toC.P.NW X.Z.Y.TB.YW X.Z.Y.LWB X.Z.Y.tWB X.Z.dWB
  sUB     : MsgsGl X.Z.R.on.ol.toC.P.NU X.Z.Y.TB.YU X.Z.Y.LUB X.Z.Y.tUB X.Z.dUB
  sOB     : MsgsGl X.Z.R.on.ol.toC.P.NO X.Z.Y.TB.YO X.Z.Y.LOB X.Z.Y.tOB X.Z.dOB
  /-- the index's folds -/
  own₀    : X.Z.R.toLdObjD.Own3₀
  /-- the request -/
  req     : ReqRefGlU p X.R X.core X.first X.c X.Ls X.T X.qφ X.q X.κ
  places  : X.R.PlacesOK p₀ plR
  pl₁     : X.Z.R.HypPl₁
  /-- the link's test and the offline test's three: within a third -/
  tK      : RunGlAt X.Z.R.Kc.run X.Z.twK X.Z.dK
  t₁      : RunGlAt X.Z.R.TP₀.D₁ X.Z.tw₁ X.Z.d₁
  t₂      : RunGlAt X.Z.R.TP₀.D₂ X.Z.tw₂ X.Z.d₂
  t₃      : RunGlAt X.Z.R.X.run X.Z.tw₃ X.Z.d₃
  /-- the session's three tests: below the Johnson radius -/
  t₁B     : RunGlJAt X.Z.R.TB₀.D₁ X.Z.tw₁B X.Z.d₁B
  t₂B     : RunGlJAt X.Z.R.TB₀.D₂ X.Z.tw₂B X.Z.d₂B
  t₃B     : RunGlJAt X.Z.R.XB.run X.Z.tw₃B X.Z.d₃B

namespace Spec

def glFinal_req : Prop :=
  Cb.BCHKS46F F →
  ∀ (Kc : Type) (pp : ℕ) (R : LdORE F E Kc) (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
      (L : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞),
    ReqRefGlU pp R core first b L T qφ q κ → LdReqRefDJU LayGl pp R core first b L T qφ q κ

/-- The generic record, at this field, under the statement on codes (`Cb.BCHKS46F`) (not all
hypotheses are named here: see the statement below). -/
def glFinal_hyp : Prop :=
  Cb.BCHKS46F F →
  ∀ (X : LdFinJ F E) [∀ b, Fintype (X.Z.Zw.K.wfI X.Z.Zw.Rl b → E)] (Fp : Type) [Field Fp]
      [Fintype Fp] [Algebra Fp E] (V : X.Z.Zw.StdW Fp) (p₀ : LdLinPl X.R.O.d.ol.toC)
      (plR : X.R.Bn → X.R.S.Ent → Prop) (a k msg r e mca : ℕ),
    Final X V p₀ plR a k msg r e mca →
    X.Z.HypRefJU LayGl p X.R X.core X.first X.c X.Ls X.T X.qφ X.q X.κ V p₀ plR

/-- How a guard can meet the record. -/
def glFinal_of : Prop :=
  ∀ (X : LdFinJ F E) [∀ b, Fintype (X.Z.Zw.K.wfI X.Z.Zw.Rl b → E)] (Fp : Type) [Field Fp]
      [Fintype Fp] [Algebra Fp E] (V : X.Z.Zw.StdW Fp) (p₀ : LdLinPl X.R.O.d.ol.toC)
      (plR : X.R.Bn → X.R.S.Ent → Prop) (a k msg r e mca : ℕ),
    FinJ X V p₀ plR a k msg r e mca →
    LdReqRefLayD LayGl p X.R X.first X.c X.Ls X.T → Final X V p₀ plR a k msg r e mca

end Spec

theorem glFinal_req : Spec.glFinal_req := fun H Kc pp _ _ _ _ L T _ _ _ h =>
  { duty := h.duty,
    std := ⟨glReqJohn_send Kc _ _ h.std.1,
        glReqJohn_list H Kc _ _ _ L pp h.std.2.1,
        glReqJohn_body Kc _ T.A pp h.std.2.2⟩,
    deg := h.deg, ev := h.ev, tie := h.tie, own := h.own, layD := h.layD, fmt := h.fmt
    bFirst := h.bFirst, bSegs := h.bSegs, bTail := h.bTail, bLast := h.bLast }

theorem glFinal_of : Spec.glFinal_of := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h hl =>
  { wfIs := h.wfIs, sndIs := h.sndIs, reqIs := h.reqIs, onIs := h.onIs, code := h.code, ha := h.ha, hk := h.hk, hp := h.hp, h3 := h.h3, smp := h.smp, model := h.model, wfStd := h.wfStd, wfBody := h.wfBody, wfBd := h.wfBd, wfAtL := h.wfAtL, wfAtB := h.wfAtB, wfNoPad := h.wfNoPad, wfRest2 := h.wfRest2, wfM := h.wfM, plS := h.plS, fW := h.fW, fU := h.fU, fO := h.fO, sW := h.sW, sU := h.sU, sO := h.sO, rdK := h.rdK, fK := h.fK, sK := h.sK, plB := h.plB, fWB := h.fWB, fUB := h.fUB, fOB := h.fOB, sWB := h.sWB, sUB := h.sUB, sOB := h.sOB, own₀ := h.own₀, places := h.places, pl₁ := h.pl₁, tK := h.tK, t₁ := h.t₁, t₂ := h.t₂, t₃ := h.t₃, t₁B := h.t₁B, t₂B := h.t₂B, t₃B := h.t₃B
    req := { duty := h.req.duty, std := h.req.std, deg := h.req.deg, ev := h.req.ev, tie := h.req.tie, own := h.req.own, layD := hl, fmt := h.req.fmt, bFirst := h.req.bFirst, bSegs := h.req.bSegs, bTail := h.req.bTail, bLast := h.req.bLast } }

theorem glFinal_hyp : Spec.glFinal_hyp := fun H X _ Fp _ _ _ _ _ _ a k msg r e mca h =>
  { wfIs := h.wfIs
    sndIs := h.sndIs
    reqIs := h.reqIs
    onIs := h.onIs
    wfJ :=
      { isStd := h.wfStd, ok := (glReqJohn_msgs Fp _ _ _ _ _ h.wfM).1, body := h.wfBody,
        bdDat := h.wfBd, plL := h.wfAtL, plB := h.wfAtB, noPad := h.wfNoPad, rest2 := h.wfRest2
        conf3 := gl3_conf X.Z.Zw.W.Cf a k msg r e mca h.code h.ha h.hk h.hp h.h3 h.smp h.model
        near := (glReqJohn_msgs Fp _ _ _ _ _ h.wfM).2 }
    sOff :=
      { places := h.plS, okW := (glReqJohn_msgs _ _ _ _ _ _ h.sW).1,
        okU := (glReqJohn_msgs _ _ _ _ _ _ h.sU).1, okO := (glReqJohn_msgs _ _ _ _ _ _ h.sO).1,
        fairW := h.fW, fairU := h.fU, fairO := h.fO
        nearW := (glReqJohn_msgs _ _ _ _ _ _ h.sW).2,
          nearU := (glReqJohn_msgs _ _ _ _ _ _ h.sU).2,
          nearO := (glReqJohn_msgs _ _ _ _ _ _ h.sO).2 }
    sLink := { ok := (glReqJohn_msgs _ _ _ _ _ _ h.sK).1, reads := h.rdK, fair := h.fK,
               near := (glReqJohn_msgs _ _ _ _ _ _ h.sK).2 }
    sOn :=
      { places := h.plB, okW := (glReqJohn_msgs _ _ _ _ _ _ h.sWB).1,
        okU := (glReqJohn_msgs _ _ _ _ _ _ h.sUB).1, okO := (glReqJohn_msgs _ _ _ _ _ _ h.sOB).1,
        fairW := h.fWB, fairU := h.fUB, fairO := h.fOB
        nearW := (glReqJohn_msgs _ _ _ _ _ _ h.sWB).2,
          nearU := (glReqJohn_msgs _ _ _ _ _ _ h.sUB).2,
          nearO := (glReqJohn_msgs _ _ _ _ _ _ h.sOB).2 }
    own₀ := h.own₀
    req := glFinal_req H X.Kc p X.R X.core X.first X.c X.Ls X.T X.qφ X.q X.κ h.req
    places := h.places
    pl₁ := h.pl₁
    pK := gl3_runAt _ _ _ h.tK
    p₁ := gl3_runAt _ _ _ h.t₁
    p₂ := gl3_runAt _ _ _ h.t₂
    p₃ := gl3_runAt _ _ _ h.t₃
    p₁B := glJ_runAt H _ _ _ h.t₁B
    p₂B := glJ_runAt H _ _ _ h.t₂B
    p₃B := glJ_runAt H _ _ _ h.t₃B }

end Cb.Gl
