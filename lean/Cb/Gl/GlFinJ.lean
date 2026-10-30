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
Cb/Gen/CodeListRS.lean.) Cb/Gl/GlFinJ.lean: the conditions over p = 2^64 - 2^32 + 1 (on codes,
radii, maps of coefficients, and those listed under Limits, the model's duty among them), as one
structure that has no hypothesis on the size of a list and none on mutual correlated agreement; the
generic hypotheses on the protocol object follow from it under the hypothesis `Cb.BCHKS46F F` on
mutual correlated agreement.

Exactly: the object at the reference request over p with plain Reed-Solomon codes: the offline phase
and the link (their tests on groups; the index's code) within a third of the distances, all groups
of a session below the Johnson radius: one record of conditions in which no bound on a list, no
agreement, no bound on a fold's bad points and no clause "two members of one list agree at few
seeds" is asked; under the one hypothesis BCHKS46F F, by name, it gives the generic record
Z.HypRefJ.

Definitions and statements (`Cb.Gl.Spec.glFinJ_req`, `Cb.Gl.Spec.glFinJ_hyp`); the proofs, an
assembly, are in Cb/Gl/GlFinJProofs.lean.
Cb/Obj/LdObjectDataRefJ.lean (Z.HypRefJ) still asks, of codes: laws, distances, what encodings
hide (inside Y.OK t), the configuration within a third, "the sample is a zero-evader" beyond unique
decoding, and agreement (`MCArows`, `MCAat`) in the batch test's three towers and in each closing of
the request. Here, with F the integers modulo p and E = F[x] / (x^3 - 2): the encoded index under rs
a k msg r (Cb/Gl/GlCodes.lean); every other code `GlC` / `GlJ` (Cb/Gl/GlLd.lean, Cb/Gl/GlLdJ.lean:
built from families of plain Reed-Solomon codes on subgroups of orders at most 2^32).

Main names:
  `ReqRefGl pp R core first b L T qφ q κ`: the request's record `LdReqRefDJ`
    (Cb/Req1/LdReqJohn.lean) with std : IsStdGl first ∧ ProtoGlL pp L ∧ ProtoGlA T.A pp
    (Cb/GlVal/GlReqJohn.lean); all other clauses as they stand there (the model's duty; degree,
    evader and tie of the final batching; own; lay, layT, layB; formats; numbers).
  `FinJ X V p₀ plR a k msg r e mca`: X : LdFinJ F E (Cb/Obj/LdObjectDataRefJFin.lean), V the data of
    the standard sender of weights-formedness, p₀, plR the plan's places:
    code .. model: msg + r ≤ k + 1 (a write-up of ours (lean/CREDITS.md) has equality:
    wider here, and within a third nothing hangs on it; by a reading); the configuration's sample
    map (a zero-evader on vectors with pads in F);
    the model of the configuration;
    wfStd .. wfRest2, wfM: weights-formedness: sender and mask places are the standard ones (an
    equation); five clauses on places and on the data map; Zw.Rest2 p (its fields:
    Cb/Ld/LdWfEnd.lean); `MsgsGl` of its family;
    own₀: D.Own3₀ (Cb/Obj/LdObjectDataRefJ.lean): radii and numbers of the index's folds,
    equations;
    places, pl₁: as in Z.HypRefJ;
    t₁B, t₂B, t₃B: `RunGlJAt` (Cb/Gl/GlObjMix.lean): the batch test's three, below the Johnson
    radius; the counts for agreement stand in the towers as data, bounded from below through `GlJ`
    (Cb/Gl/GlLdJ.lean, Cb/Gl/GlCopy.lean).
  `Spec.glFinJ_req`: BCHKS46F F → ReqRefGl .. → LdReqRefDJ ..
  `Spec.glFinJ_hyp`: BCHKS46F F → FinJ X V p₀ plR a k msg r e mca → X.Z.HypRefJ p X.R X.core X.first
    X.c X.Ls X.T X.qφ X.q X.κ V p₀ plR.

Where BCHKS46F F enters: T.John of the batch test's three towers, and the agreement of the three
codes of each closing of the request. Nowhere else: offline phase, link and all sendings use
nothing. It is a hypothesis by name, no axiom; its source gives an outline of a proof; nobody of us
has checked a proof.

Limits: what is still asked and is not "families and numbers":
  (1) The model's duty (req.duty), and the model of the configuration (model : `ModelOK`,
      Cb/Obj/LdObjectConfMore.lean).
  (2) Zero knowledge of the request: lay, layT, layB, as they stand in `LdReqRefDS`.
  (3) That each public map of coefficients is a zero-evader with its stated error (no code, no
      list): `Evader.OK` of every bridge, batching and switch; `Sample.OK` of each switch's sample;
      the configuration's sample map. These forms have a theorem in this library: equality weights
      (`Cb.ok_eqPt`, `ok_eqNum`), independent coefficients (`ok_indep`), powers (`ok_powers`), the
      line (`ldBat_ok_line`), the one coefficient (`ldZero_ok_one`), Lagrange weights
      (`ldZero_ok_lag`). Whether these are all the forms that stand at these places has not been
      examined.
  (4) Clauses that speak of the codes' words, though of no list and no agreement: Fits of each
      group, the held messages' laws, the laws of each shape's view.
  (5) Equations, places, formats, seeds, the numbers' clauses (idle at κ = ⊤), the other fields of
      Zw.Rest2 p (Cb/Ld/LdWfEnd.lean).
  (6) Asked as they stand too: in each format, Y.Fmt.zk (Cb/Gl/GlSenders.lean); at each switch of a
      tower: `Sample.PrivateSim` of the switch's sample.
Mask rows: both forms are admitted (the constructor `copy` of `GlC` and of `GlJ`): native rows
(short words read by repetition: a reading with a multiplicity) and copied rows (long words in which
nothing forces the copies to agree; the code is then the repetition of the mask code, a subcode of a
longer Reed-Solomon code, and its agreement costs the assumed count at the long length and one list
more: Cb/Gl/GlCopy.lean, Cb/Gl/GlCopyJ.lean). Which form a row has is the data's choice. The
write-up's rule for a group that mixes the two forms of rows is "the repetition stands for all
its mask rows"; here each member has its own count: by reading, at most the write-up's
number.
Copied rows inside an object: not at a guard of this record.

(In a segment's closing at the reference parameters no agreement of a mask
code is used: one mask row, no mask variable is folded.)
The hypothesis is wider than the write-up's restatement of the assumed theorem: Cb.BCHKS46F
Gl.F speaks of all finite extensions of the base field, the write-up of E alone (points in
the base field in both). It follows from the source's theorem, which is stated for every finite
field. The extensions are used in one step only, that rows cost nothing (`Cb.rows_cost_nothingF`);
the write-up has that step by a lemma on every E-linear code, which this file does not have;
the library has its core as `Cb.Spec.rows_free_abs` (Cb/Ld/LdRelRowsEAbs.lean).
Declared difference: at a radius not below half the distance every oracle message is over E, with
one pad entry of E for each answer (the clause on the sample asks a zero-evader on all vectors over
E), and so are all messages of the same sending: the pads' field is one for a sending of the
request, one for the seven sendings of the two tests and the link (so with a session's sending not
below half the distance all seven have their pads in E; the write-up's messages of the
linear test and of the link are over E: no difference there), one for weights-formedness. In the
write-up most rows of a segment (packed cells, digits, re-encoded kept messages) are over
the base field, with as many pad entries of the base field for an answer as E has dimension; there
the sample is a zero-evader on vectors over the base field only, and the members of a list are over
the base field. Why not otherwise: in the standard sender's layout the data and the free entries of
a message are elements of E by type, and any such vector can stand in the message; so a format over
a proper subfield can be met only by a member that holds pad entries alone (proved, under the
hypotheses of its statement: Cb/Req1/LdReqJohnSubNo.lean: Cb.ld_subfield_noData). (The theorem holds
at every radius below the distance: all messages of the standard senders are words over E, offline
too; only the pads may lie in a subfield, within unique decoding.) The lemma on lists itself (a
member of the list of a word over a subfield is over the subfield) stands, generic, beside:
Cb/Req1/LdReqJohnSub.lean; nothing above but that theorem's proof uses it.
Sendings offline and at the link may stand below the Johnson radius too (`MsgsGl` has both cases):
lists are proved there, so nothing is assumed by that; the write-up has them at 2 e below the
distance.
This file does not say that `FinJ` can be met: no instance in this file.
It does not say that the counts are small against the field: the assumed count is at least 350 times
the length.
Whether the source proves what it states: that is not said either.

The plan of the linear test is the one without a splitting.
No bound is evaluated.

Terms: lean/GLOSSARY.md: agreement, below the Johnson radius, bridge, closing, code switch,
configuration, encoded index, evader, final batching, fold, group, guard, held, layout, link, list,
not below half the distance, object, offline test, oracle message, plan,
record, reference request, sample, segment, sending, session, standard sender, the model's duty,
tower, unique decoding, weights-formedness.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.GlVal.GlReqJohn
import Cb.Obj.LdObjectDataRefJFin
import Cb.Gl.GlObjMix

set_option autoImplicit false

namespace Cb.Gl
open Code Prob Blocks Iop Hiop IOR IOR.Chain Cb.Ood
open scoped ENNReal

/-- The record of the reference request, at this field. -/
structure ReqRefGl {Kc : Type} (pp : ℕ) (R : LdORE F E Kc)
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
  lay    : L.LayJ pp (ldReqRef1 R first b L T).base₀
  layT   : T.A.ZkAt pp (fun f =>
    ∃ g,
      L.LaidJ (ldReqRef1 R first b L T).base₀ g ∧
      ∀ Y : MaskFact b.J.W → Prop, Y g → T.entry.After Y f)
  layB   : ∃ (Rd : R.S.Ent → Prop) (Rr : R.S.O → Prop),
    (∀ n, R.Rd n → Rd n) ∧
    ∃ g,
      L.LaidJ (ldReqRef1 R first b L T).base₀ g ∧
      ∀ Y : MaskFact b.J.W → Prop, Y g →
        T.tail.After Y
          (R.X.src.wideFact Rd Rr (R.X.atOwn R.X.wAt) R.X.mask.Mk fun M => R.X.atVal R.X.wAt M)
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

/-- The object at the reference request, at this field: the conditions. -/
structure FinJ (X : LdFinJ F E) [∀ b, Fintype (X.Z.Zw.K.wfI X.Z.Zw.Rl b → E)] {Fp : Type} [Field Fp]
    [Fintype Fp] [Algebra Fp E] (V : X.Z.Zw.StdW Fp) (p₀ : LdLinPl X.R.O.d.ol.toC)
    (plR : X.R.Bn → X.R.S.Ent → Prop) (a k msg r e mca : ℕ) : Prop where
  /-- which terms stand in the object -/
  wfIs    : (⟨X.Z.R.W, X.Z.R.Bw⟩ : Σ W : LdOWf F E, W.P.Blk) = ⟨X.Z.Zw.W, X.Z.Zw.G.B⟩
  sndIs   : X.Z.R.toLdObjD = X.Z.R.toLdObjD.std X.Z.Y
  reqIs   : X.Z.R.toLdObjD.pack =
    ldRefPack X.R X.core X.first X.first.tgt (.nil X.first.tgt)
      (LdProg.all_nilK _ _) X.c X.Ls X.T X.qφ X.q
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
  wfStd   : (⟨X.Z.Zw.D, X.Z.Zw.X⟩ : Σ D, X.Z.Zw.K.MaskPl D X.Z.Zw.Rl) =
    ⟨X.Z.Zw.W.P.stdD V.Y V.dat V.w0,
      X.Z.Zw.K.stdX X.Z.Zw.Rl V.Y V.dat V.w0 V.nAt V.RdW V.atL V.pl V.hpl⟩
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
  req     : ReqRefGl p X.R X.core X.first X.c X.Ls X.T X.qφ X.q X.κ
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

def glFinJ_req : Prop :=
  Cb.BCHKS46F F →
  ∀ (Kc : Type) (pp : ℕ) (R : LdORE F E Kc) (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
      (L : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞),
    ReqRefGl pp R core first b L T qφ q κ → LdReqRefDJ pp R core first b L T qφ q κ

/-- The generic record, at this field, under the statement on codes (`Cb.BCHKS46F`).
(not all hypotheses are named here: see the statement below) -/
def glFinJ_hyp : Prop :=
  Cb.BCHKS46F F →
  ∀ (X : LdFinJ F E) [∀ b, Fintype (X.Z.Zw.K.wfI X.Z.Zw.Rl b → E)] (Fp : Type) [Field Fp]
      [Fintype Fp] [Algebra Fp E] (V : X.Z.Zw.StdW Fp) (p₀ : LdLinPl X.R.O.d.ol.toC)
      (plR : X.R.Bn → X.R.S.Ent → Prop) (a k msg r e mca : ℕ),
    FinJ X V p₀ plR a k msg r e mca →
    X.Z.HypRefJ p X.R X.core X.first X.c X.Ls X.T X.qφ X.q X.κ V p₀ plR

end Spec
end Cb.Gl
