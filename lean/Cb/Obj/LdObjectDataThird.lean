-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectDataThird.lean: book-keeping for the hypotheses of a holographic IOP: the object with
the hypotheses of `Z.Hyp p`, among them properties of the request's program and of the sender `Zw.D`
of weights-formedness, all radii within a third of the distances (of some the records ask less:
"Limits"): no hypothesis on a list or on agreement is left, but inside the request's program and in
the senders' clauses "evades".

Its main statement is an implication between two records of hypotheses: `Cb.Spec.ldObjZ3_hyp`:
`Z.Hyp p` ⇒ `Z.toZ.Hyp p 1`.
Definitions, statements and proofs: an assembly.
The object, "on data" and the request's program: the head of Cb/Obj/LdObjectData.lean.
A radius e is within a third of a distance d if 3 e < d (`LdCf.Third.lt`,
Cb/Obj/LdObjectThirdTests.lean).
A bound on lists says that every word has at most L codewords within the radius e (`ListAt`,
Cb/Ld/LdRel.lean; for the messages of an oracle message: `OMsg.ListLE`, Cb/Ld/LdSig.lean).
Agreement is mutual correlated agreement, as a count of exceptional coefficients (`MCAat`,
Cb/Ld/LdRel.lean; `MCArows`, Cb/Ld/LdRelRows.lean).
A regime is the side condition on the encoded index at a fold: "no collision" (`K.free`) or "it
decodes with its record" (`K.dec0`, `onDec`).
Cb/Obj/LdObjectData.lean's `Z.Hyp p L` asks bounds on lists and on agreement: the list of the index
code (in `Cf.OK`), the bounds on the bad points of the three kinds of folds of the index, the list
of each test's complex, those inside each tower, the lists of the oracle messages sent.
Some of them are proved beyond a third of the distance. Of the lists: at 2 e below the distance in
this file (by `ldT3_list`, Cb/Obj/LdObjectThirdTestsProofs.lean, and `ldThird_bridge`,
Cb/Ld/LdTowerThird.lean); the index code's in Cb/Obj/LdObjectConfMore.lean: `ldCm_list_unique`,
`ldCm_list_johnson`, under their hypotheses; of any code with the laws below the Johnson radius
(`ld_list_johnson`: stated in Cb/Ld/LdRelJohnson.lean, proved in Cb/Ld/LdRelJohnsonProofs.lean). Of
the folds' bounds: those by the regime "it decodes with its record", at e + eM below the distance
(`Par3`, `e'far`; by `ldLk_foldErr`, Cb/Ld/LdLinkProofs.lean, at the link's first index alone, and
`ldOB_foldErr`, Cb/Obj/LdObjectLinB.lean). On agreement: a weak bound, no proximity gap
(Cb/Ld/LdRelAny.lean: `ld_mca_sets`, from the laws), and within half the distance a bound
(`agreeHalf`, Cb/Gl/GlAgreeHalf.lean) for the Reed-Solomon families of `IsGlJ` (Cb/Gl/GlLdJ.lean).
For the folds' bounds by the regime "no collision", and for agreement inside the towers, this file
uses no proof beyond a third: `ldCm_mca_third` (Cb/Obj/LdObjectConfMore.lean) and `T.Third`
(Cb/Obj/LdObjectTowerThird.lean) ask 3 e below the distance.
Within a third all the bounds named follow from laws and distances: lists of one member, agreement e
+ 1.

Main names:
  `LdObjZ3 F E`: data only, but for the proofs inside its fields' types (among them `LdObjD.ne`,
    `LdCf.hp`, `LdLinPl.hU` .., `LdLinPlT.hc₁`, `hc₂`, `LdLkP.Cl.all`): `R : LdObjR`; `Zw`; `Y`;
    seven towers without numbers for lists and agreement (`D.Tow3`, an `LdTowG3`); distances (its
    fields: see the record).
  `T.Third3 ..`, `P.StdThird ..`: what the standard senders ask, without lists: in their place a
    distance with 2 e below it, and "the bound is 1"; "evades" stays (`evW`, `evU`, `evO`; `ev`).
  `D.Own3`: `D.HypOwn` without the three bounds on bad points of folds and without `fitsK`, `fitsB`:
    in their place conditions on radii, regimes and numbers (these fields, under three of the
    record's four labels: see the record; the link's first index: `D.Par3`: its docstring). And
    without `EndOK`: in its place `D.EndStd`.
  `Z.Hyp p` (its fields: see the record).

Notation: `p`: a natural number (`Spec.ldObjZ_hyp`, Cb/Obj/LdObjectData.lean, asks `CharP E p`); the
`1` in `Z.toZ.Hyp p 1`: the argument `L` of `LdObjZ.Hyp`: a natural number (`LdCf.OK L`,
Cb/Obj/LdObjectConf.lean, says that it bounds the lists at the radius of decoding); `eM`: a natural
number (`LdCf.eM`, Cb/Obj/LdObjectConf.lean; as `LdIx.eM` of `Cf.X`, Cb/Ld/LdFoldEq.lean: the radius
of decoding, in columns); `e'`: a natural number (the radius at which the fold is tested: the field
`e'` of `LdOL`, Cb/Obj/LdObjectLin.lean, here `D.W.O.e'`, `D.on.ol.e'`); `e₀`: a natural number (the
radius at the link's first index, the parent's: `D.K.e₀`); `e₁`: a natural number (the radius of the
link's further index: `D.K.e₁`); `Cf.εThird e`: the error of a fold of the index at the radius e,
within a third (Cb/Obj/LdObjectThirdTests.lean).

Limits: what is left that speaks of lists or agreement is only what stands inside `r.Hyp` (the
request's program is a parameter), and the clauses `evW`, `evU`, `evO` of `Third3` and `ev` of
`StdThird` (`OMsg.Evades`, Cb/Ld/LdSig.lean: two different messages of one list have the same
answers at no more than `o.Z.err` seeds (`o` the oracle message, `o.Z` its sample map)).
Six clauses on the sender `Zw.D` of weights-formedness are not on data: it is a free value with laws
(Cb/Ld/LdWfEnd.lean: `Rest0`, `Rest1`).
That `Z.Hyp p` can be met is not shown in this file. No instance that meets the hypotheses of
`ldObjZ3_hyp` is part of this library; as far as the library shows, this theorem may hold of
nothing.
This file says nothing beyond a third, but where a clause asks less: 2 e below the distance
(`Third3`, `StdThird`, `Pre3`), e + eM below it (`Par3`, `e'far`).
Declared, on the safe side: offline and at the link the numbers keep a second summand ("one member
of the list") that this protocol's technical report does not have where the record has no answers.
No difference:
for 2 eM below the distance the technical report takes the link's first index by the regime here
"it decodes with its record" (no bad point, a larger radius, fewer locations): `D.Par3`'s second
case admits it. The tight forms are in Cb/Obj/LdObjectThirdNil.lean, Cb/Obj/LdObjectLinkAt.lean,
Cb/Obj/LdObjectThirdEnd.lean.
`Z.Hyp p` is a point of the parameter space chosen for "no hypothesis on a list or on agreement"
(but inside the request's program and in the senders' clauses "evades"), not the reference:
in a note of ours that is not in this repository the groups of a session stand at a larger radius,
under an assumed theorem on lists and agreement; the files made once may stand within a third.
In Cb/Obj/LdObjectDataMix.lean and Cb/Obj/LdObjectDataRefJ.lean the groups of a session may stand at
a larger radius, and there agreement is a hypothesis ("Limits" in their heads say what else is
left).
Online the request is not built: its program r is a parameter, and its "conditions" are the security
properties (found by reading). Its moves: `LdMv`, Cb/Req1/LdSeg.lean; what each asks: `LdMv.Hyp`. At
a move `sub a b c`, `r.Hyp` is `c.AllB` for any chain c: completeness and round-by-round knowledge
soundness, link by link, are assumed of a parameter. At a move `fold D l` it asks of any link l the
whole bundle `GoodT`, honest-verifier zero knowledge included: that l is the proximity test that
closes each segment. A move `step` asks `StepT` (its clauses `acc`, `know`: the arithmetization).
For every first sending d and every chain c to the last stage there is a request with r.Hyp ↔ d.Hyp
∧ c.AllB. So "an accepted proof implies `Rno`" (the model's relaxed relation, Hiop/RecConf.lean) is,
online, assumed at the level of the oracle reduction: that the claim on the instance x is about the
extracted index is not derived from data.



In Lean the reference request is a term (Cb/Req1/LdReqRef*.lean,
Cb/Obj/LdObjectDataRef.lean). Among what is asked as a property of terms
there: each closing's fold link, senders, entry and exit steps, the model's side, where the masks
come from. No theorem of this library states that the hypotheses of `ldReqRefFinal`
(Cb/Req1/LdReqRefFinal.lean) can be met together.


On `rZk`. What honest-verifier zero knowledge asks of the request's program is `r.ZkS`
(Cb/Req1/LdReqS.lean), beside
its hypotheses (`r.Hyp`): `r.Zk` with the set of fresh facts closed, at each segment's entry and
before the last part, under join at one reading, a coarser reading, another type for the same masks.
`r.Zk` gives `r.ZkS` (`ldReqS_of_zk`). Why: in a write-up of ours (lean/CREDITS.md) a later
segment's sumcheck that ends at a map of the index has own masks from two sendings; by our reading
`r.Zk` cannot be met by that layout.
Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Obj.LdObjectData
import Cb.Obj.LdObjectThirdTestsProofs
import Cb.Ld.LdWfEndThird
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- a tower within a third, as a concrete tower on the test's complex -/
def LdRunD.up3
    {E : Type} [Field E] [Fintype E] {S : Sig E} (D : LdRunD S) (T : D.Tow3) : D.Tow := T.toG

/-- from a test within a third to the test with its tower -/
theorem LdRunD.Pre3.pre {E : Type} [Field E] [Fintype E] {S : Sig E} {D : LdRunD S} {T : D.Tow3}
    {d : ℕ} (h : D.Pre3 T d) : D.Pre (D.up3 T) :=
  ⟨h.isT, h.isQ, h.ev, by rw [h.isL]; exact ldThird_bridge E S D.G d h.laws h.dist h.half,
    h.fits, ldTowG3_hyp T h.tow⟩

/-- What the three standard senders of a test ask, without lists. ("evades" stays) -/
structure LdLinP.Std.Third3 {F E ι κ J Y : Type} [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] {P : LdLinP E ι κ J Y} (T : P.Std F) (LW : P.NW.O → ℕ) (LU : P.NU.O → ℕ)
    (LO : P.NO.O → ℕ) (tW : P.NW.O → ℕ) (tU : P.NU.O → ℕ) (tO : P.NO.O → ℕ) (dW : P.NW.O → ℕ)
    (dU : P.NU.O → ℕ) (dO : P.NO.O → ℕ) : Prop where
  places : T.Places
  okW   : T.YW.OK tW
  okU   : T.YU.OK tU
  okO   : T.YO.OK tO
  lawsW : ∀ a, (P.NW.om a).C.Laws
  fairW : P.SdW.Fair
  distW : ∀ a, (P.NW.om a).C.Dist (dW a)
  ltW   : ∀ a, 2 * (P.NW.om a).e < dW a
  oneW  : ∀ a, LW a = 1
  evW   : ∀ a, (P.NW.om a).Evades
  lawsU : ∀ a, (P.NU.om a).C.Laws
  fairU : P.SdU.Fair
  distU : ∀ a, (P.NU.om a).C.Dist (dU a)
  ltU   : ∀ a, 2 * (P.NU.om a).e < dU a
  oneU  : ∀ a, LU a = 1
  evU   : ∀ a, (P.NU.om a).Evades
  lawsO : ∀ a, (P.NO.om a).C.Laws
  fairO : P.SdO.Fair
  distO : ∀ a, (P.NO.om a).C.Dist (dO a)
  ltO   : ∀ a, 2 * (P.NO.om a).e < dO a
  oneO  : ∀ a, LO a = 1
  evO   : ∀ a, (P.NO.om a).Evades

theorem LdLinP.Std.Third3.hyp {F E ι κ J Y : Type} [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] {P : LdLinP E ι κ J Y} {T : P.Std F} {LW : P.NW.O → ℕ} {LU : P.NU.O → ℕ}
    {LO : P.NO.O → ℕ} {tW : P.NW.O → ℕ} {tU : P.NU.O → ℕ} {tO : P.NO.O → ℕ} {dW : P.NW.O → ℕ}
    {dU : P.NU.O → ℕ} {dO : P.NO.O → ℕ} (h : T.Third3 LW LU LO tW tU tO dW dU dO) :
    T.Hyp LW LU LO tW tU tO :=
  { places := h.places, okW := h.okW, okU := h.okU, okO := h.okO
    lawsW := h.lawsW, fairW := h.fairW,
      listW := fun a => by
          rw [h.oneW a]; exact ldT3_list E _ (dW a) (h.lawsW a) (h.distW a) (h.ltW a), evW := h.evW
    lawsU := h.lawsU, fairU := h.fairU,
      listU := fun a => by
          rw [h.oneU a]; exact ldT3_list E _ (dU a) (h.lawsU a) (h.distU a) (h.ltU a), evU := h.evU
    lawsO := h.lawsO, fairO := h.fairO, listO := fun a => by rw [h.oneO a]; exact ldT3_list E _ (dO a) (h.lawsO a) (h.distO a) (h.ltO a), evO := h.evO }

/-- What the standard sender of the link asks, without lists. ("evades" stays) -/
structure LdLkP.StdThird {F E ι κ J Λ : Type} [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] (P : LdLkP E ι κ J Λ) (Sd : P.N.Seeds) (L t : P.N.O → ℕ) (Y : P.N.StdL F)
    (ix : ∀ a, Y.Dt a → Option (κ ⊕ κ)) (dN : P.N.O → ℕ) : Prop where
  ok    : Y.OK t
  reads : Y.Reads ix fun m => Sum.elim (P.uv₀ m) (P.uv₁ m)
  laws  : ∀ a, (P.N.om a).C.Laws
  fair  : Sd.Fair
  dist  : ∀ a, (P.N.om a).C.Dist (dN a)
  lt    : ∀ a, 2 * (P.N.om a).e < dN a
  one   : ∀ a, L a = 1
  ev    : ∀ a, (P.N.om a).Evades

theorem LdLkP.StdThird.hyp {F E ι κ J Λ : Type} [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] {P : LdLkP E ι κ J Λ} {Sd : P.N.Seeds} {L t : P.N.O → ℕ} {Y : P.N.StdL F}
    {ix : ∀ a, Y.Dt a → Option (κ ⊕ κ)} {dN : P.N.O → ℕ} (h : P.StdThird Sd L t Y ix dN) :
    P.StdHyp Sd L t Y ix :=
  ⟨h.ok, h.reads, h.laws, h.fair,
    fun a => by rw [h.one a]; exact ldT3_list E _ (dN a) (h.laws a) (h.dist a) (h.lt a), h.ev⟩

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The request's last base joint is one of the two standard ones. -/
def LdObjD.EndStd (T : LdObjD F E) : Prop :=
  (∃ core' : T.on.ol.S.Msg × T.W.Cf.conf.PIdx → T.Kr,
    (⟨T.Wz, T.piz, T.Bz⟩ : Σ (Wz : Type) (_ : Wz → T.W.Cf.conf.PIdx),
        Rels T.Kr (T.on.ol.Cl × T.W.Cf.conf.Rec) T.W.Cf.conf.E0 (T.on.ol.S.Msg × Wz)) =
      ⟨T.W.Cf.conf.PIdx, id, T.on.ol.bEnd core'⟩) ∨
  ∃ (G : Type) (core' : T.on.ol.S.Msg × (T.W.Cf.conf.PIdx × G) → T.Kr),
    (⟨T.Wz, T.piz, T.Bz⟩ : Σ (Wz : Type) (_ : Wz → T.W.Cf.conf.PIdx),
        Rels T.Kr (T.on.ol.Cl × T.W.Cf.conf.Rec) T.W.Cf.conf.E0 (T.on.ol.S.Msg × Wz)) =
      ⟨T.W.Cf.conf.PIdx × G, Prod.fst, T.on.ol.bEndG G core'⟩

theorem LdObjD.EndStd.ok {T : LdObjD F E} (h : T.EndStd) : T.on.ol.EndOK T.piz T.Bz := by
  have key : ∀ x : Σ (Wz : Type) (_ : Wz → T.W.Cf.conf.PIdx),
      Rels T.Kr (T.on.ol.Cl × T.W.Cf.conf.Rec) T.W.Cf.conf.E0 (T.on.ol.S.Msg × Wz),
    ((∃ core', x = ⟨T.W.Cf.conf.PIdx, id, T.on.ol.bEnd core'⟩) ∨
      ∃ (G : Type) (core' : T.on.ol.S.Msg × (T.W.Cf.conf.PIdx × G) → T.Kr),
        x = ⟨T.W.Cf.conf.PIdx × G, Prod.fst, T.on.ol.bEndG G core'⟩) →
      T.on.ol.EndOK x.2.1 x.2.2 := by
    rintro _ (⟨core', rfl⟩ | ⟨G, core', rfl⟩)
    · exact T.on.ol.endOK core'
    · exact T.on.ol.endOKG G core'
  exact key ⟨T.Wz, T.piz, T.Bz⟩ h

/-- The fold of the link's first index (the parent's): one of two regimes. Either "no collision", a
radius e₀ at most eM, the error within a third; or, as the write-up's reference has it, "it
decodes with its record", any radius with e₀ + eM below the distance, error 0. -/
def LdObjD.Par3 (T : LdObjD F E) : Prop :=
  (T.on0K = T.K.free ∧ T.K.e₀ ≤ T.W.Cf.eM ∧ T.ε₀ = T.W.Cf.εThird T.K.e₀) ∨
  (T.on0K = T.K.dec0 ∧ T.K.e₀ + T.W.Cf.eM < T.W.Cf.C₀.d ∧ T.ε₀ = 0)

/-- `HypOwn` within a third. -/
structure LdObjD.Own3 (T : LdObjD F E) : Prop where
  lay    : T.LayOK
  q₀e    : T.q₀ ∅
  /-- the offline test's fold -/
  e'le   : T.W.O.e' ≤ T.W.Cf.eM
  εfIs   : T.εf = T.W.Cf.εThird T.W.O.e'
  pyInj  : Function.Injective T.W.O.py
  /-- the link's two folds: the first index by either regime, the further one by the first -/
  par    : T.Par3
  on1Is  : T.on1K = T.K.free
  e₁le   : T.K.e₁ ≤ T.W.Cf.eM
  ε₁Is   : T.ε₁ = T.W.Cf.εThird T.K.e₁
  plInj  : Function.Injective T.K.pl
  bearK  : ∀ a, T.Kc.t ≤ T.Sl.t a
  /-- the request -/
  rHyp   : T.r.Hyp
  rZk    : T.r.ZkS
  rFmt   : T.r.Fmt (T.on.ol.fmtA T.cr T.qφ) (T.on.ol.fmtZAt T.Bz T.piz T.qiB)
  rEnd   : T.EndStd
  /-- the online test's fold: the index decodes with its record -/
  onBIs  : T.onB = T.on.ol.onDec
  εfBIs  : T.εfB = 0
  e'far  : T.on.ol.e' + T.W.Cf.eM < T.W.Cf.C₀.d
  pyInjB : Function.Injective T.on.ol.py
  monoB  : ∀ U V, V ⊆ U → T.qaB U → T.qaB V

theorem LdObjD.Own3.own {T : LdObjD F E} (h : T.Own3) (hC : T.W.Cf.Third) : T.HypOwn := by
  have hl := ldCm_list_unique F E T.W.Cf hC.dist (by have := hC.lt; omega)
  have hlt : T.W.Cf.eM < T.W.Cf.C₀.d := by have := hC.lt; omega
  exact
    { lay := h.lay, q₀e := h.q₀e
      fold := by
        rw [h.εfIs]
        exact ldLin_foldErr T.W.O.toC.P T.W.Cf.C₀.d _ 1 (ldCm_dist F E T.W.Cf hC.dist) hlt h.e'le
          (ldCm_mca_third F E T.W.Cf T.W.O.e' hC.dist (by have := hC.lt; have := h.e'le; omega))
          (ldCm_list_le F E T.W.Cf 1 T.W.O.e' hl h.e'le)
      pyInj := h.pyInj
      fitsK := by
        rcases h.par with ⟨e0, -, -⟩ | ⟨e0, -, -⟩
        · rw [e0, h.on1Is]
          exact ⟨fun _ _ _ hh => hh, fun _ _ hh => hh⟩
        · rw [e0, h.on1Is]
          exact ⟨fun _ _ hd _ => hd, fun _ _ hh => hh⟩
      foldK := by
        rcases h.par with ⟨e0, hle, hε⟩ | ⟨e0, hfar, hε⟩
        · rw [e0, h.on1Is, hε, h.ε₁Is]
          exact ldLk_foldErr_rec T.K.P T.W.Cf.C₀.d _ 1 _ 1 (ldCm_dist F E T.W.Cf hC.dist) hlt hle
            h.e₁le (ldCm_mca_third F E T.W.Cf T.K.e₀ hC.dist (by have := hC.lt; omega))
            (ldCm_list_le F E T.W.Cf 1 T.K.e₀ hl hle)
            (ldCm_mca_third F E T.W.Cf T.K.e₁ hC.dist (by have := hC.lt; have := h.e₁le; omega))
              (ldCm_list_le F E T.W.Cf 1 T.K.e₁ hl h.e₁le)
        · rw [e0, h.on1Is, hε, h.ε₁Is]
          exact ldLk_foldErr T.K.P T.W.Cf.C₀.d _ 1 (ldCm_dist F E T.W.Cf hC.dist) hfar h.e₁le
            (ldCm_mca_third F E T.W.Cf T.K.e₁ hC.dist (by have := hC.lt; have := h.e₁le; omega))
            (ldCm_list_le F E T.W.Cf 1 T.K.e₁ hl h.e₁le)
      plInj := h.plInj, bearK := h.bearK, rHyp := h.rHyp, rZk := h.rZk,
        rFmt := h.rFmt, rEnd := h.rEnd.ok
      fitsB := by rw [h.onBIs]; exact (ldOB_fits F E T.on.ol).1
      foldB := by rw [h.onBIs, h.εfBIs]; exact ldOB_foldErr F E T.on.ol hC.dist h.e'far
      pyInjB := h.pyInjB, monoB := h.monoB }

end

/-- The object within a third: the data. -/
structure LdObjZ3 (F E : Type) [Field F] [Field E] [Fintype F] [Fintype E] [Algebra F E] where
  R    : LdObjR F E
  Zw   : LdWfE F E
  Y    : R.toLdObjD.StdS
  twK  : R.Kc.run.Tow3
  tw₁  : R.TP₀.D₁.Tow3
  tw₂  : R.TP₀.D₂.Tow3
  tw₃  : R.X.run.Tow3
  tw₁B : R.TB₀.D₁.Tow3
  tw₂B : R.TB₀.D₂.Tow3
  tw₃B : R.XB.run.Tow3
  /-- distances -/
  dS   : Zw.W.P.S.O → ℕ
  dK   : ℕ
  d₁   : ℕ
  d₂   : ℕ
  d₃   : ℕ
  d₁B  : ℕ
  d₂B  : ℕ
  d₃B  : ℕ
  dW   : R.W.O.toC.P.NW.O → ℕ
  dU   : R.W.O.toC.P.NU.O → ℕ
  dO   : R.W.O.toC.P.NO.O → ℕ
  dN   : R.K.P.N.O → ℕ
  dWB  : R.on.ol.toC.P.NW.O → ℕ
  dUB  : R.on.ol.toC.P.NU.O → ℕ
  dOB  : R.on.ol.toC.P.NO.O → ℕ

namespace LdObjZ3
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (Z : LdObjZ3 F E)

def toZ : LdObjZ F E :=
  { R := Z.R, Zw := Z.Zw, Y := Z.Y, twK := Z.R.Kc.run.up3 Z.twK, tw₁ := Z.R.TP₀.D₁.up3 Z.tw₁,
    tw₂ := Z.R.TP₀.D₂.up3 Z.tw₂, tw₃ := Z.R.X.run.up3 Z.tw₃
    tw₁B := Z.R.TB₀.D₁.up3 Z.tw₁B, tw₂B := Z.R.TB₀.D₂.up3 Z.tw₂B, tw₃B := Z.R.XB.run.up3 Z.tw₃B }

structure Hyp (p : ℕ) : Prop where
  wfIs  : (⟨Z.R.W, Z.R.Bw⟩ : Σ W : LdOWf F E, W.P.Blk) = ⟨Z.Zw.W, Z.Zw.G.B⟩
  sndIs : Z.R.toLdObjD = Z.R.toLdObjD.std Z.Y
  wf3   : Z.Zw.Third p Z.dS
  sOff  : Z.Y.TS.Third3 Z.Y.LW Z.Y.LU Z.Y.LO Z.Y.tW Z.Y.tU Z.Y.tO Z.dW Z.dU Z.dO
  sLink : Z.R.K.P.StdThird Z.Y.SdK Z.Y.LK Z.Y.tK Z.Y.YK Z.Y.ixK Z.dN
  sOn   : Z.Y.TB.Third3 Z.Y.LWB Z.Y.LUB Z.Y.LOB Z.Y.tWB Z.Y.tUB Z.Y.tOB Z.dWB Z.dUB Z.dOB
  own   : Z.R.toLdObjD.Own3
  pl    : Z.R.HypPl
  pK    : Z.R.Kc.run.Pre3 Z.twK Z.dK
  p₁    : Z.R.TP₀.D₁.Pre3 Z.tw₁ Z.d₁
  p₂    : Z.R.TP₀.D₂.Pre3 Z.tw₂ Z.d₂
  p₃    : Z.R.X.run.Pre3 Z.tw₃ Z.d₃
  p₁B   : Z.R.TB₀.D₁.Pre3 Z.tw₁B Z.d₁B
  p₂B   : Z.R.TB₀.D₂.Pre3 Z.tw₂B Z.d₂B
  p₃B   : Z.R.XB.run.Pre3 Z.tw₃B Z.d₃B

end LdObjZ3

def Spec.ldObjZ3_hyp (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Prop :=
  ∀ (Z : LdObjZ3 F E) (p : ℕ), Z.Hyp p → Z.toZ.Hyp p 1

theorem ldObjZ3_hyp (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.ldObjZ3_hyp F E := by
  intro Z p h
  have hC : Z.R.W.Cf.Third := by
    have key : ∀ x : Σ W : LdOWf F E, W.P.Blk, x = ⟨Z.Zw.W, Z.Zw.G.B⟩ → x.1.Cf.Third := by
      rintro _ rfl
      exact h.wf3.conf3
    exact key ⟨Z.R.W, Z.R.Bw⟩ h.wfIs
  exact
    { wfIs := h.wfIs
      sndIs := h.sndIs
      wfOK := ldWfEnd3_ok Z.Zw p Z.dS h.wf3
      sndOK := ⟨h.sOff.hyp, h.sLink.hyp, h.sOn.hyp⟩
      own := h.own.own hC
      pl := h.pl
      pK := h.pK.pre
      p₁ := h.p₁.pre
      p₂ := h.p₂.pre
      p₃ := h.p₃.pre
      p₁B := h.p₁B.pre
      p₂B := h.p₂B.pre
      p₃B := h.p₃B.pre }

end Cb
