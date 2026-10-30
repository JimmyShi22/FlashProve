-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/SpecStage.lean: four stage-by-stage statements; Spec.linkShift
(SpecShift.lean) is built from three of them. Definitions and statements only.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

No proof here: bodyShift and walkSame are proved in Induct.lean, frontShift and frontWalk in
LinkShift.lean.

Two runs of the prover's algorithm stand side by side at the same challenges D. The honest run has
coins Kr and prover state Pr. The run at the data 0 has coins Ks and state Ps. d is the difference
of the two states. The shift of the coins is shB along the stages, and shC for the whole link
(Johnson/LinkSim/AtText/ShiftDefs.lean).

What this file states. All four hold for all parameters.
  Spec.bodyShift   suppose the public premises on sizes (FitsBody) and AtStage hold, and the
                 claim left at the base case is true at the honest run's last message. Then both
                 runs have the same groups of columns, and disclose the same rounds but for one
                 item: the honest run's rounds are the other run's with the element of the base
                 case's first round replaced by tauStar.
  Spec.walkSame    under the same premises, without the claim: the shift of the coins computed
                 along the run at the data 0 is the same as the one computed along the honest run.
  Spec.frontShift  under Sizes, with C' := C + shC: the five rounds before the first stage (the
                 front) are the same at X, C and at the data 0, C'; so is the verifier's state after
                 the batching; and AtStage holds in front of the first stage.
  Spec.frontWalk   the front's own pieces of the shift are the same along the other run.

How it fits. LinkShift.lean and Induct.lean prove these, and build Spec.linkShift and
Spec.linkShiftIn from walkSame, frontShift and frontWalk. In bodyShift's place the chain takes
bodyShiftOr (SpecShiftIn.lean), of which bodyShift is a case; no declaration uses bodyShift.
Spec.linkShiftIn is used in the proof of homeExact (Johnson/LinkSim/AtHome/Home.lean).
SpecShift.lean's head explains why the claim left at the base case is a premise.

The other names (namespace OnBytes.LinkSim.AtText).
  openedAt       the sampled positions at which the tree in hand at a stage is opened.
  WordRel        at the last stage, the masking word's difference is minus the sampled element times
                 the difference of the last message and of its tails.
  AtStage        what holds in front of a stage. Both runs share one verifier state t (by the
                 statement's form: one variable). Its fields: st, Pr = Ps + d; col, the trees in
                 hand have equal columns at the positions at which they are opened; foldW, where a
                 fold follows, its coefficients differ by foldShift; word, at the last stage,
                 WordRel; fr, new and W, all later coin variables differ by shB.

Limits.
- No finite type of coins is here: the statements are on coin variables.

Notes. The proofs use no further premise on sizes. At a plan of one stage, AtStage's field word
would be asked of the first difference, whose masking word the front sets to 0; it need not hold
there. The public premises on sizes exclude such a plan (rest_ne,
Johnson/LinkSim/AtText/PlacesProof.lean).

Sources. This file carries out the plan of AtText/ShiftDefs.lean, and the note on sources in that
file's head holds here too.

Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.ShiftDefs
import Johnson.LinkSim.AtText.SpecShift

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Desc.K15 (P15 p12Of)
open H2K.Pub (sgOf)
open H2K.JointK (laidOf)
open Johnson.Prover.Link

/-- The sampled positions at which the tree in hand at a stage is opened: at the switch's second
round, or at the base case's. -/
def openedAt (D : ℕ → Fmt.Drawn) (rest : List Fmt.M1.Stage) (cur : Fmt.M1.Stage) (o : ℕ) : List ℕ :=
  openAt (sgOf cur).C.a
    (if rest.isEmpty then (D (o + 1)).poss else (D (o + 2 + ((sgOf cur).h + (sgOf cur).g))).poss)

/-- At the last stage: the masking word's difference. -/
structure WordRel (D : ℕ → Fmt.Drawn) (cur : Fmt.M1.Stage) (o : ℕ) (d : PS) : Prop where
  sM : ∀ i, d.sM i = -(toE ((D o).elems.headD (0, 0, 0)) * mainOf (sgOf cur) (μOf (sgOf cur) d) i)
  sT : ∀ q, d.sT q = -(toE ((D o).elems.headD (0, 0, 0)) * d.tM 0 q)
  fM : ∀ i, d.fM 0 i = -(toE ((D o).elems.headD (0, 0, 0)) * maskOf (sgOf cur) (μOf (sgOf cur) d) i)
  fT : ∀ q, d.fT 0 q = -(toE ((D o).elems.headD (0, 0, 0)) * d.tZ 0 q)

/-- **What holds in front of a stage.** -/
structure AtStage (p : P12) (D : ℕ → Fmt.Drawn) (rest : List Fmt.M1.Stage) (j : ℕ)
    (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (Kr Ks : BCoins) (Pr Ps d : PS)
    (colr cols : ℕ → List UInt64) : Prop where
  st : Pr = addPS Ps d
  col : ∀ x ∈ Fmt.listOf (openedAt D rest cur o), colr x = cols x
  foldW : rest ≠ [] → Ks.W (sgOf cur) j = Kr.W (sgOf cur) j +
    foldShift (sgOf cur) (vecG (sgOf cur) (rowOf t)) (μOf (sgOf cur) d) fun n => D (o + n)
  word : rest = [] → WordRel D cur o d
  fr : ∀ i, j ≤ i → Ks.fr i = Kr.fr i + (shB p Kr D rest j cur l o t Pr colr d).fr i
  new : ∀ i, j ≤ i → Ks.new i = addPS (Kr.new i) ((shB p Kr D rest j cur l o t Pr colr d).new i)
  W : ∀ σ i, j < i → Ks.W σ i = Kr.W σ i + (shB p Kr D rest j cur l o t Pr colr d).W σ i

/-- Statement only; proved as bodyShift in Induct.lean. **Along the stages the two runs disclose the
same, but for one item**, under FitsBody, AtStage and the claim left at the base case. -/
def Spec.bodyShift : Prop :=
  ∀ (p : P12) (D : ℕ → Fmt.Drawn) (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid)
    (o : ℕ) (t : T12) (Kr Ks : BCoins) (Pr Ps d : PS) (colr cols : ℕ → List UInt64),
    FitsBody D rest cur o → AtStage p D rest j cur l o t Kr Ks Pr Ps d colr cols →
    ClaimTrue p (bodyEnd p Kr D rest j cur l o t Pr colr) →
    (bodyAll p Kr rest j cur l o t Pr colr D).gs = (bodyAll p Ks rest j cur l o t Ps cols D).gs ∧
      (bodyAll p Kr rest j cur l o t Pr colr D).rs =
        (bodyAll p Ks rest j cur l o t Ps cols D).rs.set
          ((bodyEnd p Ks D rest j cur l o t Ps cols).o - o)
          ⟨[.e (tauStar p (bodyEnd p Ks D rest j cur l o t Ps cols) D)],
            D (bodyEnd p Ks D rest j cur l o t Ps cols).o⟩

/-- Statement only; proved as walkSame in Induct.lean. **Computed along the other run, the shift of
the coins is the same.** -/
def Spec.walkSame : Prop :=
  ∀ (p : P12) (D : ℕ → Fmt.Drawn) (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid)
    (o : ℕ) (t : T12) (Kr Ks : BCoins) (Pr Ps d : PS) (colr cols : ℕ → List UInt64),
    FitsBody D rest cur o → AtStage p D rest j cur l o t Kr Ks Pr Ps d colr cols →
    shB p Ks D rest j cur l o t Ps cols d = shB p Kr D rest j cur l o t Pr colr d

/-- Statement only; proved as frontShift in LinkShift.lean. **The front**: under Sizes, the front is
the same at the data 0 with the changed coins, and AtStage holds in front of the first stage. -/
def Spec.frontShift : Prop :=
  ∀ (P : P15) (S : Sz) (t : ℕ) (X : LIn S) (C : LCoins) (D : ℕ → Fmt.Drawn), Sizes P S t D →
    ∀ first rest, (p12Of P).nums.stages = first :: rest →
    lFront S t X C D = lFront S t (zeroIn X) (addC C (shC P S t X X C D)) D ∧
      lT P S t X C D = lT P S t (zeroIn X) (addC C (shC P S t X X C D)) D ∧
      AtStage (p12Of P) D rest 0 first ((laidOf (p12Of P)).drop 1) 6 (lT P S t X C D) C.body
        (addC C (shC P S t X X C D)).body (lPS P S X C D)
        (lPS P S (zeroIn X) (addC C (shC P S t X X C D)) D) (d0 P S t X X C D) (lCol P S X C D)
        (lCol P S (zeroIn X) (addC C (shC P S t X X C D)) D)

/-- Statement only; proved as frontWalk in LinkShift.lean. **The front's own pieces of the shift
are the same along the other run.** -/
def Spec.frontWalk : Prop :=
  ∀ (P : P15) (S : Sz) (t : ℕ) (X : LIn S) (C : LCoins) (D : ℕ → Fmt.Drawn), Sizes P S t D →
    shC P S t X (zeroIn X) (addC C (shC P S t X X C D)) D = shC P S t X X C D

end OnBytes.LinkSim.AtText
