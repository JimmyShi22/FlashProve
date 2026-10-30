-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/KnowRecut.lean: a round whose verifier message has one value joins the next prover message:
all properties of the interface with a witness are kept, under the conditions below.

This file is about the interactive oracle proofs that the compiler takes: merging a round whose
verifier message is trivial into the next round keeps, under the hypotheses of the statements,
round-by-round knowledge soundness and the other properties, with the same numbers.
Definitions, statements and proofs.
The plans may cut as well as join: a joined message can be cut again, between its oracles, in the
same pass (step "cut", Iop/Recut.lean); only the step "chal" (two verifier messages become one) is
excluded, since it adds errors.

Why: The constructions let a block send its mask oracle in a round of its own, whose verifier
message has one value; a print of this protocol's technical report (lean/CREDITS.md) sends
it together with the block's first message.
Iop/BatchRecut.lean has the passage at the interface: rounds are cut and joined along a plan
(`XPlan`, Iop/Recut.lean; step "msg": (m1 . u) (m2 . c2) becomes ((m1, m2) . c2); `BatchProtocol.recut`), with
all properties of `Iop.BatchProtocol.Props` but soundness, which is supplied (`Spec.recutPropsB`). It does not
know the witness. Here: the properties with a witness (`BatchProtocol.SoundK`, `BatchProtocol.PropsK`,
Hiop/Interface.lean), which are among the hypotheses of the compiler's statements
(CompileK/Main.lean).
The proofs go as in CompileK/KnowPull.lean: `SndBK` is the late form of (Snd-B) of the guarded
protocol for the empty language, so `Iop.BatchRecut.sndBL_recut` applies to the guarded protocol.

Main names, each under the hypotheses of its statement:
  `XPlan.NoChal` (Blocks/GrindSmallMsg.lean): the plan joins no two verifier messages (no step
    "chal").
  `Orcs.old P o`: the prover's oracles of the old shape, read off those of the new one: the same
    symbols at the same positions, up to the renaming of positions (`OPos.oldEquiv`).
  `Spec.read_old`: the oracles of the transcript read back are the oracles read back.
  `Spec.guard_recut`: "guard, then recut" and "recut, then guard with the extractor wit ∘ Orcs.old"
    are the same batch IOP.
  `Spec.sndBK_recut`: (Snd-B) with a witness is kept: same relation, extractor wit ∘ Orcs.old, the
    errors `Err.recut`.
  `Spec.below_recut`: along a plan that joins no two verifier messages, a bound on all errors is
    kept: the error of a joined round is 0 · |C2| + 1 · e2; a first piece that is cut off has the
    error 0.
  `Spec.soundK_recut`: `BatchProtocol.SoundK` is kept, with the same εs.
  `Spec.propsK_recut`: `BatchProtocol.PropsK` is kept, with the same numbers.
The conditions: the plans' laws (at a join the first verifier message has one value); no step "chal"
in any of the three plans (`XPlan.NoChal`), from which `AXPlan.Kinds` follows
(`AXPlan.kinds_of_noChal`, CompileK/KnowJoin.lean); the laws of the session's annotated cuts
(`AXPlan.OK`); if `L.late = some n`, `AXPlan.Late` of the session's plan at n (among its clauses:
the plan leaves the round "late" the first of its new round); at least one slot; εs < 1 (then a
round with one verifier message has the error 0).
The extractor after the join is the old one on the same symbols. It sees no verifier message.

Limits: this file does not say which rounds are joined. It does not say that the format of a
session's rounds is kept: `Iop.recutFmtB`, for plans that fit. The oracles of a joined message do
not become one interleaved word: the joined round's positions are the positions of both, side by
side; the compiler makes one tree over all positions of a component (the shared one, or a slot's) of
the joined message (padded to a power of two), unless a later cut gives each oracle a round of its
own.
The parameter lists of the sub-protocols are not touched: the join stands behind
them, at the finished interface.

Terms: lean/GLOSSARY.md: guard, interface, plan, session, slot, (Snd-B).
-/
import CompileK.KnowExt
import Hiop.InterfaceProofs
import Iop.BatchRecutProofs
import Iop.BatchJoinProofs
import Iop.RecutKit
import Blocks.GrindSmallMsg

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

/- "The plan joins no two verifier messages": `XPlan.NoChal` is in Blocks/GrindSmallMsg.lean. -/

/-- The prover's oracles of the old shape, read off those of the new one. -/
def Orcs.old {s : Shape} (P : XPlan s) (o : Orcs P.shape) : Orcs s :=
  fun p =>
    (Equiv.apply_symm_apply (OPos.oldEquiv P) p) ▸
      OSym.old P ((OPos.oldEquiv P).symm p) (o ((OPos.oldEquiv P).symm p))

namespace Spec

def read_old : Prop :=
  ∀ (s : Shape) (P : XPlan s), P.OK → ∀ τ : Tr P.shape, (Tr.old P τ).read = Orcs.old P τ.read

def guard_recut : Prop :=
  ∀ (X W : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E) (R : X → E.Str → W → Prop)
      (wit : X → Orcs Q.loc.shape → W) (P : XPlan Q.loc.shape) (Z : AXPlan P Q.ann),
    P.OK → (Q.guard R wit).recut P Z = (Q.recut P Z).guard R (fun x o => wit x (Orcs.old P o))

/-- States, under the hypotheses below: (Snd-B) with a witness is kept, at the errors
`Err.recut P ε`. -/
def sndBK_recut : Prop :=
  ∀ (X W : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E) (P : XPlan Q.loc.shape) (Z : AXPlan P Q.ann),
    P.OK → AXPlan.OK P Q.ann Z → AXPlan.Kinds P Q.ann Z →
    ∀ (N : ℕ), 0 < N →
      ∀ (early : X → X) (late : Option ℕ), (∀ n, late = some n → AXPlan.Late P Q.ann Z n) →
        ∀ (R : X → E.Str → W → Prop) (wit : X → Orcs Q.loc.shape → W) (ε : Err Q.loc.shape),
          ε.UnitZero → Q.SndBK N early late R wit ε →
          (Q.recut P Z).SndBK N early (late.map P.idx) R
            (fun x o => wit x (Orcs.old P o)) (Err.recut P ε)

/-- States, under the hypotheses below: a bound on all errors is kept. -/
def below_recut : Prop :=
  ∀ (s : Shape) (P : XPlan s), P.OK → P.NoChal →
    ∀ (ε : Err s) (c : ℝ≥0∞), ε.UnitZero → Err.Below ε c → Err.Below (Err.recut P ε) c

/-- States, under the hypotheses below: index-binding round-by-round knowledge soundness is kept,
with the same bound. -/
def soundK_recut : Prop :=
  ∀ (I X W : Type) (L : BatchProtocol I X) (Rno : I → X → W → Prop) (wit : X → Orcs L.onlineBatch.loc.shape → W)
      (εs : ℝ≥0∞) (XT : XPlan L.offline.shape) (XL : XPlan L.link.shape) (XB : XPlan L.onlineBatch.loc.shape)
      (ZB : AXPlan XB L.onlineBatch.ann) (hK : AXPlan.Kinds XB L.onlineBatch.ann ZB),
    XT.OK → XL.OK → XB.OK → XT.NoChal → XL.NoChal → XB.NoChal → AXPlan.OK XB L.onlineBatch.ann ZB →
    0 < L.maxBatchSize → (∀ n, L.late = some n → AXPlan.Late XB L.onlineBatch.ann ZB n) → εs < 1 →
    L.SoundK Rno wit εs → (L.recut XT XL XB ZB hK).SoundK Rno (fun x o => wit x (Orcs.old XB o)) εs

/-- States, under the hypotheses below: all properties with a witness are kept, with the same
numbers. -/
def propsK_recut : Prop :=
  ∀ (I X W : Type) (L : BatchProtocol I X) (Ryes Rno : I → X → W → Prop) (wit : X → Orcs L.onlineBatch.loc.shape → W)
      (M : LH.Nums) (XT : XPlan L.offline.shape) (XL : XPlan L.link.shape) (XB : XPlan L.onlineBatch.loc.shape)
      (ZB : AXPlan XB L.onlineBatch.ann) (hK : AXPlan.Kinds XB L.onlineBatch.ann ZB),
    XT.OK → XL.OK → XB.OK → XT.NoChal → XL.NoChal → XB.NoChal → AXPlan.OK XB L.onlineBatch.ann ZB →
    0 < L.maxBatchSize → (∀ n, L.late = some n → AXPlan.Late XB L.onlineBatch.ann ZB n) → M.εs < 1 →
    L.PropsK Ryes Rno wit M →
    (L.recut XT XL XB ZB hK).PropsK Ryes Rno (fun x o => wit x (Orcs.old XB o)) M

end Spec

/-- The oracles read back, at the old name of a new position. -/
theorem Orcs.old_apply {s : Shape} (P : XPlan s) (o : Orcs P.shape) (q : OPos P.shape) :
    Orcs.old P o (OPos.oldEquiv P q) = OSym.old P q (o q) := by
  have key : ∀ (q' : OPos P.shape) (_ : q' = q) (hp : OPos.oldEquiv P q' = OPos.oldEquiv P q),
      hp ▸ OSym.old P q' (o q') = OSym.old P q (o q) := by
    rintro _ rfl _
    rfl
  exact key _ (Equiv.symm_apply_apply _ q) _

theorem read_old : Spec.read_old := by
  intro s P hP τ
  funext p
  obtain ⟨q, rfl⟩ := (OPos.oldEquiv P).surjective p
  rw [Tr.read_old P hP, Orcs.old_apply]

open Classical in
/-- Under `hP`, two verifiers decide alike: the one that reads the witness off `(Tr.old P τ).read`,
and the one that reads it off `Orcs.old P τ.read`. -/
theorem KnowRecut.accept_eq {X W : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof X E)
    (R : X → E.Str → W → Prop) (wit : X → Orcs Q.loc.shape → W)
    (P : XPlan Q.loc.shape) (hP : P.OK) :
    (fun (x : X) (y : E.Str) (τ : Tr P.shape) =>
        Q.loc.accept x y (Tr.old P τ) && !decide (R x y (wit x (Tr.old P τ).read))) =
      fun x y τ =>
        Q.loc.accept x y (Tr.old P τ) && !decide (R x y (wit x (Orcs.old P τ.read))) := by
  funext x y τ
  rw [read_old _ P hP]

theorem guard_recut : Spec.guard_recut := fun X _ E Q R wit P Z hP =>
  congrArg (fun acc : X → E.Str → Tr P.shape → Bool =>
      (⟨{ Q.loc.recut P with accept := acc }, Q.ann.recut P Z⟩ : BatchInteractiveOracleProof X E))
    (KnowRecut.accept_eq Q R wit P hP)

theorem sndBK_recut : Spec.sndBK_recut := by
  intro X W E Q P Z hP hZ hK N hN early late hl R wit ε hε h
  have h' : ((Q.guard R wit).recut P Z).SndBL
      N early (late.map P.idx) (fun _ _ => False) (Err.recut P ε) :=
    BatchRecut.sndBL_recut (Q := Q.guard R wit) hP hZ hK hN hl hε h
  exact cast
    (congrArg (fun acc : X → E.Str → Tr P.shape → Bool =>
        (⟨{ Q.loc.recut P with accept := acc }, Q.ann.recut P Z⟩ : BatchInteractiveOracleProof X E).SndBL
          N early (late.map P.idx) (fun _ _ => False) (Err.recut P ε))
      (KnowRecut.accept_eq Q R wit P hP)) h'

theorem below_recut : Spec.below_recut := by
  intro s P
  induction P with
  | nil => intro _ _ _ _ _ _; trivial
  | keep r P ih =>
      rintro hP hn ⟨e, ε⟩ c hu hb
      exact ⟨hb.1, ih hP hn ε c hu.2 hb.2⟩
  | cut k P ih =>
      rintro hP hn ⟨e, ε⟩ c hu hb
      exact ⟨by rw [Nat.cast_zero]; exact zero_le _, ih hP.2 hn (e, ε) c hu hb⟩
  | @msg r1 r2 s u P ih =>
      rintro hP hn ⟨e1, e2, ε⟩ c hu hb
      have h1 : Fintype.card r1.Chal = 1 := card_eq_one_of_forall hP.1
      have he : e1 = 0 := hu.1 h1
      have e : e1 * Fintype.card r2.Chal + Fintype.card r1.Chal * e2 = e2 := by
        rw [he, h1, Nat.zero_mul, Nat.zero_add, Nat.one_mul]
      refine ih hP.2 hn (e1 * Fintype.card r2.Chal + Fintype.card r1.Chal * e2, ε) c
        ⟨fun hcard => ?_, hu.2.2⟩ ⟨?_, hb.2.2⟩
      · rw [e]
        exact hu.2.1 hcard
      · rw [e]
        exact hb.2.1
  | chal r1 r2 np P ih => intro _ hn; exact hn.elim

theorem soundK_recut : Spec.soundK_recut := by
  intro I X W L Rno wit εs XT XL XB ZB hK hT hL hB nT nL nB hZ hN hl h1 h
  exact
    ⟨let ⟨ε, hb, hs⟩ := h.sndT; ⟨Err.recut XT ε, below_recut _ XT hT nT ε εs (BatchJoin.unitZero_of_below h1 hb) hb, hs.recut XT⟩,
     let ⟨ε, hb, hs⟩ := h.sndL; ⟨Err.recut XL ε, below_recut _ XL hL nL ε εs (BatchJoin.unitZero_of_below h1 hb) hb, hs.recut XL⟩,
     let ⟨ε, hb, hs⟩ := h.sndB; ⟨Err.recut XB ε, below_recut _ XB hB nB ε εs (BatchJoin.unitZero_of_below h1 hb) hb,
       sndBK_recut _ _ _ L.onlineBatch XB ZB hB hZ hK L.maxBatchSize hN L.early L.late hl _ wit ε
         (BatchJoin.unitZero_of_below h1 hb) hs⟩⟩

theorem propsK_recut : Spec.propsK_recut := by
  intro I X W L Ryes Rno wit M XT XL XB ZB hK hT hL hB nT nL nB hZ hN hl h1 h
  have hS := soundK_recut I X W L Rno wit M.εs XT XL XB ZB hK hT hL hB nT nL nB hZ hN hl h1 h.soundK
  exact ⟨recutPropsB I X L _ _ M XT XL XB ZB hK M.εs hT hL hB hZ
      h.props (sound_of_soundK _ _ _ _ _ _ _ hS),
    hS⟩

end Iop
