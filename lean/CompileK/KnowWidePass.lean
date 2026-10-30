-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/KnowWidePass.lean: the interface with a wide witness map through the passes: verifier
messages made from blocks, tests (proof of work), rounds cut and joined.

This file is about the interactive oracle proofs that the compiler takes: three rewritings of their
rounds keep round-by-round knowledge soundness for a wide witness map, each under its hypotheses and
with the errors told below.
Definitions, statements and proofs: the wide forms of CompileK/KnowPull.lean, Hiop/GrindK.lean,
CompileK/GrindPullK.lean, CompileK/KnowRecut.lean, CompileK/GrindKRecut.lean. An assembly over
Ior/KnowWidePass.lean (one batch IOP) and the theorems of Iop/ on `BatchProtocol.Props` for the passes.
The witness map (Hiop/KnowWide.lean) reads the instance, the encoded index and a slot's whole local
transcript. Each pass reads the transcript back (`Tr.push`, `Tr.strip`, `Tr.old`), and the witness
map is carried by that map. The compiler's door: its statements for any interface L, any data D
(`DataK`, CompileK/Main.lean) and any work (`Work`, CompileK/GrindMain.lean).
`BatchProtocol.SoundKT` (Hiop/KnowWide.lean): round-by-round soundness of the test and of the link, and
round-by-round knowledge soundness of the batch IOP with the witness map wit, all errors, as
probabilities, at most εs. `BatchProtocol.PropsKT`: `BatchProtocol.Props` for the two languages, and `BatchProtocol.SoundKT`.

Main names, each under the hypotheses of its statement:
  `Spec.soundAtKT_pull`, `Spec.soundAtKT_draws`, `Spec.grindSoundAtKT`, `Spec.soundAtKT_recut`:
    three explicit lists: `Err.pull`, `Err.grind` (the same counts), `Err.recut`.
  `Spec.soundKT_draws`, `Spec.propsKT_draws`: blocks: εs becomes κ₀^K εs; all properties with the
    numbers `M.pullB (κ₀ ^ dr.K) (κ₀ ^ n) L.maxBatchSize`.
  `Spec.soundKGT_draws`, `Spec.grindSoundKGT`: `BatchProtocol.SoundKGT` (round errors bounded by c with
    their bits of work credited): blocks turn c into κ₀^K c; with the tests in, `BatchProtocol.SoundKT` at c.
  `Spec.propsNoAccKT_drawsGrind`: the door's lemma, wide: from `BatchProtocol.PropsKT` of L and `BatchProtocol.SoundKGT`
    at c, the interface "blocks, then tests" has all properties but acceptance, with knowledge
    soundness at κ₀^K c.
  `Spec.soundKT_recut`, `Spec.propsKT_recut`, `Spec.soundKGT_recut`: cuts and joins (no two verifier
    messages joined): same bound, same numbers; the conditions of CompileK/KnowRecut.lean and
    CompileK/GrindKRecut.lean.
  By parts, for cuts and joins (for blocks and tests: Ior/KnowWidePass.lean):
  `WitP.old P w`, `Spec.witOf_old`: the carried map is again given by parts (oracles' symbols, plain
    parts, verifier messages, each read back by its own map).
  `Spec.blindFrom_old`: if w does not read the verifier messages from the old round j on, the
    carried map does not read them from the new round on in which the old round j begins
    (`XPlan.idx`).
  `Spec.witOf_door`, `Spec.blindFrom_door`: the map at the door with work, "blocks, then tests", is
    given by parts too: (w.push σ).strip (g.pull σ); the same j.

Limits: this file says nothing on the compiled argument. No instance.

Terms: lean/GLOSSARY.md.
-/
import CompileK.GrindPullK
import CompileK.GrindKRecut
import Hiop.KnowWide
import Ior.KnowWidePass

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

/-- After cuts and joins. -/
def WitP.old {X W : Type} {E : ExtSpec} {s : Shape} (P : XPlan s) (w : WitP X E s W) :
    WitP X E P.shape W :=
  fun x y o pl ρ => w x y (Orcs.old P o) (Plains.old P pl) (Rho.old P ρ)

namespace Spec

def soundAtKT_pull : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop)
      (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (εT : Err L.offline.shape)
      (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape) (σT : Samplers L.offline.shape)
      (σL : Samplers L.link.shape) (σB : Samplers L.onlineBatch.loc.shape),
    σT.Fib → σL.Fib → σB.Fib → L.SoundAtKT Rno wit εT εL εB →
    (L.pull σT σL σB).SoundAtKT
      Rno (fun x y τ => wit x y (Tr.push σB τ)) (Err.pull σT εT) (Err.pull σL εL) (Err.pull σB εB)

def soundAtKT_draws : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop)
      (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (εT : Err L.offline.shape)
      (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape) (lam : ℕ) (dr : L.Draws lam) (κ₀ : ℝ≥0∞),
    dr.Good κ₀ → L.SoundAtKT Rno wit εT εL εB →
    (L.draws dr).SoundAtKT Rno (fun x y τ => wit x y (Tr.push (Samplers.ofDraws _ dr.B) τ))
      (Err.pull (Samplers.ofDraws _ dr.T) εT) (Err.pull (Samplers.ofDraws _ dr.Lk) εL)
      (Err.pull (Samplers.ofDraws _ dr.B) εB)

def grindSoundAtKT : Prop :=
  ∀ (W : Type) [Inhabited W] (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop)
      (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (gT : GBits L.offline.shape)
      (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) (εT : Err L.offline.shape)
      (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape),
    L.SoundAtKT Rno wit εT εL εB →
    (L.grind W gT gL gB).SoundAtKT Rno (fun x y τ => wit x y (Tr.strip gB τ)) (Err.grind gT εT)
      (Err.grind gL εL) (Err.grind gB εB)

def soundAtKT_recut : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop)
      (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn)
      (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape)
      (XT : XPlan L.offline.shape) (XL : XPlan L.link.shape) (XB : XPlan L.onlineBatch.loc.shape)
      (ZB : AXPlan XB L.onlineBatch.ann) (hK : AXPlan.Kinds XB L.onlineBatch.ann ZB),
    XB.OK → AXPlan.OK XB L.onlineBatch.ann ZB → 0 < L.maxBatchSize →
    (∀ n, L.late = some n → AXPlan.Late XB L.onlineBatch.ann ZB n) →
    εB.UnitZero → L.SoundAtKT Rno wit εT εL εB →
    (L.recut XT XL XB ZB hK).SoundAtKT
      Rno (fun x y τ => wit x y (Tr.old XB τ)) (Err.recut XT εT) (Err.recut XL εL) (Err.recut XB εB)

/-- Blocks. -/
def soundKT_draws : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop)
      (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (εs : ℝ≥0∞) (lam : ℕ)
      (dr : L.Draws lam) (κ₀ : ℝ≥0∞),
    1 ≤ κ₀ → dr.Good κ₀ → L.SoundKT Rno wit εs →
    (L.draws dr).SoundKT Rno
      (fun x y τ => wit x y (Tr.push (Samplers.ofDraws _ dr.B) τ)) (κ₀ ^ dr.K * εs)

def propsKT_draws : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Ryes Rno : I → X → Wn → Prop)
      (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (M : LH.Nums) (lam n : ℕ)
      (dr : L.Draws lam) (κ₀ : ℝ≥0∞),
    1 ≤ κ₀ → dr.Good κ₀ → dr.TotLe n → L.PropsKT Ryes Rno wit M →
    (L.draws dr).PropsKT Ryes Rno (fun x y τ => wit x y (Tr.push (Samplers.ofDraws _ dr.B) τ))
      (M.pullB (κ₀ ^ dr.K) (κ₀ ^ n) L.maxBatchSize)

def soundKGT_draws : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop)
      (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (lam : ℕ) (dr : L.Draws lam)
      (κ₀ : ℝ≥0∞) (gT : GBits L.offline.shape) (gL : GBits L.link.shape)
      (gB : GBits L.onlineBatch.loc.shape) (c : ℝ≥0∞),
    1 ≤ κ₀ → dr.Good κ₀ → L.SoundKGT Rno wit gT gL gB c →
    (L.draws dr).SoundKGT Rno (fun x y τ => wit x y (Tr.push (Samplers.ofDraws _ dr.B) τ))
      (gT.pull (Samplers.ofDraws _ dr.T)) (gL.pull (Samplers.ofDraws _ dr.Lk))
      (gB.pull (Samplers.ofDraws _ dr.B)) (κ₀ ^ dr.K * c)

/-- Tests: for an inhabited type W of nonces, with the tests put in, "at most c counting the work"
gives knowledge soundness at c. -/
def grindSoundKGT : Prop :=
  ∀ (W : Type) [Inhabited W] (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop)
      (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (gT : GBits L.offline.shape)
      (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) (c : ℝ≥0∞),
    L.SoundKGT Rno wit gT gL gB c →
    (L.grind W gT gL gB).SoundKT Rno (fun x y τ => wit x y (Tr.strip gB τ)) c

/-- The door's lemma, wide. -/
def propsNoAccKT_drawsGrind : Prop :=
  ∀ (W : Type) [Inhabited W] (I X Wn : Type) (L : BatchProtocol I X) (Ryes Rno : I → X → Wn → Prop)
      (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (M : LH.Nums) (lam n : ℕ)
      (dr : L.Draws lam) (κ₀ : ℝ≥0∞) (gT : GBits L.offline.shape) (gL : GBits L.link.shape)
      (gB : GBits L.onlineBatch.loc.shape) (c : ℝ≥0∞),
    1 ≤ κ₀ → dr.Good κ₀ → dr.TotLe n → L.PropsKT Ryes Rno wit M → L.SoundKGT Rno wit gT gL gB c →
    (L.drawsGrind W dr gT gL gB).PropsNoAccKT Ryes Rno
      (fun x y τ =>
        wit x y
          (Tr.push (Samplers.ofDraws _ dr.B) (Tr.strip (gB.pull (Samplers.ofDraws _ dr.B)) τ)))
      { M.pullB (κ₀ ^ dr.K) (κ₀ ^ n) L.maxBatchSize with εs := κ₀ ^ dr.K * c }

/-- Cuts and joins. -/
def soundKT_recut : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop)
      (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (εs : ℝ≥0∞)
      (XT : XPlan L.offline.shape) (XL : XPlan L.link.shape) (XB : XPlan L.onlineBatch.loc.shape)
      (ZB : AXPlan XB L.onlineBatch.ann) (hK : AXPlan.Kinds XB L.onlineBatch.ann ZB),
    XT.OK → XL.OK → XB.OK → XT.NoChal → XL.NoChal → XB.NoChal → AXPlan.OK XB L.onlineBatch.ann ZB →
    0 < L.maxBatchSize → (∀ n, L.late = some n → AXPlan.Late XB L.onlineBatch.ann ZB n) → εs < 1 →
    L.SoundKT Rno wit εs →
    (L.recut XT XL XB ZB hK).SoundKT Rno (fun x y τ => wit x y (Tr.old XB τ)) εs

def propsKT_recut : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Ryes Rno : I → X → Wn → Prop)
      (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (M : LH.Nums)
      (XT : XPlan L.offline.shape) (XL : XPlan L.link.shape) (XB : XPlan L.onlineBatch.loc.shape)
      (ZB : AXPlan XB L.onlineBatch.ann) (hK : AXPlan.Kinds XB L.onlineBatch.ann ZB),
    XT.OK → XL.OK → XB.OK → XT.NoChal → XL.NoChal → XB.NoChal → AXPlan.OK XB L.onlineBatch.ann ZB →
    0 < L.maxBatchSize → (∀ n, L.late = some n → AXPlan.Late XB L.onlineBatch.ann ZB n) → M.εs < 1 →
    L.PropsKT Ryes Rno wit M →
    (L.recut XT XL XB ZB hK).PropsKT Ryes Rno (fun x y τ => wit x y (Tr.old XB τ)) M

def soundKGT_recut : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop)
      (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (gT : GBits L.offline.shape)
      (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) (c : ℝ≥0∞)
      (XT : XPlan L.offline.shape) (XL : XPlan L.link.shape) (XB : XPlan L.onlineBatch.loc.shape)
      (ZB : AXPlan XB L.onlineBatch.ann) (hK : AXPlan.Kinds XB L.onlineBatch.ann ZB),
    XT.OK → XL.OK → XB.OK → XT.NoChal → XL.NoChal → XB.NoChal → AXPlan.OK XB L.onlineBatch.ann ZB →
    0 < L.maxBatchSize → (∀ n, L.late = some n → AXPlan.Late XB L.onlineBatch.ann ZB n) → c < 1 → gT.UnitFree →
    gL.UnitFree → gB.UnitFree → L.SoundKGT Rno wit gT gL gB c →
    (L.recut XT XL XB ZB hK).SoundKGT
      Rno (fun x y τ => wit x y (Tr.old XB τ)) (gT.recut XT) (gL.recut XL) (gB.recut XB) c

/-- By parts, after cuts and joins. -/
def witOf_old : Prop :=
  ∀ (X W : Type) (E : ExtSpec) (s : Shape) (P : XPlan s) (w : WitP X E s W),
    P.OK → (fun x y (τ : Tr P.shape) => witOf w x y (Tr.old P τ)) = witOf (w.old P)

def blindFrom_old : Prop :=
  ∀ (X W : Type) (E : ExtSpec) (s : Shape) (P : XPlan s) (w : WitP X E s W) (j : ℕ),
    P.NoChal → w.BlindFrom j → (w.old P).BlindFrom (P.idx j)

/-- By parts, at the door with work: "blocks, then tests". -/
def witOf_door : Prop :=
  ∀ (Nn : Type) [Inhabited Nn] (X W : Type) (E : ExtSpec) (s : Shape) (σ : Samplers s)
      (g : GBits s) (w : WitP X E s W),
    (fun x y (τ : Tr ((s.pull σ).grind Nn (g.pull σ))) =>
        witOf w x y (Tr.push σ (Tr.strip (g.pull σ) τ))) =
      witOf ((w.push σ).strip (g.pull σ))

def blindFrom_door : Prop :=
  ∀ (Nn : Type) [Inhabited Nn] (X W : Type) (E : ExtSpec) (s : Shape) (σ : Samplers s) (g : GBits s)
      (w : WitP X E s W) (j : ℕ),
    w.BlindFrom j → ((w.push σ).strip (Nn := Nn) (g.pull σ)).BlindFrom j

end Spec

theorem soundAtKT_pull : Spec.soundAtKT_pull := fun _ X Wn L _ wit _ _ εB _ _ σB hT hL hB h =>
  ⟨h.sndT.pull hT, h.sndL.pull hL,
    sndBKT_pull X Wn _ L.onlineBatch σB hB L.maxBatchSize L.early L.late _ wit εB h.sndB⟩

theorem soundAtKT_draws : Spec.soundAtKT_draws := fun I X Wn L Rno wit εT εL εB _ _ _ hg h =>
  soundAtKT_pull I X Wn L Rno wit εT εL εB _ _ _ hg.1.fibS hg.2.1.fibS hg.2.2.fibS h

theorem grindSoundAtKT : Spec.grindSoundAtKT := fun W _ _ X Wn L _ wit gT gL gB _ _ εB h =>
  ⟨h.sndT.grind gT, h.sndL.grind gL,
    sndBKT_grind W X Wn _ L.onlineBatch gB L.maxBatchSize L.early L.late _ wit εB h.sndB⟩

theorem soundAtKT_recut :
    Spec.soundAtKT_recut := fun _ X Wn L _ wit _ _ εB XT XL XB ZB hK hB hZ hN hl hu h =>
  ⟨h.sndT.recut XT, h.sndL.recut XL,
    sndBKT_recut X Wn _ L.onlineBatch XB ZB hB hZ hK L.maxBatchSize hN L.early L.late hl _ wit εB hu h.sndB⟩

theorem soundKGT_draws : Spec.soundKGT_draws := by
  rintro I X Wn L Rno wit lam dr κ₀ gT gL gB c h1 hg ⟨εT, εL, εB, hA, eT, eL, eB⟩
  exact ⟨_, _, _,
    soundAtKT_draws I X Wn L Rno wit εT εL εB lam dr κ₀ hg hA,
    eT.pull (drawsGood lam κ₀ h1 _ dr.T hg.1 dr.K _ (le_max_left _ _) le_rfl),
    eL.pull (drawsGood lam κ₀ h1 _ dr.Lk hg.2.1 dr.K _
        (le_trans (le_max_left _ _) (le_max_right _ _)) le_rfl),
    eB.pull (drawsGood lam κ₀ h1 _ dr.B hg.2.2 dr.K _
        (le_trans (le_max_right _ _) (le_max_right _ _)) le_rfl)⟩

theorem soundKT_draws : Spec.soundKT_draws := by
  intro I X Wn L Rno wit εs lam dr κ₀ h1 hg h
  obtain ⟨εT, εL, εB, hA, bT, bL, bB⟩ := (soundKT_iff_at I X Wn L Rno wit εs).1 h
  exact (soundKT_iff_at I X Wn (L.draws dr) Rno _ _).2
    ⟨_, _, _,
      soundAtKT_draws I X Wn L Rno wit εT εL εB lam dr κ₀ hg hA,
      bT.pull (drawsGood lam κ₀ h1 _ dr.T hg.1 dr.K _ (le_max_left _ _) le_rfl),
      bL.pull (drawsGood lam κ₀ h1 _ dr.Lk hg.2.1 dr.K _
          (le_trans (le_max_left _ _) (le_max_right _ _)) le_rfl),
      bB.pull (drawsGood lam κ₀ h1 _ dr.B hg.2.2 dr.K _
          (le_trans (le_max_right _ _) (le_max_right _ _)) le_rfl)⟩

theorem propsKT_draws : Spec.propsKT_draws := by
  intro I X Wn L Ryes Rno wit M lam n dr κ₀ h1 hg hn h
  exact ⟨drawsPropsB I X L _ _ M lam n dr κ₀ h1 hg hn h.props,
    soundKT_draws I X Wn L Rno wit M.εs lam dr κ₀ h1 hg h.soundKT⟩

theorem grindSoundKGT : Spec.grindSoundKGT := by
  rintro W _ I X Wn L Rno wit gT gL gB c ⟨εT, εL, εB, hA, bT, bL, bB⟩
  exact (soundKT_iff_at I X Wn (L.grind W gT gL gB) Rno _ c).2
    ⟨_, _, _, grindSoundAtKT W I X Wn L Rno wit gT gL gB εT εL εB hA,
      (Err.below_grind_iff gT εT c).2 bT, (Err.below_grind_iff gL εL c).2 bL,
      (Err.below_grind_iff gB εB c).2 bB⟩

theorem propsNoAccKT_drawsGrind : Spec.propsNoAccKT_drawsGrind := by
  intro W _ I X Wn L Ryes Rno wit M lam n dr κ₀ gT gL gB c h1 hg hn h hS
  have hK := grindSoundKGT W I X Wn (L.draws dr) Rno _ _ _ _ _
    (soundKGT_draws I X Wn L Rno wit lam dr κ₀ gT gL gB c h1 hg hS)
  exact ⟨grindDrawsProps W h1 hg hn h.props (sound_of_soundKT I X Wn _ Rno _ _ hK), hK⟩

theorem soundKT_recut : Spec.soundKT_recut := by
  intro I X Wn L Rno wit εs XT XL XB ZB hK hT hL hB nT nL nB hZ hN hl h1 h
  obtain ⟨εT, εL, εB, hA, bT, bL, bB⟩ := (soundKT_iff_at I X Wn L Rno wit εs).1 h
  exact (soundKT_iff_at I X Wn (L.recut XT XL XB ZB hK) Rno _ εs).2
    ⟨_, _, _,
      soundAtKT_recut I X Wn L Rno wit εT εL εB XT XL XB ZB hK hB hZ hN hl
        (BatchJoin.unitZero_of_below h1 bB) hA,
      below_recut _ XT hT nT εT εs (BatchJoin.unitZero_of_below h1 bT) bT,
      below_recut _ XL hL nL εL εs (BatchJoin.unitZero_of_below h1 bL) bL,
      below_recut _ XB hB nB εB εs (BatchJoin.unitZero_of_below h1 bB) bB⟩

theorem propsKT_recut : Spec.propsKT_recut := by
  intro I X Wn L Ryes Rno wit M XT XL XB ZB hK hT hL hB nT nL nB hZ hN hl h1 h
  have hS :=
    soundKT_recut I X Wn L Rno wit M.εs XT XL XB ZB hK hT hL hB nT nL nB hZ hN hl h1 h.soundKT
  exact ⟨recutPropsB I X L _ _ M XT XL XB ZB hK M.εs hT hL hB hZ
      h.props (sound_of_soundKT _ _ _ _ _ _ _ hS),
    hS⟩

theorem soundKGT_recut : Spec.soundKGT_recut := by
  rintro I X Wn L Rno wit gT gL gB c XT XL XB ZB hK hT hL hB nT nL nB hZ hN hl hc uT uL
    uB ⟨εT, εL, εB, hA, bT, bL, bB⟩
  have zT := unitZero_of_belowG _ gT εT c hc uT bT
  have zL := unitZero_of_belowG _ gL εL c hc uL bL
  have zB := unitZero_of_belowG _ gB εB c hc uB bB
  exact ⟨_, _, _,
    soundAtKT_recut I X Wn L Rno wit εT εL εB XT XL XB ZB hK hB hZ hN hl zB hA,
    belowG_recut _ XT hT nT gT εT c zT bT,
    belowG_recut _ XL hL nL gL εL c zL bL,
    belowG_recut _ XB hB nB gB εB c zB bB⟩

theorem witOf_old : Spec.witOf_old := by
  intro X W E s P w hP
  funext x y τ
  show w x y (Tr.old P τ).read (Tr.old P τ).plains (Tr.old P τ).rho =
    w x y (Orcs.old P τ.read) (Plains.old P τ.plains) (Rho.old P τ.rho)
  rw [Tr.plains_old, Tr.rho_old, read_old s P hP]

theorem blindFrom_old : Spec.blindFrom_old := fun _ _ _ s P _ j hn h x y _ _ ρ ρ' hρ =>
  h x y _ _ _ _ (agreeTo_old s P hn j ρ ρ' hρ)

theorem witOf_door : Spec.witOf_door := by
  intro Nn _ X W E s σ g w
  have e1 := witOf_push X W E s σ w
  have e2 := witOf_strip Nn X W E (s.pull σ) (g.pull σ) (w.push σ)
  rw [← e2, ← e1]

theorem blindFrom_door : Spec.blindFrom_door := fun Nn _ X W E s σ g w j h =>
  blindFrom_strip Nn X W E (s.pull σ) (g.pull σ) (w.push σ) j (blindFrom_push X W E s σ w j h)

end Iop
