-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Glue.lean: the compiler's theorem for languages, from `L.Props` and the side conditions.

Statements and proofs; an assembly, no mathematics.
The plainest theorem of Compile/Batch with batches (`mainBatchKEGrWithBOf`,
Compile/Batch/PubProgMainBGr.lean; scheme `argBKE`: links in the key, fresh coins, no seed, no
pruned paths) has its hypotheses in the form made for rounds with tests. Here they are met at the
generic wires, which have no tests: no proof of work.

Main names:
  `BatchProtocol.Props.noAcc`, `grFitB_of_ok`: two lemmas on (Acc) (the fields accT, accL, accB of
    `BatchProtocol.Complete`, Iop/Batch.lean).
  (That the hiding properties give three good simulators is Compile/Batch/Life.lean: `exists_sims`.)
  `Spec.languageTop`, the statement: under the hypotheses of its statement, for every interface L
    with `L.Props`, verifier messages made from λ-bit blocks by any samplers that obey their law,
    and the generic wires, the scheme `argBKE` is, in the sense of ZKCP/Gen.lean, a doubly
    zero-knowledge commit-and-prove argument for the pair of languages (Ryes, Rno), with the
    extractor `extractorBK`, the compiler's simulator around simulators of the three IOPs, and the
    bounds `alphaBG`, `epsB`, `zetaBGen` with the hash terms for one budget.
  `Spec.languageTopWith`: the same for given simulators of the three IOPs that are good.


Limits: the relations have no witness here (the witness type is Unit): index binding is soundness
for the language of Rno, with an extracted index, and no witness is extracted. Knowledge is
CompileK/KnowBinding.lean's. The simulators of the three IOPs are not named in `languageTop`: they
exist by `L.Props`.

Terms: lean/GLOSSARY.md.
-/
import Compile.Batch.PubProgMainBGr
import Compile.Batch.HopTot
import Compile.Batch.GrOK
import Compile.Batch.Life
import Iop.BatchOne
import Top.ProgDraw

set_option autoImplicit false

namespace Iop

/-- All properties give the properties without (Acc). -/
theorem BatchProtocol.Props.noAcc {I X : Type} {L : BatchProtocol I X} {Ryes Rno : I → X → Prop}
    {M : LH.Nums} (h : L.Props Ryes Rno M) : L.PropsNoAcc Ryes Rno M where
  sub := h.sub
  wired := h.wired
  sound := h.sound
  reads := h.reads
  hidden := h.hidden
  prT := h.complete.prT
  prL := h.complete.prL
  prB := h.complete.prB
  localT := h.localT
  localL := h.localL
  localB := h.localB
  cohB := h.cohB
  pointT := h.pointT
  pointL := h.pointL
  pointB := h.pointB

end Iop

namespace Compile.Batch
open Iop Rom ZKCP Top.Batch Top.ProgDraw
open Compile.BatchLife (Sims)
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- At a wire without tests (`W.OK`), (Acc) and locality give what the compiler's theorem asks on
tests. -/
theorem grFitB_of_ok {W : QueryLayout lam L} (hW : W.OK) {Ryes : I → X → Prop}
    (aT : L.honestOfflineProver.Acc fun _ _ => True) (aL : L.honestLinkProver.Acc fun _ _ => True)
    (aB : L.honestOnlineBatchProver.Acc fun w x => Ryes w.1 x) (lT : L.offline.IsLocal)
    (lL : L.link.IsLocal) (lB : L.onlineBatch.loc.IsLocal) : GrFitB W Ryes where
  T := fit_ok _ W.T _ hW.T.sh lT ((BatchOne.acc_one_iff L.honestOfflineProver _).2 aT)
  Lk := fit_ok _ W.Lk _ hW.Lk.sh lL ((BatchOne.acc_one_iff L.honestLinkProver _).2 aL)
  B := fit_ok L.honestOnlineBatchProver W.B _ hW.B.sh lB aB

namespace Spec

/-- The compiler's theorem for languages at given good simulators of the three IOPs. (not all
hypotheses are named here: see the statement below) -/
def languageTopWith : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (pT : L.offline.shape.IsPoint) (pL : L.link.shape.IsPoint)
      (pB : L.onlineBatch.loc.shape.IsPoint) (z : L.Symbol) (no : OpenNums) (dr : L.Draws lam)
      (ax : L.Aux pT pL pB) (p : Params) (i₀ : I) (Ryes Rno : I → X → Prop) (M : LH.Nums)
      (κ₀ : ℝ≥0∞) (n : ℕ) (h : L.Props Ryes Rno M),
    1 ≤ κ₀ → dr.Good κ₀ → dr.TotLe n → L.Opens no → L.maxBatchSize = 2 ^ ax.depthReq →
    L.onlineBatch.ann.Fmt → Budget p (numsDraw lam L dr M κ₀ n) →
    ∀ Sm : Sims L, Sm.Good Ryes M.zT M.zL M.zO →
      Gen.IsZKCPArgWith (relPair Ryes Rno h.sub)
        (argBKE (WBd lam L pT pL pB z no dr ax) (WPBd lam L pT pL pB dr ax) p) L.maxBatchSize
        (extractorBK (WBd lam L pT pL pB z no dr ax))
        (simBKGr (WBd lam L pT pL pB z no dr ax) p (simsD lam L dr Sm) i₀)
        (alphaBG (WBd lam L pT pL pB z no dr ax) (numsDraw lam L dr M κ₀ n))
        (epsB (WBd lam L pT pL pB z no dr ax) (numsDraw lam L dr M κ₀ n))
        (zetaBGen (LBd lam L dr) p (numsDraw lam L dr M κ₀ n)
          (hashTermsBGTot (WBd lam L pT pL pB z no dr ax) p))

/-- The compiler's theorem for languages, from `L.Props` and the side conditions. -/
def languageTop : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (pT : L.offline.shape.IsPoint) (pL : L.link.shape.IsPoint)
      (pB : L.onlineBatch.loc.shape.IsPoint) (z : L.Symbol) (no : OpenNums) (dr : L.Draws lam)
      (ax : L.Aux pT pL pB) (p : Params) (i₀ : I) (Ryes Rno : I → X → Prop) (M : LH.Nums)
      (κ₀ : ℝ≥0∞) (n : ℕ) (h : L.Props Ryes Rno M),
    1 ≤ κ₀ → dr.Good κ₀ → dr.TotLe n → L.Opens no → L.maxBatchSize = 2 ^ ax.depthReq →
    L.onlineBatch.ann.Fmt → Budget p (numsDraw lam L dr M κ₀ n) →
    ∃ Sm : Sims L,
      Sm.Good Ryes M.zT M.zL M.zO ∧
      Gen.IsZKCPArgWith (relPair Ryes Rno h.sub)
        (argBKE (WBd lam L pT pL pB z no dr ax) (WPBd lam L pT pL pB dr ax) p) L.maxBatchSize
        (extractorBK (WBd lam L pT pL pB z no dr ax))
        (simBKGr (WBd lam L pT pL pB z no dr ax) p (simsD lam L dr Sm) i₀)
        (alphaBG (WBd lam L pT pL pB z no dr ax) (numsDraw lam L dr M κ₀ n))
        (epsB (WBd lam L pT pL pB z no dr ax) (numsDraw lam L dr M κ₀ n))
        (zetaBGen (LBd lam L dr) p (numsDraw lam L dr M κ₀ n)
          (hashTermsBGTot (WBd lam L pT pL pB z no dr ax) p))

end Spec

theorem languageTopWith : Spec.languageTopWith := by
  intro I X lam L pT pL pB z no dr ax p i₀ Ryes Rno M κ₀ n h h1 hg hr ho hN hF hBu Sm hS
  have hP : (LBd lam L dr).Props Ryes Rno (numsDraw lam L dr M κ₀ n) :=
    drawsPropsB I X L Ryes Rno M lam n dr κ₀ h1 hg hr h
  have hW := wireBDOK I X lam L pT pL pB z no dr ax ho hN
  exact mainBatchKEGrWithBOf (WBd lam L pT pL pB z no dr ax) (WPBd lam L pT pL pB dr ax) p Ryes Rno
    (numsDraw lam L dr M κ₀ n) hP.noAcc hW.1.toG
    (grFitB_of_ok hW.1 hP.complete.accT hP.complete.accL hP.complete.accB
      hP.localT hP.localL hP.localB)
    hW.2 (hF.pull _) hBu (simsD lam L dr Sm)
    (simsD_good lam L dr h1 hg hr (by rw [hN]; exact Nat.two_pow_pos _) hS) i₀ L.maxBatchSize le_rfl
    (hopU_of_hopB le_rfl (hopB_total (WBd lam L pT pL pB z no dr ax) p))

theorem languageTop : Spec.languageTop := by
  intro I X lam L pT pL pB z no dr ax p i₀ Ryes Rno M κ₀ n h h1 hg hr ho hN hF hBu
  obtain ⟨Sm, hS⟩ := Compile.BatchLife.exists_sims h.hidden
  exact ⟨Sm, hS,
    languageTopWith I X lam L pT pL pB z no dr ax p i₀ Ryes Rno M κ₀ n h h1
      hg hr ho hN hF hBu Sm hS⟩

end Compile.Batch
