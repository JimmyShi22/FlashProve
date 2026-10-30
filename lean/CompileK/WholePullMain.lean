-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/WholePullMain.lean: the hypotheses of the compiler, with honest-verifier zero knowledge of
the whole object as its zero-knowledge hypothesis on the protocol (its other hypotheses: under Main
names).

Definitions, statements and proofs.
The compiler asks of the interface the bundle `BatchProtocol.PropsK`, in which zero
knowledge stands run by run: exact simulators of single runs (`BatchProtocol.Hiding`), the numbers of
positions read and "an encoded index hides b positions" (`BatchProtocol.Reads`); and of the numbers the
budget. Here these three are replaced by one hypothesis, `HVZKWhole` (Hiop/Whole.lean) of the
interface L itself (before verifier messages are made from blocks), at the bounds that the scheme
needs (`DataK.bounds`; `starBounds`, CompileK/PrivacyWhole.lean).

Main names:
  `BatchProtocol.PropsKW`: all properties of the interface with a witness but for zero knowledge: R_yes ⊆
    R_no on languages, Wired, round-by-round knowledge soundness (`BatchProtocol.SoundK`,
    Hiop/Interface.lean), completeness, locality, coherence, point oracles. Of the numbers M only
    εs, pT, pL, pO are read.
  `FitKW`: the side conditions of CompileK/Main.lean's `FitK` without the budget; and κ₀ ≠ ∞.
  `zWhole D κ₀ n z`: the error after the blocks: factor (one factor κ₀^n for the offline run and
    for each link, (κ₀^n)^maxBatchSize for each of the leaves · s1 sessions) times z.















Why `BatchProtocol.PropsKW.fill`: `propsK_draws`
(CompileK/KnowPull.lean) and the theorem of Compile/Batch on completeness
(`completeBatchUGr`) take the whole bundle of properties.
The bundle is filled with the hiding properties that every interface has
(`hiding_trivial`: simulators with error 1; `reads_trivial`: an encoded index hides 0 positions,
and a run reads at most all positions); α and ε do not read these numbers.

Limits: two privacy bounds stand side by side, and neither implies the other: `zetaBGen`
(run by run: n · maxBatchSize · zO for n batches) and `zetaWhole` (the error z of the
whole object at bounds that allow leaves · s1 sessions, paid at once, whatever n is, and multiplied
by the factor of all runs). The simulator of the hypothesis is the named one, simWhole L Sm i₀, for
a triple Sm of functions of which nothing else is asked. The limits named in the headers of
CompileK/Main.lean, CompileK/PrivacyWhole.lean and CompileK/WholePull.lean hold here too.

Terms: lean/GLOSSARY.md.
-/
import CompileK.Main
import CompileK.Glue
import CompileK.GenWitProofs
import CompileK.KnowPull
import CompileK.KnowLocal
import CompileK.KnowBinding
import CompileK.KnowBindingUp
import Top.Extraction
import ZKCP.ExtractionMaps
import CompileK.PrivacyWhole
import CompileK.WholePull
import Hiop.InterfaceProofs

set_option autoImplicit false

noncomputable section

namespace Iop
open Prob
open scoped ENNReal

variable {I X W : Type}

/-- two laws on a type with at most one element are equal -/
theorem pmf_subsingleton {α : Type} [Subsingleton α] (p q : PMF α) : p = q := by
  have h : ∀ (r : PMF α) (a : α), r a = 1 := fun r a => by
    have := r.tsum_coe
    rwa [tsum_eq_single a fun b hb => absurd (Subsingleton.elim b a) hb] at this
  exact PMF.ext fun a => by rw [h p a, h q a]

/-- Every interface: an encoded index hides 0 positions, and a run reads at most all positions. -/
theorem BatchProtocol.reads_trivial (L : BatchProtocol I X) : L.Reads 0 L.wordLength (2 * L.wordLength) (2 * L.wordLength) L.wordLength where
  cntT := fun _ _ => (Finset.card_le_univ _).trans (le_of_eq (Fintype.card_fin _))
  cntLp := fun _ _ =>
    (Finset.card_filter_le _ _).trans ((Finset.card_le_univ _).trans (le_of_eq (by simp [two_mul])))
  cntLc := fun _ _ =>
    (Finset.card_filter_le _ _).trans ((Finset.card_le_univ _).trans (le_of_eq (by simp [two_mul])))
  cntB := fun _ _ => (Finset.card_le_univ _).trans (le_of_eq (Fintype.card_fin _))
  hidE := fun S hS _ _ => by
    obtain rfl := Finset.card_eq_zero.1 (Nat.le_zero.1 hS)
    exact pmf_subsingleton _ _

/-- Every interface: simulators with error 1. -/
theorem BatchProtocol.hiding_trivial (L : BatchProtocol I X) (Ryes : I → X → Prop) : L.Hiding Ryes 1 1 1 where
  hidT := ⟨fun _ _ _ => PMF.pure none, fun _ _ _ => pr_le_one _ _⟩
  hidL := ⟨fun _ _ _ => PMF.pure none, fun _ _ _ => pr_le_one _ _⟩
  hidB := ⟨fun _ _ _ _ => PMF.pure fun _ => none, fun w x _ J xs _ => by
    rcases J.eq_empty_or_nonempty with rfl | hJ
    · refine le_trans (le_of_eq ?_) (zero_le _)
      rw [show {ρ | L.honestOnlineBatchProver.output w x ρ ∅ ≠ PMF.pure fun _ => none} = (∅ : Set _)
          from Set.eq_empty_of_forall_notMem fun ρ h => h (pmf_subsingleton _ _)]
      exact pr_empty _
    · refine (pr_le_one _ _).trans ?_
      rw [mul_one]
      exact_mod_cast hJ.card_pos⟩

/-- All properties with a witness, but for zero knowledge. Of M only εs, pT, pL, pO are read. -/
structure BatchProtocol.PropsKW (L : BatchProtocol I X) (Ryes Rno : I → X → W → Prop)
    (wit : X → Orcs L.onlineBatch.loc.shape → W) (M : LH.Nums) : Prop where
  sub      : ∀ i x, (∃ w, Ryes i x w) → ∃ w, Rno i x w
  wired    : L.Wired
  soundK   : L.SoundK Rno wit M.εs
  complete : L.Complete (fun i x => ∃ w, Ryes i x w) M.pT M.pL M.pO
  localT   : L.offline.IsLocal
  localL   : L.link.IsLocal
  localB   : L.onlineBatch.loc.IsLocal
  cohB     : L.onlineBatch.ann.Coherent
  pointT   : Nonempty L.offline.shape.IsPoint
  pointL   : Nonempty L.link.shape.IsPoint
  pointB   : Nonempty L.onlineBatch.loc.shape.IsPoint

theorem BatchProtocol.PropsK.toKW {L : BatchProtocol I X} {Ryes Rno : I → X → W → Prop}
    {wit : X → Orcs L.onlineBatch.loc.shape → W} {M : LH.Nums} (h : L.PropsK Ryes Rno wit M) :
    L.PropsKW Ryes Rno wit M :=
  ⟨h.props.sub, h.props.wired, h.soundK, h.props.complete, h.props.localT, h.props.localL,
    h.props.localB, h.props.cohB, h.props.pointT, h.props.pointL, h.props.pointB⟩

/-- the numbers M with the hiding numbers that every interface has -/
def LH.Nums.noZK (M : LH.Nums) (n : ℕ) : LH.Nums :=
  { M with b := 0, qT := n, qpar := 2 * n, qch := 2 * n, qon := n, zT := 1, zL := 1, zO := 1 }

theorem BatchProtocol.PropsKW.fill {L : BatchProtocol I X} {Ryes Rno : I → X → W → Prop}
    {wit : X → Orcs L.onlineBatch.loc.shape → W} {M : LH.Nums} (h : L.PropsKW Ryes Rno wit M) :
    L.PropsK Ryes Rno wit (M.noZK L.wordLength) :=
  ⟨⟨h.sub, h.wired, sound_of_soundK I X W L Rno wit M.εs h.soundK, L.reads_trivial,
      L.hiding_trivial _, h.complete, h.localT, h.localL, h.localB, h.cohB,
      h.pointT, h.pointL, h.pointB⟩,
    h.soundK⟩

end Iop

namespace Compile.Batch
open Iop Rom ZKCP Top.Batch Top.ProgDraw Hiop
open Compile.BatchLife (Sims)
open scoped ENNReal

variable {I X : Type} {L₀ : BatchProtocol I X} {lam : ℕ} (D : DataK L₀ lam)

/-- Conditions on numbers and formats: FitK without the budget; the bias of a block is finite. -/
structure FitKW (κ₀ : ℝ≥0∞) (n : ℕ) : Prop where
  one_le : 1 ≤ κ₀
  ne_top : κ₀ ≠ ⊤
  good   : D.dr.Good κ₀
  totLe  : D.dr.TotLe n
  opens  : L₀.Opens D.no
  slots  : L₀.maxBatchSize = 2 ^ D.ax.depthReq
  fmt    : L₀.onlineBatch.ann.Fmt

theorem FitK.toKW {D : DataK L₀ lam} {M : LH.Nums} {κ₀ : ℝ≥0∞} {n : ℕ}
    (h : FitK D M κ₀ n) (ht : κ₀ ≠ ⊤) : FitKW D κ₀ n :=
  ⟨h.one_le, ht, h.good, h.totLe, h.opens, h.slots, h.fmt⟩

/-- the bounds on the environment that the scheme needs -/
abbrev DataK.bounds : Bounds := Hiop.Star.starBounds L₀ D.p.leaves D.p.s1

/-- the error of the whole object after the verifier messages are made from blocks -/
def zWhole (κ₀ : ℝ≥0∞) (n : ℕ) (z : ℝ≥0∞) : ℝ≥0∞ := Hiop.Pull.factor D.bounds L₀.maxBatchSize (κ₀ ^ n) (κ₀ ^ n) (κ₀ ^ n) * z

end Compile.Batch
