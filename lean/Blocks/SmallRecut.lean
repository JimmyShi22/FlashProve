-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/SmallRecut.lean: `Small D` for the errors after rounds are cut and joined (`Err.recut`).

`Small D ε` (Blocks/Small.lean): every count of the list ε, times D, is at most the number of values
of the verifier message. (Words of this library: lean/GLOSSARY.md.)
 * `small_recut_keepAll`, `small_recut_app`, `small_recut_thenX`: plans that are composed
   (Iop/Recut.lean, Iop/RecutKit.lean).
 * `props_recut`: for any interface (`BatchProtocol`): from all properties (`BatchProtocol.Props`) before the pass,
   soundness for three explicit lists of errors (Iop/SoundAt.lean) whose images under `Err.recut`
   satisfy `Small D`, and the further hypotheses in the statement: all properties afterwards, with
   εs = 1/D. All other numbers are the old ones.
Limit: nothing at concrete parameters.
-/
import Blocks.SmallJoin
import Iop.RecutKit
import Iop.BatchRecutProofs

set_option autoImplicit false

namespace Blocks
open Iop
open scoped ENNReal

theorem small_recut_keepAll (D : ℕ) :
    ∀ {s : Shape} (ε : Err s), Small D ε → Small D (Err.recut (XPlan.keepAll s) ε)
  | [], _, _ => trivial
  | _ :: _, (_, ε), h => ⟨h.1, small_recut_keepAll D ε h.2⟩

theorem small_recut_app (D : ℕ) {s t : Shape} (P : XPlan s) (Q : XPlan t)
    (b : Err t) (hb : Small D (Err.recut Q b)) :
    ∀ a : Err s, Small D (Err.recut P a) → Small D (Err.recut (XPlan.app P Q) (Err.app a b)) := by
  induction P with
  | nil => intro _ _; exact hb
  | keep r P ih => exact fun a h => ⟨h.1, ih a.2 h.2⟩
  | cut c P ih => exact fun a h => ⟨h.1, ih a h.2⟩
  | msg r1 r2 u P ih => exact fun a h => ih (a.1 * Fintype.card r2.Chal + Fintype.card r1.Chal * a.2.1, a.2.2) h
  | chal r1 r2 np P ih => exact fun a h => ih (a.1 * Fintype.card r2.Chal + Fintype.card r1.Chal * a.2.1, a.2.2) h

/-- The first pieces of a chain of cuts have the error 0. -/
theorem small_recut_thenX (D : ℕ) {r : Round} (p : RPlan r) {s : Shape} (X : XPlan (p.last :: s))
    (ε : ℕ × Err s) (h : Small D (Err.recut X (show Err (p.last :: s) from ε))) :
    Small D (Err.recut (p.thenX X) (show Err (r :: s) from ε)) := by
  induction p with
  | keep r => exact h
  | cut c rest ih => exact ⟨by rw [Nat.zero_mul]; exact Nat.zero_le _, ih X h⟩


/-- Rounds cut and joined in one pass, for any interface. (not all hypotheses are named here: see
the statement below) -/
theorem props_recut {I X : Type} {L : BatchProtocol I X} {Ryes Rno : I → X → Prop} {M : LH.Nums}
    {εT : Err L.offline.shape} {εL : Err L.link.shape} {εB : Err L.onlineBatch.loc.shape}
    {XT : XPlan L.offline.shape} {XL : XPlan L.link.shape} {XB : XPlan L.onlineBatch.loc.shape}
    {ZB : AXPlan XB L.onlineBatch.ann} (hK : AXPlan.Kinds XB L.onlineBatch.ann ZB) (hP : L.Props Ryes Rno M)
    (hS : L.SoundAt Rno εT εL εB) (xT : XT.OK) (xL : XL.OK) (xB : XB.OK)
    (hZ : AXPlan.OK XB L.onlineBatch.ann ZB) (hN : 0 < L.maxBatchSize) (hU : εB.UnitZero)
    (hl : ∀ n, L.late = some n → AXPlan.Late XB L.onlineBatch.ann ZB n) {D : ℕ} (hD : 0 < D)
    (sT : Small D (Err.recut XT εT)) (sL : Small D (Err.recut XL εL))
    (sB : Small D (Err.recut XB εB)) :
    (L.recut XT XL XB ZB hK).Props Ryes Rno { M with εs := (D : ℝ≥0∞)⁻¹ } :=
  recutPropsB I X L Ryes Rno M XT XL XB ZB hK _ xT xL xB hZ hP
    ((hS.recut hK xB hZ hN hU hl).sound
      (below_of_small hD sT) (below_of_small hD sL) (below_of_small hD sB))

end Blocks
