-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/ChallUHopR.lean: the state after a reveal (`Step.reveal`, Rom/Defer.lean, which also
tells mode R), written out. Generic in the family of oracles.

  `revealSt`, `run_reveal`  the state after a reveal
  `runLazy_bind_pure'`  a lazy run of a computation whose result is mapped by a function

Limits: this file does not prove that a game is mode R of a challenger.
-/
import Compile.Batch.ChallU
import Rom.Bridge

noncomputable section

namespace Compile.Batch
open Iop Rom ZKCP Prob
open Compile.GlueB (GCall GAdm)
open Compile.Life2
  (virt viewVals chall_reply runLazy_bind_pure run_fresh0 run_bind map_fst_call map_fst_query
    viewVals_dummy run_false_virt run_false_eq_erase vals_prefix runLazy_query releaseAll_false)

namespace HopD

/-! ## Generic in the family of oracles -/

section Generic
variable {S : OSpec} {sp : Split S} {β γ : Type}

/-- the state after a reveal of ts -/
def revealSt (m : Bool) (d : DSt S) (ts : List Tok) : DSt S :=
  { d with
    table := (releaseAll m (d.shown ++ ts) d.evs d.table).2, shown := d.shown ++ ts,
    evs := (releaseAll m (d.shown ++ ts) d.evs d.table).1,
    viol := d.viol || !closedUnder (d.shown ++ ts) (releaseAll m (d.shown ++ ts) d.evs d.table).1 ||
        ts.any (fun u => decide (d.vals.length ≤ u)) }

theorem run_reveal (m : Bool) (ts : List Tok) (k : List Bits → Step S sp β) (d : DSt S) :
    (Step.reveal ts k).run m d = (k (ts.map d.val)).run m (revealSt m d ts) := rfl


theorem runLazy_bind_pure' (c : OComp S β) (f : β → γ) (T : Table S) :
    (c.bind fun o => OComp.pure (f o)).runLazy T = (c.runLazy T).map fun y => (f y.1, y.2) :=
  runLazy_bind_pure c f T

end Generic

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
  (i : I) (pp : PProg lam L W.K)

end HopD

open HopD

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

end Compile.Batch
