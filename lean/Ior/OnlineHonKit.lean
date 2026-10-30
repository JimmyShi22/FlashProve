-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/OnlineHonKit.lean: tools for the honest side of "an IOR in every slot, then a batch IOP"
(Ior/Batch.lean: `online`, `onlineHonest`).

In standard terms: lemmas on the honest prover of a composition: an interactive oracle reduction
run for each instance of a batch, then an interactive oracle proof for the whole batch.

Lemmas only, but for the definition `backB`; the theorems are in Ior/OnlineHon.lean.

What a slot is: the head of Ior/OnlineHon.lean.

 1. The verifier's randomness after a first part of local rounds.
 2. One slot of the composed honest side: its withheld set is "the first part is withheld by F's
    honest side, or the second by Q's" (`mem_withheld`); its run is F's run followed by the run of
    Q's slot on the explicit part and the slot's witness that F's prover hands on, with `sh w` for
    the shared part (`run_one`).
 3. A law over uniform coins from finite non-empty sets (shared, one pair for each slot): draw the
    first components of all slots; if, given these, the law over the rest is a kernel of functions
    of the single first components in J, then the whole law is "independent draws for the slots of
    J, then the kernel" (`law_split`).

Limits: views and simulators are not here (Ior/OnlineHonView.lean, Ior/OnlineHon.lean).

Terms: lean/GLOSSARY.md.
-/
import Ior.Batch
import Blocks.Batch.ProbPi
import Iop.BatchUnif
import Prob.LawKit

set_option autoImplicit false

namespace Iop
namespace OnlineHon
open Prob Prob.Indep
open scoped ENNReal

/-! ## 1. The verifier's randomness of the second part -/

theorem back_lo :
    ∀ (s : Shape) {t : Shape} (A' : RoundSplits t) (ρ : Rho (s ++ t)),
      RhoLo.back s (Rho.lo (RoundSplits.app (RoundSplits.const (RAnn.ofSlot .lo) s) A') ρ) =
        Rho.lo A' (Rho.snd (s := s) ρ)
  | [], _, _, _ => rfl
  | _ :: s, _, A', (_, ρ) => back_lo s A' ρ

theorem back_sh :
    ∀ (s : Shape) {t : Shape} (A' : RoundSplits t) (ρ : Rho (s ++ t)),
      RhoSh.back s (Rho.sh (RoundSplits.app (RoundSplits.const (RAnn.ofSlot .lo) s) A') ρ) =
        Rho.sh A' (Rho.snd (s := s) ρ)
  | [], _, _, _ => rfl
  | _ :: s, _, A', (_, ρ) => back_sh s A' ρ

/-- The verifier messages of the second part, for the whole batch. -/
def backB {N : ℕ} :
    (s : Shape) → {t : Shape} → {A' : RoundSplits t} →
    BRho N (s ++ t) (RoundSplits.app (RoundSplits.const (RAnn.ofSlot .lo) s) A') → BRho N t A'
  | [], _, _, ρ => ρ
  | _ :: s, _, _, (_, ρ) => backB s ρ

theorem slot_backB {N : ℕ} (j : Fin N) :
    ∀ (s : Shape) {t : Shape} {A' : RoundSplits t}
        (ρ : BRho N (s ++ t) (RoundSplits.app (RoundSplits.const (RAnn.ofSlot .lo) s) A')),
      (backB s ρ).slot j = Rho.snd (s := s) (ρ.slot j)
  | [], _, _, _ => rfl
  | _ :: s, _, _, (_, ρ) => slot_backB j s ρ

/-! ## 2. One slot of the composed honest side -/

section Slot
variable {X Xl Wt WA W0 Wj : Type} {E0 Ej : ExtSpec} (F : IOR X E0 Xl (E0.prod Ej))
  (Q : BIOP Xl (E0.prod Ej)) (HF : F.Honest WA (W0 × Wj)) (HQ : Q.Honest W0 Wj) (ext : Wt → E0.Str)
  (sh : Wt → W0) (inp : Wt → X → WA)

theorem mem_withheld (w : Wt) (x : X) (ρ : Rho (F.shape ++ Q.ior.shape)) :
    ρ ∈ (onlineHonest F Q HF HQ ext sh inp).one.withheld w x ↔
    Rho.fst ρ ∈ HF.withheld (inp w x) x ∨ Rho.snd (s := F.shape) ρ ∈ HQ.withheld := by
  show ((RhoLo.front F.shape (A' := Q.ann)
              (Rho.lo (RoundSplits.app (RoundSplits.const (RAnn.ofSlot .lo) F.shape) Q.ann) ρ) ∈ HF.Bad ∨
          RhoLo.back F.shape (A' := Q.ann)
              (Rho.lo (RoundSplits.app (RoundSplits.const (RAnn.ofSlot .lo) F.shape) Q.ann) ρ) ∈ HQ.Bad) ∨
        HQ.stop0 (RhoSh.back F.shape (A' := Q.ann)
              (Rho.sh (RoundSplits.app (RoundSplits.const (RAnn.ofSlot .lo) F.shape) Q.ann) ρ)) = true) ∨
      RhoLo.front F.shape (A' := Q.ann)
          (Rho.lo (RoundSplits.app (RoundSplits.const (RAnn.ofSlot .lo) F.shape) Q.ann) ρ) ∈
        HF.Hid (inp w x) x ↔
    (Rho.fst ρ ∈ HF.Bad ∨ Rho.fst ρ ∈ HF.Hid (inp w x) x) ∨
    (Rho.lo Q.ann (Rho.snd (s := F.shape) ρ) ∈ HQ.Bad ∨
      HQ.stop0 (Rho.sh Q.ann (Rho.snd (s := F.shape) ρ)) = true)
  rw [RhoLo.front_lo, back_lo, back_sh]
  tauto

theorem run_one (w : Wt) (x : X) (c0 : HQ.Coin0) (c1 : HF.Coin)
    (c2 : HQ.Coin) (ρ : Rho (F.shape ++ Q.ior.shape)) :
    (Strat.run ((onlineHonest F Q HF HQ ext sh inp).one.strat w x (c0, (c1, c2))) ρ).1 =
      Tr.app ((HF.strat (inp w x) x c1).run (Rho.fst ρ)).1
        ((HQ.one (sh w) ((HF.strat (inp w x) x c1).run (Rho.fst ρ)).2.1
            ((HF.strat (inp w x) x c1).run (Rho.fst ρ)).2.2.2 (c0, c2)).run
          (Rho.snd (s := F.shape) ρ)).1 := by
  show (Strat.run
      (SStrat.zip (SStrat.skip .lo F.shape (HQ.strat0 (sh w) c0))
        (LStrat.bind .lo (HF.strat (inp w x) x c1) fun o => HQ.strat (sh w) c0 o.1 o.2.2 c2)) ρ).1 =
    _
  rw [zip_skip_bind, Strat.run_bind]
  rfl

end Slot

/-! ## 3. A law over the coins of a batch -/

theorem law_split {ι C0 C1 C2 V Out : Type} [Fintype ι] [DecidableEq ι] [Fintype C0] [Nonempty C0]
    [Fintype C1] [Nonempty C1] [Fintype C2] [Nonempty C2] (J : Finset ι) (hv : J → C1 → V)
    (f : C0 × (ι → C1 × C2) → Out) (K : (J → V) → PMF Out)
    (h : ∀ c1 : ι → C1, (unif (C0 × (ι → C2))).map (fun c' => f (c'.1, fun i => (c1 i, c'.2 i))) =
      K fun j => hv j (c1 j.1)) :
    (unif (C0 × (ι → C1 × C2))).map f = (pis fun j : J => (unif C1).map (hv j)).bind K := by
  let e : (ι → C1) × (C0 × (ι → C2)) ≃ C0 × (ι → C1 × C2) :=
    { toFun := fun p => (p.2.1, fun i => (p.1 i, p.2.2 i))
      invFun := fun c => (fun i => (c.2 i).1, (c.1, fun i => (c.2 i).2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← map_unif_equiv e, PMF.map_comp, map_unif_prod, ← map_unif_pis, ← map_unif_restrict J,
    PMF.map_comp, PMF.bind_map]
  exact congrArg _ (funext fun c1 => h c1)

end OnlineHon
end Iop
