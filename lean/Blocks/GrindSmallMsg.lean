-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/GrindSmallMsg.lean: plans that merge no two verifier messages (Iop/Recut.lean;
Iop/GrindRecut.lean: `GBits.recut`).

  `XPlan.NoChal`: a plan that merges no two verifier messages (no step (J2) of Iop/Recut.lean).
  `XPlan.noChal_keepAll`, `noChal_app`, `noChal_msgFrom`, `noChal_msgAll`: how it composes.
  `GBits.recutEx_msgAll`: all rounds of a list s without bits merged into the next round: no bits
  are dropped and no two merged, if that holds of the plan that follows.
-/
import Blocks.GrindSmall
import Iop.GBitsSumF
import Iop.RecutRuns

set_option autoImplicit false

namespace Iop

/-- no merge of two verifier messages -/
def XPlan.NoChal : {s : Shape} → XPlan s → Prop
  | _, .nil => True
  | _, .keep _ P => P.NoChal
  | _, .cut _ P => P.NoChal
  | _, .msg _ _ _ P => P.NoChal
  | _, .chal _ _ _ _ => False

theorem XPlan.noChal_keepAll : ∀ s : Shape, (XPlan.keepAll s).NoChal
  | [] => trivial
  | _ :: s => XPlan.noChal_keepAll s

theorem XPlan.noChal_app {s t : Shape} (P : XPlan s) (Q : XPlan t) (hQ : Q.NoChal) :
    P.NoChal → (XPlan.app P Q).NoChal := by
  induction P with
  | nil => exact fun _ => hQ
  | keep r P ih => exact ih
  | cut c P ih => exact ih
  | msg r1 r2 u P ih => exact ih
  | chal r1 r2 np P ih => exact fun h => h.elim

theorem XPlan.noChal_msgFrom :
    ∀ (h : Round) (s : Shape) (u : h.Chal) (ρ : Rho s) {r : Round} {t : Shape}
        {Q : XPlan (Round.intoFrom h s r :: t)},
      Q.NoChal → (XPlan.msgFrom h s u ρ Q).NoChal
  | _, [], _, _, _, _, _, hQ => hQ
  | h, b :: s, _, ρ, _, _, _, hQ => XPlan.noChal_msgFrom (h.joinMsg b) s ρ.1 ρ.2 hQ

theorem XPlan.noChal_msgAll :
    ∀ (s : Shape) (ρ : Rho s) {r : Round} {t : Shape} {Q : XPlan (Round.into s r :: t)},
      Q.NoChal → (XPlan.msgAll s ρ Q).NoChal
  | [], _, _, _, _, hQ => hQ
  | h :: s, ρ, _, _, _, hQ => XPlan.noChal_msgFrom h s ρ.1 ρ.2 hQ

theorem GBits.recutEx_msgFrom :
    ∀ (h : Round) (s : Shape) (u : h.Chal) (ρ : Rho s) {r : Round} {t : Shape}
        (Q : XPlan (Round.intoFrom h s r :: t)) (g : GBits (r :: t)),
      GBits.RecutEx Q (show GBits (Round.intoFrom h s r :: t) from g) →
      GBits.RecutEx (XPlan.msgFrom h s u ρ Q)
        (show GBits (h :: (s ++ r :: t)) from (0, GBits.app (GBits.zero s) g))
  | _, [], _, _, _, _, _, _, hQ => ⟨rfl, hQ⟩
  | h, b :: s, _, ρ, _, _, Q, g, hQ => ⟨rfl, GBits.recutEx_msgFrom (h.joinMsg b) s ρ.1 ρ.2 Q g hQ⟩

/-- Rounds without bits, merged into the next: `RecutEx`, if Q has it. -/
theorem GBits.recutEx_msgAll :
    ∀ (s : Shape) (ρ : Rho s) {r : Round} {t : Shape}
        (Q : XPlan (Round.into s r :: t)) (g : GBits (r :: t)),
      GBits.RecutEx Q (show GBits (Round.into s r :: t) from g) →
      GBits.RecutEx (XPlan.msgAll s ρ Q) (GBits.app (GBits.zero s) g)
  | [], _, _, _, _, _, hQ => hQ
  | h :: s, ρ, _, _, Q, g, hQ => GBits.recutEx_msgFrom h s ρ.1 ρ.2 Q g hQ

end Iop

