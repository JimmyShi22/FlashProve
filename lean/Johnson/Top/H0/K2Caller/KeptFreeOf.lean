-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/KeptFreeOf.lean: the code switch: THE PROMISE IN FRONT `KeptFree`
(PlainGood.lean: no kept slot of the open word has a collision at its held OOD sample's seed) AT THE
MADE READINGS (TopAt.lean), from what the table of joints promises of the kept members' own
committed words.

Main names:
  `clash_iff_clashW`: a collision at a word as it is sent is a collision at its long form: by
    unfolding.
  `faAt_congr`: `faAt` (CarryK2.lean) reads the oracles through the columns by key and leaf alone.
  `keptFree_of`: from: the text makes a front of the verifier's state, with a frame · each kept slot
    of the made open word is the long form of a word f k as it is sent (`slot_word`, SlotWord.lean,
    gives that at the table's own word) · f k has no collision at an OOD seed that evaluates as the
    held one does (`clash_congr`, Johnson/Desc/Sound/Seed.lean).
Limits. The two facts on the words and the seeds are premises. Nothing on soundness. On hiding
nothing.

-/
import Johnson.Top.H0.K2Caller.TopAt
import Johnson.Top.H0.K2Caller.SlotWord
import Johnson.Desc.Sound.Seed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Strs FileDescription)
open VerifiableInference.Desc.Sound (Frame wordAt)
open VerifiableInference.Desc.First.K2Hands

/-- A collision at a word as it is sent is a collision at its long form. -/
theorem clash_iff_clashW {E : Type} [Field E] (o : OMsg E) (f : o.Str) (ρ : o.Z.D) :
    o.Clash f ρ ↔ o.ClashW (o.upW f) ρ := Iff.rfl

/-- `faAt` (CarryK2.lean) reads the oracles through the columns by key and leaf alone. -/
theorem faAt_congr {r : SwRow} {H : r.OK} {Y Y' : Type} (p : K2.P2)
    (orc : Y → ℕ → ℕ → List UInt64) (orc' : Y' → ℕ → ℕ → List UInt64)
    (smp : _root_.Tw.K2.Front → SwitchFrame → (vecD (plainD r H)).held.Smp)
    (x : VerifiableInference.Desc.First.S × _root_.Tw.K2.Front × SwitchFrame) (y : Y) (y' : Y')
    (h : orc y = orc' y') : faAt r H p orc smp x y = faAt r H p orc' smp x y' := by
  unfold faAt
  rw [h]

variable {F : Frame}

section
variable {r : SwRow} {H : r.OK}
  (iJ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
    r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
    r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
  (p : K2.P2) (orc : F.E.Str → ℕ → ℕ → List UInt64)
  (smp : _root_.Tw.K2.Front → SwitchFrame → (vecD (plainD r H)).held.Smp)
  (d₀ : (Cb.Pv.SendLoc.stage (selZ (Letters.plain r H) iJ iQ).sw).X ×
    (Cb.Pv.SendLoc.stage (selZ (Letters.plain r H) iJ iQ).sw).Ex.Str) (y₀ : F.E.Str)

/-- **`KeptFree` AT THE MADE READINGS**, from: each kept slot of the made open word is the long form
    of
a word f k as it is sent · f k has no collision at an OOD seed that evaluates as the held OOD
sample's seed does. -/
theorem keptFree_of (a : Rec × F.E.Str) {fx : _root_.Tw.K2.Front} {W₀ : SwitchFrame}
    (h1 : K2.frontAt p a.1 = some fx) (h2 : K2.frameAt fx = some W₀)
    (f : ∀ k : {x // (plainHd r H).cl x}, ((sigOf r.cs r.lo).om k.1.1).Str)
    (hw : ∀ k, (plainHd r H).sW k (faAt r H p orc smp (a.1, fx, W₀) a.2).2.1.1 =
      ((sigOf r.cs r.lo).om k.1.1).upW (f k))
    (hc : ∀ k, ∃ ρ, ((sigOf r.cs r.lo).om k.1.1).Z.val ρ =
        ((sigOf r.cs r.lo).om k.1.1).Z.val (smp fx W₀ k).1 ∧
      ¬ ((sigOf r.cs r.lo).om k.1.1).Clash (f k) ρ) :
    KeptFree iJ iQ (strsTop iJ iQ p orc smp d₀) (inXTop iJ iQ p orc smp d₀ y₀) a := by
  intro k
  rw [lawFa_top iJ iQ orc smp d₀ y₀ a h1 h2]
  obtain ⟨ρ, hm, hn⟩ := hc k
  intro hcl
  apply hn
  rw [VerifiableInference.Desc.Sound.clash_congr _ _ _ _ hm, clash_iff_clashW, ← hw k]
  exact hcl

end

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.faAt_congr
#print axioms VerifiableInference.Desc.First.K2Caller.keptFree_of
