-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/PointFill.lean: AT THE FILLED LETTERS (Johnson/Desc/Sound/BordersSharedFill.lean): WHAT THE TABLE's EXTRACTOR AT "LIN point" PAYS BY ITS MAKE. Small lemmas. (pinJT_extS_one: the joint with step (S5)'s premise on the extractor, typed).

  cells_extS_one: block number 1's extractor lays the cells: what the stored table decodes to; the fixed value where it decodes to nothing.
  pinT_extS: THE SECOND HALF OF STEP (S4) (Johnson/Desc/Sound/PointTie.lean): where the decoder gives something (the shared chain's promise on the table, as Johnson/Desc/Sound/TablePromiseAt.lean fills it), the cells' pin holds AT THE WITNESS THAT
    THE EXTRACTOR LAYS, whatever the witness behind.
  msg_extS_one, pad_extS_one: it leaves every message and every pad as it was: so whatever reads no cell rides over it (step (S5)'s premise on the extractor, at every letter that reads the witness through msg and pad alone).
  pinJT_extS_one: SO EVERY PIN, AT EVERY TENANT AND EVERY READER OF SAMPLES, IS KEPT BY IT (a pin reads of the witness its member's two components alone: pin_congr, Johnson/Desc/Sound/World.lean): step (S5)'s premise "the extractor keeps both pins",
    at pin₁ := pinJT.

Limits. The decoder, the codes, arr, the samples' reader are letters.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.BordersSharedFill
import Johnson.Desc.Sound.TablePromiseAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc.Shared

section
variable (cs : OnBytes.Codes) {Xi S₂ Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp₂ : S₂ → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → S₂ → Option Cells) (c₀ : Cells)
  (N : NumbersS) (split : Bool)

theorem lays_one (split : Bool) : laysAtS split 1 = [.cells] := by
  cases split <;> decide

theorem mineS_one : mineS N ms split 1 = [] := by
  unfold mineS
  rw [lays_one]
  refine List.filter_eq_nil_iff.2 fun x _ => ?_
  simp

/-- Block number 1's extractor lays the cells. -/
theorem cells_extS_one (s : S₂) (y : Strs) (w : Wit Cells Tok MsgT) :
    (extS cs G arr smp₂ ms decT₂ c₀ N split 1 s y w).cells = (decT₂ y.cell s).getD c₀ := by
  show (if (laysAtS split 1).contains Comp.cells then _ else w.cells) = _
  rw [lays_one]
  rfl

/-- **The cells' pin holds at what the extractor lays, where the decoder gives something.** -/
theorem pinT_extS (s : S₂) (y : Strs) (w : Wit Cells Tok MsgT) (h : decodesOf decT₂ s y) :
    pinWOf decT₂ s y (extS cs G arr smp₂ ms decT₂ c₀ N split 1 s y w) := by
  show decT₂ y.cell s = some (extS cs G arr smp₂ ms decT₂ c₀ N split 1 s y w).cells
  rw [cells_extS_one]
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 h
  rw [hc]
  rfl

/-- It leaves every message as it was. -/
theorem msg_extS_one (s : S₂) (y : Strs) (w : Wit Cells Tok MsgT) (n : ℕ) :
    (extS cs G arr smp₂ ms decT₂ c₀ N split 1 s y w).msg n = w.msg n := by
  refine extAt_other cs G arr smp₂ decT₂ c₀ _ _ _ _ s y w n ?_
  rw [mineS_one]
  simp

/-- It leaves every pad as it was. -/
theorem pad_extS_one (s : S₂) (y : Strs) (w : Wit Cells Tok MsgT) (j t : ℕ) :
    (extS cs G arr smp₂ ms decT₂ c₀ N split 1 s y w).pad j t = w.pad j t := by
  refine extAt_other_pad cs G arr smp₂ decT₂ c₀ _ _ _ _ s y w j t ?_
  rw [mineS_one]
  simp

/-- Every pin is kept by it. -/
theorem pinJT_extS_one {A : Type}
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp) (ms' : List Mem)
    (j t : ℕ) (a : A) (y' : Strs) (s : S₂) (y : Strs) (w : Wit Cells Tok MsgT)
    (h : pinJT cs G arr smp ms' j t a y' w) :
    pinJT cs G arr smp ms' j t a y' (extS cs G arr smp₂ ms decT₂ c₀ N split 1 s y w) :=
  ⟨h.1, fun x hx hs => pin_congr cs G arr smp x.1 x.2 a y' w _
    (msg_extS_one cs G arr smp₂ ms decT₂ c₀ N split s y w _)
    (pad_extS_one cs G arr smp₂ ms decT₂ c₀ N split s y w _ _) (h.2 x hx hs)⟩

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.pinT_extS
#print axioms VerifiableInference.Desc.Sound.msg_extS_one
#print axioms VerifiableInference.Desc.Sound.pad_extS_one
#print axioms VerifiableInference.Desc.Sound.pinJT_extS_one
