-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/SeedMove.lean: THE SAMPLE THAT IS READ OFF A RECORD's ROWS, AT TWO MEMBERS THAT
ARE ALIKE, AND AT A SEED THAT IS KNOWN. Theorems, proved.

`smpOf forms ans` (Seed.lean) is the reading of a record's samples that is meant: some seed whose
rows are the record's, by choice, with the record's targets. A law of another list (a code switch's,
of a whole group's list) speaks of the seed that was drawn. What ties the two is no equation of
seeds.
  `om_alike` (proved): two members that are alike (`Alike`, PinMove.lean) have one oracle message of
    the library. `sample_cross` (proved): the step that crosses from one such to an equal one.
  `smpOf_at_seed` (proved): where the record's rows are the library's rows at a seed ρ (`SeedIs`)
    and its targets are v: `smpOf` gives a sample with the answers v, at a seed that the library's
    sample map reads as it reads ρ.
  `sample_of_seed` (proved): the two together: IN THE FORM IN WHICH A LAW OF ANOTHER LIST IS TIED TO
    THE RECORD (`KeptTies.hs`, KeptJoin.lean).
Limits. That the record holds one set of rows and targets for two members that are alike (two HEq)
is a premise: whoever fills forms and ans shows it (a record keeps a message's sample rows by its
oracle's number, which hangs on the seat). `SeedIs` at the seed that was drawn is the law of the
sending's kind. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.Seed
import Johnson.Desc.Sound.PinMove

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Fo.Peel Cb Johnson.Pack OnBytes.Slice

/-- The step that crosses from one oracle message of the library to an equal one. q: a reading of a
sample that, at every seed whose rows are F and at the targets V, gives a sample with these targets
at a seed that is read as that one is. -/
theorem sample_cross {o o₂ : OMsg GE} (ho : o = o₂) (F : Option (o.Z.S → o.C.J → GE))
    (F₂ : Option (o₂.Z.S → o₂.C.J → GE)) (V : Option (o.Z.S → GE)) (V₂ : Option (o₂.Z.S → GE))
    (hF : HEq F F₂) (hV : HEq V V₂) (q : Option o.Smp)
    (hq : ∀ ρ v, F = some (o.Z.mat ρ) → V = some v →
      ∃ z, q = some z ∧ z.2 = v ∧ o.Z.val z.1 = o.Z.val ρ)
    (z₀ : o₂.Smp) (hρ : F₂ = some (o₂.Z.mat z₀.1)) (hv : V₂ = some z₀.2) :
    ∃ z : o₂.Smp, HEq q (some z) ∧ z.2 = z₀.2 ∧ o₂.Z.val z.1 = o₂.Z.val z₀.1 := by
  subst ho
  obtain rfl := eq_of_heq hF
  obtain rfl := eq_of_heq hV
  obtain ⟨z, e, h2, h3⟩ := hq _ _ hρ hv
  exact ⟨z, by rw [e], h2, h3⟩

section
variable (cs : OnBytes.Codes)

/-- Two members that are alike have one oracle message of the library. -/
theorem om_alike (x x₂ : Mem) (h : Alike x x₂) :
    (sigOf cs x.1.l).om x.2 = (sigOf cs x₂.1.l).om x₂.2 := by
  show portOmZ cs (x.1.l.get x.2).1 (x.1.l.get x.2).2 =
    portOmZ cs (x₂.1.l.get x₂.2).1 (x₂.1.l.get x₂.2).2
  rw [h.1]

variable {A : Type}
  (forms : A → (s : Sending) → (i : Fin s.l.length) →
    Option (((sigOf cs s.l).om i).Z.S → ((sigOf cs s.l).om i).C.J → GE))
  (ans : A → (s : Sending) → (i : Fin s.l.length) → Option (((sigOf cs s.l).om i).Z.S → GE))

/-- **At a seed that is known**: a sample with the record's targets, at a seed that is read as that
one is. -/
theorem smpOf_at_seed (a : A) (s : Sending) (i : Fin s.l.length)
    (ρ : ((sigOf cs s.l).om i).Z.D) (v : ((sigOf cs s.l).om i).Z.S → GE)
    (hρ : SeedIs cs forms a s i ρ) (hv : ans a s i = some v) :
    ∃ z, smpOf cs forms ans a s i = some z ∧ z.2 = v ∧
      ((sigOf cs s.l).om i).Z.val z.1 = ((sigOf cs s.l).om i).Z.val ρ := by
  have g : ∃ ρ', SeedIs cs forms a s i ρ' := ⟨ρ, hρ⟩
  refine ⟨(g.choose, v), ?_, rfl, seedIs_val cs forms a s i _ _ g.choose_spec hρ⟩
  unfold smpOf
  rw [dif_pos g, hv]
  rfl

/-- **The two together.** -/
theorem sample_of_seed (a : A) (x : Mem) (s : Sending) (i : Fin s.l.length) (h : Alike x ⟨s, i⟩)
    (hF : HEq (forms a x.1 x.2) (forms a s i)) (hV : HEq (ans a x.1 x.2) (ans a s i))
    (z₀ : ((sigOf cs s.l).om i).Smp) (hρ : SeedIs cs forms a s i z₀.1)
    (hv : ans a s i = some z₀.2) :
    ∃ z : ((sigOf cs s.l).om i).Smp, HEq (smpOf cs forms ans a x.1 x.2) (some z) ∧ z.2 = z₀.2 ∧
      ((sigOf cs s.l).om i).Z.val z.1 = ((sigOf cs s.l).om i).Z.val z₀.1 := by
  exact sample_cross (om_alike cs x ⟨s, i⟩ h) (forms a x.1 x.2) (forms a s i) (ans a x.1 x.2)
    (ans a s i) hF hV (smpOf cs forms ans a x.1 x.2)
    (fun ρ v e1 e2 => smpOf_at_seed cs forms ans a x.1 x.2 ρ v e1 e2) z₀ hρ hv

end

end VerifiableInference.Desc.Sound
