-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegFitUnder.lean: several open tests: the locations of a test that is under a claim.

Definitions, statements (Cb.Spec.ldSegUnder_*) and proofs.
In standard terms: book-keeping for the end of proximity tests inside the preamble of a request, a
chain of interactive oracle reductions (`LdReq`, Cb/Req1/LdReq.lean), where several tests are open
at once: a step that only re-brackets the explicit part, so that the next test's locations can be
stated. An open test: `heldB` (Cb/Req1/LdSegKit.lean).

Why: when several groups close in one segment, their tests are open at the same time, one inside
what the other carries (Cb/Req1/LdSegClose.lean). After the locations of the outer test the stage
reads: "a claim Ψ (what these locations leave), beside a base joint that still holds an open test".
The move "loc" (Cb/Req1/LdSegKit.lean: `LdLocD`) needs the open test's part of the explicit part in
front.

Main names:
  `D.underStep Y Ψ` (`D : LdLocD E Kc`, `Y : Type`, `Ψ : Y → D.S.Msg → Prop`): the step without
    rounds from `D.overSt Y Ψ` to `(D.under Y Ψ).src`: the explicit part (y, ((x, samples), st)) is
    re-bracketed to ((x, samples), (y, st)).
  `D.underP Y Ψ`: the list of two moves: that step; the locations.
  `Spec.ldSegUnder_near`: `D.Near → (D.under Y Ψ).Near`.
  `Spec.ldSegUnder_hyp`: `D.Hyp → (D.underP Y Ψ).Hyp`; its moves are of the kinds that the last part
    of a segment may hold (`LdSeg.locT`, Cb/Req1/LdSeg.lean).
So any number of open tests is closed one after the other, the one that was opened last first (not
stated here; for two tests: `LdNestD.locP`, Cb/Req1/LdSegFitTwo.lean).

Limits: this file does not say in which order the locations of several open tests should come.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegFit
import Cb.Req1.LdSegCloseProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood IOR

namespace LdLocD
variable {E Kc : Type} [Field E] [Fintype E] (D : LdLocD E Kc) (Y : Type) (Ψ : Y → D.S.Msg → Prop)

/-- D's base joint before the locations, with the claim Ψ; the open test's part of the explicit part
in front -/
def underA : Rels Kc ((D.Xc × D.hd.Smp) × (Y × D.St₀)) (D.C.ext.prod D.E₀) (D.S.Msg × D.Wp) where
  rel  := fun x y w => Ψ x.2.1 w.1 ∧ D.A.rel (x.1, x.2.2) y w
  relR := fun a w => Ψ a.1.2.1 w.1 ∧ D.A.relR ((a.1.1, a.1.2.2), a.2) w
  on   := fun a => D.A.on ((a.1.1, a.1.2.2), a.2)
  core := D.A.core

/-- The same locations, with Ψ among what else is claimed. -/
@[reducible] def under : LdLocD E Kc :=
  { S := D.S, P := D.P, C := D.C, e := D.e, t := D.t, hd := D.hd, Xc := D.Xc, St₀ := Y × D.St₀,
    Wp := D.Wp, E₀ := D.E₀, Φ := D.Φ, cut := D.cut, A₁ := claimRels Ψ D.A₁, A := D.underA Y Ψ }

/-- Where the outer locations end: Ψ beside D's base joint. -/
@[reducible] def overSt : LdStage E Kc :=
  ⟨D.S, Y × ((D.Xc × D.hd.Smp) × D.St₀), D.C.ext.prod D.E₀, D.Wp, claimRels Ψ D.A⟩

def underStep : LdMv (D.overSt Y Ψ) (D.under Y Ψ).src :=
  ldStepF D.S (claimRels Ψ D.A) (D.underA Y Ψ) fun st => (st.2.1, (st.1, st.2.2))

def underP : LdProg (D.overSt Y Ψ) (D.under Y Ψ).tgt :=
  .snoc (.snoc (.nil _) (D.underStep Y Ψ)) (.loc (D.under Y Ψ))

end LdLocD

namespace Spec

def ldSegUnder_near : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (D : LdLocD E Kc) (Y : Type) (Ψ : Y → D.S.Msg → Prop),
    D.Near → (D.under Y Ψ).Near

def ldSegUnder_hyp : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (D : LdLocD E Kc) (Y : Type) (Ψ : Y → D.S.Msg → Prop),
    D.Hyp → (D.underP Y Ψ).Hyp ∧ (D.underP Y Ψ).All fun t => t = .loc ∨ t = .step

end Spec

theorem ldSegUnder_near : Spec.ldSegUnder_near := by
  intro E Kc _ _ D Y Ψ h
  refine ⟨fun x y w => ?_, fun a w => ?_, fun a => h.on _, fun w => h.core w⟩
  · constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨a1, a2, a3⟩ := (h.rel _ _ _).1 h2
      exact ⟨a1, a2, h1, a3⟩
    · rintro ⟨a1, a2, h1, a3⟩
      exact ⟨h1, (h.rel (x.1, x.2.2) y w).2 ⟨a1, a2, a3⟩⟩
  · constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨a1, a2, a3⟩ := (h.relR _ _).1 h2
      exact ⟨a1, a2, h1, a3⟩
    · rintro ⟨a1, a2, h1, a3⟩
      exact ⟨h1, (h.relR ((a.1.1, a.1.2.2), a.2) w).2 ⟨a1, a2, a3⟩⟩

theorem ldSegUnder_hyp : Spec.ldSegUnder_hyp := by
  intro E Kc _ _ D Y Ψ h
  have hs : (D.underStep Y Ψ).Hyp :=
    ldStepF_hyp D.S _ _ _ (fun _ _ _ h => h) (fun _ _ h => h) (fun _ => rfl) (fun _ _ _ _ h => h)
  have hl : (D.under Y Ψ).Hyp := ⟨ldSegUnder_near E Kc D Y Ψ h.near, h.laws⟩
  refine ⟨(LdProg.hyp_snoc _ (LdMv.loc (D.under Y Ψ))).2
      ⟨(LdProg.hyp_snoc _ (D.underStep Y Ψ)).2 ⟨LdProg.hyp_nil _, hs⟩, hl⟩,
    ?_⟩
  rw [LdLocD.underP, LdProg.All, LdProg.All, LdProg.All]
  exact ⟨⟨trivial, Or.inr rfl⟩, Or.inl rfl⟩

end Cb
