-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/OwesHeadKinds.lean: KindPaid (OwesByKind.lean) AT THE KINDS K6, K7, K8 AND K11, FROM THE HOUSE's LAW AT
THE KIND's NUMBERS. A joining; the written list of places by the kernel.

  `head_kinds`   where the written list has a place of these kinds
  `k6_paid`, `k7_paid`, `k8_paid`, `k11_paid`   KindPaid from the house's statements at these numbers

Limits. The house's statements (FiveAtBorder, or PlaysS and ExchangeS) are hypotheses here, at letters L: these houses'
files lie in no round yet, and their theorems are called by whoever joins them. Nothing on any property.
-/
import Johnson.AtFull.Shape.Scope.OwesByKind
import Johnson.Desc.ProofFile.Honest.Thread.FiveAtBorder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape.Scope
open VerifiableInference.Desc (KindName Place)
open VerifiableInference.Desc.First (Item)
open ProofFile.Honest

/-- The written list's K6, K7, K8 and K11, by the kernel. -/
theorem ps_head_kinds : (P5J.At.ps.zipIdx.all fun x =>
    (x.1.kind != KindName.K6 || x.2 == 341) && (x.1.kind != KindName.K7 || x.2 == 338) &&
      (x.1.kind != KindName.K11 || x.2 == 346) &&
      (x.1.kind != KindName.K8 || x.2 == 343 || (List.range 24).any fun l => x.2 == 14 * l + 6)) = true := by
  decide +kernel

theorem head_kinds {b : Nat} {p : Place} (h : P5J.At.ps[b]? = some p) :
    (p.kind = KindName.K6 → b = 341) ∧ (p.kind = KindName.K7 → b = 338) ∧
      (p.kind = KindName.K11 → b = 346) ∧
      (p.kind = KindName.K8 → b = 343 ∨ ∃ l, l < 24 ∧ b = 14 * l + 6) := by
  have m : (p, b) ∈ P5J.At.ps.zipIdx := List.mem_zipIdx_iff_getElem?.2 h
  have e := List.all_eq_true.1 ps_head_kinds (p, b) m
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq, ne_eq, List.any_eq_true,
    List.mem_range] at e
  obtain ⟨⟨⟨e6, e7⟩, e11⟩, e8⟩ := e
  refine ⟨fun k => e6.resolve_left (not_not.2 k), fun k => e7.resolve_left (not_not.2 k),
    fun k => e11.resolve_left (not_not.2 k), fun k => ?_⟩
  rcases e8 with (e | e) | ⟨l, hl, e⟩
  · exact absurd k e
  · exact Or.inl e
  · exact Or.inr ⟨l, hl, e⟩

section
variable {W₀ Rc Tr X : Type} {Bk : ProverCoinCounts} {L : LettersF Bk W₀ Rc Tr X}
  {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}

/-- **K6**: its one place, from the house's five. -/
theorem k6_paid {fall : Nat → VerifiableInference.Desc.First.S → List Fmt.Drawn → Option String}
    (h : FiveAtBorder L.thread Said fall 341) : KindPaid L Said KindName.K6 := fun _ _ hb hk =>
  ((head_kinds hb).1 hk) ▸ paidAt_of_five h

/-- **K7**: its one place, from the house's plays and exchange. -/
theorem k7_paid (hP : PlaysS L.thread Said 338) (hX : ExchangeS L.thread Said 338) :
    KindPaid L Said KindName.K7 := fun _ _ hb hk =>
  ((head_kinds hb).2.1 hk) ▸ ⟨fun _ => hP, fun _ => owedAt_of_exchange hX⟩

/-- **K11**: its one place, from the house's five. -/
theorem k11_paid {fall : Nat → VerifiableInference.Desc.First.S → List Fmt.Drawn → Option String}
    (h : FiveAtBorder L.thread Said fall 346) : KindPaid L Said KindName.K11 := fun _ _ hb hk =>
  ((head_kinds hb).2.2.1 hk) ▸ paidAt_of_five h

/-- **K8**: at each segment, from the house's plays and exchange. -/
theorem k8_paid (hP : ∀ l, l < 24 → PlaysS L.thread Said (14 * l + 6)) (hP₃ : PlaysS L.thread Said 343)
    (hX : ∀ l, l < 24 → ExchangeS L.thread Said (14 * l + 6)) (hX₃ : ExchangeS L.thread Said 343) :
    KindPaid L Said KindName.K8 := fun _ _ hb hk => by
  rcases (head_kinds hb).2.2.2 hk with rfl | ⟨l, hl, rfl⟩
  · exact ⟨fun _ => hP₃, fun _ => owedAt_of_exchange hX₃⟩
  · exact ⟨fun _ => hP l hl, fun _ => owedAt_of_exchange (hX l hl)⟩
end

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.ps_head_kinds
#print axioms Johnson.AtFull.Shape.Scope.k6_paid
#print axioms Johnson.AtFull.Shape.Scope.k7_paid
#print axioms Johnson.AtFull.Shape.Scope.k8_paid
#print axioms Johnson.AtFull.Shape.Scope.k11_paid
