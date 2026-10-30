-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/OwesKinds.lean: FIVE FIELDS OF FirstOwed (OwesByKind.lean): THE KINDS K1, K2,
K9, K10, K13, EACH FROM ITS HOUSE's TOP LAW, WHICH STANDS HERE AS A NAMED HYPOTHESIS. A joining.

  kindPaid_of_exchange   KindPaid from PlaysS and ExchangeS at every number of the kind
  kindPaid_of_five       from FiveAtBorder (K2's k2_five, K10's k10_five_first)
  kindPaid_of_fiveJ      from FiveAtBorderJ (K1's k1_fiveJ_paid, K9's fiveJ_at_k9_first)
  k13_at_355             the written list has the kind K13 at number 355 alone
  k13_paid               from FiveAtBorder at 355 (K13's k13_five_at_firstScript)

Limits. EVERY TOP LAW IS A PREMISE HERE, with that law's own open premises.
 Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.OwesByKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape.Scope
open VerifiableInference.Desc (Place KindName)
open ProofFile.Honest ProofFile.Honest.FirstThread

section
variable {W₀ Rc Tr X : Type} {Bk : ProverCoinCounts} {L : LettersF Bk W₀ Rc Tr X}
  {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop} {κ : KindName}

/-- From the sender's play and the whole exchange, at every number of the kind. -/
theorem kindPaid_of_exchange
    (h : ∀ b p, P5J.At.ps[b]? = some p → p.kind = κ →
      PlaysS L.thread Said b ∧ ExchangeS L.thread Said b) :
    KindPaid L Said κ :=
  fun b p hp hk => ⟨fun _ => (h b p hp hk).1, fun _ => owedAt_of_exchange (h b p hp hk).2⟩

/-- From the five statements, at every number of the kind. -/
theorem kindPaid_of_five
    {fall : Nat → VerifiableInference.Desc.First.S → List Fmt.Drawn → Option String}
    (h : ∀ b p, P5J.At.ps[b]? = some p → p.kind = κ → FiveAtBorder L.thread Said fall b) :
    KindPaid L Said κ :=
  fun b p hp hk => paidAt_of_five (h b p hp hk)

/-- From the five statements with J in hand, at every number of the kind. -/
theorem kindPaid_of_fiveJ {J : Nat → VerifiableInference.Desc.First.S → Prop}
    {fall : Nat → VerifiableInference.Desc.First.S → List Fmt.Drawn → Option String}
    (h : ∀ b p, P5J.At.ps[b]? = some p → p.kind = κ → FiveAtBorderJ L.thread Said J fall b) :
    KindPaid L Said κ :=
  fun b p hp hk => paidAt_of_fiveJ (h b p hp hk)

end

/-- What the written list says of K13, by the kernel. -/
theorem k13_check : (P5J.At.ps.zipIdx.all fun x =>
    x.1.kind != KindName.K13 || x.2 == 355) = true := by
  decide +kernel

/-- The kind K13 stands at 355 alone. -/
theorem k13_at_355 {b : Nat} {p : Place} (h : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K13) : b = 355 := by
  have m : (p, b) ∈ P5J.At.ps.zipIdx := List.mem_zipIdx_iff_getElem?.2 h
  have e := List.all_eq_true.1 k13_check (p, b) m
  simp only [Bool.or_eq_true, bne_iff_ne, beq_iff_eq, ne_eq] at e
  rcases e with e | e
  · exact absurd hk e
  · exact e

/-- **THE KIND K13's FIELD**, from the five statements at its one number. -/
theorem k13_paid {W₀ Rc Tr X : Type} {Bk : ProverCoinCounts} {L : LettersF Bk W₀ Rc Tr X}
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    {fall : Nat → VerifiableInference.Desc.First.S → List Fmt.Drawn → Option String}
    (h : FiveAtBorder L.thread Said fall 355) : KindPaid L Said KindName.K13 :=
  fun b p hp hk => by
    obtain rfl := k13_at_355 hp hk
    exact paidAt_of_five h

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.kindPaid_of_exchange
#print axioms Johnson.AtFull.Shape.Scope.kindPaid_of_five
#print axioms Johnson.AtFull.Shape.Scope.kindPaid_of_fiveJ
#print axioms Johnson.AtFull.Shape.Scope.k13_at_355
#print axioms Johnson.AtFull.Shape.Scope.k13_paid
