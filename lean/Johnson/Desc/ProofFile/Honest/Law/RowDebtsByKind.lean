--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/RowDebtsByKind.lean: `RowDebtsP` (Johnson/T3/OwedOfKinds.lean: what stays beside the
head for the online clause of zero knowledge) FROM WHAT EACH KIND PAYS. Three of its five fields are paid kind by
kind: `kinds` is "at every kind" already; `hbud` is gathered from `KindBud` (Johnson/M1/BudGather.lean); the end
of `threads` from `KindOnAtRun` (Honest/Law/UseByKind.lean). Here the three cuts are laid together, so that Lean
holds them against the structure's own fields.

TURNED, AND WHY. This file's structure and its gather stood at a return of the maker alone (A.F, A.B), though the three
cuts are general in the description and the book: a side that has a description and no such return could not gather by
kind. The general forms now stand in Honest/Law/RowDebtsAtByKind.lean (`KindShareAt`, `rowDebtsAt_of_kinds`,
`rowDebtsP_of_kindsAt`). Here `KindShare` is that structure at A.F and A.B, by abbreviation, and `rowDebtsP_of_kinds` is a
corollary. Both names, their letters and the theorem's statement are as they were.

WHAT IT IS NOT. A lemma that sorts hypotheses: nothing is paid. The fields `input` and `hst`, and that a family of
invariants T exists, are no kind's, and stay premises as they are. A kind of which G holds no list pays all
three shares emptily. Nothing on soundness, completeness or hiding.

  `KindShare`          one kind's three shares, at one family of invariants for each input, coins and return
  `rowDebtsP_of_kinds`   **`RowDebtsP` from the shares of all kinds**
-/
import Johnson.Desc.ProofFile.Honest.Law.RowDebtsAtByKind

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest
open VerifiableInference.Desc (KindName)
open VerifiableInference.Compilation (RowDebtsP)

variable {W₀ Rc Tr X₀ X : Type} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
  {G : Sides A.F A.B W₀ Rc OnBytes.TableKey Tr X₀ X}
  {H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X} {Rel : W₀ → Rc → ProofFile.Inst → Prop}

/-- **One kind's three shares of `RowDebtsP`**, at a family of invariants T that is the same for all kinds: `KindShareAt`
(Honest/Law/RowDebtsAtByKind.lean: fields pays, bud, on) at the description and the book of a return of the maker. An
abbreviation, meant as a hypothesis or as a theorem's end. -/
abbrev KindShare (A : OnlineProverWithDescription W₀ Rc Tr X₀ X) (G : Sides A.F A.B W₀ Rc OnBytes.TableKey Tr X₀ X)
    (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X) (Rel : W₀ → Rc → ProofFile.Inst → Prop)
    (T : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready A.F A.B (G.prover H) w₀ rc x k = .ok R →
      ThreadsP A.F A.B (G.prover H) w₀ rc x k R) (κ : KindName) : Prop :=
  KindShareAt A.F A.B G H Rel T κ

/-- **`RowDebtsP` from the shares of all kinds.** input, hst: its two fields that are no kind's. T: one family
of invariants. A corollary of `rowDebtsP_of_kindsAt`. -/
theorem rowDebtsP_of_kinds
    (input : ∀ w₀ rc x, Rel w₀ rc x → H.inRange w₀ = true ∧ (H.trace w₀ x).isSome = true)
    (hst : ∀ w₀ rc x, Rel w₀ rc x → ∀ d ∈ A.F.roundsDeclaredByBlocks.1 ++ A.F.roundsDeclaredByBlocks.2.1 ++ A.F.roundsDeclaredByBlocks.2.2, ∀ t ∈ d.stored,
      ∀ y, y < 2 ^ t.sh.a → ∃ u, H.storedWords w₀ rc t.item y = some u ∧ u.length = t.sh.W)
    (T : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready A.F A.B (G.prover H) w₀ rc x k = .ok R →
      ThreadsP A.F A.B (G.prover H) w₀ rc x k R)
    (shares : ∀ κ, KindShare A G H Rel T κ) : RowDebtsP A G H Rel :=
  rowDebtsP_of_kindsAt input hst T shares

end ProofFile.Honest

#print axioms ProofFile.Honest.KindShare
#print axioms ProofFile.Honest.rowDebtsP_of_kinds
