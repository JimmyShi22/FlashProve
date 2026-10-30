-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/RowDebtsAtByKind.lean: `RowDebtsAt` (Johnson/T3/OwedOfKindsAt.lean: what stays beside any description's rows) FROM WHAT
EACH KIND PAYS, GENERAL IN THE DESCRIPTION, THE BOOK, THE LISTS AND THE PROVER. No return of the maker `onlineProverFromPublicFiles` is among its letters: so a side that has a
description and no such return can gather by kind too. `RowDebtsP` (Johnson/T3/OwedOfKinds.lean), which stands at a return's own description and book, is
gathered from the same shares.

Three of the five fields that the two structures share are paid kind by kind: `kinds` is "at every kind" already; `hbud` is gathered from `KindBud`
(Johnson/M1/BudGather.lean); the end of `threads` from `KindOnAtEveryRun` (Honest/Law/UseByKind.lean). The three cuts are general in the description and
the book as they stand. Here they are laid together at these letters, so that Lean holds them against both structures' own fields.

WHAT IT IS NOT. Lemmas that sort hypotheses: nothing is paid. The fields `input` and `hst`, that a family of invariants T exists, and the six fields of
`RowDebtsAt` that a head pays online (plan, book, seats, plainSeal, rooted, returns) are no kind's, and stay premises, each in the field's own text. A kind
of which G holds no list pays all three shares emptily (`kindShareAt_none`). Nothing on soundness, completeness or hiding.

  `KindShareAt`          one kind's three shares, at one family of invariants for each input, coins and return of `ready`
  **`rowDebtsAt_of_kinds`**   `RowDebtsAt` from the shares of all kinds and the eight premises that are no kind's
  `kindShareAt_none`     a kind of which G holds no list pays all three shares, for want of a list
  `owed_of_kind_shares`  so `Owed` at the muted lists: the rule that spends `RowDebtsAt` (`owed_of_kindsAt`), behind the gather
  **`rowDebtsP_of_kindsAt`**  `RowDebtsP` from the same shares at a return's description and book
-/
import Johnson.T3.OwedOfKindsAt
import Johnson.M1.BudGather
import Johnson.Desc.ProofFile.Honest.Law.UseByKind

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest
open VerifiableInference.Desc (KindName FileDescription)
open VerifiableInference.Compilation (RowDebtsP RowDebtsAt)

section General
variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-- **One kind's three shares of `RowDebtsAt`**, at a family of invariants T that is the same for all kinds. General in the description F, the book Bk,
the lists G, the prover H and the relation Rel. A definition, meant as a hypothesis or as a theorem's end. -/
structure KindShareAt (F : FileDescription Xi) (Bk : ProverCoinCounts) (G : Sides F Bk W₀ Rc Ky Tr X₀ X)
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) (Rel : W₀ → Rc → Xi → Prop)
    (T : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      ThreadsP F Bk (G.prover H) w₀ rc x k R) (κ : KindName) : Prop where
  /-- fits, exact and fresh of `Good` at every list of the kind -/
  pays : VerifiableInference.Compilation.KindPays G κ
  /-- the kind's share of `BudDebts` -/
  bud : Johnson.M1.KindBud G κ
  /-- the kind's share of "On at the run, list by list" -/
  on : KindOnAtEveryRun (G := G) (H := H) Rel T κ

variable {F : FileDescription Xi} {Bk : ProverCoinCounts} {G : Sides F Bk W₀ Rc Ky Tr X₀ X}
  {H : Prover W₀ Rc Xi Ky Tr X₀ X} {Rel : W₀ → Rc → Xi → Prop}

/-- A kind of which the lists hold no list pays all three shares, for want of a list: at such a kind the structure says nothing. -/
theorem kindShareAt_none
    (T : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      ThreadsP F Bk (G.prover H) w₀ rc x k R) {κ : KindName}
    (h₁ : ∀ L ∈ G.first, L.place.kind ≠ κ) (h₂ : ∀ L ∈ G.shared, L.place.kind ≠ κ)
    (h₃ : ∀ L ∈ G.second, L.place.kind ≠ κ) : KindShareAt F Bk G H Rel T κ where
  pays := ⟨fun L hL e => absurd e (h₁ L hL), fun L hL e => absurd e (h₂ L hL),
    fun L hL e => absurd e (h₃ L hL)⟩
  bud := Johnson.M1.kindBud_none h₁ h₂ h₃
  on := fun _ _ _ _ _ _ _ _ _ _ _ _ => kindOnAtRun_none _ _ _ h₁ h₂ h₃

/-- **`RowDebtsAt` from the shares of all kinds.** input, hst: its two fields on the prover that are no kind's. T: one family of invariants. plan, book,
seats, plainSeal, rooted, returns: the six that a head pays online; here premises. -/
theorem rowDebtsAt_of_kinds
    (input : ∀ w₀ rc x, Rel w₀ rc x → H.inRange w₀ = true ∧ (H.trace w₀ x).isSome = true)
    (hst : ∀ w₀ rc x, Rel w₀ rc x → ∀ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ t ∈ d.stored,
      ∀ y, y < 2 ^ t.sh.a → ∃ u, H.storedWords w₀ rc t.item y = some u ∧ u.length = t.sh.W)
    (T : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      ThreadsP F Bk (G.prover H) w₀ rc x k R)
    (shares : ∀ κ, KindShareAt F Bk G H Rel T κ)
    (plan : F.planOk = true) (book : Bk.word F = none) (seats : G.seated = true)
    (plainSeal : sealPlain F = true) (rooted : rootedAll F (G.prover H) = true)
    (returns : ∀ w₀ rc x, Rel w₀ rc x → ∀ k, ∃ R, ready F Bk (G.prover H) w₀ rc x k = .ok R) :
    RowDebtsAt F Bk G H Rel where
  kinds := fun κ => (shares κ).pays
  input := input
  hst := hst
  hbud := Johnson.M1.budDebts_of_kinds fun κ => (shares κ).bud
  threads := fun w₀ rc x hrel k R hR =>
    ⟨T w₀ rc x hrel k R hR, fun ρ r due silent run =>
      onAtEveryRun_of_kinds (fun κ => (shares κ).on) w₀ rc x hrel k R hR ρ r due silent run⟩
  plan := plan
  book := book
  seats := seats
  plainSeal := plainSeal
  rooted := rooted
  returns := returns

/-- **So `Owed` at the muted lists**, from the same premises: the rule that spends `RowDebtsAt`, behind the gather. -/
theorem owed_of_kind_shares
    (input : ∀ w₀ rc x, Rel w₀ rc x → H.inRange w₀ = true ∧ (H.trace w₀ x).isSome = true)
    (hst : ∀ w₀ rc x, Rel w₀ rc x → ∀ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ t ∈ d.stored,
      ∀ y, y < 2 ^ t.sh.a → ∃ u, H.storedWords w₀ rc t.item y = some u ∧ u.length = t.sh.W)
    (T : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      ThreadsP F Bk (G.prover H) w₀ rc x k R)
    (shares : ∀ κ, KindShareAt F Bk G H Rel T κ)
    (plan : F.planOk = true) (book : Bk.word F = none) (seats : G.seated = true)
    (plainSeal : sealPlain F = true) (rooted : rootedAll F (G.prover H) = true)
    (returns : ∀ w₀ rc x, Rel w₀ rc x → ∀ k, ∃ R, ready F Bk (G.prover H) w₀ rc x k = .ok R) :
    Owed F Bk H G.mute Rel :=
  VerifiableInference.Compilation.owed_of_kindsAt
    (rowDebtsAt_of_kinds input hst T shares plan book seats plainSeal rooted returns)

end General

section Online
variable {W₀ Rc Tr X₀ X : Type} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
  {G : Sides A.F A.B W₀ Rc OnBytes.TableKey Tr X₀ X}
  {H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X} {Rel : W₀ → Rc → ProofFile.Inst → Prop}

/-- **`RowDebtsP` from the same shares**, at the description and the book of a return of the maker. The six further premises are not asked: `RowDebtsP` has
no such field. -/
theorem rowDebtsP_of_kindsAt
    (input : ∀ w₀ rc x, Rel w₀ rc x → H.inRange w₀ = true ∧ (H.trace w₀ x).isSome = true)
    (hst : ∀ w₀ rc x, Rel w₀ rc x → ∀ d ∈ A.F.roundsDeclaredByBlocks.1 ++ A.F.roundsDeclaredByBlocks.2.1 ++ A.F.roundsDeclaredByBlocks.2.2, ∀ t ∈ d.stored,
      ∀ y, y < 2 ^ t.sh.a → ∃ u, H.storedWords w₀ rc t.item y = some u ∧ u.length = t.sh.W)
    (T : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready A.F A.B (G.prover H) w₀ rc x k = .ok R →
      ThreadsP A.F A.B (G.prover H) w₀ rc x k R)
    (shares : ∀ κ, KindShareAt A.F A.B G H Rel T κ) : RowDebtsP A G H Rel where
  kinds := fun κ => (shares κ).pays
  input := input
  hst := hst
  hbud := Johnson.M1.budDebts_of_kinds fun κ => (shares κ).bud
  threads := fun w₀ rc x hrel k R hR =>
    ⟨T w₀ rc x hrel k R hR, fun ρ r due silent run =>
      onAtEveryRun_of_kinds (fun κ => (shares κ).on) w₀ rc x hrel k R hR ρ r due silent run⟩

end Online

end ProofFile.Honest

#print axioms ProofFile.Honest.KindShareAt
#print axioms ProofFile.Honest.kindShareAt_none
#print axioms ProofFile.Honest.rowDebtsAt_of_kinds
#print axioms ProofFile.Honest.owed_of_kind_shares
#print axioms ProofFile.Honest.rowDebtsP_of_kindsAt
