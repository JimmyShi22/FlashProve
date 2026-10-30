-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/AtPureWiderK10Kinds.lean: the eleven lists of `widerFillOwnC`
(Honest/AtPureWiderK10.lean), each with its kind, in the form that the laws of
Honest/Thread/FirstFillPairs.lean ask of a choice of fields. One definition; five short lemmas.

  `ownPairsC`           `FirstFill.ownPairs`, by the authors of K5's rounds
     (Honest/Thread/FirstFillOwn.lean: the ten, each with its kind), then `(closeLotAt I S, .K10)`
  `widerFillOwnC_pairs`   `(widerFillOwnC …).lots = (ownPairsC …).map (·.1)`, by `rfl`
  `ownPairsC_kinds`     under `FirstFill.LongKinds L I Z G`: every side of each of the eleven stands
     at a place of the list's kind
  `ownPairsC_nodup`     no kind stands twice among the eleven
  `ten_not_K10`         under `LongKinds`: NO SIDE OF THE TEN STANDS AT A PLACE OF THE KIND K10
  `ten_not_K10_plain`   that at the lists of `widerFillAt` (the first ten of `widerFillAtC`): no
     premise

What it is for. A law that asks of a choice of fields «every other list has no side at my kind, or
my sides» is paid at `widerFillOwnC` by `FirstFill.pairs_ho` from `widerFillOwnC_pairs`,
`ownPairsC_kinds` and, by one step more, `ownPairsC_nodup`. `ready` (Honest/Frame.lean) refuses
where two sides stand at one place: `ten_not_K10` (at the plain lists `ten_not_K10_plain`) says,
with `closeLotAt_kinds` (Honest/AtPureWiderK10.lean), that the closings' sides meet none of the
ten's.

Limits.
  * `LongKinds` is a premise of `ownPairsC_kinds` and of `ten_not_K10`; the other three lemmas take
    none.
  * Of a side these statements read its place alone.
  * `ownPairsC_nodup` says that no kind stands twice among these eleven pairs. Of a list of pairs in
    which a kind does stand twice that statement is false; the laws that speak of one kind alone
    (`FirstFill.pairs_ho`, Honest/Thread/FirstFillPairs.lean; not imported here) are then the ones
    to call.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.AtPureWiderK10
import Johnson.Desc.ProofFile.Honest.Thread.FirstFillOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (KindName)

variable {W₀ X : Type}

/-- **The eleven lists, in the order of `widerFillOwnC`, each with its kind.** A definition: nothing
is claimed of it. -/
def ownPairsC (L : LongLots W₀ X) (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    List (HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X × KindName) :=
  FirstFill.ownPairs L I S O ++ [(closeLotAt I S, .K10)]

/-- The lists of `widerFillOwnC` are the pairs' first halves. -/
theorem widerFillOwnC_pairs (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    (widerFillOwnC own₀ L I o S O).lots = (ownPairsC L I S O).map (·.1) := rfl

/-- **Every side of each of the eleven stands at a place of the list's kind.** CONDITIONAL: K. -/
theorem ownPairsC_kinds {L : LongLots W₀ X} {I : WiderIn W₀} (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) {Z : Pub} {G : Ground} (K : FirstFill.LongKinds L I Z G) :
    ∀ r ∈ ownPairsC L I S O, ∀ x ∈ r.1.halves Z G, x.place.kind = r.2 := by
  intro r hr
  rcases List.mem_append.1 hr with h | h
  · exact K.all r h
  · obtain rfl : r = (closeLotAt I S, .K10) := by simpa using h
    exact closeLotAt_kinds I S Z G

/-- No kind stands twice among the eleven. -/
theorem ownPairsC_nodup (L : LongLots W₀ X) (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) : ((ownPairsC L I S O).map (·.2)).Nodup := by
  have hn : ([KindName.K1, .K2, .K7, .K11, .K13, .K3, .K4, .K5, .K6, .K8, .K10] :
      List KindName).Nodup := by
    decide
  exact hn

/-- **NO SIDE OF `widerFillOwn`'s TEN LISTS STANDS AT A PLACE OF THE KIND K10.** CONDITIONAL: K. -/
theorem ten_not_K10 (own₀ : X) {L : LongLots W₀ X} {I : WiderIn W₀} (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {Z : Pub} {G : Ground}
    (K : FirstFill.LongKinds L I Z G) :
    ∀ M ∈ (widerFillOwn own₀ L I o S O).lots, ∀ x ∈ M.halves Z G,
      x.place.kind ≠ KindName.K10 := by
  intro M hM x hx h10
  rw [FirstFill.widerFillOwn_lots] at hM
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hM
  have hk : r.2 = KindName.K10 := (K.all r hr x hx).symm.trans h10
  have hin : KindName.K10 ∈ (FirstFill.ownPairs L I S O).map (·.2) :=
    hk ▸ List.mem_map.2 ⟨r, hr, rfl⟩
  have hno : KindName.K10 ∉
      ([KindName.K1, .K2, .K7, .K11, .K13, .K3, .K4, .K5, .K6, .K8] : List KindName) := by decide
  exact hno hin

/-- That at the lists of `widerFillAt` (the first ten of `widerFillAtC`): no premise. -/
theorem ten_not_K10_plain (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) (Z : Pub) (G : Ground) :
    ∀ M ∈ (widerFillAt I o S O).lots, ∀ x ∈ M.halves Z G, x.place.kind ≠ KindName.K10 :=
  ten_not_K10 () o S O (FirstFill.longKinds_plain I o S O Z G)

end ProofFile.Honest

#print axioms ProofFile.Honest.widerFillOwnC_pairs
#print axioms ProofFile.Honest.ownPairsC_kinds
#print axioms ProofFile.Honest.ownPairsC_nodup
#print axioms ProofFile.Honest.ten_not_K10
#print axioms ProofFile.Honest.ten_not_K10_plain
