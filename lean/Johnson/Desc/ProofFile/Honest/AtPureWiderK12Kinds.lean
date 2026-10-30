-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/AtPureWiderK12Kinds.lean: the twelve lists of `widerFillOwnCP`
(Honest/AtPureWiderK12.lean), each with its kind, in the form that the laws of
Honest/Thread/FirstFillPairs.lean and `atPure_first_find_pairs` (Honest/FirstFindPairs.lean) ask of
a choice of fields. One definition; five short lemmas. The sister of
Honest/AtPureWiderK10Kinds.lean.

  `ownPairsCP`            `ownPairsC` (Honest/AtPureWiderK10Kinds.lean: the eleven, each with its
     kind), then `(proxLotAt I S, .K12)`
  `widerFillOwnCP_pairs`  `(widerFillOwnCP …).lots = (ownPairsCP …).map (·.1)`, by `rfl`
  `ownPairsCP_kinds`      under `FirstFill.LongKinds L I Z G`: every side of each of the twelve
     stands at a place of the list's kind
  `ownPairsCP_nodup`      no kind stands twice among the twelve
  `eleven_not_K12`        under `LongKinds`: no side of `widerFillOwnC`'s eleven lists stands at a
     place of the kind K12
  `eleven_not_K12_plain`  that at the lists of `widerFillAtC` (the first eleven of `widerFillAtCP`):
     no premise

What it is for. `ready` (Honest/Frame.lean) refuses where two sides stand at one place. Under
`LongKinds`: `eleven_not_K12` says, with `proxLotAt_kinds` (Honest/AtPureWiderK12Places.lean), that
the proximity test's side meets none of the eleven's. And what the first chain of the prover that
`onlineProverFromPublicFiles` returns finds at a place of a kind is what that kind's own list finds there: a side: by
`atPure_first_find_pairs`; a side or none: by `FirstFill.fill_find_eq` with `FirstFill.pairs_hex`
and `FirstFill.pairs_ho`; from `widerFillOwnCP_pairs`, `ownPairsCP_kinds` and `ownPairsCP_nodup`
(`pairs_ho`'s premise hu by one step more).

Limits.
  * `LongKinds` is a premise of `ownPairsCP_kinds` and of `eleven_not_K12`; the other three lemmas
    take none. Five of the twelve shares of `ownPairsCP_kinds` are that premise's own clauses,
    handed back.
  * Of a side these statements read its place alone. THE TWO PARTS OF THE PROXIMITY TEST's SIDE
    CANNOT REFUSE: that a side is found at the test's place is no ground that they play
    (Honest/AtPureWiderK12.lean, Limits).
  * Nothing here says that `proxLotAt` has a side.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.AtPureWiderK12Places
import Johnson.Desc.ProofFile.Honest.AtPureWiderK10Kinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (KindName)

variable {W₀ X : Type}

/-- **The twelve lists, in the order of `widerFillOwnCP`, each with its kind.** A definition:
nothing is claimed of it. -/
def ownPairsCP (L : LongLots W₀ X) (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    List (HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X × KindName) :=
  ownPairsC L I S O ++ [(proxLotAt I S, .K12)]

/-- The lists of `widerFillOwnCP` are the pairs' first halves. -/
theorem widerFillOwnCP_pairs (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    (widerFillOwnCP own₀ L I o S O).lots = (ownPairsCP L I S O).map (·.1) := rfl

/-- **Every side of each of the twelve stands at a place of the list's kind.** CONDITIONAL: K. -/
theorem ownPairsCP_kinds {L : LongLots W₀ X} {I : WiderIn W₀} (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) {Z : Pub} {G : Ground} (K : FirstFill.LongKinds L I Z G) :
    ∀ r ∈ ownPairsCP L I S O, ∀ x ∈ r.1.halves Z G, x.place.kind = r.2 := by
  intro r hr
  rcases List.mem_append.1 hr with h | h
  · exact ownPairsC_kinds S O K r h
  · obtain rfl : r = (proxLotAt I S, .K12) := by simpa using h
    exact proxLotAt_kinds I S Z G

/-- No kind stands twice among the twelve. -/
theorem ownPairsCP_nodup (L : LongLots W₀ X) (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) : ((ownPairsCP L I S O).map (·.2)).Nodup := by
  have hn : ([KindName.K1, .K2, .K7, .K11, .K13, .K3, .K4, .K5, .K6, .K8, .K10, .K12] :
      List KindName).Nodup := by
    decide
  exact hn

/-- **NO SIDE OF `widerFillOwnC`'s ELEVEN LISTS STANDS AT A PLACE OF THE KIND K12.** CONDITIONAL: K.
-/
theorem eleven_not_K12 (own₀ : X) {L : LongLots W₀ X} {I : WiderIn W₀} (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {Z : Pub} {G : Ground}
    (K : FirstFill.LongKinds L I Z G) :
    ∀ M ∈ (widerFillOwnC own₀ L I o S O).lots, ∀ x ∈ M.halves Z G,
      x.place.kind ≠ KindName.K12 := by
  intro M hM x hx h12
  rw [widerFillOwnC_pairs] at hM
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hM
  have hk : r.2 = KindName.K12 := (ownPairsC_kinds S O K r hr x hx).symm.trans h12
  have hin : KindName.K12 ∈ (ownPairsC L I S O).map (·.2) :=
    hk ▸ List.mem_map.2 ⟨r, hr, rfl⟩
  have hno : KindName.K12 ∉
      ([KindName.K1, .K2, .K7, .K11, .K13, .K3, .K4, .K5, .K6, .K8, .K10] : List KindName) := by
    decide
  exact hno hin

/-- That at the lists of `widerFillAtC` (the first eleven of `widerFillAtCP`): no premise. -/
theorem eleven_not_K12_plain (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) (Z : Pub) (G : Ground) :
    ∀ M ∈ (widerFillAtC I o S O).lots, ∀ x ∈ M.halves Z G, x.place.kind ≠ KindName.K12 :=
  eleven_not_K12 () o S O (FirstFill.longKinds_plain I o S O Z G)

end ProofFile.Honest

#print axioms ProofFile.Honest.ownPairsCP
#print axioms ProofFile.Honest.widerFillOwnCP_pairs
#print axioms ProofFile.Honest.ownPairsCP_kinds
#print axioms ProofFile.Honest.ownPairsCP_nodup
#print axioms ProofFile.Honest.eleven_not_K12
#print axioms ProofFile.Honest.eleven_not_K12_plain
