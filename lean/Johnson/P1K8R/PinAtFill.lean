-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/PinAtFill.lean: the honest online filling's lots, sorted for the pin.

  term_lots   every lot of onlineProverPartsInUse is the smallness test's, or it is quiet and stands at
              other kinds
  term_second every half of its last chain is quiet

Limits. Lots alone: no run, no maker.
-/
import Johnson.P1K8R.QuietK1K13
import Johnson.P1K8R.QuietK3K6
import Johnson.P1K8R.QuietK10K12W
import Johnson.P1K8R.QuietW
import Johnson.Desc.ProofFile.Honest.AtPureWiderK12Kinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open ProofFile ProofFile.Honest
open VerifiableInference.Desc (Place KindName)

variable {W₀ : Type}

/-- W's lot stands at a place of the kind K1. -/
theorem wLot_kind (I : WiderIn W₀) (o : SecondHashFunctionArgument) (O : OnlineProverArguments) (Z : Pub) (G : Ground) :
    ∀ x ∈ (wLotAt (X := Unit) I o O).halves Z G, x.place.kind = KindName.K1 := by
  intro x hx
  rw [wLotAt_halves] at hx
  cases hm : OnBytes.linMessageW Z.first.lin with
  | none =>
    rw [hm] at hx
    cases hx
  | some msg =>
    rw [hm] at hx
    obtain rfl := List.mem_singleton.1 hx
    rfl

/-- The smallness test's lot in the filling. -/
abbrev termSmall : HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit :=
  K8.smallLot id fun _ G _ l => K3.matsOwn G.W l

/-- **Every lot of the filling is the smallness test's, or it is quiet and stands at other kinds.** -/
theorem term_lots (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ∀ L ∈ (onlineProverPartsInUse I o S O).lots, L = termSmall ∨
      (LotQuiet L ∧ ∀ Z G, ∀ x ∈ L.halves Z G, x.place.kind ≠ KindName.K8) := by
  intro L hL
  have e : (onlineProverPartsInUse I o S O).lots =
      (ownPairsCP (LongLots.plain o S O) I S O).map (·.1) ++ [wLotAt I o O] := rfl
  rw [e] at hL
  rcases List.mem_append.1 hL with h | h
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h
    have hk : ∀ Z G, ∀ x ∈ r.1.halves Z G, x.place.kind = r.2 := fun Z G =>
      ownPairsCP_kinds S O (FirstFill.longKinds_plain I o S O Z G) r hr
    have hne : r.2 ≠ KindName.K8 → ∀ Z G, ∀ x ∈ r.1.halves Z G, x.place.kind ≠ KindName.K8 :=
      fun h Z G x hx => by rw [hk Z G x hx]; exact h
    simp only [ownPairsCP, ownPairsC, FirstFill.ownPairs, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact .inr ⟨k1_quiet I o S O, hne (by simp)⟩
    · exact .inr ⟨k2_quiet I S, hne (by simp)⟩
    · exact .inr ⟨k7_quiet, hne (by simp)⟩
    · exact .inr ⟨k11_quiet I o S O, hne (by simp)⟩
    · exact .inr ⟨k13_quiet I o S O, hne (by simp)⟩
    · exact .inr ⟨k3_quiet I o S O, hne (by simp)⟩
    · exact .inr ⟨k4_quiet I, hne (by simp)⟩
    · exact .inr ⟨k5_quiet O, hne (by simp)⟩
    · exact .inr ⟨k6_quiet I o S O, hne (by simp)⟩
    · exact .inl rfl
    · exact .inr ⟨K10K12.closeLotAt_quiet I S, hne (by simp)⟩
    · exact .inr ⟨K10K12.proxLotAt_quiet I S, hne (by simp)⟩
  · obtain rfl := List.mem_singleton.1 h
    refine .inr ⟨wLot_quiet I o O, fun Z G x hx => ?_⟩
    rw [wLot_kind I o O Z G x hx]
    decide

/-- The smallness test's lot is a lot of the filling. -/
theorem term_small_mem (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    termSmall ∈ (onlineProverPartsInUse I o S O).lots := by
  have e : (onlineProverPartsInUse I o S O).lots =
      (ownPairsCP (LongLots.plain o S O) I S O).map (·.1) ++ [wLotAt I o O] := rfl
  rw [e]
  refine List.mem_append_left _ (List.mem_map.2 ⟨(termSmall, KindName.K8), ?_, rfl⟩)
  simp [ownPairsCP, ownPairsC, FirstFill.ownPairs]

/-- **No half of the filling's lots stands at a place of the kind frame.** -/
theorem term_no_frame (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ∀ L ∈ (onlineProverPartsInUse I o S O).lots, ∀ Z G, ∀ x ∈ L.halves Z G,
      x.place.kind ≠ KindName.frame := by
  intro L hL Z G x hx
  have e : (onlineProverPartsInUse I o S O).lots =
      (ownPairsCP (LongLots.plain o S O) I S O).map (·.1) ++ [wLotAt I o O] := rfl
  rw [e] at hL
  rcases List.mem_append.1 hL with h | h
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h
    rw [ownPairsCP_kinds S O (FirstFill.longKinds_plain I o S O Z G) r hr x hx]
    simp only [ownPairsCP, ownPairsC, FirstFill.ownPairs, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · obtain rfl := List.mem_singleton.1 h
    rw [wLot_kind I o O Z G x hx]
    decide

end P1K8

#print axioms P1K8.term_small_mem
#print axioms P1K8.term_lots
#print axioms P1K8.term_no_frame
