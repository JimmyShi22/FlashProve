-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PlanQXLawsProofs.lean.
TWO: CUT BY PROGRAM out of the library's Run/PlanQXLawsProofs.lean (only what the entry's clause
holds and stands on a declaration that the sibling says again), then turned by hand where it had to
be. THE HEAD BELOW IS THE LIBRARY's AND SPEAKS OF THE LIBRARY's FILE: much of what it announces IS
NOT HERE, and what it says of "one root | one tree a round" is not true of this file. HERE STAND
ONLY: okX_own, wantedXL_len, xWanted_len, own_of_wantedXL, psofX_local, wqX_okg.

Run/PlanQXLawsProofs.lean: the proofs of Run/PlanQXLaws.lean.

That the verifier is local is proved as in Run/PlanQSLaws.lean (rhoS_eq, rvS_congr, colAtS_congr),
with the view's entries treated case by case on their key. The count of external reads is by
induction over the rounds, with the openings' counts split by the number of the round.

Terms: lean/GLOSSARY.md.

-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library: a test by Lean's evaluator, which
   leaves no declaration. So nothing that is checked of declarations is checked of such a run. No
   clause of a soundness theorem of this library speaks of a run. -/
import Run.PlanQXLawsProofs
import OnBytes.TypedOracleCompiler.Run.PlanQX   -- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.PlanQS   -- TWO: reached in the library through files that are not said again
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.PlanQSMore
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.PlanQTypes
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFn
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ParseChain
import OnBytes.TypedOracleCompiler.Run.ParseBS  -- TWO: reached in the library through files that are not said again
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFnThin
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFnTag
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinDefs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ThinDefs
import OnBytes.TypedOracleCompiler.Run.ThinTie  -- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinDet  -- TWO: reached in the library through files that are not said again
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.VerifyDet
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ThinTieProofs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinDetProofs
import OnBytes.TypedOracleCompiler.Run.TwinTie  -- TWO: reached in the library through files that are not said again
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinTiePureProofs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinTiePure
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.VerifyDetProofs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ParseThin
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.PlanPull
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.PlanQSLaws
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Compile.Batch.ImplOf
import OnBytes.TypedOracleCompiler.Run.PlanQXLaws
import Iop.WireOK

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Run.Twin (allLo)
export _root_.Run.PQ (key_ge weX_ok keepX keepX_own list_len partA_len small_nil all_congr_mem)
open Run.Twin (RS PS)

theorem okX_own : Spec.okX_own := by
  intro ds a xs h d hd n hn
  unfold okX at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.2 d hd n hn

/-! ## The count -/


theorem wantedXL_len (a : Nat) (all : List RD) (xs : List XO) :
    ∀ (i : Nat) (ds : List RD) (Ds : List _root_.Fmt.Drawn), (∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16) →
      ((wantedXL a all xs i ds Ds).filterMap keepX).length ≤
        ((xs.filter fun o => decide (i ≤ o.round)).map (·.count)).sum
  | _, [], _, _ => by simp [wantedXL]
  | _, _ :: _, [], _ => by simp [wantedXL]
  | i, d :: ds, D :: Ds, h => by
      have ih := wantedXL_len a all xs (i + 1) ds Ds fun e he => h e (List.mem_cons_of_mem _ he)
      rw [wantedXL, List.filterMap_append, List.filterMap_append, List.length_append,
        List.length_append, sum_split i xs]
      refine le_trans
        (Nat.add_le_add
          (Nat.add_le_add (le_trans (List.length_filterMap_le _ _) (partA_len a D _))
            (Nat.le_of_eq (congrArg List.length (small_nil _ ?_)))) ih) (by simp)
      intro kx hkx
      obtain ⟨n, hn, hm⟩ := List.mem_flatMap.1 hkx
      split at hm
      · cases hm
      · obtain ⟨x, _, rfl⟩ := List.mem_map.1 hm
        exact h d List.mem_cons_self n hn

theorem xWanted_len : Spec.xWanted_len := by
  intro a ds xs Ds h
  have := wantedXL_len a ds xs 0 ds Ds h
  rw [List.filter_eq_self.2 (fun o _ => decide_eq_true (Nat.zero_le _))] at this
  exact this

/-! ## Locality -/

/-- an entry of wantedX whose key is no stored tree's is an entry of the old road's wanted -/
theorem own_of_wantedXL (a : Nat) (all : List RD) (xs : List XO) (kx : Nat × Nat)
    (h0 : kx.1 ≠ storedKey false) (h1 : kx.1 ≠ storedKey true) :
    ∀ (i : Nat) (ds : List RD) (Ds : List _root_.Fmt.Drawn),
      kx ∈ wantedXL a all xs i ds Ds → kx ∈ wantedL all ds Ds
  | _, [], _, h => by simp [wantedXL] at h
  | _, _ :: _, [], h => by simp [wantedXL] at h
  | i, d :: ds, D :: Ds, h => by
      rw [wantedXL] at h
      rw [wantedL]
      have h' := h
      rcases List.mem_append.1 h' with hab | hr
      · rcases List.mem_append.1 hab with ha | hb
        · obtain ⟨o, _, hm⟩ := List.mem_flatMap.1 ha
          obtain ⟨x, _, rfl⟩ := List.mem_map.1 hm
          cases hw : o.which with
          | false => exact absurd (by show storedKey o.which = storedKey false; rw [hw]) h0
          | true => exact absurd (by show storedKey o.which = storedKey true; rw [hw]) h1
        · exact List.mem_append_left _ hb
      · exact List.mem_append_right _ (own_of_wantedXL a all xs kx h0 h1 (i + 1) ds Ds hr)

theorem psofX_local : Spec.psofX_local := by
  rintro C ds a xs dec x y y' ⟨m0, c0, τ⟩ ⟨m0', c0', τ'⟩ hρ hp he hr
  have e1 : τ.rho = τ'.rho := congrArg Prod.snd hρ
  have e2 : τ.plains = τ'.plains := congrArg Prod.snd hp
  have he' : ∀ wx ∈ xWanted a ds xs (drawnSL C ds τ.rho),
      ∀ p, xPos (2 ^ a) wx = some p → (twoExternalStrings (2 ^ a) SgX).rd y p = (twoExternalStrings (2 ^ a) SgX).rd y' p := by
    intro wx hwx p hpos
    refine he p ?_
    show p ∈ ((xWanted a ds xs (drawnSL C ds τ.rho)).filterMap (xPos (2 ^ a))).toFinset
    rw [List.mem_toFinset, List.mem_filterMap]
    exact ⟨wx, hwx, hpos⟩
  have hc : symbolsCarryTheirPositions a ds xs (drawnSL C ds τ.rho) y = symbolsCarryTheirPositions a ds xs (drawnSL C ds τ.rho) y' := by
    unfold symbolsCarryTheirPositions
    refine all_congr_mem _ _ _ fun wx hwx => ?_
    cases hpos : xPos (2 ^ a) wx with
    | none => rfl
    | some p =>
        show (((twoExternalStrings (2 ^ a) SgX).rd y p).1 == wx.2) = (((twoExternalStrings (2 ^ a) SgX).rd y' p).1 == wx.2)
        rw [he' wx hwx p hpos]
  have hv : viewX C ds a xs y τ = viewX C ds a xs y' τ' := by
    unfold viewX
    rw [rvS_congr C ds τ τ' e1 e2, rhoS_eq, rhoS_eq, ← e1]
    congr 1
    refine filterMap_congr_mem _ _ _ fun kx hkx => ?_
    by_cases h0 : kx.1 = storedKey false
    · rw [if_pos h0, if_pos h0]
      have hw : (false, kx.2) ∈ xWanted a ds xs (drawnSL C ds τ.rho) :=
        List.mem_filterMap.2 ⟨kx, hkx, if_pos h0⟩
      cases hpos : xPos (2 ^ a) (false, kx.2) with
      | none => rfl
      | some p =>
          show some (kx.1, kx.2, ((twoExternalStrings (2 ^ a) SgX).rd y p).2) =
            some (kx.1, kx.2, ((twoExternalStrings (2 ^ a) SgX).rd y' p).2)
          rw [he' _ hw p hpos]
    · rw [if_neg h0, if_neg h0]
      by_cases h1 : kx.1 = storedKey true
      · rw [if_pos h1, if_pos h1]
        have hw : (true, kx.2) ∈ xWanted a ds xs (drawnSL C ds τ.rho) :=
          List.mem_filterMap.2 ⟨kx, hkx, by rw [if_neg h0, if_pos h1]⟩
        cases hpos : xPos (2 ^ a) (true, kx.2) with
        | none => rfl
        | some p =>
            show some (kx.1, kx.2, ((twoExternalStrings (2 ^ a) SgX).rd y p).2) =
              some (kx.1, kx.2, ((twoExternalStrings (2 ^ a) SgX).rd y' p).2)
            rw [he' _ hw p hpos]
      · rw [if_neg h1, if_neg h1]
        rw [colAtS_congr C ds τ τ' kx.1 kx.2 fun p hpos => ?_]
        refine hr (Sum.inr p) ?_
        show (Sum.inr p : OPos (Twin.up (SOf C ds))) ∈
          (((wanted ds (drawnSL C ds τ.rho)).filterMap fun nx =>
            (posAtS C ds nx.1 nx.2).map fun p => (Sum.inr p : OPos (Twin.up (SOf C ds))))).toFinset
        rw [List.mem_toFinset, List.mem_filterMap]
        exact ⟨kx, own_of_wantedXL a ds xs kx h0 h1 0 ds _ hkx, by rw [hpos]; rfl⟩
  show (passSL C ds (rhoSL C ds τ) && everyOpeningHasItsDraws xs (drawnSL C ds (rhoSL C ds τ)) &&
      symbolsCarryTheirPositions a ds xs (drawnSL C ds (rhoSL C ds τ)) y && dec (viewX C ds a xs y τ)) =
    (passSL C ds (rhoSL C ds τ') && everyOpeningHasItsDraws xs (drawnSL C ds (rhoSL C ds τ')) &&
      symbolsCarryTheirPositions a ds xs (drawnSL C ds (rhoSL C ds τ')) y' && dec (viewX C ds a xs y' τ'))
  rw [rhoS_eq, rhoS_eq, ← e1, hc, hv]

/-! ## The wiring -/

theorem wqX_okg : Spec.wqX_okg := fun C K chal ds a xs dec dec₀ hown h =>
  { sh := h.sh
    ext := weX_ok a
    opens := fun x ρ pl => by
      have h1 := h.opens x ρ pl
      have h1' : ((((wanted ds (drawnSL C ds ρ.2)).filterMap fun nx =>
            (posAtS C ds nx.1 nx.2).map fun p =>
              (Sum.inr p : OPos (Twin.up (SOf C ds))))).toFinset).card ≤ nOpen ds :=
        le_trans (Nat.le_add_right _ _) h1
      show (List.toFinset _).card + (List.toFinset _).card ≤ nOpen ds + (xs.map (·.count)).sum
      exact Nat.add_le_add h1'
        (le_trans (List.toFinset_card_le _)
          (le_trans (List.length_filterMap_le _ _) (xWanted_len a ds xs _ hown)))
    depth := ⟨⟨fun _ he => (by cases he), fun _ he => (by cases he)⟩,
      depthSL C K chal _ ds fun d hd =>
        le_trans ((foldl_max_le (fun d : RD => depthOf d.trees) ds 0).2 d hd) (le_max_left _ _)⟩ }

end TypedOracleCompiler.Run.PQ
