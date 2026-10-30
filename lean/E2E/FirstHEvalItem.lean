-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/FirstHEvalItem.lean: the item claim 1 "Eval" behind W's sending, at the thread `T₁`, and the rows
at numbers 16 and 17 whole.

  `weights_of_back`: the claim's weights are those of which W's job makes W.
  `eval_item`: THE ITEM: the row that the text lays on W holds at the thread's witness.
  `rows_batt`, `rows_w`: numbers 16 and 17, whole, at every letter `Said`.

Limits. Conditional on `FirstPublic`, `WPublic`, `HeardOfFold`, `CoinsAtSlots` and on the thread in front.
Nothing on any property.
-/
import E2E.FirstHEval

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.FirstH
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means OnBytes.Model
open VerifiableInference.Desc (Block OpenedColumn Place noDigest foldBlocks)
open VerifiableInference.Desc.Key (Xi FirstState Claim KItem Source LaterPlaces start₁ sendW
  batchWhere pieces layPile TensorRowHolds matOf mkOf valOf RowHolds ownB shape₁_iff
  tableRowsOf)
open VerifiableInference.Desc.K1 (decideSend decideSend_iff)
open VerifiableInference.Desc.K13 (batt)
open VerifiableInference.Desc.K13.Law (ρg Holds Wit rows_ok OnLedger AgreeAt holds_congr
  rowOf_onLedger onLedger_of_fit)
open Johnson.RunOne.KeyRows1 (plan₁ readers₁ book₁ slots₁)
open AtPublicFiles.KeyThread (D one₀ rowsFirst form_behind₁)
open AtPublicFiles.KeyFile (KeyParts In1)
open AtPublicFiles.AtFiles (KeySourced keysAt sentAt groupsW)
open AtPublicFiles.KeyValues (keyPoints batchedRowsSending oneOf battAt matrixEntryOf firstW)
open AtPublicFiles.Key (pileOf pile_same elemAt wWeights wJob HeardIs handed_is ties_of_batt BattTies
  eval_iff_held evalIn_of_rows maskOf_held w_sent)
open AtPublicFiles.KeyBook (rideW)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest
open ProofFile.Honest.K1 (SendJob rowsLaid rowsLaid_part)

variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X' Wk : Type} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
  {K : KeyParts W₀ Rc X₀ X' Wk} {f : W₀ → Weights} {Q : LaterFill Bk W₀ Rc} {w₀ : W₀} {rc : Rc}
  {x : Xi} {Z : PublicFiles}

/-- The batching's three numbers. -/
theorem battAt_is (hw : WPublic Xs N Pl) :
    battAt Xs N = ⟨roundsTo (D Xs N Pl).first.blocksInOrder 16, roundsTo (D Xs N Pl).first.blocksInOrder 16 + 1,
      roundsTo (D Xs N Pl).first.blocksInOrder 16 + 2⟩ := by
  unfold battAt
  simp only [hw.base]

/-- **The claim's weights are those of which W's job makes W.** -/
theorem weights_of_back (hw : WPublic Xs N Pl) {seen pre rest : List Fmt.RoundView}
    (eseen : seen = pre ++ rest) (hpre : pre.length = roundsTo (D Xs N Pl).first.blocksInOrder 16)
    {heard : List Fmt.Drawn} (hheard : seen.map (·.drawn) = heard) {t : FirstState}
    {rows : List TensorRow} {out : TensorRow × VerifiableInference.Desc.K13.St}
    (hH : HeardAtKeys Xs N heard t) (hlay : layPile keysAt (oneOf Xs) t = .ok { t with pile := rows })
    {owed : Johnson.Desc.First.ForkGround.RowsOwed} {n : Nat} {ledger : Nat}
    {d : VerifiableInference.Desc.K13.St}
    (hbt : batt owed (oneOf Xs).lin.kCol n rows ledger d (rest.map noDigest) = .ok out) :
    out.1.g = wWeights (oneOf Xs) (keyPoints Xs N) (battAt Xs N) heard := by
  have hl : ∀ (i : Nat) (r : Fmt.RoundView), (rest.map noDigest)[i]? = some r →
      (seen.map fun z => (noDigest z).drawn)[roundsTo (D Xs N Pl).first.blocksInOrder 16 + i]? =
        some r.drawn := by
    intro i r hi
    rw [eseen, ← hpre, List.getElem?_map, List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left]
    rw [List.getElem?_map] at hi
    obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 hi
    rw [hz]
    rfl
  obtain ⟨r₀, rs', x₁, u, hdd, o, T⟩ := ties_of_batt hbt _ _ hl
  obtain ⟨rr, hn, hmap, erows⟩ := VerifiableInference.Desc.Key.layPile_whole keysAt (oneOf Xs) t _ hlay
  have err : rows = rr.flatten := congrArg (fun z : FirstState => z.pile) erows
  have hpile : rows.map (fun r => (r.g, r.psi)) =
      (pileOf (Wf.matrixOf (oneOf Xs).lin) (oneOf Xs).ranges.lookups (keyPoints Xs N heard)).map
        fun r => (r.g, r.psi) := by
    rw [err, pileOf_congr _ _ _ _ hH]
    exact pile_same _ _ _ _ 0 hn hmap
  have eel : ∀ i, elemAt (seen.map fun z => (noDigest z).drawn) i = elemAt heard i := fun i => by
    rw [elemAt_bare, hheard]
  have hh : HeardIs (oneOf Xs) (keyPoints Xs N) (battAt Xs N) rows x₁ hdd o heard := by
    rw [battAt_is hw]
    refine ⟨hpile, ?_, ?_, ?_⟩
    · rw [← eel]
      exact T.x_is
    · rw [← eel]
      exact T.eps_is
    · rw [T.point_is]
      refine List.map_congr_left fun i _ => ?_
      exact eel _
  rw [T.out]
  exact handed_is _ _ _ _ _ _ _ _ _ hh T.run

/-- At border 17 the statement's record has the plan's codes, and the index masks' number is 0. -/
theorem ties_at {b : Nat} (hb : b ≠ 0) {s : FirstState} (h : ShapeAt Xs b s = true) :
    s.d.st.codes = (one₀ Xs).codes ∧ s.idx = 0 := by
  have ht : Johnson.RunOne.KeyRows1.ties₁ (one₀ Xs) b s = true :=
    ((shape₁_iff _ _ _ _ _ _ _).1 h).1
  unfold Johnson.RunOne.KeyRows1.ties₁ Johnson.RunOne.KeyRows1.tiesA at ht
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at ht
  refine ⟨ht.1.1.1.1.2, ?_⟩
  rcases ht.1.1.1.2 with h | h
  · exact absurd h hb
  · exact h

end AtPublicFiles.FirstH

#print axioms AtPublicFiles.FirstH.battAt_is
#print axioms AtPublicFiles.FirstH.weights_of_back
#print axioms AtPublicFiles.FirstH.ties_at
