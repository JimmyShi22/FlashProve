--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/Part4/OwnTaken.lean: THE KEY FILE's OWN PROXIMITY TEST: THE JOB's
THREE TREES ARE THE TABLES TAKEN OVER, AND THE THREE TABLES HAVE THE DECLARED WIDTHS: the proofs of
`TakenAtTheOwnTest` and `WidthsAtTheOwnTest` (K12/Part4/OwnTakenStatements.lean).

WHAT IT IS NOT. All that the head of the statements' file says it is not. NOT IN FRONT OF A LAW OVER
COINS. Under `OwnTestGround`, whose fields on letters can be false at a filling; that the offline
prover's Script lays the three texts of `TablesTakenOver` is not shown. No stand of a thread is shown
to be reached. Nothing on completeness, on soundness or on what is hidden.

  `sendTable_words`      a sending's text of a table has the shape's width, where the cut returns and
                         the tree is there: the like of `sendTable_depth` (K12/DepthsOfText.lean)
  `w_cut`                W's sender's own coins are there, at all of a run's coins
  `takenAtTheOwnTest`, `widthsAtTheOwnTest`   the two statements
-/
import Johnson.Desc.ProofFile.Honest.K12.Part4.OwnTakenVectorW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Part4
open VerifiableInference.Desc.Key (Source LaterPlaces descriptionFromSource)
open VerifiableInference.Desc (Place)
open AtPublicFiles.KeyBook (KeyPub keyBook)
open AtPublicFiles.KeyFile (KeyParts In1 In2 randK14)
open AtPublicFiles.KeyTest (sIdx sW)
open ProofFile.Honest.K14 (jobOmega sendingPart)
open ProofFile.Honest.K12.AtKey (takenOwn)

/-- **A sending's text of a table has the shape's width.** -/
theorem sendTable_words {Bk : ProverCoinCounts} {W : Type} (J : K14.SendJob) (wit : W → K14.Ask) (pl : Place)
    (ch i : ℕ) (k : Coins Bk) (w : W) (h : List Fmt.Drawn)
    (hcut : ((k.look ch ⟨pl, 0⟩).2.cut ⟨0, 0⟩ (sendingPart J).takes).isSome = true)
    (hi : i < ((VerifiableInference.Desc.Own.treesMade J.Q.codes J.Q.sent).getD
      {}).shapes.toList.length) :
    (K14.sendTable J wit pl ch i k w h).2.words =
      ((((VerifiableInference.Desc.Own.treesMade J.Q.codes J.Q.sent).getD {}).shapes.toList.map
        fun t => t.mainWidth + t.maskWidth).getD i 0) := by
  unfold K14.sendTable
  cases hc : (k.look ch ⟨pl, 0⟩).2.cut ⟨0, 0⟩ (sendingPart J).takes with
  | none =>
    rw [hc] at hcut
    cases hcut
  | some own =>
    show ((K14.sendTablesAt J own (wit w) h).getD i _).words = _
    unfold K14.sendTablesAt K14.sentTables
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_zipIdx,
      List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]

section
variable {S Cl V Pb W₀ Rc X₀ X Wk : Type} {K₀ : KeyPub}
  {T : Thread (keyBook K₀) S Cl V (In1 W₀ Rc) X Pb} {K : KeyParts W₀ Rc X₀ X Wk} {Xs : Source}
  {Nr : H2U.PlaceNums} {Pl : LaterPlaces} {toCommon : In1 W₀ Rc → In2 W₀ Rc}

/-- W's sender's own coins are there, at all of a run's coins. -/
theorem w_cut (G : OwnTestGround T K Xs Nr Pl toCommon) (k : Coins (keyBook K₀)) :
    ∃ c₀ : Cs (K1.dueR K.w.P K.w.ride),
      K1.lentCut k 0 ⟨K.w.P.place, 0⟩ (K1.dueR K.w.P K.w.ride) = some c₀ := by
  have F := w_facts_at G
  obtain ⟨e₁, e₃, -, -, -, -, -, -, -, -, hdue, -, -⟩ := w_book_at G
  have hplace : (⟨K.w.P.place, 0⟩ : Addr) = sW := by
    rw [G.wPlace]
    rfl
  rw [hplace]
  exact Option.isSome_iff_exists.1 (cut_of_due k 0 (Nat.zero_le 1) sW
    (K1.dueR K.w.P K.w.ride) (by
      show _ ≤ (dueAt (keyBook K₀).first sW).f ∧ _ ≤ (dueAt (keyBook K₀).first sW).e
      rw [F.due, hdue]
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩))

end

theorem takenAtTheOwnTest : TakenAtTheOwnTest := by
  intro S Cl V Pb W₀ Rc X₀ X Wk K₀ T K Xs Nr Pl toCommon G k m c hl i hi
  match i, hi with
  | 0, _ => exact takenIndexMasks S Cl V Pb W₀ Rc X₀ X Wk K₀ T K Xs Nr Pl toCommon G k m c hl
  | 1, _ => exact takenVectorW S Cl V Pb W₀ Rc X₀ X Wk K₀ T K Xs Nr Pl toCommon G k m c hl
  | 2, _ => exact takenOmega S Cl V Pb W₀ Rc X₀ X Wk K₀ T K Xs Nr Pl toCommon G k m c hl
  | n + 3, h => exact absurd h (by simp [takenOwn])

theorem widthsAtTheOwnTest : WidthsAtTheOwnTest := by
  intro S Cl V Pb W₀ Rc X₀ X Wk K₀ T K Xs Nr Pl toCommon G x hx k w h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · obtain ⟨c₀, hcut⟩ := index_cut G k
    have F := index_facts_at G
    show (T.table (.taken 0 0) k w h).2.words = 3
    rw [G.tables.indexMasks, (treeTbl_at 0 id K.idx K.own₀ 0 k c₀ hcut F.plan F.trees w h).2.1]
    exact F.width
  · obtain ⟨c₀, hcut⟩ := w_cut G k
    have F := w_facts_at G
    show (T.table (.taken 0 5) k w h).2.words = 12
    rw [G.tables.vectorW, (treeTbl_at 0 id K.w K.own₀ 0 k c₀ hcut F.plan F.trees w h).2.1]
    exact F.width
  · obtain ⟨own, hown⟩ := omega_cut G k
    have F := facts_at G K.send.atPoint
    show (T.table (.taken 1 1) k w h).2.words = 36
    rw [G.tables.omega]
    show (K14.sendTable (jobOmega K.send) _ (K14.sendPlace 5) 1 0 k _ _).2.words = 36
    rw [sendTable_words _ _ _ _ _ _ _ _ (by rw [hown]; rfl) (by
      have e := congrArg List.length F.tree
      rw [List.length_map] at e
      rw [e]
      decide)]
    exact F.words

end ProofFile.Honest.K12.Part4

#print axioms ProofFile.Honest.K12.Part4.sendTable_words
#print axioms ProofFile.Honest.K12.Part4.w_cut
#print axioms ProofFile.Honest.K12.Part4.takenAtTheOwnTest
#print axioms ProofFile.Honest.K12.Part4.widthsAtTheOwnTest
