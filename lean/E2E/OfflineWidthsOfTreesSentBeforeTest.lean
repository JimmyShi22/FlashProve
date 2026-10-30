-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/OfflineWidthsOfTreesSentBeforeTest.lean: `hwide` of `last_done`: every old opening of the last chain's own test
is at hand, at the width that the round declares: the tables that it takes over from the two earlier
chains have just these widths.

  `tree_words`, `send_words`   a sending's table has its tree's width, where the book has the part's coins
  `written widths`: `widthIdx`, `widthW`, `widthOmega`   three numbers off the written plan
  `old_opens_full`   the old openings of the own test, each with its source and width (the kernel)
  `hand_widths`   the statement, at a thread, from these

Limits. Widths and sources alone: nothing on what a table holds. Conditional on the seat, on
`T.taken` and on the three tables' widths; the value's own tables pay those in the last section
wherever the kernel lines say yes. Nothing on any property.
-/
import E2E.OfflineLaying
import E2E.KeyLastTrees
import E2E.KeyOwnSeat
import E2E.KeyTreesKey
import Johnson.Desc.ProofFile.Honest.K1.TableShape
import Johnson.Desc.ProofFile.Honest.K1.ScriptAtLaw
import Johnson.Desc.ProofFile.Honest.K1.ScriptLots
import Johnson.Desc.ProofFile.Honest.K14.SendingsPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12
open VerifiableInference.Desc (Block FileDescription Place)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Own (treesMade)
open AtPublicFiles.KeyThread (takenIn decl₃)
open AtPublicFiles.KeyLay (parIK parWK)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub atFull of_atFull)
open AtPublicFiles.AtFiles.Full (QK)
open H2K.Member (piKWFull)

section Tables
variable {Bk : ProverCoinCounts} {W Wl X : Type}

/-- **A sending's table has its tree's width**, where the book covers the part's count. -/
theorem tree_words (ch : Nat) (hc : ch ≤ 1) (wit : Wl → W) (J : K1.SendJob W X) (own₀ : X) (τ : Nat)
    (t : OnBytes.TreeShape)
    (hb : K1.bookCovers Bk ch ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride) = true)
    (ht : J.P.trees[τ]? = some t) (k : Coins Bk) (w : Wl) (h : List Fmt.Drawn) :
    (K1.treeTbl ch wit J own₀ τ k w h).2.words = t.mainWidth + t.maskWidth := by
  have hs := (K1.lentCut_isSome k ch hc ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride)).trans hb
  obtain ⟨c, hcut⟩ := Option.isSome_iff_exists.1 hs
  obtain ⟨T, hT, -, hw⟩ := K1.treeTables_at J.P (K1.rowsLaid J own₀ c (wit w) h) τ t ht
  unfold K1.treeTbl
  rw [hcut]
  show (((K1.treeTables J.P (K1.rowsLaid J own₀ c (wit w) h))[τ]?).getD K1.wordlessTable).words = _
  rw [hT]
  exact hw

/-- **A shared sending's table has its tree's width**, where the part's coins are there. -/
theorem send_words {Wa : Type} (J : K14.SendJob) (wit : Wa → K14.Ask) (pl : Place) (ch i : Nat)
    (t : OnBytes.TreeShape) (k : Coins Bk) (w : Wa) (h : List Fmt.Drawn)
    (hc : ((k.look ch ⟨pl, 0⟩).2.cut ⟨0, 0⟩ (K14.sendingPart J).takes).isSome = true)
    (ht : ((treesMade J.Q.codes J.Q.sent).getD {}).shapes.toList[i]? = some t) :
    (K14.sendTable J wit pl ch i k w h).2.words = t.mainWidth + t.maskWidth := by
  obtain ⟨own, hown⟩ := Option.isSome_iff_exists.1 hc
  unfold K14.sendTable
  simp only [hown]
  unfold K14.sendTablesAt K14.sentTables
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx, ht]

end Tables

/-- The width of the written message of index masks' tree. -/
def widthIdx : Nat := ((parIK.trees[0]?).map fun t => t.mainWidth + t.maskWidth).getD 0

/-- The width of W's tree. -/
def widthW : Nat := ((parWK.trees[0]?).map fun t => t.mainWidth + t.maskWidth).getD 0

/-- The width of the first tree of the shared sending of Omega. -/
def widthOmega : Nat :=
  (((((treesMade (K14.jobOmega ⟨QK, 0⟩).Q.codes (K14.jobOmega ⟨QK, 0⟩).Q.sent).getD {}).shapes.toList)[0]?).map
    fun t => t.mainWidth + t.maskWidth).getD 0

/-- **The old openings of the own test, each with its source and width.** By evaluation: it can say
no. -/
theorem old_opens_full :
    ((proximityTestKind guardedProximityTestParts piKWFull : Block T12 Unit).rounds.flatMap (·.opens)).all (fun o =>
                                     !oldSrc 0 o.2 || (o.2 == .taken 0 0 && o.1.W == widthIdx) ||
                                       (o.2 == .taken 0 5 && o.1.W == widthW) || (o.2 == .taken 1 1 && o.1.W == widthOmega)) = true := by
  decide +kernel

section Hand
variable {Xi : Type} {Bk : ProverCoinCounts} {S Cl V W X Pb : Type}

/-- What `takenIn` holds: the sources of the rounds' openings that are taken. -/
theorem mem_takenIn {l : List Fmt.DeclaredRound} {d : Fmt.DeclaredRound} (hd : d ∈ l)
    {o : Fmt.Shape × Fmt.TreeSource} (ho : o ∈ d.opens) {c j : Nat} (he : o.2 = .taken c j) :
    Fmt.TreeSource.taken c j ∈ takenIn l := by
  unfold takenIn
  refine List.mem_filterMap.2 ⟨o, List.mem_flatMap.2 ⟨d, hd, ho⟩, ?_⟩
  rw [he]

/-- **`hwide` at a thread**, from the seat, the list of taken sources and the three tables. -/
theorem hand_widths (F : FileDescription Xi) (T : Thread Bk S Cl V W X Pb) (blk : Block F.S₃ F.Cl)
    (hb : F.second.blocksInOrder[2]? = some blk)
    (hr : blk.rounds = (proximityTestKind guardedProximityTestParts piKWFull : Block T12 Unit).rounds)
    (hT : T.taken = takenIn (decl₃ F)) (k : Coins Bk) (m : Mid W X)
    (h0 : (T.tableAt (.taken 0 0) k m).2.words = widthIdx)
    (h5 : (T.tableAt (.taken 0 5) k m).2.words = widthW)
    (h1 : (T.tableAt (.taken 1 1) k m).2.words = widthOmega) :
    ∀ d' ∈ (proximityTestKind guardedProximityTestParts piKWFull : Block T12 Unit).rounds, ∀ o ∈ d'.opens, oldSrc 0 o.2 = true →
      o.2 ∈ T.hand 2 ∧ (T.tableAt o.2 k m).2.words = o.1.W := by
  intro d' hd o ho hold
  have hm : d' ∈ decl₃ F := by
    refine List.mem_flatMap.2 ⟨blk, List.mem_of_getElem? hb, ?_⟩
    rw [hr]
    exact hd
  have hall := List.all_eq_true.1 old_opens_full o (List.mem_flatMap.2 ⟨d', hd, ho⟩)
  simp only [hold, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq] at hall
  have hand : ∀ c j, o.2 = .taken c j → o.2 ∈ T.hand 2 := fun c j e => by
    unfold Thread.hand
    rw [hT, e]
    exact List.mem_append_left _ (mem_takenIn hm ho e)
  rcases hall with (⟨e, w⟩ | ⟨e, w⟩) | ⟨e, w⟩
  · exact ⟨hand _ _ e, by rw [e, h0, w]⟩
  · exact ⟨hand _ _ e, by rw [e, h5, w]⟩
  · exact ⟨hand _ _ e, by rw [e, h1, w]⟩

/-- The three sources do stand among the old openings. By evaluation. -/
theorem old_opens_there :
    ((proximityTestKind guardedProximityTestParts piKWFull : Block T12 Unit).rounds.flatMap (·.opens)).any (fun o =>
                                     o.2 == .taken 0 0) = true ∧
    ((proximityTestKind guardedProximityTestParts piKWFull : Block T12 Unit).rounds.flatMap (·.opens)).any (fun o =>
                                     o.2 == .taken 0 5) = true ∧
    ((proximityTestKind guardedProximityTestParts piKWFull : Block T12 Unit).rounds.flatMap (·.opens)).any (fun o =>
                                     o.2 == .taken 1 1) = true := by decide +kernel

/-- A source that the own test opens is taken over by the last chain. -/
theorem source_taken (F : FileDescription Xi) (blk : Block F.S₃ F.Cl) (hb : F.second.blocksInOrder[2]? = some blk)
    (hr : blk.rounds = (proximityTestKind guardedProximityTestParts piKWFull : Block T12 Unit).rounds) {c j : Nat}
    (h : ((proximityTestKind guardedProximityTestParts piKWFull : Block T12 Unit).rounds.flatMap (·.opens)).any (fun o =>
                                     o.2 == .taken c j) = true) :
    Fmt.TreeSource.taken c j ∈ takenIn (decl₃ F) := by
  obtain ⟨o, ho, he⟩ := List.any_eq_true.1 h
  obtain ⟨d', hd, hod⟩ := List.mem_flatMap.1 ho
  have hm : d' ∈ decl₃ F := by
    refine List.mem_flatMap.2 ⟨blk, List.mem_of_getElem? hb, ?_⟩
    rw [hr]
    exact hd
  exact mem_takenIn hm hod (beq_iff_eq.1 he)

end Hand

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.tree_words
#print axioms AtPublicFiles.OfflineRows.send_words
#print axioms AtPublicFiles.OfflineRows.old_opens_full
#print axioms AtPublicFiles.OfflineRows.hand_widths
#print axioms AtPublicFiles.OfflineRows.old_opens_there
#print axioms AtPublicFiles.OfflineRows.source_taken
