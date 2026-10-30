-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MgAt/K11Pub.lean: THE CLAUSE ON PUBLIC ITEMS OF THE SECOND TIE OF THE MERGE OF
THE CLAIMS ON THE COMMITTED TABLE (kind K11), AT THE COMPOSED MEANING `mgAll D Mg`. One small lemma,
one theorem. It proves nothing of any sub-protocol's soundness. Typed by the kind's own authors as a
hand to the composed meaning's.

Why. The table's condition behind the merge asks every public test that is open there, or tied to an
item that is open there (`pubHeld`, Johnson/Desc/First/Borders.lean). `merge_t2`
(Johnson/Top/H0/MergeLaw/TieOneTwo.lean) takes that as its premise hPub.

What is said. `merge_pubHeld`: across the merge's accepting step from a to b: `pubHeld (mgAll D Mg)
O Q (z, a) = true → pubHeld (mgAll D Mg) O' Q' (z, b) = true`, where every item that is asked behind
is one of seven, or stands in the list keep.
  THE SEVEN. "ledger m", "freeAbove m": kept by hand (`merge_keeps_ledger`, LedgerBehind.lean).
    "indexIs", "indexThere": their tests read the statement and what goes on to the later chains,
    which the merge's step leaves (`isLocal`, Johnson/Top/H0/MergeLaw/Law.lean). "hasRow m": MADE:
    the premise hRow, at the layer's own layout, number of claims and row's shape
    (`MergeFront.hasRow`, EntryFront.lean, gives it at the merge's layout, at ONE claim and at its
    own letter for the shape: the two meet where D.d1.lay is the merge's layout, D.d1.ncl m = 1 and
    D.d1.lin is that letter: three equations that are asked here by nobody). "formsIn m 9 merged":
    MADE: the premise hMade, at the reader of the merge's own run, carried to the link's readers by
    `forms_link_merge` (MergedAtLink.lean). "leftOn m": THE COMPOSED TEST THERE IS `true` BY
    DEFINITION: NOTHING IS SHOWN OF IT.
  keep: the items that other authors' lemmas carry across the merge: the premise hkeep.
  `formsIn_congr`: the public test on a run's forms hangs on the readers through the one answer
    alone.

THE PREMISES THAT ARE LEFT. Closed facts on the table: hL (what is asked behind is among the seven
and keep), hIn (four of the seven, and keep, are asked in front), hsub (segment m is the output
head's). hkeep. hRow, hMade. hlk, hst, hr: as in K11.lean beside this file.

Limits. Every premise is shown at no closed value here. What the public items say beside their tests
is another clause of the tie. Nothing on soundness.
-/
import Johnson.Desc.Sound.MgAll
import Johnson.Desc.First.PubAllAt
import Johnson.Desc.Sound.MgAt.Runs
import Johnson.Top.H0.MergeLaw.LedgerBehind
import Johnson.Top.H0.MergeLaw.MergedAtLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc (Link Claim Place)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers pubHeld pubOfItems ledgerB
  freeAboveB)
open VerifiableInference.Desc.First.MergeLaw
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeClaim headMergeDecide)
open Johnson.Desc.First.Walk.Law (hasRow)

/-- The public test on a run's forms hangs on the readers through the one answer alone. -/
theorem formsIn_congr (Rd Rd' : K9.Readers) (own : List (ℕ × ℕ)) (piece : ℕ) (run : String) (s : S)
    (h : Rd.forms piece run s = Rd'.forms piece run s) :
    K9.formsIn Rd own piece run s = K9.formsIn Rd' own piece run s := by
  unfold K9.formsIn
  rw [h]

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **THE PUBLIC TESTS BEHIND THE MERGE, AT THE COMPOSED MEANING**: the clause on public items of
the merge's second tie. keep: the items that other authors' lemmas carry across the merge. -/
theorem merge_pubHeld (Pm : HeadMergeP) (m : ℕ) (O O' : List Item) (Q Q' : List Pub)
    (keep : List Pub) (z : P) {a b : S} {rs : List Fmt.RoundView}
    (hy : headMergeDecide Pm a rs = .ok b)
    -- closed facts on the table
    (hL : ∀ q ∈ Q' ++ pubOfItems O', q ∈ [Pub.ledger m, .freeAbove m, .leftOn m, .indexIs,
      .indexThere, .hasRow m, .formsIn m 9 "merged"] ++ keep)
    (hIn : ∀ q ∈ [Pub.ledger m, .freeAbove m, .indexIs, .indexThere] ++ keep,
      q ∈ Q ++ pubOfItems O)
    (hsub : D.links[m]? = some .head)
    -- what others carry
    (hkeep : ∀ q ∈ keep, (mgAll D Mg).pub q (z, a) = true → (mgAll D Mg).pub q (z, b) = true)
    -- what the merge makes
    (hRow : hasRow D.d1.lay (D.d1.ncl m) D.d1.lin b = true)
    (l : Link S Claim) (name : String) (r : ℕ → S → Except String (List Claim × S))
    (hlk : D.lk m = some l)
    (hst : ((K9.statesOfLink l 8).find? fun x => x.1 == "the merge") = some (name, r))
    (hr : ∀ n t y, r n t = .ok y ↔ headMergeClaim n t = .ok y)
    (hMade : K9.formsIn (K9.Readers.ofStates (mergeStates "the merge")) (D.N.group m) 8 "the merge"
      b = true) :
    pubHeld (mgAll D Mg) O Q (z, a) = true → pubHeld (mgAll D Mg) O' Q' (z, b) = true := by
  unfold pubHeld
  rw [List.all_eq_true, List.all_eq_true]
  intro H q hq
  have front : ∀ q ∈ [Pub.ledger m, .freeAbove m, .indexIs, .indexThere] ++ keep,
      (mgAll D Mg).pub q (z, a) = true := fun q hq => H q (hIn q hq)
  have hl : ledgerB a = true := front (.ledger m) (by simp)
  have hf : ((D.pubD.nsOf m).any fun n => freeAboveB n a) = true := front (.freeAbove m) (by simp)
  obtain ⟨n, hn, hfn⟩ := (Option.any_eq_true _ _).1 hf
  obtain ⟨k1, k2⟩ := merge_keeps_ledger Pm hy n hl hfn
  obtain ⟨_, _, _, _, eb, _⟩ := isLocal Pm a rs b hy
  have eo : b.out = a.out := by rw [eb]
  have es : b.st = a.st := by rw [eb]
  have hq' := hL q hq
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hq'
  rcases hq' with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hk
  · exact k1
  · show ((D.pubD.nsOf m).any fun n => freeAboveB n b) = true
    rw [hn]
    exact k2
  · rfl
  · have h0 : K13.indexIsC D.pubD.N.indexNo a = true := front .indexIs (by simp)
    show K13.indexIsC D.pubD.N.indexNo b = true
    unfold K13.indexIsC at h0 ⊢
    rw [eo]
    exact h0
  · have h0 : K13.indexThereC a = true := front .indexThere (by simp)
    show K13.indexThereC b = true
    unfold K13.indexThereC at h0 ⊢
    rw [eo, es]
    exact h0
  · exact hRow
  · show ((D.runs m 9 "merged").all fun p =>
      if D.ah p.1 p.2 then K9.formsInA (D.Rd m) (D.N.sent m) (D.N.group m) p.1 p.2 b
      else K9.formsIn (D.Rd m) (D.N.group m) p.1 p.2 b) = true
    have e : D.runs m 9 "merged" = [(8, "the merge")] := by
      show runsAt D.links m 9 "merged" = _
      rw [runsAt_of D.links m .head hsub]
      exact runs_head.2.2.2.2.2.2.2
    have hah : D.ah 8 "the merge" = false := by
      show ("the merge" == "K8.equations") = false
      decide
    rw [e]
    simp only [List.all_cons, List.all_nil, Bool.and_true, hah, Bool.false_eq_true, if_false]
    rw [formsIn_congr (D.Rd m) (K9.Readers.ofStates (mergeStates "the merge")) _ 8 "the merge" b ?_]
    · exact hMade
    · have hRd : D.Rd m =
          K9.readersOfLink (K9.holesAt X (VerifiableInference.OnPublicFiles.headLink X) m l) l :=
        K9.readersAt_some D.lk X _ m l hlk
      rw [hRd]
      exact forms_link_merge X _ m l 8 "the merge" name (by decide) r hst hr b
  · exact hkeep q hk (front q (by simp [hk]))

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.merge_pubHeld
