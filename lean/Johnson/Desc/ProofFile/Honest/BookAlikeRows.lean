-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookAlikeRows.lean: THE MAKERS OF THE BOOK OF COINS' ROWS, CUTS,
MERGES AND SEGMENTS' STRETCHES GIVE ONE ANSWER AT TWO LISTS OF SUB-PROTOCOLS THAT ARE ALIKE BLOCK BY
BLOCK, IN ORDER: eleven congruences.
Written by the authors of the honest side of the linear claim's shared rounds (K14), in the frame's
folder, not by the frame's authors; the makers are theirs. CONDITIONAL, each on the premise that the
two blocks, or the two lists, are alike. Theorems alone; no definition.

The relation is the library's own (Johnson/AtFull/ProofPlan/PlanAlike.lean): Alike₂ b b': place,
rounds, oracles and before are equal, and where b's own test on the plan passes b' 's does. Of it
place and rounds alone are spent here.

  planParts_alike     at two blocks: a sub-protocol's parts, by the maker's own cut
  planPartsIn_alike   the parts of all sub-protocols of a list
  partsWhere_alike    the parts of those whose place passes a test: in a link; in no link
  linksIn_alike       the links' numbers, in the lists' order
  cutsIn_alike        the cut at each sub-protocol of a list that has a round
  mergesByName_alike  the guess which masked sumchecks are merges
  rowsIn_alike        a chain's rows: the same list, or the same refusal
  switchRows_alike    the rows of a chain's switches: the same list, or the same refusal
  segmentWants_alike  a segment's stretches
  linksWants_alike    all links' stretches and the next free entry, or the same refusal
  cutsOf_alike        at two descriptions whose three chains are alike: the book's field cuts

How. planParts_alike by unfolding and partsCut_alike; planPartsIn_alike, partsWhere_alike,
linksIn_alike and cutsIn_alike each by an induction on List.Forall₂; linksWants_alike by a recursion
on the list of links; segmentWants_alike is partsWhere_alike under the maker's own text; the rest by
unfolding and rewriting with these, with the library's alike₂_rounds and with seedRounds_alike,
addrOfRound_alike and ownerOf_alike (Honest/BookAlike.lean). THE ANSWERS ARE EQUAL AS VALUES, THE
REFUSALS' WORDS TOO.

Limits. NO RETURN IS SHOWN BY IT, AT ANY LIST: IT CARRIES ONE. That two lists are alike is not had
here. Nothing on any test's verdict. Bookkeeping on lists. Kin: the nine congruences of
Honest/BookAlike.lean, over which it stands, and Honest/BookSharedAlike.lean (the short list's).
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.BookAlike

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place Alike₂ alike₂_rounds)

variable {S Cl S' Cl' : Type}

/-- **A sub-protocol's parts at two blocks that are alike.** CONDITIONAL: h. -/
theorem planParts_alike {b : Block S Cl} {b' : Block S' Cl'} (h : Alike₂ b b') :
    planParts b = planParts b' := by
  unfold planParts
  rw [h.1, h.2.1, partsCut_alike h]

section
variable {l : List (Block S Cl)} {l' : List (Block S' Cl')} (h : List.Forall₂ Alike₂ l l')
include h

/-- The parts of all sub-protocols of a list. CONDITIONAL: h: the lists are alike. -/
theorem planPartsIn_alike : l.flatMap planParts = l'.flatMap planParts := by
  induction h with
  | nil => rfl
  | @cons b b' l l' hb _ ih => simp only [List.flatMap_cons, planParts_alike hb, ih]

/-- CONDITIONAL: h. **The parts of the sub-protocols whose place passes a test**: one lemma for "in
the link number n" (segmentWants) and "in no link" (spendingBook). -/
theorem partsWhere_alike (t : Place → Bool) :
    (l.filter fun b => t b.place).flatMap planParts =
      (l'.filter fun b => t b.place).flatMap planParts := by
  induction h with
  | nil => rfl
  | @cons b b' l l' hb _ ih =>
    by_cases ht : t b'.place = true
    · rw [List.filter_cons_of_pos (by show t b.place = true; rw [hb.1]; exact ht),
        List.filter_cons_of_pos (by show t b'.place = true; exact ht), List.flatMap_cons,
        List.flatMap_cons, planParts_alike hb, ih]
    · rw [List.filter_cons_of_neg (by show ¬ t b.place = true; rw [hb.1]; exact ht),
        List.filter_cons_of_neg (by show ¬ t b'.place = true; exact ht), ih]

/-- CONDITIONAL: h. The links' numbers, in the lists' order. -/
theorem linksIn_alike : l.filterMap (·.place.link) = l'.filterMap (·.place.link) := by
  induction h with
  | nil => rfl
  | @cons b b' l l' hb _ ih => simp only [List.filterMap_cons, hb.1, ih]

/-- The cut at each sub-protocol of a list that has a round. CONDITIONAL: h. -/
theorem cutsIn_alike : cutsIn l = cutsIn l' := by
  unfold cutsIn
  induction h with
  | nil => rfl
  | @cons b b' l l' hb _ ih =>
    simp only [List.filter_cons, hb.2.1]
    split
    · simp only [List.map_cons, hb.1, partsCut_alike hb, ih]
    · exact ih

/-- The guess which masked sumchecks are merges. CONDITIONAL: h. -/
theorem mergesByName_alike : mergesByName l = mergesByName l' := by
  unfold mergesByName
  rw [planPartsIn_alike h]

/-- CONDITIONAL: h. The same list of rows, or the same refusal. -/
theorem rowsIn_alike (c : Johnson.G.ChainSends) (later : List Fmt.DeclaredRound) :
    rowsIn l c later = rowsIn l' c later := by
  unfold rowsIn
  simp only [seedRounds_alike h, alike₂_rounds l l' h, addrOfRound_alike h]

/-- CONDITIONAL: h. The same list of rows, or the same refusal. -/
theorem switchRows_alike (c : Johnson.G.ChainSends)
    (first : String → Option (OnBytes.Code × OnBytes.Code)) :
    switchRows l c first = switchRows l' c first := by
  unfold switchRows
  simp only [seedRounds_alike h, alike₂_rounds l l' h, addrOfRound_alike h]

/-- The stretches of the segment in the link number n, and the next free entry. CONDITIONAL: h. -/
theorem segmentWants_alike (n : Nat) (row idx : MsgAt) (merges : List Addr) (t : Nat) :
    segmentWants l n row idx merges t = segmentWants l' n row idx merges t :=
  congrArg (fun ps => partsWants row idx merges ps 0 t)
    (partsWhere_alike h fun p => p.link == some n)

/-- CONDITIONAL: h. The same stretches and the same next free entry, or the same refusal. -/
theorem linksWants_alike (c : Johnson.G.ChainSends) (later : List Fmt.DeclaredRound) (idx : MsgAt)
    (merges : List Addr) (ls : List Nat) (t : Nat) :
    linksWants l c later idx merges ls t = linksWants l' c later idx merges ls t := by
  induction ls generalizing t with
  | nil => rfl
  | cons n ls ih =>
    show (match ownerOf maskRowRun l c later s!"link {n}, moment 0" isMaskRowMsg with
      | none =>
        (.error s!"segment {n}: its mask row is not found" : Except String (List Want × Nat))
      | some row => (linksWants l c later idx merges ls (segmentWants l n row idx merges t).2).map
          fun (y : List Want × Nat) => ((segmentWants l n row idx merges t).1 ++ y.1, y.2)) =
      (match ownerOf maskRowRun l' c later s!"link {n}, moment 0" isMaskRowMsg with
      | none =>
        (.error s!"segment {n}: its mask row is not found" : Except String (List Want × Nat))
      | some row => (linksWants l' c later idx merges ls (segmentWants l' n row idx merges t).2).map
          fun (y : List Want × Nat) => ((segmentWants l' n row idx merges t).1 ++ y.1, y.2))
    rw [ownerOf_alike h]
    cases ownerOf maskRowRun l' c later s!"link {n}, moment 0" isMaskRowMsg with
    | none => rfl
    | some row => simp only [segmentWants_alike h, ih]

end

/-- **The book's field cuts at two descriptions.** CONDITIONAL: h₁, h₂, h₃: the three chains' flat
lists are alike. -/
theorem cutsOf_alike {Xi Xi' : Type} {W : FileDescription Xi} {F : FileDescription Xi'}
    (h₁ : List.Forall₂ Alike₂ W.first.blocksInOrder F.first.blocksInOrder)
    (h₂ : List.Forall₂ Alike₂ W.shared.blocksInOrder F.shared.blocksInOrder)
    (h₃ : List.Forall₂ Alike₂ W.second.blocksInOrder F.second.blocksInOrder) : cutsOf W = cutsOf F := by
  unfold cutsOf
  rw [cutsIn_alike h₁, cutsIn_alike h₂, cutsIn_alike h₃]

end ProofFile.Honest

#print axioms ProofFile.Honest.planParts_alike
#print axioms ProofFile.Honest.planPartsIn_alike
#print axioms ProofFile.Honest.partsWhere_alike
#print axioms ProofFile.Honest.linksIn_alike
#print axioms ProofFile.Honest.cutsIn_alike
#print axioms ProofFile.Honest.mergesByName_alike
#print axioms ProofFile.Honest.rowsIn_alike
#print axioms ProofFile.Honest.switchRows_alike
#print axioms ProofFile.Honest.segmentWants_alike
#print axioms ProofFile.Honest.linksWants_alike
#print axioms ProofFile.Honest.cutsOf_alike
