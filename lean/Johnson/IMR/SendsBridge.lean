-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/SendsBridge.lean: KIND-FREE BUT FOR ITS LAST LEMMA; IT IMPORTS NO FILE OF Johnson/IMR/
BUT Johnson/IMR/SendsFold.lean: FROM «WHAT ONE SENDING LAYS INTO THE BOOK», SAID PLACE BY PLACE
(Johnson/Desc/Book/Seated.lean: Book.Seated; SeatedBy, Johnson/Desc/K1/Law/SeatedAtRecord.lean), TO
Appends codes [sent] B B' (Johnson/Desc/K12/Coin/BookAppends.lean), SAID IN LISTS: so that
firstAtS_seated | commitAtS_seated | atM4_seated pay the debt SendsAt (Johnson/IMR/SendsFold.lean).


  places_of_seated  B'.place.toList = B.place.toList ++ placesOf B.trees.size n lay.
  shapes_of_seated  B'.trees.toList.map (·.shape) = B.trees.toList.map (·.shape) ++ lay.shapes.toList.
  appends_of_seated layTrees codes sent = some lay → Book.Seated B B' sent.size n0 lay num src → Appends codes [sent] B B'.
  sends_of_seatedBy a sub-protocol each of whose step's acceptings is SeatedBy P and leaves the code table, at P.codes = codes: SendsAt ft codes [P.sent] b.

What is not claimed. That a sub-protocol's accepting is SeatedBy: K1's files' to show. P.codes = codes: a premise on the plan. No soundness.
-/
import Johnson.IMR.SendsFold
import Johnson.Desc.K1.Law.SeatedAtRecord

set_option autoImplicit false

namespace IM

open OnBytes (Codes OracleNotice TreeBook TreeLay layTrees)
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K12.Coin (Laid laidFrom placesOf Appends)
open ProofFile (Cl)

theorem places_of_seated {B B' : TreeBook} {n n0 : ℕ} {lay : TreeLay} {num : ℕ → ℕ}
    {src : ℕ → Fmt.Src} (h : VerifiableInference.Desc.Book.Seated B B' n n0 lay num src) :
    B'.place.toList = B.place.toList ++ placesOf B.trees.size n lay := by
  apply List.ext_getElem?
  intro j
  rw [Array.getElem?_toList]
  by_cases hj : j < B.place.size
  · rw [h.places j hj, List.getElem?_append_left (by rw [Array.length_toList]; exact hj),
      Array.getElem?_toList]
  · rw [List.getElem?_append_right (by rw [Array.length_toList]; omega), Array.length_toList]
    unfold placesOf
    rw [List.getElem?_map]
    by_cases hi : j - B.place.size < n
    · have e := h.new (j - B.place.size) hi
      rw [h.step, show B.place.size + (j - B.place.size) = j by omega] at e
      rw [e, List.getElem?_range hi]
      rfl
    · rw [Array.getElem?_eq_none (by rw [h.count]; omega),
        List.getElem?_eq_none (by rw [List.length_range]; omega)]
      rfl

theorem shapes_of_seated {B B' : TreeBook} {n n0 : ℕ} {lay : TreeLay} {num : ℕ → ℕ}
    {src : ℕ → Fmt.Src} (h : VerifiableInference.Desc.Book.Seated B B' n n0 lay num src) :
    B'.trees.toList.map (·.shape) = B.trees.toList.map (·.shape) ++ lay.shapes.toList := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_map, Array.getElem?_toList]
  by_cases hj : j < B.trees.size
  · rw [h.trees j hj, List.getElem?_append_left
      (by rw [List.length_map, Array.length_toList]; exact hj), List.getElem?_map,
      Array.getElem?_toList]
  · rw [List.getElem?_append_right (by rw [List.length_map, Array.length_toList]; omega),
      List.length_map, Array.length_toList, Array.getElem?_toList]
    by_cases hi : j - B.trees.size < lay.shapes.size
    · obtain ⟨t, e, hs, -⟩ := h.made (j - B.trees.size) hi
      rw [show B.trees.size + (j - B.trees.size) = j by omega] at e
      rw [e, Option.map_some, hs, Array.getElem?_eq_getElem hi, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem hi]
      rfl
    · rw [Array.getElem?_eq_none (by rw [h.size]; omega), Array.getElem?_eq_none (by omega)]
      rfl

/-- **From the book said place by place to the book said in lists.** -/
theorem appends_of_seated {codes : Codes} {sent : Array OracleNotice} {lay : TreeLay}
    {B B' : TreeBook} {n0 : ℕ} {num : ℕ → ℕ} {src : ℕ → Fmt.Src}
    (hl : layTrees codes sent = some lay)
    (h : VerifiableInference.Desc.Book.Seated B B' sent.size n0 lay num src) :
    Appends codes [sent] B B' := by
  refine ⟨{ places := placesOf B.trees.size sent.size lay ++ [],
            shapes := lay.shapes.toList ++ [] }, ?_, ?_, ?_⟩
  · show ((layTrees codes sent).bind fun lay => _) = _
    rw [hl]
    rfl
  · show _ = _ ++ (placesOf B.trees.size sent.size lay ++ [])
    rw [List.append_nil]
    exact places_of_seated h
  · show _ = _ ++ (lay.shapes.toList ++ [])
    rw [List.append_nil]
    exact shapes_of_seated h

/-- **SeatedBy pays the debt.** -/
theorem sends_of_seatedBy {ft : ℕ} {codes : Codes} {P : VerifiableInference.Desc.K1.Par}
    {b : Block S Cl} (hP : P.codes = codes)
    (h : ∀ (s s' : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (n : ℕ),
      b.step ft s rs cols = .ok (s', n) → s'.st.codes = s.st.codes ∧
        VerifiableInference.Desc.K1.SeatedBy P s.book s.st.oracles.size s.roots s'.book
          s'.st.oracles.size s'.roots) : SendsAt ft codes [P.sent] b := by
  intro s s' rs cols n hy hc
  obtain ⟨c1, H⟩ := h s s' rs cols n hy
  refine ⟨c1.trans hc, appends_of_seated (hP ▸ H.lay) H.seated, fun _ => ?_⟩
  unfold InStep
  rw [H.msgs, H.seated.count, H.seated.step]

end IM

#print axioms IM.places_of_seated
#print axioms IM.shapes_of_seated
#print axioms IM.appends_of_seated
#print axioms IM.sends_of_seatedBy
