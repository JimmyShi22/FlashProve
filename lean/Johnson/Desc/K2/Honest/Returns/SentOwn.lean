-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/SentOwn.lean: WHAT THE LAW ON A SEGMENT's FIRST PLACE (`LinkFits`,
Returns/Link.lean) ASKS OF THE MESSAGES THAT THE SWITCH ANNOUNCES BEHIND THE KEPT COPIES (the
segment's own first messages, the fresh mask), AT WHAT THE SENDING RETURNS (`sentAt`,
Returns/Sends.lean): their numbers; that each own message may join the new group; that their numbers
differ; and "no column is left", carried over the sending. Statements and proofs.

  `extract_at`, `extract_get`   an entry of a cut of an array
  `notices_other`   the announced list behind the carrying message and the kept copies: the others
  `other_at`        the number of the j-th of the others: the count in front + 1 + the kept copies
                    + j
  `own_at`          entry j of `ownPairs`: the j-th own message with that number
  `OwnPlain`        THE PREMISES, AT THE FRONT x AND THE NEW GROUP G: more others than own messages
                    · the j-th of the others is announced with an answer; it has the group's codes
                    where it has rows of the sort; it has a main row if the j-th own message has a
                    life
  `own_mask`, `own_join`, `own_differ`   `LinkFits`' fields `theMask`, `join`, `differ`, at these
                    terms (`numbers` is Returns/SendsMore.lean's `sentAt_others`)
  `leftAfter_older`   the columns that the reading leaves are one at two books with the same older
                    trees

Limits. `OwnPlain` is shown nowhere here. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Returns.SentFront
import Johnson.Desc.K2.Honest.Returns.SentRead
import Johnson.Desc.K2.Honest.Returns.BehindOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open OnBytes.Params (ReqMessage)
open _root_.Tw.K2 (Par9 Front Col switchNotices)
open VerifiableInference.Desc.First.K2 (behindArgs outOf notices_size)

theorem extract_at {α : Type} (A : Array α) (s e j : Nat) (v : α)
    (h : (A.extract s e)[j]? = some v) : A[s + j]? = some v ∧ j < e - s := by
  obtain ⟨hj, rfl⟩ := Array.getElem?_eq_some_iff.1 h
  have hj' := hj
  rw [Array.size_extract] at hj'
  refine ⟨?_, by omega⟩
  rw [Array.getElem_extract]
  exact Array.getElem?_eq_getElem _

theorem extract_get {α : Type} (A : Array α) (s e j : Nat) (he : e ≤ A.size) (hj : j < e - s) :
    (A.extract s e)[j]? = A[s + j]? := by
  have h1 : j < (A.extract s e).size := by
    rw [Array.size_extract]
    omega
  rw [Array.getElem?_eq_getElem h1, Array.getElem_extract]
  exact (Array.getElem?_eq_getElem _).symm

theorem notices_other (T : SwitchTarget) (others : Array OracleNotice) (j : Nat) :
    (switchNotices T others)[1 + T.kept.size + j]? = others[j]? := by
  unfold switchNotices
  rw [Array.getElem?_append_right (by simp)]
  simp

section
variable (P : Par9) (x : Front) (B : TreeBook) (roots : Nat) (rS rL : Fmt.RoundView) (cols : List OpenedColumn)
  (Q : K1.Par) (hs : Q.sent = switchNotices x.T x.others) (pos : Positions)
include hs

/-- The number of the j-th message behind the kept copies. -/
theorem other_at (j v : Nat)
    (h : (outOf (behindArgs P x (sentAt Q x.st B roots rS rL) rL cols) pos).others[j]? = some v) :
    v = x.st.oracles.size + (1 + x.T.kept.size + j) ∧ j < x.others.size := by
  have hN : Q.sent.size = 1 + x.T.kept.size + x.others.size := by rw [hs, notices_size]
  obtain ⟨h1, h2⟩ := extract_at (sentAt Q x.st B roots rS rL).ids (1 + x.T.kept.size)
    (sentAt Q x.st B roots rS rL).ids.size j v h
  rw [sentAt_idsSize] at h2
  rw [sentAt_ids Q x.st B roots rS rL _ (by omega)] at h1
  exact ⟨(Option.some.inj h1).symm, by omega⟩

/-- Entry j of the own messages with their numbers. -/
theorem own_at (j : Nat) (q : ReqMessage × Nat)
    (h : (ownPairs x (outOf (behindArgs P x (sentAt Q x.st B roots rS rL) rL cols) pos))[j]? =
      some q) :
    x.own[j]? = some q.1 ∧ q.2 = x.st.oracles.size + (1 + x.T.kept.size + j) ∧
      j < x.others.size := by
  unfold ownPairs at h
  rw [OnBytes.zipT_eq, List.getElem?_zip_eq_some, Array.getElem?_toList] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h3, _⟩ := extract_at _ _ _ _ _ h2
  rw [Nat.zero_add] at h3
  exact ⟨h1, other_at P x B roots rS rL cols Q hs pos j q.2 h3⟩

/-- **The premises, at the front.** -/
structure OwnPlain (x : Front) (G : Group) : Prop where
  more : x.own.length < x.others.size
  each : ∀ (j : Nat) (m : ReqMessage), x.own[j]? = some m → ∃ n, x.others[j]? = some n ∧
    n.shape.answers ≠ 0 ∧ (n.shape.mainRows = 0 ∨ n.shape.code = G.code) ∧
    (n.shape.maskRows = 0 ∨ n.shape.maskCode = G.maskCode) ∧ (0 < m.life → 0 < n.shape.mainRows)

theorem own_mask {G : Group} (F : OwnPlain x G) :
    (outOf (behindArgs P x (sentAt Q x.st B roots rS rL) rL cols) pos).others[x.own.length]? =
      some (x.st.oracles.size + (1 + x.T.kept.size + x.own.length)) := by
  have hN : Q.sent.size = 1 + x.T.kept.size + x.others.size := by rw [hs, notices_size]
  have hm := F.more
  show ((sentAt Q x.st B roots rS rL).ids.extract (1 + x.T.kept.size)
    (sentAt Q x.st B roots rS rL).ids.size)[x.own.length]? = _
  rw [extract_get _ _ _ _ (Nat.le_refl _) (by rw [sentAt_idsSize]; omega),
    sentAt_ids Q x.st B roots rS rL _ (by omega)]

theorem own_join {G : Group} (F : OwnPlain x G) :
    ∀ q ∈ ownPairs x (outOf (behindArgs P x (sentAt Q x.st B roots rS rL) rL cols) pos),
      MayJoin (sentAt Q x.st B roots rS rL).st G.code G.maskCode q.2 (decide (0 < q.1.life)) ∧
        q.2 ≠ (sentAt Q x.st B roots rS rL).ids.getD 0 noId ∧
        q.2 ∉ ((sentAt Q x.st B roots rS rL).ids.extract 1 (1 + x.T.kept.size)).toList := by
  intro q hq
  have hN : Q.sent.size = 1 + x.T.kept.size + x.others.size := by rw [hs, notices_size]
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hq
  obtain ⟨h1, h2, _⟩ := own_at P x B roots rS rL cols Q hs pos j q hj
  obtain ⟨n, hn, a0, a1, a2, a3⟩ := F.each j q.1 h1
  obtain ⟨m, e, s, p, _⟩ := new_at Q x.st B roots rS rL (1 + x.T.kept.size + j) n.shape
    (by rw [hs, notices_other, hn]; rfl) a0
  refine ⟨⟨m, by rw [h2]; exact e, p, by rw [s]; exact a1, by rw [s]; exact a2, fun hk => ?_⟩,
    ?_, ?_⟩
  · rw [s]
    exact a3 (of_decide_eq_true hk)
  · rw [show (sentAt Q x.st B roots rS rL).ids.getD 0 noId = x.st.oracles.size from
      numbers_first Q _ (by omega), h2]
    omega
  · rw [show ((sentAt Q x.st B roots rS rL).ids.extract 1 (1 + x.T.kept.size)).toList =
      (List.range x.T.kept.size).map (x.st.oracles.size + 1 + ·) from
      numbers_kept Q _ _ (by omega), h2]
    intro hin
    obtain ⟨i, hi, e'⟩ := List.mem_map.1 hin
    have := List.mem_range.1 hi
    omega

theorem own_differ :
    ((ownPairs x (outOf (behindArgs P x (sentAt Q x.st B roots rS rL) rL cols) pos)).map
      (·.2)).Nodup := by
  rw [List.Nodup, List.pairwise_iff_getElem]
  intro a b ha hb hab
  rw [List.length_map] at ha hb
  rw [List.getElem_map, List.getElem_map]
  have e1 := (own_at P x B roots rS rL cols Q hs pos a _ (List.getElem?_eq_getElem ha)).2.1
  have e2 := (own_at P x B roots rS rL cols Q hs pos b _ (List.getElem?_eq_getElem hb)).2.1
  rw [e1, e2]
  omega

end

theorem leftAfter_older (pos : Positions) {B B' : TreeBook}
    (ht : ∀ t, t < B.trees.size → B'.trees[t]? = B.trees[t]?) :
    ∀ (ts : List Nat) (c : List OpenedColumn), (∀ t ∈ ts, t < B.trees.size) →
      leftAfter pos B' ts c = leftAfter pos B ts c
  | [], _, _ => rfl
  | t :: ts, c, h => by
    have eo : ownAt pos B' t = ownAt pos B t := by
      unfold ownAt
      rw [ht t (h t List.mem_cons_self)]
    show leftAfter pos B' ts (c.drop (ownAt pos B' t).size) = leftAfter pos B ts _
    rw [eo]
    exact leftAfter_older pos ht ts _ fun t' h' => h t' (List.mem_cons_of_mem _ h')

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.own_at
#print axioms VerifiableInference.Desc.K2.Honest.Returns.own_mask
#print axioms VerifiableInference.Desc.K2.Honest.Returns.own_join
#print axioms VerifiableInference.Desc.K2.Honest.Returns.own_differ
#print axioms VerifiableInference.Desc.K2.Honest.Returns.leftAfter_older
#print axioms VerifiableInference.Desc.K2.Honest.Returns.extract_at
#print axioms VerifiableInference.Desc.K2.Honest.Returns.extract_get
#print axioms VerifiableInference.Desc.K2.Honest.Returns.notices_other
#print axioms VerifiableInference.Desc.K2.Honest.Returns.other_at
