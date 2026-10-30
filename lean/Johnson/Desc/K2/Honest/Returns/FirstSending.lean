-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/FirstSending.lean: THE FIRST SEGMENT's FIRST SENDING, IN THE BOOK OF
TREES OF EVERY LATER STATE: its messages have the numbers from 0 on and stand where `layTrees` lays
them; and, UNDER THE SHAPE's OWN PUBLIC TEST `reqShapeOk` (a premise here), WHAT RIDES AT THE START
HAS A GREATER CLASS OF LEAVES THAN THE SEGMENT's OWN MESSAGES OF MOMENT 0 AND THE FRESH MASK. The
first: in the goals' scope, from the returns of one fold; the second: on the shape's text alone. A
tool for `ReadFits.own` at the switch into group 1 (with Returns/TreeClass.lean). Statements with
their proofs.

  `le_foldl_max`, `class_le_most`, `riders_above` on the shape's text (OnBytes/Iop/Req.lean): a
                    segment's message's class is at most `reqMostClass`; under `reqShapeOk` a
                    rider's is above it
  `first_sent` the opening's list of messages, written out: the own messages of moment 0, the fresh
                    mask, what rides at the start
  `first_class` under `reqShapeOk`: number i up to the fresh mask's, number j behind it ⊢ the class
                    at i is below the class at j; the fresh mask's class is 0 there, by unfolding
  `first_places` THE TOP: from the fold's returns at the cuts 3 and k, 3 ≤ k up to the front's
                    length: the count at 3 is the list's length; `layTrees` lays the list at the
                    public codes; and in the book at k message number i of the list has the place
                    (its tree, its part) of that layout

By, all the library's: `PlacesStay`, `seatKeeps_places` (Johnson/IMR/BookFitsSeat.lean): every older
place stays, over every sub-protocol in front · `SeatKeeps.frames` (Johnson/IMR/SeatKeeps.lean),
`open_between` (Johnson/IMR/WalkGivesAt.lean) · `Seated` (Johnson/Desc/Book/Seated.lean) ·
`k1_first_sits`, `Joined.yes` (Johnson/IMR/FirstSeats.lean), `hear_at_flat`
(Johnson/IMR/FlatIx.lean), `flatIx_scope` (Johnson/IMR/FlatScope.lean) · `firstAtS_two`
(Johnson/IMR/GroupZero.lean) · `firstAtS_seated`, `SeatedBy`
(Johnson/Desc/K1/Law/SeatedAtRecord.lean) · `laid_is_start` (Johnson/IMR/GroupAt.lean),
`start_empty` (Johnson/IMR/BookSeat.lean), `start_msgs` (Johnson/IMR/KeptJoin.lean) · `framesOf_st`
(Johnson/IMR/GroupFill.lean) · `fold_back`, `fold_next` (Johnson/IMR/FoldTools.lean).
`first_places`' descent to the text's yes is the library's `entry_at_zero`'s
(Johnson/IMR/FrameEntry.lean), retyped.

Limits. That a fold returns is shown of no proof here. Nothing behind the place behind the last
segment. This file's imports are heavy. Nothing on any property.



-/
import Johnson.IMR.FlagsZeroNamed
import Johnson.IMR.AtReach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open OnBytes.Params (ReqMessage ReqLink ReqShape)
open VerifiableInference.Desc (foldBlocks Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open Meaning.K2 (PlacesStay seatKeeps_places open_between frontOf firstAtS_two laid_is_start
  start_empty start_msgs framesOf_st fold_back fold_next)
open ProofFile (Cl)

/-- A member of a list is at most the list's greatest. -/
theorem le_foldl_max : ∀ (l : List Nat) (a x : Nat), x ∈ l ∨ x ≤ a → x ≤ l.foldl max a
  | [], a, x, h => by
    rcases h with h | h
    · cases h
    · exact h
  | y :: l, a, x, h => by
    refine le_foldl_max l (max a y) x ?_
    rcases h with h | h
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inr (Nat.le_max_right _ _)
      · exact Or.inl h
    · exact Or.inr (Nat.le_trans h (Nat.le_max_left _ _))

theorem class_le_most {s : ReqShape} {L : ReqLink} (hL : L ∈ s.link) {m : ReqMessage}
    (hm : m ∈ L.messages) : m.leafClass ≤ reqMostClass s := by
  unfold reqMostClass
  exact le_foldl_max _ 0 _ (Or.inl (List.mem_flatMap.2 ⟨L, hL, List.mem_map.2 ⟨m, hm, rfl⟩⟩))

theorem riders_above {s : ReqShape} (h : reqShapeOk s = true) :
    ∀ n ∈ s.atStart, reqMostClass s < n.leafClass := by
  unfold reqShapeOk at h
  simp only [Bool.and_eq_true] at h
  have a := h.1.1.1.1.2
  intro n hn
  have b := List.all_eq_true.1 a n hn
  simp only [Bool.and_eq_true, decide_eq_true_eq] at b
  exact b.2

/-- **The opening's list of messages, written out.** -/
theorem first_sent (q : Params.First) (gp : _root_.Desc.Plain.GPar) :
    (K1.firstPar q gp).sent =
      (((K1.frame₀ q).atMoment 0).map
          (fun m => ({ shape := m.shape, leafClass := m.leafClass } : OracleNotice)) ++
        [foldMaskNotice ((K1.frame₀ q).foldShape 0 {})] ++ q.shape.atStart).toArray := by
  simp [K1.Par.sent, K1.firstPar, K1.firstParts, K1.firstLaid, ReqFrame.notices]

/-- **What rides at the start has a greater class of leaves.** -/
theorem first_class {q : Params.First} (gp : _root_.Desc.Plain.GPar)
    (hok : reqShapeOk q.shape = true) {i j : Nat} (hi : i ≤ ((K1.frame₀ q).atMoment 0).length)
    (hj : ((K1.frame₀ q).atMoment 0).length < j) (hj' : j < (K1.firstPar q gp).sent.size) :
    ((K1.firstPar q gp).sent.getD i default).leafClass <
      ((K1.firstPar q gp).sent.getD j default).leafClass := by
  rw [first_sent] at hj' ⊢
  simp only [List.size_toArray, List.length_append, List.length_map, List.length_cons,
    List.length_nil] at hj'
  have hl : ((((K1.frame₀ q).atMoment 0).map
      (fun m => ({ shape := m.shape, leafClass := m.leafClass } : OracleNotice)) ++
        [foldMaskNotice ((K1.frame₀ q).foldShape 0 {})]).length) =
      ((K1.frame₀ q).atMoment 0).length + 1 := by simp
  -- the one behind: a rider
  have e2 : ∃ n ∈ q.shape.atStart, ((((K1.frame₀ q).atMoment 0).map
      (fun m => ({ shape := m.shape, leafClass := m.leafClass } : OracleNotice)) ++
        [foldMaskNotice ((K1.frame₀ q).foldShape 0 {})] ++ q.shape.atStart).toArray.getD j
        default) = n := by
    have hk : j - (((K1.frame₀ q).atMoment 0).length + 1) < q.shape.atStart.length := by omega
    refine ⟨q.shape.atStart[j - (((K1.frame₀ q).atMoment 0).length + 1)], List.getElem_mem hk, ?_⟩
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      List.getElem?_append_right (by rw [hl]; omega), hl, List.getElem?_eq_getElem hk]
    rfl
  obtain ⟨n, hn, en⟩ := e2
  rw [en]
  refine Nat.lt_of_le_of_lt ?_ (riders_above hok n hn)
  -- the one in front: an own message, or the fresh mask
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_append_left (by rw [hl]; omega)]
  rcases Nat.lt_or_ge i ((K1.frame₀ q).atMoment 0).length with lt | ge
  · rw [List.getElem?_append_left (by rw [List.length_map]; exact lt), List.getElem?_map,
      List.getElem?_eq_getElem lt]
    show (((K1.frame₀ q).atMoment 0)[i]).leafClass ≤ _
    have hm : ((K1.frame₀ q).atMoment 0)[i] ∈ (K1.frame₀ q).atMoment 0 := List.getElem_mem lt
    generalize ((K1.frame₀ q).atMoment 0)[i] = x at hm ⊢
    unfold ReqFrame.atMoment at hm
    have hm' := (List.mem_filter.1 hm).1
    cases hL : (K1.frame₀ q).shape.link[(K1.frame₀ q).link]? with
    | none =>
      rw [hL] at hm'
      cases hm'
    | some L =>
      rw [hL] at hm'
      exact class_le_most (List.mem_of_getElem? hL) hm'
  · obtain rfl : i = ((K1.frame₀ q).atMoment 0).length := by omega
    rw [List.getElem?_append_right (by simp), List.length_map, Nat.sub_self]
    exact Nat.zero_le _

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The first sending's messages in every later book.** -/
theorem first_places (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R R₁ Rk : List Fmt.RoundView} {C C₁ Ck : List VerifiableInference.Desc.OpenedColumn}
    {t₁ t : S} {k : Nat} (h3 : 3 ≤ k) (hk : k ≤ (frontOf c).length)
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (3)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁))
    (f : foldBlocks 0 (c.blocksInOrder.take (k)) (ProofFile.startS Z p) R C = .ok (t, Rk, Ck)) :
    t₁.st.oracles.size = (K1.firstPar Bs.G₀.first (K1.gpOf Z)).sent.size ∧
      ∃ ly, layTrees Bs.G₀.first.codes (K1.firstPar Bs.G₀.first (K1.gpOf Z)).sent = some ly ∧
        ∀ i, i < (K1.firstPar Bs.G₀.first (K1.gpOf Z)).sent.size →
          t.book.place[i]? = some (ly.tree.getD i 0, ly.part.getD i 0) := by
  obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 2) f₁
  have e0s := laid_is_start hS hR O f₀
  obtain ⟨Lk, b, eLk, e0, J⟩ := IM.k1_first_sits hS hR O
  have i0 : c.blocksInOrder[2]? = some b := by
    have q := IM.hear_at_flat eLk e0
    rwa [(IM.flatIx_scope hS hR O (by omega : 0 ≤ 24) 0).trans
      (by omega : 14 * 0 + 0 + 2 = 2)] at q
  obtain ⟨rs, gs, d⟩ := fold_next i0 f₀ f₁
  obtain ⟨fs, fr, m, hfs, hf, y1, -, y3, -, -⟩ := J.yes d
  revert y1
  generalize rs.take _ = rs'
  generalize gs.take _ = gs'
  intro y1
  have y' : (K1.firstSegmentOpening Bs.G₀.first (K1.gpOf Z) : Block S Unit).decide t₀ rs' gs' = .ok m := y1
  obtain ⟨r₁, r₂, er⟩ := firstAtS_two y'
  rw [er] at y'
  have SB := K1.firstAtS_seated _ _ t₀ m r₁ r₂ _ y'
  have z1 : t₀.st.oracles.size = 0 := by
    rw [e0s, start_msgs O.pub p]
    rfl
  have z2 : t₀.book.trees.size = 0 := by
    rw [e0s, (start_empty O.pub p).1]
    rfl
  have st1 : t₁.st = m.st := framesOf_st hfs fr (List.mem_of_getElem? hf) m t₁ y3
  have k1 : PlacesStay m.book t₁.book :=
    (seatKeeps_places.frames trivial hfs fr (List.mem_of_getElem? hf)).2.1 m t₁ y3
  have k2 : PlacesStay t₁.book t.book :=
    open_between seatKeeps_places O trivial (fun _ _ _ => trivial) h3 hk f₁ f
  refine ⟨by rw [st1, SB.msgs, z1, Nat.zero_add], _, SB.lay, fun i hi => ?_⟩
  have a := SB.seated.new i hi
  rw [z1, z2, Nat.zero_add, Nat.zero_add] at a
  rw [(k1.trans k2) i (Array.getElem?_eq_some_iff.1 a).1]
  exact a

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.le_foldl_max
#print axioms VerifiableInference.Desc.K2.Honest.Returns.class_le_most
#print axioms VerifiableInference.Desc.K2.Honest.Returns.riders_above
#print axioms VerifiableInference.Desc.K2.Honest.Returns.first_sent
#print axioms VerifiableInference.Desc.K2.Honest.Returns.first_class
#print axioms VerifiableInference.Desc.K2.Honest.Returns.first_places
