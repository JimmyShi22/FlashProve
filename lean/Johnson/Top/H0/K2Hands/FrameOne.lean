-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/FrameOne.lean: one frame, up to the messages' numbers, for all
fronts with one public side by place. Theorems; the tests' text stands in FramePin.lean.

Why this form: see FramePin.lean's head. ONE frame for the two fronts
cannot be met by a record's front and a written front, whose
messages bear other numbers.

  `anewOf x`: the numbers that the switch's sending gives the messages for the kept rows.
  `ids_zero`, `anew_size`: g's number at a front is the number of messages in front; there are as
     many new numbers as the target has messages for kept rows: neither hangs on the other
     announcements.
  `pin_facts`: what `pinB`'s yes says, clause by clause.
  `skel_kept`, `skel_g`: in the statement that the frame at a front reads, a kept old message has
     the shape that it has in front, and g has the target's shape.
  `frame_pin`: at `pinB x₀ x = true`, where the frame at x₀ is W₀, the frame at x is
     `renumber W₀ ‹x's own numbers›`.
  `realOf W₀ x`: that frame.
  `nums_of_test`: what `numsB`'s yes says.
  `renumber_get`, `renumber_kept_rows`: a renumbered frame's kept places, one by one; their rows.
  `front_nine`: frameIs, z32, twoOld, codes, keptPos, keptRows, ell, first, next of `FrontAt`
     (TiePaid.lean) at x AND AT THE FRAME `realOf W₀ x`, from `pinB x₀ x = true`, three facts on x₀
     alone (its frame is W₀; its codes are cs; `frontPubB` says yes at it) and two on x: no kept
     old message stands twice; `Tied` at x's own announcements.
Limits. x₀ is not made of the plan here. `pinB` and `numsB` are tests on the front of a record:
who makes them true along the chain is not said. Nothing on soundness.

-/
import Johnson.Top.H0.K2Hands.FramePin
import Johnson.Top.H0.K2Hands.FrameRenumbered
import Johnson.Top.H0.K2Hands.FrontPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes
open _root_.Tw.K2 (switchNotices)

/-- The numbers of the messages that take the kept rows, as the frame at a front cuts them. -/
def anewOf (x : _root_.Tw.K2.Front) : Array ℕ :=
  (K2.idsOf x).extract 1 (1 + x.T.kept.size)

theorem notices_size (T : SwitchTarget) (others : Array OracleNotice) :
    (switchNotices T others).size = 1 + T.kept.size + others.size := by
  simp [switchNotices]
  omega

theorem ids_zero (x : _root_.Tw.K2.Front) : (K2.idsOf x).getD 0 noId = x.st.oracles.size := by
  have h : 0 < (switchNotices x.T x.others).size := by rw [notices_size]; omega
  simp [K2.idsOf, Array.getD, h]

theorem anew_size (x : _root_.Tw.K2.Front) : (anewOf x).size = x.T.kept.size := by
  unfold anewOf K2.idsOf
  simp only [Array.size_extract, Array.size_map, Array.size_range, notices_size]
  omega

/-- What the test's yes says. -/
structure Pinned (x₀ x : _root_.Tw.K2.Front) : Prop where
  codes : x.st.codes = x₀.st.codes
  shapes : keptShapes x = keptShapes x₀
  below : ∀ o ∈ (switchKept x.f.rows).toList, o < x.st.oracles.size
  below₀ : ∀ o ∈ (switchKept x₀.f.rows).toList, o < x₀.st.oracles.size
  shape : x.T.shape = x₀.T.shape
  main : x.T.main = x₀.T.main
  rest : x.T.rest = x₀.T.rest
  kept : x.T.kept.toList.map (·.shape) = x₀.T.kept.toList.map (·.shape)
  code : x.f.rows.code = x₀.f.rows.code
  maskCode : x.f.rows.maskCode = x₀.f.rows.maskCode
  masks : x.f.rows.masks = x₀.f.rows.masks
  keptRows : x.f.rows.keptRows = x₀.f.rows.keptRows

theorem below_of_test {x : _root_.Tw.K2.Front} (h : keptBelowB x = true) :
    ∀ o ∈ (switchKept x.f.rows).toList, o < x.st.oracles.size := by
  intro o ho
  have := Array.all_eq_true_iff_forall_mem.1 h o (Array.mem_toList_iff.1 ho)
  simpa using this

theorem pin_facts {x₀ x : _root_.Tw.K2.Front} (h : pinB x₀ x = true) : Pinned x₀ x := by
  simp only [pinB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩, a12⟩ := h
  exact ⟨a1, a2, below_of_test a3, below_of_test a4, a5, a6, a7, a8, a9, a10, a11, a12⟩

/-- In the statement that the frame reads, g has the target's shape. -/
theorem skel_g (x : _root_.Tw.K2.Front) :
    ((K2.skelOf x).oracles[x.st.oracles.size]?).map (·.shape) = some x.T.shape := by
  have e := OnBytes.Slice.stSent_new x.st (switchNotices x.T x.others) 0
  rw [Nat.add_zero] at e
  unfold K2.skelOf
  rw [e]
  simp [switchNotices]

/-- The kept old messages, place by place, in the two statements that the two frames read. -/
theorem skel_alike {x₀ x : _root_.Tw.K2.Front} (P : Pinned x₀ x) :
    Alike (K2.skelOf x) (K2.skelOf x₀) (switchKept x.f.rows).toList
      (switchKept x₀.f.rows).toList := by
  have hs := P.shapes
  unfold keptShapes at hs
  have hl : (switchKept x.f.rows).toList.length = (switchKept x₀.f.rows).toList.length := by
    have := congrArg List.length hs
    simpa using this
  refine List.forall₂_iff_get.2 ⟨hl, fun i hi hi₀ => ?_⟩
  have e := congrArg (·[i]?) hs
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi₀,
    Option.map_some, Option.some.injEq] at e
  unfold K2.skelOf
  simp only [List.get_eq_getElem]
  rw [OnBytes.Slice.stSent_old _ _ _ (P.below _ (List.getElem_mem hi)),
    OnBytes.Slice.stSent_old _ _ _ (P.below₀ _ (List.getElem_mem hi₀))]
  exact e

/-- The written frame with a front's own numbers. -/
def realOf (W₀ : SwitchFrame) (x : _root_.Tw.K2.Front) : SwitchFrame :=
  renumber W₀ x.st.oracles.size (switchKept x.f.rows) (anewOf x)

/-- **ONE FRAME, UP TO THE MESSAGES' NUMBERS, FOR ALL FRONTS WITH ONE PUBLIC SIDE BY PLACE.** -/
theorem frame_pin {x₀ x : _root_.Tw.K2.Front} {W₀ : SwitchFrame} (h0 : K2.frameAt x₀ = some W₀)
    (h : pinB x₀ x = true) : K2.frameAt x = some (realOf W₀ x) := by
  have P := pin_facts h
  have hA := skel_alike P
  have hsz : (anewOf x).size = (switchKept x.f.rows).size := by
    -- the maker's own guard at x₀, carried over by the two lists' lengths
    have g0 : (anewOf x₀).size = (switchKept x₀.f.rows).size := frame_guard h0
    have k1 : x.T.kept.size = x₀.T.kept.size := by
      have := congrArg List.length P.kept
      simpa using this
    have k2 : (switchKept x.f.rows).size = (switchKept x₀.f.rows).size := by
      have := alike_length hA
      simpa using this
    rw [anew_size, k1, k2, ← g0, anew_size]
  unfold K2.frameAt at h0 ⊢
  rw [ids_zero] at h0 ⊢
  exact frame_renumber h0 P.codes P.code P.maskCode P.masks P.keptRows hA P.shape P.main P.rest
    (by rw [skel_g, skel_g, P.shape]) hsz

theorem nums_of_test {grp rows n0 : ℕ} {olds : List ℕ} {x : _root_.Tw.K2.Front}
    (h : numsB grp rows n0 olds x = true) :
    x.f.group = grp ∧ (∃ G, x.st.groups[grp]? = some G ∧ G.rows.size = rows) ∧
      x.st.oracles.size = n0 ∧ (switchKept x.f.rows).toList = olds := by
  simp only [numsB, Bool.and_eq_true, beq_iff_eq, Option.any_eq_true_iff_get] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  obtain ⟨hs, h2⟩ := h2
  obtain ⟨G, hG⟩ := Option.isSome_iff_exists.1 hs
  refine ⟨h1, ⟨G, by rw [← h1]; exact hG, ?_⟩, h3, h4⟩
  simpa [hG] using h2

/-! ## The nine clauses at the renumbered frame -/

theorem renumber_get (W : SwitchFrame) (g : ℕ) (olds anew : Array ℕ) (a : ℕ) :
    (renumber W g olds anew).kept[a]? = (W.kept[a]?).map fun k =>
      { k with old := olds.getD a noId, anew := anew.getD a noId } := by
  simp [renumber, List.getElem?_mapIdx]

theorem renumber_kept_rows (W : SwitchFrame) (g : ℕ) (olds anew : Array ℕ) :
    (renumber W g olds anew).kept.map (·.rows) = W.kept.map (·.rows) := by
  refine List.ext_getElem? fun a => ?_
  rw [List.getElem?_map, List.getElem?_map, renumber_get]
  cases W.kept[a]? <;> rfl

/-- The kept old messages, place by place, in the two statements in front. -/
theorem front_alike {x₀ x : _root_.Tw.K2.Front} (P : Pinned x₀ x) :
    Alike x.st x₀.st (switchKept x.f.rows).toList (switchKept x₀.f.rows).toList := by
  have hs := P.shapes
  unfold keptShapes at hs
  have hl : (switchKept x.f.rows).toList.length = (switchKept x₀.f.rows).toList.length := by
    have := congrArg List.length hs
    simpa using this
  refine List.forall₂_iff_get.2 ⟨hl, fun i hi hi₀ => ?_⟩
  have e := congrArg (·[i]?) hs
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi₀,
    Option.map_some, Option.some.injEq] at e
  simp only [List.get_eq_getElem]
  exact e

theorem keptPos_pin {x₀ x : _root_.Tw.K2.Front} (P : Pinned x₀ x) (h : K2.KeptPos x₀.T) :
    K2.KeptPos x.T := by
  intro i hi
  have hl : x.T.kept.size = x₀.T.kept.size := by
    have := congrArg List.length P.kept
    simpa using this
  have hi₀ : i < x₀.T.kept.size := by rw [← hl]; exact hi
  have e := congrArg (·[i]?) P.kept
  simp only [List.getElem?_map, Array.getElem?_toList, Array.getElem?_eq_getElem hi,
    Array.getElem?_eq_getElem hi₀, Option.map_some, Option.some.injEq] at e
  rw [e]
  exact h i hi₀

/-- **NINE CLAUSES OF WHAT IS ASKED OF THE STATEMENT IN FRONT, AT THE FRAME WITH THE FRONT's OWN
NUMBERS.** -/
theorem front_nine {cs : Codes} {l : List (OracleShape × ℕ)} {W₀ : SwitchFrame}
    {x₀ x : _root_.Tw.K2.Front} (h0 : K2.frameAt x₀ = some W₀) (hcs : x₀.st.codes = cs)
    (hb : frontPubB l.length x₀ = true) (h : pinB x₀ x = true)
    (hn : keptOnceB x.f.rows = true) (ht : Tied l (switchNotices x.T x.others)) :
    K2.frameAt x = some (realOf W₀ x) ∧ (realOf W₀ x).zk.logN ≤ 32 ∧
    (∀ (a a' : ℕ) (k k' : KeptPlace), (realOf W₀ x).kept[a]? = some k →
      (realOf W₀ x).kept[a']? = some k' → k.old = k'.old → a = a') ∧
    x.st.codes = cs ∧ K2.KeptPos x.T ∧
    x.f.rows.keptRows = ((realOf W₀ x).kept.map (·.rows)).sum ∧
    (∀ (a : ℕ) (k : KeptPlace), (realOf W₀ x).kept[a]? = some k →
      (x.st.codes.base.getD (x.st.oracles.getD k.old default).shape.code default).ell =
        (realOf W₀ x).code.ell) ∧
    (∃ g0 : 0 < l.length, (l.get ⟨0, g0⟩).1 = x.T.shape) ∧
    ∀ i (hi : i < x.T.kept.size), ∃ h : 1 + i < l.length,
      (l.get ⟨1 + i, h⟩).1 = x.T.kept[i].shape := by
  have P := pin_facts h
  have hW := frame_pin h0 h
  simp only [frontPubB, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨⟨b1, -⟩, b3⟩, b4⟩, b5⟩, b6⟩ := hb
  have hl : x.T.kept.size = x₀.T.kept.size := by
    have := congrArg List.length P.kept
    simpa using this
  obtain ⟨f1, f2⟩ := first_next_of_tied ht (by rw [hl]; exact b6)
  have hz : W₀.zk.logN ≤ 32 := z32_at h0 b1
  refine ⟨hW, hz, twoOld_at hW hn, P.codes.trans hcs,
    keptPos_pin P (keptPos_of_test b3), ?_, ?_, f1, f2⟩
  · unfold realOf
    rw [renumber_kept_rows, P.keptRows]
    exact keptRows_at h0 b4
  · intro a k hk
    unfold realOf at hk
    rw [renumber_get] at hk
    obtain ⟨k₀, hk₀, rfl⟩ := Option.map_eq_some_iff.1 hk
    have e0 := ell_at h0 b5 a k₀ hk₀
    obtain ⟨-, -, -, -, -, -, -, hK⟩ := Johnson.Top.H.frame_fields _ _ _ _ _ W₀ h0
    have hk₁ := hk₀
    rw [hK] at hk₁
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hk₁
    obtain ⟨i, hi, rfl⟩ := hk₁
    obtain ⟨ha, rfl⟩ := List.getElem?_eq_some_iff.1 hi
    simp only [List.length_range] at ha
    simp only [List.getElem_range] at e0 ⊢
    have hA := front_alike P
    have ha' : a < (switchKept x.f.rows).size := by
      have := alike_length hA
      simp only [Array.length_toList] at this
      rw [this]
      exact ha
    have e := alike_get hA a (by simpa using ha') (by simpa using ha)
    have a1 : (switchKept x.f.rows).getD a noId =
        (switchKept x.f.rows).toList[a]'(by simpa using ha') := by simp [Array.getD, ha']
    have a2 : (switchKept x₀.f.rows).getD a noId =
        (switchKept x₀.f.rows).toList[a]'(by simpa using ha) := by simp [Array.getD, ha]
    show (x.st.codes.base.getD (x.st.oracles.getD ((switchKept x.f.rows).getD a noId)
      default).shape.code default).ell = W₀.code.ell
    rw [a1, shape_at e, P.codes, ← a2]
    exact e0

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.front_nine
#print axioms VerifiableInference.Desc.First.K2Hands.frame_pin
#print axioms VerifiableInference.Desc.First.K2Hands.nums_of_test
