-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/FrontPub.lean: seven public clauses of what the law of the switch of groups
asks of the statement in front, down to one test with code on the front; and the kept slots at the
frame's own index. Definitions with code, and theorems with their proofs.

What is said.
  `slotsAll_frame`: `SlotsAll` (Numbering.lean) at the frame's own index: a kept member's number,
    and a row of it. `slotsAll_equiv`: along a bijection of the index.
  `maskShortB`, `z32_of_codes`, `z32_at`: the frame's mask code is no longer than 2 ^ 32 where no
    mask code of the statement's codes is.
  `keptOnceB`, `twoOld_of_once`, `twoOld_at`: two places of the frame's kept list with one old
    message are one place, where no kept member stands twice in the carried rows' layout.
  `keptRowsB`, `keptRows_at`; `ellB`, `ell_at`: the carried rows' count of kept rows; the kept
    members' codes' message length.
  `first_next_of_tied`: the typed list begins with the target's shape and goes on with the kept
    messages' shapes: from `Tied` (TiedAt.lean) and "the list is as long as these".
  `keptPosB`, `keptPos_of_test`: each message that takes a kept member has a main row.
  `frontPubB n x`, `front_pub`: ONE TEST for the seven: its yes, `Tied`, and `K2.frameAt x = some
    W₀` give the clauses z32, twoOld, keptPos, keptRows, ell, first, next of `FrontAt`
    (TiePaid.lean), to the letter.

Limits. `frontPubB` IS A TEST ON THE FRONT THAT THE TEXT MAKES OF A RECORD, NOT ON THE PLANNER's
LISTS: by reading the maker `switchFrame` and the target's test `switchTargetCheck`
(OnBytes/Iop/Cs.lean) whole, the verifier's text asks neither z32 nor twoOld: so the test's yes is
something for the promise in front to hold (a public item, made along the chain from the frame's and
the codes' facts), or to be carried to written values: it pays nothing by itself. That the frame at
the front is one frame W₀ for all statements is not touched. Nothing on soundness.

-/
import Johnson.Top.H0.K2Hands.TiedAt
import Johnson.Top.H0.K2Hands.Numbering
import Johnson.Top.H0.K2Hands.FrameOfFront
import Johnson.Top.H0.K2Hands.AtYes
import Johnson.Top.H.SwitchMapsCheck

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes
open _root_.Tw.K2 (switchNotices)

/-! ## The kept slots -/

/-- **The kept slots at the frame's own index**: a kept member's number, and a row of it. -/
theorem slotsAll_frame (W : SwitchFrame) :
    SlotsAll (Σ a : Fin W.kept.length, Fin (W.kept.get a).rows) W (fun κ => κ.1.val)
      (fun κ => κ.2.val) (fun κ => W.kept.get κ.1) where
  member κ := by simp
  rowIn κ := κ.2.isLt
  two := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h1 h2
    obtain rfl : a = a' := Fin.ext h1
    obtain rfl : b = b' := Fin.ext h2
    rfl
  all a k b hk hb := by
    obtain ⟨ha, rfl⟩ := List.getElem?_eq_some_iff.1 hk
    exact ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, rfl, rfl⟩

/-- Along a bijection of the index. -/
theorem slotsAll_equiv {K K' : Type} [Fintype K] [DecidableEq K] [Fintype K'] [DecidableEq K']
    (e : K ≃ K') {W : SwitchFrame} {mem row : K' → ℕ} {pl : K' → KeptPlace}
    (A : SlotsAll K' W mem row pl) : SlotsAll K W (mem ∘ e) (row ∘ e) (pl ∘ e) where
  member κ := A.member (e κ)
  rowIn κ := A.rowIn (e κ)
  two κ κ' h1 h2 := e.injective (A.two (e κ) (e κ') h1 h2)
  all a k b hk hb := by
    obtain ⟨κ, h1, h2⟩ := A.all a k b hk hb
    exact ⟨e.symm κ, by simpa using h1, by simpa using h2⟩

/-! ## Two laws on the maker's value -/

section
variable {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : ℕ} {anew : Array ℕ}
  {W : SwitchFrame}

/-- A test with code on the codes: no mask code is longer than 2 ^ 32. -/
def maskShortB (cs : Codes) : Bool := cs.mask.all fun c => decide (c.logN ≤ 32)

/-- **The frame's mask code is short, where the codes' test says so.** By reading both texts whole:
neither the maker `switchFrame` nor the target's test `switchTargetCheck` asks it. -/
theorem z32_of_codes (h : switchFrame S old T g anew = some W) (hc : maskShortB S.codes = true) :
    W.zk.logN ≤ 32 := by
  obtain ⟨-, hz, -⟩ := Johnson.Top.H.frame_fields S old T g anew W h
  obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 hz
  have := Array.all_eq_true_iff_forall_mem.1 hc _ (Array.getElem_mem hi)
  rw [he] at this
  simpa using this

/-- A test with code on the carried rows' layout: no kept member stands twice. -/
def keptOnceB (old : SingleRows) : Bool := decide (switchKept old).toList.Nodup

/-- **Two places of the frame's kept list with one old message are one place, where no kept member
stands twice in the carried rows' layout.** By reading both texts whole: neither the maker nor the
target's test asks it. -/
theorem twoOld_of_once (h : switchFrame S old T g anew = some W) (hn : keptOnceB old = true)
    (a a' : ℕ) (k k' : KeptPlace) (hk : W.kept[a]? = some k) (hk' : W.kept[a']? = some k')
    (ho : k.old = k'.old) : a = a' := by
  obtain ⟨-, -, -, -, -, -, -, hK⟩ := Johnson.Top.H.frame_fields S old T g anew W h
  have hN : (switchKept old).toList.Nodup := of_decide_eq_true hn
  rw [hK] at hk hk'
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hk hk'
  obtain ⟨i, hi, rfl⟩ := hk
  obtain ⟨i', hi', rfl⟩ := hk'
  obtain ⟨ha, rfl⟩ := List.getElem?_eq_some_iff.1 hi
  obtain ⟨ha', rfl⟩ := List.getElem?_eq_some_iff.1 hi'
  simp only [List.length_range] at ha ha'
  simp only [List.getElem_range] at ho
  have e1 : (switchKept old).getD a noId = (switchKept old).toList[a]'(by simpa using ha) := by
    simp [Array.getD, ha]
  have e2 : (switchKept old).getD a' noId = (switchKept old).toList[a']'(by simpa using ha') := by
    simp [Array.getD, ha']
  rw [e1, e2] at ho
  exact (List.Nodup.getElem_inj_iff hN).1 ho

end

/-! ## At a front -/

/-- The statement that the frame at a front reads has the front's codes. -/
theorem skel_codes (x : _root_.Tw.K2.Front) : (K2.skelOf x).codes = x.st.codes := rfl

theorem z32_at {x : _root_.Tw.K2.Front} {W₀ : SwitchFrame} (h : K2.frameAt x = some W₀)
    (hc : maskShortB x.st.codes = true) : W₀.zk.logN ≤ 32 :=
  z32_of_codes h hc

theorem twoOld_at {x : _root_.Tw.K2.Front} {W₀ : SwitchFrame} (h : K2.frameAt x = some W₀)
    (hn : keptOnceB x.f.rows = true) :
    ∀ (a a' : ℕ) (k k' : KeptPlace), W₀.kept[a]? = some k → W₀.kept[a']? = some k' →
      k.old = k'.old → a = a' :=
  twoOld_of_once h hn

/-- A test with code on a front: the carried rows' count of kept rows is the sum of the kept
members' main rows, as the statement that the frame reads has them. -/
def keptRowsB (x : _root_.Tw.K2.Front) : Bool :=
  x.f.rows.keptRows == ((List.range (switchKept x.f.rows).size).map fun i =>
    ((K2.skelOf x).oracles.getD ((switchKept x.f.rows).getD i noId) default).shape.mainRows).sum

theorem keptRows_at {x : _root_.Tw.K2.Front} {W₀ : SwitchFrame} (h : K2.frameAt x = some W₀)
    (hb : keptRowsB x = true) : x.f.rows.keptRows = (W₀.kept.map (·.rows)).sum := by
  obtain ⟨-, -, -, -, -, -, -, hK⟩ := Johnson.Top.H.frame_fields _ _ _ _ _ W₀ h
  rw [hK, List.map_map]
  exact beq_iff_eq.1 hb

/-- A test with code on a front: every kept member's code has messages as long as the old main
code's. -/
def ellB (x : _root_.Tw.K2.Front) : Bool :=
  (switchKept x.f.rows).all fun o =>
    (x.st.codes.base.getD (x.st.oracles.getD o default).shape.code default).ell ==
      (x.st.codes.base.getD x.f.rows.code default).ell

theorem ell_at {x : _root_.Tw.K2.Front} {W₀ : SwitchFrame} (h : K2.frameAt x = some W₀)
    (hb : ellB x = true) (a : ℕ) (k : KeptPlace) (hk : W₀.kept[a]? = some k) :
    (x.st.codes.base.getD (x.st.oracles.getD k.old default).shape.code default).ell =
      W₀.code.ell := by
  obtain ⟨hc, -, -, -, -, -, -, hK⟩ := Johnson.Top.H.frame_fields _ _ _ _ _ W₀ h
  have hc' : x.st.codes.base[x.f.rows.code]? = some W₀.code := hc
  have e0 : x.st.codes.base.getD x.f.rows.code default = W₀.code := by
    rw [Array.getD_eq_getD_getElem?, hc']
    rfl
  rw [hK] at hk
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hk
  obtain ⟨i, hi, rfl⟩ := hk
  obtain ⟨ha, rfl⟩ := List.getElem?_eq_some_iff.1 hi
  simp only [List.length_range] at ha
  simp only [List.getElem_range]
  have hm : (switchKept x.f.rows).getD a noId ∈ switchKept x.f.rows := by
    simp [Array.getD, ha]
  have := Array.all_eq_true_iff_forall_mem.1 hb _ hm
  rw [← e0]
  exact beq_iff_eq.1 this

/-- **"first" and "next" from `Tied`**, where the typed list is as long as the target and its kept
messages. -/
theorem first_next_of_tied {l : List (OracleShape × ℕ)} {T : SwitchTarget}
    {others : Array OracleNotice} (ht : Tied l (switchNotices T others))
    (hl : 1 + T.kept.size ≤ l.length) :
    (∃ g0 : 0 < l.length, (l.get ⟨0, g0⟩).1 = T.shape) ∧
      ∀ i (hi : i < T.kept.size), ∃ h : 1 + i < l.length, (l.get ⟨1 + i, h⟩).1 = T.kept[i].shape :=
          by
  refine ⟨⟨by omega, ?_⟩, fun i hi => ⟨by omega, ?_⟩⟩
  · obtain ⟨n, h1, h2, -⟩ := ht ⟨0, by omega⟩
    have : (switchNotices T others)[0]? = some ⟨T.shape, T.leafClass⟩ := by
      simp [switchNotices]
    rw [this] at h1
    obtain rfl := Option.some.inj h1
    exact h2.symm
  · obtain ⟨n, h1, h2, -⟩ := ht ⟨1 + i, by omega⟩
    have : (switchNotices T others)[1 + i]? = some ⟨T.kept[i].shape, T.kept[i].leafClass⟩ := by
      unfold switchNotices
      rw [Array.getElem?_append_left (by simp; omega), Array.getElem?_append_right (by simp)]
      simp [hi]
    rw [this] at h1
    obtain rfl := Option.some.inj h1
    exact h2.symm

/-- A test with code on the target: each message that takes a kept member has a main row. -/
def keptPosB (T : SwitchTarget) : Bool := T.kept.all fun k => decide (0 < k.shape.mainRows)

theorem keptPos_of_test {T : SwitchTarget} (h : keptPosB T = true) : K2.KeptPos T := by
  intro i hi
  have := Array.all_eq_true_iff_forall_mem.1 h _ (Array.getElem_mem hi)
  simpa using this

/-- **ONE TEST WITH CODE ON A FRONT** for seven of the clauses on the statement in front. n: the
typed list's length. -/
def frontPubB (n : ℕ) (x : _root_.Tw.K2.Front) : Bool :=
  maskShortB x.st.codes && keptOnceB x.f.rows && keptPosB x.T && keptRowsB x && ellB x &&
    decide (1 + x.T.kept.size ≤ n)

/-- **SEVEN CLAUSES OF WHAT IS ASKED OF THE STATEMENT IN FRONT**, from that test's yes, `Tied`, and
the frame at the front. -/
theorem front_pub {l : List (OracleShape × ℕ)} {x : _root_.Tw.K2.Front} {W₀ : SwitchFrame}
    (h : K2.frameAt x = some W₀) (hb : frontPubB l.length x = true)
    (ht : Tied l (switchNotices x.T x.others)) :
    W₀.zk.logN ≤ 32 ∧
    (∀ (a a' : ℕ) (k k' : KeptPlace), W₀.kept[a]? = some k → W₀.kept[a']? = some k' →
      k.old = k'.old → a = a') ∧
    K2.KeptPos x.T ∧ x.f.rows.keptRows = (W₀.kept.map (·.rows)).sum ∧
    (∀ (a : ℕ) (k : KeptPlace), W₀.kept[a]? = some k →
      (x.st.codes.base.getD (x.st.oracles.getD k.old default).shape.code default).ell =
        W₀.code.ell) ∧
    (∃ g0 : 0 < l.length, (l.get ⟨0, g0⟩).1 = x.T.shape) ∧
    ∀ i (hi : i < x.T.kept.size), ∃ h : 1 + i < l.length,
      (l.get ⟨1 + i, h⟩).1 = x.T.kept[i].shape := by
  simp only [frontPubB, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩ := hb
  obtain ⟨f1, f2⟩ := first_next_of_tied ht b6
  exact ⟨z32_at h b1, twoOld_at h b2, keptPos_of_test b3, keptRows_at h b4, ell_at h b5, f1, f2⟩

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.front_pub
#print axioms VerifiableInference.Desc.First.K2Hands.slotsAll_frame
#print axioms VerifiableInference.Desc.First.K2Hands.slotsAll_equiv
#print axioms VerifiableInference.Desc.First.K2Hands.z32_of_codes
#print axioms VerifiableInference.Desc.First.K2Hands.twoOld_of_once
#print axioms VerifiableInference.Desc.First.K2Hands.first_next_of_tied
#print axioms VerifiableInference.Desc.First.K2Hands.keptPos_of_test
