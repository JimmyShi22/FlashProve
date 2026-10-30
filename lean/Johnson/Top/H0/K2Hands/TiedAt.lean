-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/TiedAt.lean: `Tied` at the three sorts of front of the switch of groups, from
one test with code on public lists. Definitions with code, and theorems with their proofs.

What is said.
  `tiedB l sent`: A TEST WITH CODE, ON PUBLIC LISTS ALONE: the typed list l goes along the planner's
    list of what is sent, entry by entry from the first: the same shape; one answer to a sample; one
    of the two cases of a pad. IT CAN FAIL.
  `tied_of_test`, `tied_of_sent`: its yes gives `Tied` (SeedJoint.lean) at announcements that are,
    as a list, that list.
  `tied_at_frame`: with `notices_sent` (NoticesSent.lean): `Tied` at the announcements that are made
    of a frame.
  `front_link`, `front_head`, `front_finish`: the front that the text makes of a record
    (`K2.frontAt`, Johnson/Top/H0/K2Hears/Long.lean) has its target and its other announcements of
    the record's frame; at the finish of the finish's own copy of the frame and of the group that is
    laid there.
  `tied_link`, `tied_head`, `tied_finish`: `Tied l (switchNotices fx.T fx.others)` at each sort of
    front.

What is left as premises. (1) The frame has the plan's shape and that shape's groups. (2) At the
head's link: the frame's link is not the first and is at most the number of links. (3) At the
finish: the finish's copy of the frame has shape and groups, stands behind the last link, and the
group that is laid is the frame's own there. (4) The test's yes at the planner's record of the
group: a closed fact wherever l and the plan are written values.

Limits. l is a letter: nothing says which list the law's caller takes. Nothing on soundness.

-/
import Johnson.Top.H0.K2Hands.NoticesSent
import Johnson.Top.H0.K2Hands.SeedJoint
import Johnson.Top.H0.K2Hears.Long

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes OnBytes.Plan OnBytes.Params Johnson.Pack
open _root_.Tw.K2 (switchNotices firstFront)

/-- **A test with code, on public lists alone**: the typed list l goes along the planner's list of
what is sent, entry by entry from the first: the same shape; one answer to a sample; a mask row, or
main rows over the extension field, or no mask row and main rows over the base field. -/
def tiedB : List (OracleShape × ℕ) → List OracleNotice → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: l, n :: sent =>
    decide (n.shape = x.1) && n.shape.answers == 1 &&
      (decide (0 < n.shape.maskRows) || n.shape.mainDeg == 3 ||
        (n.shape.maskRows == 0 && n.shape.mainDeg == 1)) && tiedB l sent

theorem tied_of_test : ∀ (l : List (OracleShape × ℕ)) (sent : List OracleNotice),
    tiedB l sent = true → ∀ i : Fin l.length, ∃ n, sent[i.val]? = some n ∧ n.shape = (l.get i).1 ∧
      n.shape.answers = 1 ∧ (CaseE n.shape ∨ CaseF n.shape)
  | [], _, _, i => i.elim0
  | _ :: _, [], h, _ => by simp [tiedB] at h
  | x :: l, n :: sent, h, i => by
    simp only [tiedB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    obtain ⟨i, hi⟩ := i
    cases i with
    | zero =>
      refine ⟨n, rfl, h1, h2, ?_⟩
      rcases h3 with (h3 | h3) | h3
      · exact Or.inl (Or.inl h3)
      · exact Or.inl (Or.inr h3)
      · exact Or.inr h3
    | succ j =>
      exact tied_of_test l sent h4 ⟨j, Nat.lt_of_succ_lt_succ hi⟩

/-- **`Tied` from the test**, at announcements that are, as a list, what the planner says is sent.
-/
theorem tied_of_sent (l : List (OracleShape × ℕ)) (notices : Array OracleNotice)
    (sent : List OracleNotice) (hn : notices.toList = sent) (h : tiedB l sent = true) :
    Tied l notices := by
  intro i
  obtain ⟨n, h1, h2⟩ := tied_of_test l sent h i
  refine ⟨n, ?_, h2⟩
  rw [← hn] at h1
  simpa using h1

/-- **`Tied` AT A FRAME**: the frame has the plan's shape and that shape's groups and stands at a
link, or at the last test, that is not the first; the test says yes at the planner's record of that
group: then the typed list is tied to the announcements of the switch into the group. -/
theorem tied_at_frame (z : ProofSized) (sub : Subproofs) (f : ReqFrame) (hs : f.shape = z.request)
    (hg : f.groups = reqGroups z.request) (h0 : 0 < f.link)
    (hl : f.link ≤ z.request.link.length) (g : ReqGroup) (hG : f.groups[f.link]? = some g)
    (l : List (OracleShape × ℕ))
    (ht : ∀ n, (framesOf z sub)[f.link]? = some n → tiedB l n.sent = true) :
    Tied l (switchNotices g.target (ReqFrame.notices (f.atMoment 0) ++
      #[foldMaskNotice (f.foldShape f.link {})])) := by
  obtain ⟨n, hn, he⟩ := notices_sent z sub f hs hg h0 hl g hG
  exact tied_of_sent l _ n.sent he (ht n hn)

/-- **The front of a later link's switch**: its target and its other announcements are made of the
record's frame. -/
theorem front_link {p : K2.P2} {s : S} {fx : _root_.Tw.K2.Front} (hp : p.stands = .link)
    (h : K2.frontAt p s = some fx) :
    0 < s.check.frame.link ∧ ∃ g, s.check.frame.groups[s.check.frame.link]? = some g ∧
      (s.check.frame.shape.link[s.check.frame.link]?).isSome = true ∧
      switchNotices fx.T fx.others = switchNotices g.target
        (ReqFrame.notices (s.check.frame.atMoment 0) ++
          #[foldMaskNotice (s.check.frame.foldShape s.check.frame.link {})]) := by
  unfold K2.frontAt at h
  rw [hp] at h
  simp only at h
  generalize s.check.frame = f at h ⊢
  unfold firstFront at h
  split at h
  · simp [Except.toOption] at h
  · split at h
    · simp [Except.toOption] at h
    · rename_i h1 h2
      split at h
      · rename_i L G hL hG
        split at h
        · simp [Except.toOption] at h
        · simp only [Except.toOption, Option.some.injEq] at h
          subst h
          exact ⟨Nat.pos_of_ne_zero (by simpa using h2), G, hG, by rw [hL]; rfl, rfl⟩
      · simp [Except.toOption] at h
      · simp [Except.toOption] at h

/-- The front of the switch at the head's link: the like. -/
theorem front_head {p : K2.P2} {s : S} {fx : _root_.Tw.K2.Front} (hp : p.stands = .head)
    (h : K2.frontAt p s = some fx) :
    ∃ g, s.check.frame.groups[s.check.frame.link]? = some g ∧
      switchNotices fx.T fx.others = switchNotices g.target
        (ReqFrame.notices (s.check.frame.atMoment 0) ++
          #[foldMaskNotice (s.check.frame.foldShape s.check.frame.link {})]) := by
  unfold K2.frontAt at h
  rw [hp] at h
  cases hh : s.here with
  | head a =>
    rw [hh] at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨G, hG, rfl⟩ := h
    exact ⟨G, hG, rfl⟩
  | _ => rw [hh] at h; simp at h

/-- The front of the finish's switch: made of the finish's own copy of the frame and of the group
that is laid there. -/
theorem front_finish {p : K2.P2} {s : S} {fx : _root_.Tw.K2.Front} (hp : p.stands = .finish)
    (h : K2.frontAt p s = some fx) :
    ∃ a g, s.here = .fin a ∧ a.G = some g ∧
      switchNotices fx.T fx.others =
        switchNotices g.target #[foldMaskNotice (a.fr.foldShape a.fr.link {})] := by
  unfold K2.frontAt at h
  rw [hp] at h
  cases hh : s.here with
  | fin a =>
    rw [hh] at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨G, hG, rfl⟩ := h
    exact ⟨a, G, rfl, hG, rfl⟩
  | _ => rw [hh] at h; simp at h

section
variable (z : ProofSized) (sub : Subproofs) (l : List (OracleShape × ℕ))

/-- **`Tied` AT THE FRONT OF A LATER LINK's SWITCH.** -/
theorem tied_link {p : K2.P2} {s : S} {fx : _root_.Tw.K2.Front} (hp : p.stands = .link)
    (h : K2.frontAt p s = some fx) (hs : s.check.frame.shape = z.request)
    (hg : s.check.frame.groups = reqGroups z.request)
    (ht : ∀ n, (framesOf z sub)[s.check.frame.link]? = some n → tiedB l n.sent = true) :
    Tied l (switchNotices fx.T fx.others) := by
  obtain ⟨h0, g, hG, hL, he⟩ := front_link hp h
  rw [he]
  refine tied_at_frame z sub _ hs hg h0 ?_ g hG l ht
  rw [hs] at hL
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hL
  exact Nat.le_of_lt (List.getElem?_eq_some_iff.1 hv).1

/-- **AT THE FRONT OF THE SWITCH AT THE HEAD's LINK.** -/
theorem tied_head {p : K2.P2} {s : S} {fx : _root_.Tw.K2.Front} (hp : p.stands = .head)
    (h : K2.frontAt p s = some fx) (hs : s.check.frame.shape = z.request)
    (hg : s.check.frame.groups = reqGroups z.request) (h0 : 0 < s.check.frame.link)
    (hl : s.check.frame.link ≤ z.request.link.length)
    (ht : ∀ n, (framesOf z sub)[s.check.frame.link]? = some n → tiedB l n.sent = true) :
    Tied l (switchNotices fx.T fx.others) := by
  obtain ⟨g, hG, he⟩ := front_head hp h
  rw [he]
  exact tied_at_frame z sub _ hs hg h0 hl g hG l ht

/-- **AT THE FRONT OF THE FINISH's SWITCH**: where the group that is laid in the finish's part is
the frame's own at its link, and every link is behind. -/
theorem tied_finish {p : K2.P2} {s : S} {fx : _root_.Tw.K2.Front} (hp : p.stands = .finish)
    (h : K2.frontAt p s = some fx)
    (hf : ∀ a, s.here = .fin a → a.fr.shape = z.request ∧ a.fr.groups = reqGroups z.request ∧
      a.fr.link = z.request.link.length ∧ 0 < a.fr.link ∧ a.G = a.fr.groups[a.fr.link]?)
    (ht : ∀ n, (framesOf z sub)[z.request.link.length]? = some n → tiedB l n.sent = true) :
    Tied l (switchNotices fx.T fx.others) := by
  obtain ⟨a, g, ha, hG, he⟩ := front_finish hp h
  obtain ⟨hs, hg, hl, h0, hGf⟩ := hf a ha
  have hm : a.fr.atMoment 0 = [] := by
    unfold ReqFrame.atMoment
    rw [hs, hl, List.getElem?_eq_none (Nat.le_refl _)]
    rfl
  have := tied_at_frame z sub a.fr hs hg h0 (Nat.le_of_eq hl) g (by rw [← hGf]; exact hG) l
    (by rw [hl]; exact ht)
  rw [hm] at this
  rw [he]
  simpa [ReqFrame.notices] using this

end

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.tied_link
#print axioms VerifiableInference.Desc.First.K2Hands.tied_head
#print axioms VerifiableInference.Desc.First.K2Hands.tied_finish
#print axioms VerifiableInference.Desc.First.K2Hands.tied_at_frame
#print axioms VerifiableInference.Desc.First.K2Hands.front_link
#print axioms VerifiableInference.Desc.First.K2Hands.front_head
