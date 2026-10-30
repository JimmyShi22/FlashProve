-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/SwitchNotices.lean: "THE BOOK BEHIND THE CODE SWITCH's SENDING IS THERE", WHEREVER
THE SWITCH STANDS (at a link, at the head, at the finish): the first of the four facts on the front
that another file's hF_of_door asks (hFr; Johnson/Desc/First/Link/Law/HFOfDoor.lean), to the sign,
FROM THREE THINGS ON THE STATE s' AT THE BORDER AND ONE TEST WITH CODE ON THE PLAN. A joining of
four groups of lemmas.

  recv_iff         what the receiving's own clauses say: the sent shapes fit the codes; the trees
  can be laid; statement and book in step okAtB cs n       the first two, as a test with code
  finNotices sh    what the finish's switch announces, as a term of the plan's shape
  noticesOkB cs sh   okAtB at what every later link's switch announces (noticesAt sh
  g, 0 < g < the number of links)
                   and at finNotices sh: ONE TEST WITH CODE ON THE PLAN's CODES AND SHAPE
  recAll_rest      RecAll passes through the way in's first step (rest)
  book_at_door     **RecAll cs sh s' · statement and book in step at s' · noticesOkB cs sh = true ·
  (at the head: s' does not stand
                   there already) ⊢ at every answer t of the way in and every front fx of t: ∃ B,
                   K2.bookAt … = some B**
THE LINK's NUMBER IS NOT ASKED: the front's own yes gives that it is a later link of the shape.
CALLED: bookAt_of (BookThere.lean), rest_st (FrontSt.lean) ·
link_notices, atMoment_pub, foldShape_pub (Johnson/Goal/Meaning/K2Share/FrontNotices.lean),
headFrontQ_rec (RecFronts.lean), finishFrontQ_group (Johnson/IMR/K2ShareAt.lean) ·
firstFront_iff, headFrontQ_iff, firstFront_st, headFrontQ_groups | _rest, finishFrontQ_st |
_fr | _rest (Johnson/Top/H0/Tw/K2C/) · doorZ_head, doorZ_finish, rest_book (Johnson/Top/H0/Walk/).
Limits. THE THREE PREMISES ON s' AND THE TEST STAND: none is shown at a reached state here. Nothing
is evaluated. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.BookThere
import Johnson.Desc.First.Link.Law.FrontStEnds
import Johnson.Goal.Meaning.K2Share.FrontNotices
import Johnson.Goal.Meaning.K2Share.RecFronts
import Johnson.IMR.K2ShareAt
import Johnson.Top.H0.Tw.K2C.FinFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.P2Notices
open OnBytes OnBytes.Model Desc.Plain
open OnBytes.Params (ReqShape)
open Meaning.K2 (RecAll FramePub framesIn)
open VerifiableInference.Desc.First.K2Caller (doorZ rest)
open VerifiableInference.Desc.First.K2 (noticesAt targetAt othersAt frameAtLink)
open _root_.Tw.K2 (switchNotices firstFront)
open _root_.Johnson.Desc.First.Walk.Tied (toOption_some doorZ_head doorZ_finish rest_book)
open VerifiableInference.Desc.LinkJoin (rest_st bookAt_of)

/-- **What the receiving's own clauses say.** -/
theorem recv_iff (S : Statement) (Bk : TreeBook) (n : Array OracleNotice) :
    Ground.ok (Ground.recvL S Bk n) = true ↔
      (n.all fun x => Own.sentShapeFits S.codes x.shape) = true ∧
        Own.treesCan S.codes n = true ∧ S.oracles.size = Bk.place.size := by
  simp only [Ground.ok, Ground.recvL, Ground.sentL, List.cons_append, List.nil_append,
    List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq]

/-- The sent shapes fit the codes, and the trees can be laid: a test with code. -/
def okAtB (cs : Codes) (n : Array OracleNotice) : Bool :=
  (n.all fun x => Own.sentShapeFits cs x.shape) && Own.treesCan cs n

/-- What the finish's switch announces: a term of the plan's shape. -/
def finNotices (sh : ReqShape) : Array OracleNotice :=
  switchNotices (targetAt sh sh.link.length)
    #[foldMaskNotice ((frameAtLink sh sh.link.length).foldShape sh.link.length {})]

/-- **The test on the plan's codes and shape**: at every later link's switch, and at the finish's.
-/
def noticesOkB (cs : Codes) (sh : ReqShape) : Bool :=
  ((List.range sh.link.length).all fun g => g == 0 || okAtB cs (noticesAt sh g)) &&
    okAtB cs (finNotices sh)

theorem ok_at_link {cs : Codes} {sh : ReqShape} (K : noticesOkB cs sh = true) {l : ℕ}
    (h0 : l ≠ 0) (hl : l < sh.link.length) : okAtB cs (noticesAt sh l) = true := by
  unfold noticesOkB at K
  have k := List.all_eq_true.1 (Bool.and_eq_true_iff.1 K).1 l (List.mem_range.2 hl)
  rcases Bool.or_eq_true_iff.1 k with e | e
  · exact absurd (beq_iff_eq.1 e) h0
  · exact e

theorem ok_at_finish {cs : Codes} {sh : ReqShape} (K : noticesOkB cs sh = true) :
    okAtB cs (finNotices sh) = true := by
  unfold noticesOkB at K
  exact (Bool.and_eq_true_iff.1 K).2

/-- From the test at the statement's codes and "in step": the book behind the sending is there. -/
theorem book_of_ok (ft : ℕ) (S : Statement) (Bk : TreeBook) (roots : ℕ) (n : Array OracleNotice)
    (h : okAtB S.codes n = true) (hs : S.oracles.size = Bk.place.size) :
    ∃ B, First.K2.bookAt ft S Bk roots n = some B := by
  unfold okAtB at h
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h
  refine bookAt_of ft S Bk roots n ((recv_iff S Bk n).2 ⟨h1, h2, hs⟩) ?_
  rw [Own.treesCan_eq] at h2
  exact Option.isSome_iff_exists.1 h2

/-- **RecAll passes through the way in's first step.** -/
theorem recAll_rest {cs : Codes} {sh : ReqShape} {s : First.S} (R : RecAll cs sh s) :
    RecAll cs sh (rest s) := by
  unfold rest
  split
  · refine ⟨R.codes, fun f hm => ?_, R.ok⟩
    simp only [framesIn, List.mem_cons, List.not_mem_nil, or_false] at hm
    rw [hm]
    exact R.live
  · exact R

/-- What a link's front's own yes gives, under the plan's frame. -/
theorem front_facts {sh : ReqShape} {S0 : Statement} {f : ReqFrame} {x : _root_.Tw.K2.Front}
    (h : firstFront S0 f = .ok x) (F : FramePub sh f) :
    f.link ≠ 0 ∧ f.link < sh.link.length ∧
      switchNotices x.T x.others = noticesAt sh f.link ∧ x.st.codes = S0.codes ∧
      x.st.oracles = S0.oracles := by
  obtain ⟨L, G, S', g, a⟩ := (_root_.Tw.K2.firstFront_iff S0 f x).1 h
  have hl := a.link
  rw [F.shape] at hl
  refine ⟨a.later, (List.getElem?_eq_some_iff.1 hl).1,
    (First.K2.link_notices h F rfl).2.2, ?_, ?_⟩
  · rw [(First.K2.firstFront_st h).1]
    rfl
  · rw [(First.K2.firstFront_st h).1]
    rfl

/-- **THE BOOK BEHIND THE SWITCH's SENDING IS THERE, WHEREVER THE SWITCH STANDS.** -/
theorem book_at_door {cs : Codes} {sh : ReqShape} {Z : ProofFile.Pub} {m : ℕ} {s' : First.S}
    (R : RecAll cs sh s') (hs : s'.st.oracles.size = s'.book.place.size)
    (K : noticesOkB cs sh = true)
    (hH : (ProofFile.pAtK2 Z m).stands = .head → ∀ a, s'.here ≠ .head a) :
    ∀ t fx, doorZ Z m s' = some t → First.K2.frontAt (ProofFile.pAtK2 Z m) t = some fx →
      ∃ B, First.K2.bookAt (First.K2.par9 (ProofFile.pAtK2 Z m)).firstTree fx.st t.book t.roots
        (switchNotices fx.T fx.others) = some B := by
  intro t fx hd hf
  have Rr : RecAll cs sh (rest s') := recAll_rest R
  have hsr : (rest s').st.oracles.size = (rest s').book.place.size := by
    rw [rest_st, rest_book]
    exact hs
  cases hp : (ProofFile.pAtK2 Z m).stands with
  | link =>
    have e : t = rest s' := by
      unfold doorZ at hd
      rw [hp] at hd
      exact (Option.some.inj hd).symm
    subst e
    obtain ⟨h0, hl, hn, hc, ho⟩ := front_facts (First.K2.front_of_link hp hf) Rr.walk
    refine book_of_ok _ _ _ _ _ ?_ (by rw [ho]; exact hsr)
    rw [hn, hc, Rr.codes]
    exact ok_at_link K h0 hl
  | head =>
    rw [doorZ_head hp (hH hp)] at hd
    have e := toOption_some hd
    have Rt : RecAll cs sh t := First.K2.headFrontQ_rec {} _ _ e Rr
    obtain ⟨x, s₁, a, k⟩ := (First.K2.headFrontQ_iff {} _ _).1 e
    have hck : t.check = (rest s').check := (First.K2.headFrontQ_rest e).2.2.2.2.1
    obtain ⟨h0, hl, -, -, -⟩ := front_facts k.front Rr.walk
    rw [← hck] at h0 hl
    have hh : t.here = .head { a with fr := x.f } := by rw [k.out]
    unfold First.K2.frontAt at hf
    rw [hp, hh] at hf
    obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.1 hf
    have F := Rt.walk
    have eT : G.target = targetAt sh t.check.frame.link := by
      unfold First.K2.targetAt
      rw [F.groups] at hG
      rw [Array.getD_eq_getD_getElem?, hG]
      rfl
    have eO : ReqFrame.notices (t.check.frame.atMoment 0) ++
        #[foldMaskNotice (t.check.frame.foldShape t.check.frame.link {})] =
        othersAt sh t.check.frame.link := by
      unfold First.K2.othersAt
      rw [First.K2.atMoment_pub F rfl, First.K2.foldShape_pub F t.check.frame.link]
    refine book_of_ok _ _ _ _ _ ?_ ?_
    · show okAtB t.st.codes (switchNotices G.target (ReqFrame.notices (t.check.frame.atMoment 0) ++
        #[foldMaskNotice (t.check.frame.foldShape t.check.frame.link {})])) = true
      rw [eT, eO, Rt.codes]
      exact ok_at_link K h0 hl
    · show t.st.oracles.size = t.book.place.size
      rw [(First.K2.headFrontQ_groups e).2.1, (First.K2.headFrontQ_rest e).1]
      exact hsr
  | finish =>
    rw [doorZ_finish hp] at hd
    have e := toOption_some hd
    obtain ⟨a, G, hh, hG, hg, Fa, Rt⟩ := Meaning.K2.finishFrontQ_group e Rr
    obtain ⟨a', G', hh', -, -, hlen, -, hlink, -⟩ := First.K2.finishFrontQ_fr e
    obtain rfl : a' = a := by
      have q := hh'.symm.trans hh
      injection q
    unfold First.K2.frontAt at hf
    rw [hp, hh] at hf
    have hf' : a'.G.map (fun G => First.K2.finFrontOf t a' G) = some fx := hf
    rw [hG] at hf'
    obtain rfl := Option.some.inj hf'
    have el : a'.fr.link = sh.link.length := by rw [hlen, Fa.shape]
    have eT : G.target = targetAt sh sh.link.length := by
      unfold First.K2.targetAt
      rw [← hlink, el] at hg
      rw [Array.getD_eq_getD_getElem?, hg]
      rfl
    refine book_of_ok _ _ _ _ _ ?_ ?_
    · show okAtB t.st.codes (switchNotices G.target
        #[foldMaskNotice (a'.fr.foldShape a'.fr.link {})]) = true
      rw [eT, el, First.K2.foldShape_pub Fa sh.link.length, Rt.codes]
      exact ok_at_finish K
    · show t.st.oracles.size = t.book.place.size
      rw [First.K2.finishFrontQ_st e, (First.K2.finishFrontQ_rest e).1]
      exact hsr

end VerifiableInference.Desc.P2Notices

#print axioms VerifiableInference.Desc.P2Notices.recv_iff
#print axioms VerifiableInference.Desc.P2Notices.recAll_rest
#print axioms VerifiableInference.Desc.P2Notices.front_facts
#print axioms VerifiableInference.Desc.P2Notices.book_at_door
