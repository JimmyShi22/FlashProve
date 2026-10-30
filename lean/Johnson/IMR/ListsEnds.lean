-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/ListsEnds.lean: WHAT THE FOLD's RETURN ALONE SAYS OF THE FIRST
RECORD, AT THE PROOF FILE's SEAT, IN THE GOALS' SCOPE:

  frames_live: every entry of the seat's list of frames leaves the live state of the calls, the book
    and the count of roots (LV, Johnson/IMR/ListsAtDraw.lean): it is a lot's block of the kind
      "frame"
    (IM.frames_from_lots): the frames' lot's (IM.frame_from) or the seal's (IM.lot_end).
  first_live: so does the chain's first block, WHICHEVER IT IS: an entry of that list under the
    front's name, or the idle front (the library's Shape.firstChain_shape; ProofFile's chainBy's text).
  behind_laid: the record t₀ behind "link 0: laid" has the first record's state of the calls, book
    and count of roots, stands between the links, and a link's first call is due there.
  start_real: SO THE FIRST RECORD IS NOT THE BLANK ONE: the request has passed the tests that read
    no reply: of the blank record's state of the calls no first call is due.
  open_recAll: RecAll (Johnson/Goal/Meaning/RecAll.lean) at every record that a fold from the first
    record over the first k entries of c.blocksInOrder returns, 2 ≤ k ≤ the length of frontOf c: FROM THE
    FOLD's RETURN ALONE: no yes of the tests on the instance is asked.
  shape_ok: so the live frame's shape passes reqShapeOk there.
  start_kept, opening_lists, first0_lists, lists_at_draw0: Johnson/IMR/ListsAtDraw.lean's top AT
    LINK 0,
    whose first sending is kind K1's opening: firstAtS_frame, firstAtS_own, ownIds_get
    (Johnson/Desc/K1/Law/FrameAtFirst.lean), firstAtS_seated (SeatedAtRecord.lean) and the library's
    firstOwn_ok.
  h1_headFr, h2_lists, lists_at_draw24: THE SAME TOP AT THE HEAD's LINK (cuts 339, 340, 343),
    whose first sending is the place "H:2": placeH2_trees
    (Johnson/Top/H0/Tw/K2C/HeadNumbers.lean), placeH2_link and headFrontQ_fr (HeadLink.lean); kind
    K7's own block writes the reply alone: reply_record
    (Johnson/Desc/Kinds/Law/ReplyPins.lean); the seats' k7_sits, k7_sits_yes
    (Johnson/IMR/FirstSeats.lean), k2_head_of, k3_of, k6_of, k1_later.
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USER: the files on the book's
names.
No soundness.
-/
import Johnson.IMR.ListsAtDraw
import Johnson.IMR.BackSeat
import Johnson.IMR.K2ShareAt
import Johnson.Desc.K1.Law.FrameAtFirst
import Johnson.Top.H0.Tw.K2C.HeadLink
import Johnson.IMR.FirstSeats
import Johnson.IMR.K6Seat
import Johnson.IMR.K7Seat
import Johnson.Desc.Kinds.Law.ReplyPins
import Johnson.Desc.First.Link.Law.Shape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Pub Cl)

variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

theorem lv_refl (s : S) : LV s s :=
  ⟨rfl, rfl, rfl, fun hB L hL => by rw [link_between hB] at hL; cases hL⟩

/-- **Every entry of the seat's list of frames.** -/
theorem frames_live (O : IM.Open o pol lay KL F Z Bs base c A B) :
    ∀ x ∈ (ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).frames, Decides LV x.2 := by
  intro x hx s rs gs t h
  obtain ⟨L, hL, b, hb, hk, -, e⟩ := IM.frames_from_lots (IM.base_made O.made).2.2.2 hx
  rw [e] at h
  have h' := ((IM.guardMark_yes b s t rs gs).1 h).1
  cases hl : b.place.link with
  | some l =>
    obtain ⟨fb, hfb, rfl⟩ := IM.frame_from hL hb hk hl
    exact frameBlock_live hfb s rs gs t h'
  | none =>
    obtain ⟨-, rfl⟩ := IM.lot_end hL hb hk hl
    have h'' : ((ChainEnd.refuse (endAsks s)).map fun _ => s) = .ok t := h'
    obtain ⟨_, -, rfl⟩ := Keeps.emap_ok h''
    exact lv_refl _

/-- **The chain's first block.** -/
theorem first_live (O : IM.Open o pol lay KL F Z Bs base c A B) : Decides LV c.first := by
  have hfr := frames_live O
  have hc := O.chain
  unfold ProofFile.chainBy at hc
  obtain ⟨z, several, hc⟩ := chainC_first hc
  obtain ⟨-, c₀, ⟨e1, -⟩, rfl⟩ := Shape.firstChain_shape hc
  refine guarded_decides _ _ ?_
  rw [e1]
  intro s rs gs t h
  have h' : (ProofFile.fill _ z _).first.decide s rs gs = .ok t := h
  revert h'
  dsimp only [ProofFile.fill]
  split
  · rename_i q hq
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hq
    exact fun k => hfr x (List.mem_of_find?_eq_some hx) s rs gs t k
  · intro k
    cases k
    exact lv_refl _

/-! ## Behind "link 0: laid" -/

theorem start_between (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (p : ProofFile.InstPub) :
    (ProofFile.startS Z p).atBetween = true := by
  have e : Z.s₀.atBetween = true := by
    have k := pub_start hZ
    unfold S.startP at k
    split at k
    · rw [← Option.some.inj k]
      rfl
    · cases k
  unfold ProofFile.startS
  dsimp only
  split
  · exact e
  · rfl

theorem flat_zero (c : Chain S Cl) :
    c.blocksInOrder[0]? = some { c.first with planOk := c.first.planOk && c.first.hasNoClaimsAndNothingAfter } := by
  unfold Chain.blocksInOrder
  rfl

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy}

/-- **The record behind "link 0: laid".** -/
theorem behind_laid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn} {t₀ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take 2) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀)) :
    t₀.check = (ProofFile.startS Z p).check ∧ t₀.book = (ProofFile.startS Z p).book ∧
      t₀.roots = (ProofFile.startS Z p).roots ∧ t₀.atBetween = true ∧
      Johnson.Desc.First.Walk.firstDue t₀.check = true := by
  obtain ⟨t', R', C', f1⟩ := fold_back (k := 1) f₀
  have fz : foldBlocks 0 (c.blocksInOrder.take 0) (ProofFile.startS Z p) R C = .ok (ProofFile.startS Z p, R, C) := rfl
  obtain ⟨rs, gs, d⟩ := fold_next (flat_zero c) fz f1
  obtain ⟨v1, v2, v3, -⟩ := first_live O _ rs gs _ d
  obtain ⟨-, fs, -, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨LkF, f, bL, bB, bC, -, -, -, -, efl, hlay, -, iL, -, dL, -⟩ := hfr 0 (by decide)
  have iL' : c.blocksInOrder[1]? = some bL := iL
  obtain ⟨rsL, gsL, dl⟩ := fold_next iL' f1 f₀
  rw [dL] at dl
  have hlf := ((hlay t' t₀).1 dl).1
  rw [efl] at hlf
  obtain ⟨et, hBm, hD, -⟩ := Johnson.Desc.First.Walk.Law.layFront_ok hlf
  rw [et]
  refine ⟨?_, v2, v3, hBm, hD⟩
  rw [← live_between hBm, v1, live_between (start_between O.pub p)]

/-- **The first record is not the blank one.** -/
theorem start_real (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn} {t₀ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take 2) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀)) :
    (Z.s₀.withReq (Verify.words32 p.request)).reqOk Z.p.X.T Z.p.X.P.h.V = true := by
  obtain ⟨e, -, -, -, hD⟩ := behind_laid hS hR O f₀
  by_contra hq
  have eb : ProofFile.startS Z p = S.blank := by
    unfold ProofFile.startS
    dsimp only
    rw [if_neg hq]
  rw [e, eb] at hD
  exact absurd hD (by decide)

/-- **RecAll AT EVERY RECORD IN FRONT OF THE BLOCKS BEHIND THE LAST LINK, FROM "link 0: laid" ON:
FROM THE FOLD's RETURN ALONE.** -/
theorem open_recAll (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : Nat} (h2 : 2 ≤ k)
    (hk : k ≤ (frontOf c).length) {p : ProofFile.InstPub} {R : List Fmt.RoundView}
    {C : List VerifiableInference.Desc.OpenedColumn}
    {r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn}
    (h : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok r) :
    RecAll Z.first.codes Z.first.shape r.1 := by
  have e : c.blocksInOrder.take 2 ++ (c.blocksInOrder.take k).drop 2 = c.blocksInOrder.take k := by
    have k' := List.take_append_drop 2 (c.blocksInOrder.take k)
    rwa [List.take_take, Nat.min_eq_left h2] at k'
  have h' := h
  rw [← e] at h'
  obtain ⟨t, rs, cols, g0, -⟩ := Keeps.foldBlocks_split 0 _ _ _ _ _ _ h'
  have hq := start_real hS hR O g0
  exact open_fold (seatKeeps_rec (k2Share _ _)) O trivial (fun _ _ _ => trivial) hk h
    (recAll_startS O.pub hq)

/-- **The live frame's shape passes the public test on shapes there.** -/
theorem shape_ok (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : Nat} (h2 : 2 ≤ k)
    (hk : k ≤ (frontOf c).length) {p : ProofFile.InstPub} {R : List Fmt.RoundView}
    {C : List VerifiableInference.Desc.OpenedColumn}
    {r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn}
    (h : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok r) :
    reqShapeOk r.1.live.frame.shape = true := by
  have Rr := open_recAll hS hR O h2 hk h
  rw [Rr.live.shape]
  have k' := Rr.ok
  simp only [reqOk, Bool.and_eq_true] at k'
  exact k'.1

/-! ## Link 0: the first sending is kind K1's opening -/

theorem start_kept (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (p : ProofFile.InstPub) :
    (ProofFile.startS Z p).check.frame.keptBefore = #[] := by
  have e : Z.s₀.check.frame.keptBefore = #[] := by
    have k := pub_start hZ
    unfold S.startP at k
    split at k
    · rw [← Option.some.inj k]
      rfl
    · cases k
  unfold ProofFile.startS
  dsimp only
  split
  · exact e
  · rfl

/-- Kind K1's opening alone. -/
theorem opening_lists {q : Params.First} {gp : _root_.Desc.Plain.GPar} {s u : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.firstSegmentOpening q gp : Block S Unit).decide s rs gs = .ok u) (hB : s.atBetween = true)
    (hR : s.roots = s.book.trees.size) (hK : s.check.frame.keptBefore = #[]) :
    FirstLists s u ∧ u.atBetween = true := by
  have hub2 : u.atBetween = true ∧ ∃ r₁ r₂, rs = [r₁, r₂] := by
    have ha := h
    unfold K1.firstSegmentOpening at ha
    dsimp only at ha
    obtain ⟨_, -, hb⟩ := bindE ha
    obtain ⟨⟨c', d'⟩, h2, hc⟩ := bindE hb
    obtain ⟨g, d₁, ids, d₂, -, hs, -⟩ := K1.firstOwn_ok _ _ _ c' _ d' rs h2
    obtain rfl := Except.ok.inj hc
    exact ⟨hB, two_of_send hs⟩
  obtain ⟨hub, r₁, r₂, rfl⟩ := hub2
  obtain ⟨g', mask, e, -, lt⟩ := K1.firstAtS_frame q gp s u r₁ r₂ gs h
  have Sd := K1.firstAtS_seated q gp s u r₁ r₂ gs h
  have eo := K1.firstAtS_own q gp s u r₁ r₂ gs h
  have esz : u.check.frame.own.size = (s.check.frame.atMoment 0).length := by
    rw [eo, Array.size_extract, K1.idsOf_size]
    omega
  refine ⟨?_, hub⟩
  unfold FirstLists
  rw [live_between hub]
  refine ⟨fun o ho => ?_, fun j o ho => ?_, esz, by rw [e], by rw [e],
    fun L hL => by rw [link_between hub] at hL; cases hL⟩
  · rw [K1.firstAtS_keptBefore q gp s u r₁ r₂ gs h, hK] at ho
    cases ho
  · have hj : j < (s.check.frame.atMoment 0).length := by
      rw [← esz]
      exact (Array.getElem?_eq_some_iff.1 ho).1
    rw [eo, K1.ownIds_get _ _ _ j (Nat.le_of_lt lt) hj] at ho
    obtain rfl := Option.some.inj ho
    refine ⟨_, Sd.seated.new j (by omega), ?_, ?_⟩
    · show s.roots ≤ s.book.trees.size + _
      omega
    · show s.book.trees.size + _ < u.roots
      have := (Sd.seated.fits j (by omega)).1
      rw [Sd.roots]
      omega

/-- Link 0's first block, as it stands in the chain. -/
theorem first0_lists {q : Params.First} {gp : _root_.Desc.Plain.GPar} {b : Block S Cl} {a : Place}
    (hk : a.kind ≠ KindName.K7)
    (hb : IM.LaidFramed Z b (K1.firstSegmentOpening q gp : Block S Unit).retype b.name a)
    {s t : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : b.decide s rs gs = .ok t) (hB : s.atBetween = true)
    (hR : s.roots = s.book.trees.size) (hK : s.check.frame.keptBefore = #[]) :
    FirstLists s t := by
  rcases hb with ha | ⟨fb, hfb, e⟩
  · have h' : (K1.firstSegmentOpening q gp : Block S Unit).decide s rs gs = .ok t :=
      ((IM.yes_alone ha hk s t rs gs).1 h).1
    exact (opening_lists h' hB hR hK).1
  · obtain ⟨u, a1, -, a2, -⟩ := IM.yes_with e h
    obtain ⟨⟨k1, k2, k3, k4, k5, -⟩, hub⟩ :=
      opening_lists (q := q) (gp := gp) (gs := []) a1 hB hR hK
    obtain ⟨v1, v2, v3, v4⟩ :=
      frameBlock_live hfb u _ _ t ((IM.guardMark_yes _ u t _ _).1 a2).1
    unfold FirstLists
    rw [v1, v2, v3]
    exact ⟨k1, k2, k3, k4, k5, v4 hub⟩

/-- **lists_at_draw (ListsAtDraw.lean) AT LINK 0**: t₀, t₁, t₄: the records of one fold from the
first record in front of kind K1's opening, behind it, and in front of kind K8's block. There is no
kept copy. -/
theorem lists_at_draw0 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ (p : ProofFile.InstPub) (R : List Fmt.RoundView)
      (C : List VerifiableInference.Desc.OpenedColumn) (t₀ t₁ t₄ : S) (R₀ R₁ R₄ : List Fmt.RoundView)
      (C₀ C₁ C₄ : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take 2) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀) →
      foldBlocks 0 (c.blocksInOrder.take 3) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁) →
      foldBlocks 0 (c.blocksInOrder.take 6) (ProofFile.startS Z p) R C = .ok (t₄, R₄, C₄) →
      ∃ L, t₄.link? = some L ∧
        (∀ o ∈ L.check.frame.keptBefore.toList, ∃ jt : Nat × Nat,
          t₄.book.place[o]? = some jt ∧ t₀.roots ≤ jt.1 ∧ jt.1 < t₁.roots) ∧
        (∀ j o : Nat, L.check.frame.own[j]? = some o → ∃ jt : Nat × Nat,
          t₄.book.place[o]? = some jt ∧
          ((j < (L.check.frame.atMoment 0).length ∧ t₀.roots ≤ jt.1 ∧ jt.1 < t₁.roots) ∨
            ((L.check.frame.atMoment 0).length ≤ j ∧ t₁.roots ≤ jt.1 ∧ jt.1 < t₄.roots))) ∧
        L.check.frame.shape = t₀.check.frame.shape ∧
        L.check.frame.link = t₀.check.frame.link ∧
        L.check.frame.link = L.link ∧ L.moments = 2 := by
  intro p R C t₀ t₁ t₄ R₀ R₁ R₄ C₀ C₁ C₄ f₀ f₁ f₄
  have h0 : c.front = [] := chainBy_noFront O.chain
  obtain ⟨Lk, b0, eL, e0, la0⟩ := IM.k1_first_of hS hR O
  have i0 : c.blocksInOrder[2]? = some b0 := by
    have k := IM.hear_at_flat eL e0
    rwa [IM.flatIx_scope hS hR O (by decide) 0] at k
  have hk0 : 2 ≤ (frontOf c).length := by
    have k := flatIx_le h0 eL e0
    rwa [IM.flatIx_scope hS hR O (by decide) 0] at k
  obtain ⟨ec, -, -, hB, -⟩ := behind_laid hS hR O f₀
  have hK : t₀.check.frame.keptBefore = #[] := by rw [ec]; exact start_kept O.pub p
  have hR0 : t₀.roots = t₀.book.trees.size := open_roots O hk0 f₀
  obtain ⟨rs0, gs0, d0⟩ := fold_next i0 f₀ f₁
  obtain ⟨t₃, v, Q13, Rl, Qv⟩ :=
    mid_stretch hS hR O 0 (by decide) p R C t₁ t₄ R₁ R₄ C₁ C₄ f₁ f₄
  exact stretch_end (first0_lists (by intro k; cases k) la0 d0 hB hR0 hK) Q13 Rl Qv

/-! ## The head's link -/

/-- The head's own part's frame, in front of the place "H:2": no message of its own yet; the shape
and the link of the walk's frame. -/
def HeadFr (s : S) : Prop :=
  ∃ a, s.here = .head a ∧ a.fr.own = #[] ∧ a.fr.shape = s.check.frame.shape ∧
    a.fr.link = s.check.frame.link

/-- Behind the place "H:1". -/
theorem h1_headFr {W : Verify.Public} {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (IM.k7Block W 24).decide s rs gs = .ok t) :
    HeadFr t := by
  obtain ⟨m, a1, a2⟩ := andThen_yes h
  have hq : K2.headFrontQ W.H.tl s = .ok m :=
    ((guarded_yes _ (fun _ => false) _ rfl s _ _ m).1 a1).1
  obtain ⟨a, ha, f1, f2, -, -, f5, -⟩ := K2.headFrontQ_fr hq
  obtain ⟨_, _, _, _, _, _, rfl⟩ := Kinds.Head.Law.Came.reply_record 24 W.hS.V a2
  exact ⟨a, ha, f5, f1, f2⟩

/-- The place "H:2". -/
theorem h2_lists {G : ProofFile.Ground} {x : Block S Unit}
    (hx : IM.K2Is Z G { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name x)
    {s t : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : x.decide s rs gs = .ok t) (hF : HeadFr s) (hR : s.roots = s.book.trees.size) :
    FirstLists s t := by
  obtain ⟨a, ha, o1, o2, o3⟩ := hF
  rcases hx with ⟨-, hm⟩ | ⟨P', n, -, -, h3⟩
  · obtain ⟨e, he⟩ := hm s rs gs
    rw [he] at h
    cases h
  · rcases h3 with ⟨hl, -⟩ | ⟨l', HP, -, -, e⟩ | ⟨l', -, e⟩
    · cases hl
    · rw [e] at h
      have h' : ((K2.codeSwitchKind (IM.k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name
                      .head n) : Block S Unit).andThen x.name (K2.headOpened x.name
                      (IM.k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name .head n).place
                      HP)).decide s rs gs = .ok t := h
      have hO : ∀ a', s.here = .head a' → a'.fr.own = #[] := by
        intro a' ha'
        rw [ha] at ha'
        injection ha' with e'
        rw [← e']
        exact o1
      obtain ⟨L, hL, t1, t2⟩ := K2.placeH2_trees h' hO hR
      obtain ⟨a', L', ha', hL', z1, z2, z3, -, z5, z6⟩ := K2.placeH2_link h'
      obtain rfl : L = L' := Option.some.inj (hL.symm.trans hL')
      have ea : a' = a := by
        rw [ha] at ha'
        injection ha' with e'
        exact e'.symm
      rw [ea] at z1 z2 z3
      unfold FirstLists
      rw [live_open hL]
      refine ⟨t1, t2, ?_, z2.trans o2, z3.trans o3, fun L'' h'' => ?_⟩
      · rw [z1, o1]
        exact Nat.zero_add _
      · obtain rfl : L = L'' := Option.some.inj (hL.symm.trans h'')
        exact ⟨z6, z5⟩
    · rw [e] at h
      obtain ⟨r₁, r₂, x', w, roots, S', f, mine, -, Lk⟩ :=
        K2.link_inv (snd := _root_.Tw.K2.sendByL8) (p := IM.k2P Z
          { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name .link n) rfl h
      rw [Lk.hHere] at ha
      cases ha

/-- **lists_at_draw (ListsAtDraw.lean) AT THE HEAD's LINK**: t₀, t₁, t₄: the records of one fold
from the first record in front of the place "H:2", behind it, and in front of kind K8's block. -/
theorem lists_at_draw24 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ (p : ProofFile.InstPub) (R : List Fmt.RoundView)
      (C : List VerifiableInference.Desc.OpenedColumn) (t₀ t₁ t₄ : S) (R₀ R₁ R₄ : List Fmt.RoundView)
      (C₀ C₁ C₄ : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take 339) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀) →
      foldBlocks 0 (c.blocksInOrder.take 340) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁) →
      foldBlocks 0 (c.blocksInOrder.take 343) (ProofFile.startS Z p) R C = .ok (t₄, R₄, C₄) →
      ∃ L, t₄.link? = some L ∧
        (∀ o ∈ L.check.frame.keptBefore.toList, ∃ jt : Nat × Nat,
          t₄.book.place[o]? = some jt ∧ t₀.roots ≤ jt.1 ∧ jt.1 < t₁.roots) ∧
        (∀ j o : Nat, L.check.frame.own[j]? = some o → ∃ jt : Nat × Nat,
          t₄.book.place[o]? = some jt ∧
          ((j < (L.check.frame.atMoment 0).length ∧ t₀.roots ≤ jt.1 ∧ jt.1 < t₁.roots) ∨
            ((L.check.frame.atMoment 0).length ≤ j ∧ t₁.roots ≤ jt.1 ∧ jt.1 < t₄.roots))) ∧
        L.check.frame.shape = t₀.check.frame.shape ∧
        L.check.frame.link = t₀.check.frame.link ∧
        L.check.frame.link = L.link ∧ L.moments = 2 := by
  intro p R C t₀ t₁ t₄ R₀ R₁ R₄ C₀ C₁ C₄ f₀ f₁ f₄
  have h0 : c.front = [] := chainBy_noFront O.chain
  have ix : ∀ i, IM.flatIx c 24 i = 338 + i := fun i =>
    (IM.flatIx_scope hS hR O (by decide) i).trans (by omega)
  -- the seats
  obtain ⟨Lk, b0, eL, e0, hj, -⟩ := IM.k7_sits hS hR O
  obtain ⟨Lk1, b1, x, eL1, e1, -, la1, hx⟩ := IM.k2_head_of hS hR O
  obtain rfl : Lk = Lk1 := Option.some.inj (eL.symm.trans eL1)
  obtain ⟨Lk2, b2, b2', eL2, e2, k3, la2⟩ := IM.k3_of hS hR O 24 (by decide) false
  obtain rfl : Lk = Lk2 := Option.some.inj (eL.symm.trans eL2)
  have e2' : Lk.hear[2]? = some b2 := e2
  obtain ⟨Lk3, b3, b3', ms, eL3, e3, -, k6, la3, -⟩ := IM.k6_of hS hR O
  obtain rfl : Lk = Lk3 := Option.some.inj (eL.symm.trans eL3)
  obtain ⟨Lk4, b4, Xl, pr, pd, reads, digits, eL4, e4, -, -, harm⟩ :=
    IM.k1_later O 24 .head (IM.subs_head hS hR O.pub O.blank) 4 rfl (by decide)
  obtain rfl : Lk = Lk4 := Option.some.inj (eL.symm.trans eL4)
  have q2 : Decides Quiet b2 := fun s rs gs t h =>
    (theStated_quiet _ _ _ _ _ _ k3).1 s rs gs t
      ((IM.yes_alone la2 (by intro k; cases k) s t rs gs).1 h).1
  have q3 : Decides Quiet b3 := fun s rs gs t h =>
    (seatedClaims_quiet k6).1 s rs gs t
      ((IM.yes_alone la3 (by intro k; cases k) s t rs gs).1 h).1
  have i0 : c.blocksInOrder[338]? = some b0 := by
    have k := IM.hear_at_flat eL e0
    rwa [ix 0] at k
  have i1 : c.blocksInOrder[339]? = some b1 := by
    have k := IM.hear_at_flat eL e1
    rwa [ix 1] at k
  have i2 : c.blocksInOrder[340]? = some b2 := by
    have k := IM.hear_at_flat eL e2'
    rwa [ix 2] at k
  have i3 : c.blocksInOrder[341]? = some b3 := by
    have k := IM.hear_at_flat eL e3
    rwa [ix 3] at k
  have i4 : c.blocksInOrder[342]? = some b4 := by
    have k := IM.hear_at_flat eL e4
    rwa [ix 4] at k
  have hk1 : 339 ≤ (frontOf c).length := by
    have k := flatIx_le h0 eL e1
    rwa [ix 1] at k
  have hk4 : 342 ≤ (frontOf c).length := by
    have k := flatIx_le h0 eL e4
    rwa [ix 4] at k
  -- "H:1"
  obtain ⟨tm, Rm, Cm, fm⟩ := fold_back (k := 338) f₀
  obtain ⟨rs0, gs0, d0⟩ := fold_next i0 fm f₀
  have hF : HeadFr t₀ := h1_headFr (IM.k7_sits_yes hS hR O hj d0).1
  -- "H:2"
  have hR0 : t₀.roots = t₀.book.trees.size := open_roots O hk1 f₀
  obtain ⟨rs1, gs1, d1⟩ := fold_next i1 f₀ f₁
  have Fl : FirstLists t₀ t₁ :=
    h2_lists hx ((IM.yes_alone la1 (by intro k; cases k) t₀ t₁ rs1 gs1).1 d1).1 hF hR0
  -- back from t₄
  obtain ⟨t₃, R₃, C₃, f₃⟩ := fold_back (k := 342) f₄
  obtain ⟨t₂, R₂, C₂, f₂⟩ := fold_back (k := 341) f₃
  obtain ⟨rs2, gs2, d2⟩ := fold_next i2 f₁ f₂
  obtain ⟨rs3, gs3, d3⟩ := fold_next i3 f₂ f₃
  obtain ⟨rs4, gs4, d4⟩ := fold_next i4 f₃ f₄
  have hR3 : t₃.roots = t₃.book.trees.size := open_roots O hk4 f₃
  obtain ⟨v, Rl, Qv⟩ : ∃ v, ReadsLists t₃ v ∧ Quiet v t₄ := by
    rcases harm with ⟨-, la⟩ | ⟨-, la⟩
    · exact alone_reads (by intro k; cases k) la d4 hR3
    · exact alone_later (by intro k; cases k) la d4 hR3
  exact stretch_end Fl (quiet_trans _ _ _ (q2 _ _ _ _ d2) (q3 _ _ _ _ d3)) Rl Qv

end

#print axioms frames_live
#print axioms first_live
#print axioms behind_laid
#print axioms start_real
#print axioms open_recAll
#print axioms shape_ok
#print axioms opening_lists
#print axioms lists_at_draw0
#print axioms h2_lists
#print axioms lists_at_draw24

end Meaning.K2
