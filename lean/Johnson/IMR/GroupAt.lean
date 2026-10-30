-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/GroupAt.lean: WHERE A LINK IS OPEN, ITS FRAME's GROUP NUMBER IS THE
LINK's NUMBER: at the proof file's seat, in the goals' scope, from the fold's return alone. "The
state": the value that the fold of the IOP as written in Lean carries from sub-protocol to
sub-protocol.
PART ONE: THE LINKS 0 TO 23, FROM BEHIND THE LINK's FIRST SUB-PROTOCOL TO IN FRONT OF THE BATCHING
(the cuts 14 l + 3 to 14 l + 9): so in front of both of kind K1's later sendings.
  Gk s t: where a link is open at s one is open at t, with the same number and the same group number
    in its frame. Reflexive, transitive. gk_of_quiet; commit_gk (kind K1's later sending: its
    files' one equation on the frame, commitAtS_frame).
  nums_grp: the numbers that kind K2's lot makes for link l bear the group l.
  switch_group: behind an accept of the code switching at link l the walk's frame bears the group l:
    BY THE TEXT's OWN GUARD (LinkIs.hGrp: the frame's group is the place's).
  start_groups, laid_is_start: at link 0: the first state has no group, and the state behind "link
    0: laid" is the first state; the opening's frame bears the number of groups in front (kind
    K1's firstAtS_group): 0.
  entry_group: behind the first sub-protocol of link l < 24 a link is open, with the number l and
    the group l.
  hear_by: hearing sub-protocols number 1 to 6 keep every relation that a Quiet step and kind K1's
    later sending keep: general, for whoever walks a link by place.
  group_at: THE TOP.
NOT HERE YET: from the batching to "cleared"; the head's link. It counts no groups: nothing is said
of the statement's number of groups but at the first state.
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USERS: kind K1's files (their law's
premise on the open link's group); the list of facts along the fold, field "groupIs".
The premises are laws' premises: that a fold returns is shown of no proof here. No soundness.
-/
import Johnson.IMR.OwnAt
import Johnson.IMR.FrontPin
import Johnson.IMR.FrontSeat
import Johnson.Desc.K1.Law.GroupAtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Cl)

/-- Where a link is open at s one is open at t, with the same number and the same group. -/
def Gk (s t : S) : Prop :=
  ∀ L, s.link? = some L → ∃ L', t.link? = some L' ∧
    L'.check.frame.group = L.check.frame.group ∧ L'.link = L.link

theorem gk_refl (s : S) : Gk s s := fun L h => ⟨L, h, rfl, rfl⟩

theorem gk_trans (a b c : S) (h : Gk a b) (k : Gk b c) : Gk a c := fun L hL => by
  obtain ⟨L₁, h1, e1, e2⟩ := h L hL
  obtain ⟨L₂, h2, f1, f2⟩ := k L₁ h1
  exact ⟨L₂, h2, f1.trans e1, f2.trans e2⟩

theorem gk_of_quiet {s t : S} (q : Quiet s t) : Gk s t := fun L hL => by
  obtain ⟨L', a, c, -, n⟩ := quiet_fwd q hL
  exact ⟨L', a, by rw [c], n⟩

/-- Kind K1's later sending. -/
theorem commit_gk {P : K1.Par} {link moment : Nat} {arrays : Option (List Nat)} {s v : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.commitAtS P link moment arrays : Block S Unit).decide s rs gs = .ok v) : Gk s v := by
  obtain ⟨r₁, r₂, rfl⟩ := commitAtS_two h
  obtain ⟨L, L', a1, a2, e, -⟩ := K1.commitAtS_frame P link moment arrays s v r₁ r₂ gs h
  obtain ⟨M, M', b1, b2, -, m2, -⟩ := K1.commitAtS_moments P link moment arrays s v _ gs h
  obtain rfl : L = M := Option.some.inj (a1.symm.trans b1)
  obtain rfl : L' = M' := Option.some.inj (a2.symm.trans b2)
  intro L₀ h₀
  obtain rfl : L = L₀ := Option.some.inj (a1.symm.trans h₀)
  exact ⟨L', a2, by rw [e], m2⟩

/-- The numbers that kind K2's lot makes for link l bear the group l. -/
theorem nums_grp {Pp : P1K2.Prep} {l : Nat} {n : P1K2.Nums} (h : P1K2.numsAt Pp (some l) = some n) :
    n.grp = l := by
  unfold P1K2.numsAt at h
  simp only [Option.getD_some, Option.bind_eq_bind, Option.pure_def] at h
  split at h
  · cases h
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨_, -, _, -, _, -, _, -, h⟩ := h
    obtain rfl := Option.some.inj h
    rfl

/-- **Behind an accept of the code switching at link l.** -/
theorem switch_group {Z : ProofFile.Pub} {G : ProofFile.Ground} {l : Nat} {x : Block S Unit}
    (hx : IM.K2Is Z G { chain := 1, link := some l, piece := 1, kind := .K2 } x.name x)
    {s u : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : x.decide s rs gs = .ok u) (hB : s.atBetween = true) : u.check.frame.group = l := by
  rcases hx with ⟨-, hm⟩ | ⟨Pp, n, -, hn, h3⟩
  · obtain ⟨e, he⟩ := hm s rs gs
    rw [he] at h
    cases h
  · rcases h3 with ⟨hl, -⟩ | ⟨l', HP, -, -, e⟩ | ⟨l', -, e⟩
    · cases hl
    · rw [e] at h
      obtain ⟨v, a1, -⟩ := andThen_yes (n := x.name) h
      obtain ⟨r₁, r₂, a, G', w, roots, -, H⟩ := K2.head_inv (snd := _root_.Tw.K2.sendByL8) rfl a1
      unfold S.atBetween at hB
      rw [H.hHere] at hB
      cases hB
    · rw [e] at h
      have h' : K2.decideWith _root_.Tw.K2.sendByL8
          (IM.k2P Z { chain := 1, link := some l, piece := 1, kind := .K2 } x.name .link n) s rs
          gs = .ok u := h
      obtain ⟨r₁, r₂, x', w, roots, S', f, mine, -, Lk⟩ := K2.link_inv rfl h'
      rw [Lk.hOut]
      show f.group = l
      rw [Lk.hGrp]
      exact nums_grp hn

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- The first state has no group. -/
theorem start_groups {o : ProofFile.SecondHashFunctionArgument} {pol KL : ByteArray}
    (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (p : ProofFile.InstPub) :
    (ProofFile.startS Z p).st.groups = #[] := by
  have e : Z.s₀.st.groups = #[] := by
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

/-- The state behind "link 0: laid" is the first state. -/
theorem laid_is_start (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn} {t₀ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take 2) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀)) :
    t₀ = ProofFile.startS Z p := by
  obtain ⟨t', R', C', f1⟩ := fold_back (k := 1) f₀
  have fz : foldBlocks 0 (c.blocksInOrder.take 0) (ProofFile.startS Z p) R C = .ok (ProofFile.startS Z p, R, C) := rfl
  obtain ⟨b, hb, -, -, -, -, hd⟩ := IM.front_of O
  obtain ⟨rs, gs, d⟩ := fold_next hb fz f1
  have e1 : t' = ProofFile.startS Z p := (hd _ rs gs _).1 d
  obtain ⟨-, fs, -, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨LkF, f, bL, bB, bC, -, -, -, -, efl, hlay, -, iL, -, dL, -⟩ := hfr 0 (by decide)
  have iL' : c.blocksInOrder[1]? = some bL := iL
  obtain ⟨rsL, gsL, dl⟩ := fold_next iL' f1 f₀
  rw [dL] at dl
  have hlf := ((hlay t' t₀).1 dl).1
  rw [efl] at hlf
  rw [(Johnson.Desc.First.Walk.Law.layFront_ok hlf).1, e1]

/-- **Behind the first sub-protocol of link l < 24 a link is open, with the number l and the group
l.** -/
theorem entry_group (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h24 : l < 24)
    {p : ProofFile.InstPub} {R R₀ R₁ : List Fmt.RoundView} {C C₀ C₁ : List VerifiableInference.Desc.OpenedColumn}
    {t₀ t₁ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 3)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁)) :
    ∃ L, t₁.link? = some L ∧ L.link = l ∧ L.check.frame.group = l := by
  obtain ⟨r, ar, hc⟩ := ctx_behind_first hS hR O h24 f₀ f₁
  obtain ⟨L, hL, eL, -, -⟩ := link_of_ctx hc (by decide)
  refine ⟨L, hL, eL, ?_⟩
  obtain ⟨hB, -⟩ := laid_at hS hR O (by omega : l < 25) f₀
  have key : ∀ {b : Block S Cl} {b' : Block S Cl} {a : Place}, IM.Joined Z l b b' a →
      c.blocksInOrder[14 * l + 2]? = some b →
      (∀ m rs gs, b'.decide t₀ rs gs = .ok m → m.atBetween = true ∧ m.check.frame.group = l) →
      L.check.frame.group = l := by
    intro b b' a J i0 hm
    obtain ⟨rs, gs, d⟩ := fold_next i0 f₀ f₁
    obtain ⟨fs, f, m, hfs, hf, y1, -, y3, -, -⟩ := J.yes d
    obtain ⟨mB, mg⟩ := hm m _ _ y1
    have v := ((framesOf_live hfs f (List.mem_of_getElem? hf)).2.1 m t₁ y3).1
    rw [← live_open hL, v, live_between mB]
    exact mg
  have ix : IM.flatIx c l 0 = 14 * l + 2 :=
    (IM.flatIx_scope hS hR O (by omega : l ≤ 24) 0).trans (by omega)
  by_cases h0 : l = 0
  · subst h0
    obtain ⟨Lk, b, eLk, e0, J⟩ := IM.k1_first_sits hS hR O
    have i0 : c.blocksInOrder[14 * 0 + 2]? = some b := by
      have k := IM.hear_at_flat eLk e0
      rwa [ix] at k
    refine key J i0 fun m rs gs y => ?_
    have y' : (K1.firstSegmentOpening Bs.G₀.first (K1.gpOf Z) : Block S Unit).decide t₀ rs gs = .ok m := y
    have hR0 : t₀.roots = t₀.book.trees.size := by
      rw [laid_is_start hS hR O f₀, (start_empty O.pub p).1, (start_empty O.pub p).2]
      rfl
    have hK : t₀.check.frame.keptBefore = #[] := by
      rw [laid_is_start hS hR O f₀]
      exact start_kept O.pub p
    obtain ⟨-, mB⟩ := opening_lists y' hB hR0 hK
    refine ⟨mB, ?_⟩
    have two : ∃ r₁ r₂, rs = [r₁, r₂] := by
      have ha := y'
      unfold K1.firstSegmentOpening at ha
      dsimp only at ha
      obtain ⟨_, -, hb⟩ := bindE ha
      obtain ⟨⟨c', d'⟩, h2, -⟩ := bindE hb
      obtain ⟨g, d₁, ids, d₂, -, hs, -⟩ := K1.firstOwn_ok _ _ _ c' _ d' rs h2
      exact two_of_send hs
    obtain ⟨r₁, r₂, rfl⟩ := two
    rw [(K1.firstAtS_group _ _ t₀ m r₁ r₂ gs y').2.1, laid_is_start hS hR O f₀,
      start_groups O.pub p]
    rfl
  · obtain ⟨Lk, b, x, eLk, e0, -, J, hx⟩ := IM.k2_link_sits hS hR O l (by omega) h24
    have i0 : c.blocksInOrder[14 * l + 2]? = some b := by
      have k := IM.hear_at_flat eLk e0
      rwa [ix] at k
    exact key J i0 fun m rs gs y =>
      ⟨switch_between hx (rs := rs) (gs := gs) y hB, switch_group hx (rs := rs) (gs := gs) y hB⟩

/-- **Hearing sub-protocols number 1 to 6 of a link in front of the head's keep every relation that
a Quiet step and kind K1's later sending keep.** -/
theorem hear_by {Rl : S → S → Prop} (ht : ∀ a b c, Rl a b → Rl b c → Rl a c)
    (hQ : ∀ s t, Quiet s t → Rl s t)
    (hC : ∀ (Q : K1.Par) (link moment : Nat) (arrays : Option (List Nat)) (s v : S)
      (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
      (K1.commitAtS Q link moment arrays : Block S Unit).decide s rs gs = .ok v → Rl s v)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 24)
    {j : Nat} (h1 : 1 ≤ j) (h6 : j ≤ 6) {Lk : Link S Cl} {b : Block S Cl}
    (eL : c.links[l]? = some Lk) (e : Lk.hear[j]? = some b) : Decides Rl b := by
  have alone : ∀ {x : Block S Cl} {a : Place}, a.kind ≠ KindName.K7 →
      IM.LaidAlone ProofFile.sameReply b x b.name a → Decides Quiet x → Decides Rl b :=
    fun hk la D s rs gs t h => hQ _ _ (D s rs gs t ((IM.yes_alone la hk s t rs gs).1 h).1)
  have k1 : j = 3 ∨ j = 5 → Decides Rl b := by
    intro hj
    have hk : (kindsBeforeBatching (IM.subAt l) (l == 0))[j]? = some KindName.K1 := by
      unfold IM.subAt
      rw [if_neg (by omega : ¬ l = 24)]
      rcases hj with rfl | rfl <;> split <;> cases (l == 0) <;> rfl
    obtain ⟨Lk', b', Xl, pr, pd, reads, digits, eL', e', -, -, harm⟩ :=
      IM.k1_later O l (IM.subAt l) (IM.subs_scope hS hR O l (by omega)) j hk
        (by rcases hj with rfl | rfl <;> decide)
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
    obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
    intro s rs gs t h
    rcases harm with ⟨-, la⟩ | ⟨-, la⟩
    · have h' : (IM.k1Reads Z Bs.G₀ l Xl pr reads).decide s rs gs = .ok t :=
        ((IM.yes_alone la (by intro k; cases k) s t rs gs).1 h).1
      obtain ⟨v, a1, a2⟩ := andThen_yes h'
      exact ht _ _ _ (hC _ _ _ _ s v _ _ a1)
        (hQ _ _ ((orLoud_whole fun b hb => readsQuietAt_quiet hb).1 v _ _ t a2))
    · exact hC _ _ _ _ s t rs gs ((IM.yes_alone la (by intro k; cases k) s t rs gs).1 h).1
  obtain rfl | rfl | rfl | rfl | rfl | rfl :
      j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  · obtain ⟨Lk', b', x, eL', e', k3, la⟩ := IM.k3_of hS hR O l (by omega) false
    have ix : IM.k3Ix l false = 1 := by
      show (if false = true then 6 else 1) + (if l = 24 then 1 else 0) = 1
      rw [if_neg (by omega : ¬ l = 24)]
      rfl
    rw [ix] at e'
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
    obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
    exact alone (by intro k; cases k) la (theStated_quiet _ _ _ _ _ _ k3).1
  · rcases Nat.even_or_odd' l with ⟨g, rfl | rfl⟩
    · obtain ⟨Lk', b', y, eL', e', -, la, -⟩ := IM.k4_of hS hR O g (by omega)
      obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
      obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
      exact alone (by intro k; cases k) la (blockAtC_quiet _).1
    · obtain ⟨Lk', b', x, a, eL', e', k5, la, -⟩ := IM.k5_of hS hR O g (by omega)
      obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
      obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
      exact alone (by intro k; cases k) la fun s rs gs t h =>
        (k5AtN_quiet _ _ _ _ k5).1 s rs gs t h
  · exact k1 (Or.inl rfl)
  · rcases Nat.even_or_odd' l with ⟨g, rfl | rfl⟩
    · obtain ⟨Lk', b', Xl, hp, eL', e', -, la, -⟩ := IM.k8_of_layers hS hR O g (by omega)
      obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
      obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
      exact alone (by intro k; cases k) la (k8Whole_quiet _).1
    · obtain ⟨Lk', b', Xl, a, eL', e', -, la, -⟩ := IM.k8_of_attention hS hR O g (by omega)
      obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
      obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
      exact alone (by intro k; cases k) la (k8Whole_quiet _).1
  · exact k1 (Or.inr rfl)
  · obtain ⟨Lk', b', x, eL', e', k3, la⟩ := IM.k3_of hS hR O l (by omega) true
    have ix : IM.k3Ix l true = 6 := by
      show (if true = true then 6 else 1) + (if l = 24 then 1 else 0) = 6
      rw [if_neg (by omega : ¬ l = 24)]
      rfl
    rw [ix] at e'
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
    obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
    exact alone (by intro k; cases k) la (theStated_quiet _ _ _ _ _ _ k3).1

/-- **AT EVERY LINK l < 24, AT THE STATE BEHIND THE FIRST 14 l + 3 + n ENTRIES OF THE FLAT LIST,
n ≤ 6 (from behind the link's first sub-protocol to in front of the batching): A LINK IS OPEN, WITH
THE NUMBER l, AND ITS FRAME BEARS THE GROUP l.** -/
theorem group_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 24)
    {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} :
    ∀ n ≤ 6, ∀ (t : S) (R' : List Fmt.RoundView) (C' : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 3 + n)) (ProofFile.startS Z p) R C = .ok (t, R', C') →
      ∃ L, t.link? = some L ∧ L.link = l ∧ L.check.frame.group = l
  | 0, _, t, R', C', f => by
    obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 14 * l + 2) f
    exact entry_group hS hR O hl f₀ f
  | n + 1, hn, t, R', C', f => by
    obtain ⟨u, Ru, Cu, fu⟩ := fold_back (k := 14 * l + 3 + n) f
    obtain ⟨L, hL, e1, e2⟩ := group_at hS hR O hl n (by omega) u Ru Cu fu
    obtain ⟨-, fs, -, hfr⟩ := IM.frame_of hS hR O
    obtain ⟨Lk, -, -, -, -, eL, hlen, -⟩ := hfr l (by omega)
    rw [if_neg (by omega : ¬ l = 24)] at hlen
    obtain ⟨b, e⟩ : ∃ b, Lk.hear[n + 1]? = some b :=
      ⟨_, List.getElem?_eq_getElem (by omega : n + 1 < Lk.hear.length)⟩
    have ib : c.blocksInOrder[14 * l + 3 + n]? = some b := by
      have q := IM.hear_at_flat eL e
      rwa [(IM.flatIx_scope hS hR O (by omega : l ≤ 24) (n + 1)).trans
        (by omega : 14 * l + (n + 1) + 2 = 14 * l + 3 + n)] at q
    obtain ⟨rs, gs, d⟩ := fold_next ib fu f
    obtain ⟨L', hL', g1, g2⟩ := hear_by gk_trans (fun _ _ => gk_of_quiet)
      (fun _ _ _ _ _ _ _ _ => commit_gk) hS hR O hl (by omega) (by omega) eL e u rs gs t d L hL
    exact ⟨L', hL', g2.trans e1, g1.trans e2⟩

end

#print axioms commit_gk
#print axioms switch_group
#print axioms laid_is_start
#print axioms entry_group
#print axioms hear_by
#print axioms group_at

end Meaning.K2
