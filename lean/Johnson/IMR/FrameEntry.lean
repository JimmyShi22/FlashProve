-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/FrameEntry.lean: Johnson/IMR/FrameAt.lean's At AND Below BEHIND THE FIRST
SUB-PROTOCOL OF A LINK l < 24, WITH THE FRAME's FIELDS; AND SO THE TOPS.
  gain_fst: the numbers of kind K2's two lists (switchGain, ownGain: GroupsAtYes.lean), written out.
  at_of_holds: from Johnson/IMR/GroupFill.lean's Holds and the frame's two lists in numbers.
  entry_at (1 ≤ l < 24): behind the code switching and "opened": with x the front that the text
    makes of the state t₀ in front, n₀ its number of messages, K the target's number of kept:
    At l #[n₀] ‹the two lists' flags› f; Below; f.moment = 1, f.link = l, f.group = l,
    f.next = later or close, f.shape = t₀'s frame's; f.keptBefore = n₀ + 1 + i (i < K);
    f.own = n₀ + 1 + K + j (j < the number of the link's messages of moment 0).
  entry_at_zero: the like at link 0, behind kind K1's opening: pre = #[], keptBefore = #[],
    own = n₀ + j.
  (The frame at the later cuts: Johnson/IMR/FrameAt.lean's walk_a, walk_b, walk_c at these entries.)
  members_at: in the letters of two kinds' files: at every cut 14 l + 3 + n, n ≤ 9, l < 24:
    a link L is open, L.link = l, L.check.frame.group = l, and the statement's group number l has
    G.members = pre ++ L.check.frame.keptBefore ++ L.check.frame.own with pre of size 0 (l = 0) or
    1; a flag a member; no number twice.
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USERS: the list of facts along the fold
(field "frameIs"); kind K8's, K10's and K2's files.
The premises are laws' premises: that a fold returns is shown of no proof here. No soundness.
-/
import Johnson.IMR.FrameAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Cl)

theorem gain_fst (x : _root_.Tw.K2.Front) :
    (K2.switchGain x ++ K2.ownGain x).map (·.1) =
      x.st.oracles.size :: (List.range x.T.kept.size).map (· + (x.st.oracles.size + 1)) ++
        (List.range x.own.length).map (· + (x.st.oracles.size + (1 + x.T.kept.size))) := by
  have hm1 : (K2.switchGain x).map (·.1) = x.st.oracles.size ::
      (List.range x.T.kept.size).map (· + (x.st.oracles.size + 1)) := by
    unfold K2.switchGain
    rw [List.map_cons, List.map_map]
    congr 1
    exact List.map_fst_zip (by simp)
  have hm2 : (K2.ownGain x).map (·.1) =
      (List.range x.own.length).map (· + (x.st.oracles.size + (1 + x.T.kept.size))) := by
    unfold K2.ownGain
    rw [List.map_map]
    exact List.map_snd_zip (by simp)
  rw [List.map_append, hm1, hm2]

theorem at_of_holds {l : Nat} {mem : List Nat} {fl : List Bool} {t : S} (H : Holds l mem fl t)
    {L : LinkCtx} (hL : t.link? = some L) (hn : L.link = l) {pre : Array Nat}
    (e : mem.toArray = pre ++ L.check.frame.keptBefore ++ L.check.frame.own) :
    At l pre fl L.check.frame t ∧ Below l t := by
  obtain ⟨G, hG, em, ek, el, hb, hnd⟩ := H
  refine ⟨⟨⟨L, hL, rfl, hn⟩, G, hG, by rw [em, e], ek, by rw [ek, em]; simp [el],
    by rw [em]; exact hnd⟩, fun G₂ hG₂ o ho => ?_⟩
  obtain rfl : G = G₂ := Option.some.inj (hG.symm.trans hG₂)
  rw [em] at ho
  exact hb o (by simpa using ho)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **BEHIND THE FIRST SUB-PROTOCOL OF LINK l, 1 ≤ l < 24.** -/
theorem entry_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h1 : 1 ≤ l)
    (h24 : l < 24) {p : ProofFile.InstPub} {R R₀ R₁ : List Fmt.RoundView}
    {C C₀ C₁ : List VerifiableInference.Desc.OpenedColumn} {t₀ t₁ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 3)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁)) :
    ∃ (x : _root_.Tw.K2.Front) (f : ReqFrame),
      _root_.Tw.K2.firstFront t₀.st t₀.check.frame = .ok x ∧
      At l #[t₀.st.oracles.size] ((K2.switchGain x ++ K2.ownGain x).map (·.2)) f t₁ ∧
      Below l t₁ ∧ f.moment = 1 ∧ f.link = l ∧ f.group = l ∧ f.next = .laterOrClose ∧
      f.shape = t₀.check.frame.shape ∧
      f.keptBefore = (Array.range x.T.kept.size).map (· + (t₀.st.oracles.size + 1)) ∧
      f.own = (Array.range x.own.length).map
        (· + (t₀.st.oracles.size + (1 + x.T.kept.size))) := by
  obtain ⟨hB, hlk0⟩ := laid_at hS hR O (by omega : l < 25) f₀
  have hc := count_at hS hR O l (by omega) t₀ R₀ C₀ f₀
  obtain ⟨L, hL, eLn, eLg⟩ := entry_group hS hR O h24 f₀ f₁
  obtain ⟨Lk, b, x0, eLk, e0, -, J, hx⟩ := IM.k2_link_sits hS hR O l h1 h24
  have i0 : c.blocksInOrder[14 * l + 2]? = some b := by
    have k := IM.hear_at_flat eLk e0
    rwa [(IM.flatIx_scope hS hR O (by omega : l ≤ 24) 0).trans
      (by omega : 14 * l + 0 + 2 = 14 * l + 2)] at k
  obtain ⟨rs, gs, d⟩ := fold_next i0 f₀ f₁
  obtain ⟨fs, fr, m, hfs, hf, y1, -, y3, -, -⟩ := J.yes d
  revert y1
  generalize rs.take _ = rs'
  generalize gs.take _ = gs'
  intro y1
  have y1' : x0.decide t₀ rs' gs' = .ok m := y1
  have mB := switch_between hx y1' hB
  have mo := switch_moment hx y1' hB
  have v := ((framesOf_live hfs fr (List.mem_of_getElem? hf)).2.1 m t₁ y3).1
  have eLc : L.check = m.check := by rw [← live_open hL, v, live_between mB]
  have st1 : t₁.st = m.st := framesOf_st hfs fr (List.mem_of_getElem? hf) m t₁ y3
  rcases hx with ⟨-, hm⟩ | ⟨Pp, n, -, -, h3⟩
  · obtain ⟨er, he⟩ := hm t₀ rs' gs'
    rw [he] at y1'
    cases y1'
  · rcases h3 with ⟨hn, -⟩ | ⟨l', HP, -, -, ex⟩ | ⟨l', -, ex⟩
    · cases hn
    · rw [ex] at y1'
      obtain ⟨w, a1, -⟩ := andThen_yes (n := x0.name) y1'
      obtain ⟨r₁, r₂, a, G', w', roots, -, H⟩ := K2.head_inv (snd := _root_.Tw.K2.sendByL8) rfl a1
      unfold S.atBetween at hB
      rw [H.hHere] at hB
      cases hB
    · rw [ex] at y1'
      have h' : K2.decideWith _root_.Tw.K2.sendByL8
          (IM.k2P Z { chain := 1, link := some l, piece := 1, kind := .K2 } x0.name .link n) t₀
          rs' gs' = .ok m := y1'
      obtain ⟨x, hxf, Hh⟩ := switch_holds rfl h'
      rw [hc] at Hh
      obtain ⟨x₂, lay₂, hx₂, -, -, -, -, k1, k2, -, -⟩ := K2.yes_link_frame rfl h'
      obtain rfl : x₂ = x := Except.ok.inj (hx₂.symm.trans hxf)
      obtain ⟨x₃, hx₃, e0s, -⟩ := K2.yes_link_groups rfl h'
      obtain rfl : x₃ = x₂ := Except.ok.inj (hx₃.symm.trans hxf)
      obtain ⟨r₁, r₂, x₄, w, roots, S', f, mine, -, Lq⟩ := K2.link_inv rfl h'
      obtain rfl : x₄ = x₃ := Except.ok.inj (Lq.hFront.symm.trans hxf)
      obtain ⟨L0, G0, S0, g, a⟩ := (_root_.Tw.K2.firstFront_iff _ _ _).1 Lq.hFront
      obtain ⟨mask, bA⟩ := (_root_.Tw.K2.firstBehind_iff _ _ _ _ _ _ _).1 Lq.hBehind
      have ho : x₄.others.size = x₄.own.length + 1 := by
        rw [a.out]
        simp [ReqFrame.notices]
      have hN : (_root_.Tw.K2.switchNotices x₄.T x₄.others).size =
          1 + x₄.T.kept.size + x₄.others.size := by
        simp [_root_.Tw.K2.switchNotices]
        omega
      have kb : m.check.frame.keptBefore =
          (Array.range x₄.T.kept.size).map (· + (t₀.st.oracles.size + 1)) := by
        rw [k1, K2.ids_cut _ _ 1 x₄.T.kept.size (by omega), e0s]
      have ow : m.check.frame.own = (Array.range x₄.own.length).map
          (· + (t₀.st.oracles.size + (1 + x₄.T.kept.size))) := by
        rw [k2, K2.mine_is rfl ho, e0s]
      have fm : m.check.frame = f := by
        rw [Lq.hOut]
        rfl
      have hnx : m.check.frame.next = .laterOrClose := by rw [fm, bA.frame]
      have hsh : m.check.frame.shape = t₀.check.frame.shape := by
        rw [fm, bA.frame]
        show x₄.f.shape = _
        rw [a.out]
      have hlk : m.check.frame.link = l := by
        rw [fm, bA.frame]
        show x₄.f.link = _
        rw [a.out]
        exact hlk0
      have em : ((K2.switchGain x₄ ++ K2.ownGain x₄).map (·.1)).toArray =
          #[t₀.st.oracles.size] ++ L.check.frame.keptBefore ++ L.check.frame.own := by
        rw [eLc, kb, ow, gain_fst, e0s]
        apply Array.toList_inj.1
        simp
      obtain ⟨a1, a2⟩ := at_of_holds (holds_st st1 Hh) hL eLn em
      exact ⟨x₄, L.check.frame, hxf, a1, a2, by rw [eLc]; exact mo, by rw [eLc]; exact hlk, eLg,
        by rw [eLc]; exact hnx, by rw [eLc]; exact hsh, by rw [eLc]; exact kb,
        by rw [eLc]; exact ow⟩

/-- **BEHIND THE FIRST SUB-PROTOCOL OF LINK 0.** -/
theorem entry_at_zero (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R R₁ : List Fmt.RoundView} {C C₁ : List VerifiableInference.Desc.OpenedColumn} {t₁ : S}
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (14 * 0 + 3)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁)) :
    ∃ f : ReqFrame,
      At 0 #[] (((ProofFile.startS Z p).check.frame.atMoment 0).map fun x => decide (0 < x.life)) f t₁ ∧
      Below 0 t₁ ∧ f.moment = 1 ∧ f.link = 0 ∧ f.group = 0 ∧ f.next = .laterOrClose ∧
      f.shape = (ProofFile.startS Z p).check.frame.shape ∧ f.keptBefore = #[] ∧
      f.own = (Array.range ((ProofFile.startS Z p).check.frame.atMoment 0).length).map
        (· + (ProofFile.startS Z p).st.oracles.size) := by
  obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 14 * 0 + 2) f₁
  have e0s := laid_is_start hS hR O f₀
  obtain ⟨Hh, -⟩ := entry_zero hS hR O f₁
  obtain ⟨L, hL, eLn, eLg⟩ := entry_group hS hR O (by omega : 0 < 24) f₀ f₁
  obtain ⟨hB, hlk0⟩ := laid_at hS hR O (by omega : 0 < 25) f₀
  obtain ⟨Lk, b, eLk, e0, J⟩ := IM.k1_first_sits hS hR O
  have i0 : c.blocksInOrder[14 * 0 + 2]? = some b := by
    have k := IM.hear_at_flat eLk e0
    rwa [(IM.flatIx_scope hS hR O (by omega : 0 ≤ 24) 0).trans
      (by omega : 14 * 0 + 0 + 2 = 14 * 0 + 2)] at k
  obtain ⟨rs, gs, d⟩ := fold_next i0 f₀ f₁
  obtain ⟨fs, fr, m, hfs, hf, y1, -, y3, -, -⟩ := J.yes d
  revert y1
  generalize rs.take _ = rs'
  generalize gs.take _ = gs'
  intro y1
  have y' : (K1.firstSegmentOpening Bs.G₀.first (K1.gpOf Z) : Block S Unit).decide t₀ rs' gs' = .ok m := y1
  obtain ⟨r₁, r₂, er⟩ := firstAtS_two y'
  rw [er] at y'
  obtain ⟨g', mask, e, -, lt⟩ := K1.firstAtS_frame _ _ t₀ m r₁ r₂ _ y'
  have hR0 : t₀.roots = t₀.book.trees.size := by
    rw [e0s, (start_empty O.pub p).1, (start_empty O.pub p).2]
    rfl
  have hK : t₀.check.frame.keptBefore = #[] := by
    rw [e0s]
    exact start_kept O.pub p
  obtain ⟨-, mB⟩ := opening_lists y' hB hR0 hK
  have v := ((framesOf_live hfs fr (List.mem_of_getElem? hf)).2.1 m t₁ y3).1
  have eLc : L.check = m.check := by rw [← live_open hL, v, live_between mB]
  have ow : m.check.frame.own = (Array.range (t₀.check.frame.atMoment 0).length).map
      (· + t₀.st.oracles.size) := by
    rw [e]
    show #[] ++ (K1.idsOf _ _).extract 0 _ = _
    rw [Array.empty_append]
    apply Array.toList_inj.1
    rw [Array.toList_extract, K1.ids_list]
    simp only [List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero, Array.toList_map,
      Array.toList_range]
    rw [← List.map_take, List.take_range, Nat.min_eq_left (Nat.le_of_lt lt)]
  have kb : m.check.frame.keptBefore = #[] := by
    rw [e]
    exact hK
  have em : ((List.range ((ProofFile.startS Z p).check.frame.atMoment 0).length).map
      (· + (ProofFile.startS Z p).st.oracles.size)).toArray =
      #[] ++ L.check.frame.keptBefore ++ L.check.frame.own := by
    rw [eLc, kb, ow, e0s]
    apply Array.toList_inj.1
    simp
  obtain ⟨a1, a2⟩ := at_of_holds Hh hL eLn em
  refine ⟨L.check.frame, a1, a2, by rw [eLc, e], ?_, eLg, by rw [eLc, e], ?_, by rw [eLc, kb],
    by rw [eLc, ow, e0s]⟩
  · rw [eLc, e]
    exact hlk0
  · rw [eLc, e, ← e0s]

/-- What At says of the frame's lists and the group, in the letters of its users. -/
theorem At.members {l : Nat} {pre : Array Nat} {fl : List Bool} {f : ReqFrame} {t : S}
    (H : At l pre fl f t) :
    ∃ L G, t.link? = some L ∧ L.link = l ∧ L.check.frame = f ∧ t.st.groups[l]? = some G ∧
      G.members = pre ++ L.check.frame.keptBefore ++ L.check.frame.own ∧ G.kept = fl.toArray ∧
      G.kept.size = G.members.size ∧ G.members.toList.Nodup := by
  obtain ⟨L, hL, e1, e2⟩ := H.link
  obtain ⟨G, hG, em, ek, es, hn⟩ := H.group
  exact ⟨L, G, hL, e2, e1, hG, by rw [e1]; exact em, ek, es, hn⟩

/-- **AT EVERY CUT 14 l + 3 + n, n ≤ 9, OF A LINK l < 24: THE GROUP's MEMBERS ARE THE FRAME's TWO
LISTS**, behind at most one number in front (the code switching's main message). -/
theorem members_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h24 : l < 24)
    {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} {n : Nat}
    (hn : n ≤ 9) {t : S} {r : List Fmt.RoundView} {q : List VerifiableInference.Desc.OpenedColumn}
    (g : foldBlocks 0 (c.blocksInOrder.take (14 * l + 3 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q)) :
    ∃ (L : LinkCtx) (G : Group) (pre : Array Nat), t.link? = some L ∧ L.link = l ∧
      L.check.frame.group = l ∧ t.st.groups[l]? = some G ∧
      pre.size = (if l = 0 then 0 else 1) ∧
      G.members = pre ++ L.check.frame.keptBefore ++ L.check.frame.own ∧
      G.kept.size = G.members.size ∧ G.members.toList.Nodup := by
  obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_cut (k := 14 * l + 3) n g
  obtain ⟨Lg, hLg, -, eg⟩ := group_open hS hR O h24 n (by omega) t r q g
  have fin : ∀ {pre : Array Nat} {fl : List Bool} {f : ReqFrame},
      pre.size = (if l = 0 then 0 else 1) → At l pre fl f t →
      ∃ (L : LinkCtx) (G : Group) (pre : Array Nat), t.link? = some L ∧ L.link = l ∧
        L.check.frame.group = l ∧ t.st.groups[l]? = some G ∧
        pre.size = (if l = 0 then 0 else 1) ∧
        G.members = pre ++ L.check.frame.keptBefore ++ L.check.frame.own ∧
        G.kept.size = G.members.size ∧ G.members.toList.Nodup := by
    intro pre fl f hp H
    obtain ⟨L, G, hL, e2, -, hG, em, -, es, hnd⟩ := H.members
    obtain rfl : Lg = L := Option.some.inj (hLg.symm.trans hL)
    exact ⟨Lg, G, pre, hL, e2, eg, hG, hp, em, es, hnd⟩
  have go : ∀ {pre : Array Nat} {fl : List Bool} {f : ReqFrame},
      pre.size = (if l = 0 then 0 else 1) → f.group = l → At l pre fl f t₁ → Below l t₁ →
      ∃ (L : LinkCtx) (G : Group) (pre : Array Nat), t.link? = some L ∧ L.link = l ∧
        L.check.frame.group = l ∧ t.st.groups[l]? = some G ∧
        pre.size = (if l = 0 then 0 else 1) ∧
        G.members = pre ++ L.check.frame.keptBefore ++ L.check.frame.own ∧
        G.kept.size = G.members.size ∧ G.members.toList.Nodup := by
    intro pre fl f hp hg H1 B1
    by_cases h2 : n ≤ 2
    · exact fin hp (walk_a hS hR O h24 f₁ H1 B1 n h2 t r q g).1
    · obtain ⟨t₃, R₃, C₃, f₃⟩ := fold_cut (k := 14 * l + 5) (n - 2)
        (by rw [show 14 * l + 5 + (n - 2) = 14 * l + 3 + n by omega]; exact g)
      by_cases h4 : n ≤ 4
      · exact fin hp (walk_b hS hR O h24 f₁ f₃ hg H1 B1 (n - 3) (by omega) t r q
          (by rw [show 14 * l + 6 + (n - 3) = 14 * l + 3 + n by omega]; exact g)).1
      · obtain ⟨t₅, R₅, C₅, f₅⟩ := fold_cut (k := 14 * l + 7) (n - 4)
          (by rw [show 14 * l + 7 + (n - 4) = 14 * l + 3 + n by omega]; exact g)
        exact fin hp (walk_c hS hR O h24 f₁ f₃ f₅ hg H1 B1 (n - 5) (by omega) t r q
          (by rw [show 14 * l + 8 + (n - 5) = 14 * l + 3 + n by omega]; exact g))
  by_cases h0 : l = 0
  · subst h0
    obtain ⟨f, a1, a2, -, -, hg, -⟩ := entry_at_zero hS hR O f₁
    exact go rfl hg a1 a2
  · obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 14 * l + 2) f₁
    obtain ⟨x, f, -, a1, a2, -, -, hg, -⟩ := entry_at hS hR O (by omega) h24 f₀ f₁
    exact go (by rw [if_neg h0]; rfl) hg a1 a2

end

#print axioms gain_fst
#print axioms entry_at
#print axioms entry_at_zero
#print axioms members_at

end Meaning.K2
