-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/GroupFill.lean: WHICH MESSAGES ARE THE MEMBERS OF A LINK's GROUP,
AND WITH WHICH FLAGS: at the proof file's seat, in the goals' scope, from the fold's return alone:
the links 1 to 23.
  Holds l mem fl t: the statement's group number l has just the members mem with the flags fl; a
    flag a member; every member is below the number of messages; no number stands twice.
  holds_st: a step that leaves the statement keeps it. commit_len, holds_commit: kind K1's later
    sending lays its own new numbers behind the members and its moment's flags behind the flags (
    K1.laterArrays_commitAtS; the two lists are equally long by the text's own test).
  switch_holds: behind an accept of the code switching at link l, where the statement had l groups
    in front: kind K2's yes_link_groups: the main message (flag false), the kept copies (the
    target's "kept again"), the link's own messages of moment 0 (life > 0), numbered on from the
    number of messages in front.
  fill_at: THE TOP: in front of the batching of link l, 1 ≤ l < 24: Holds l at the three sendings'
    lists one behind the other.
NOT HERE: link 0 (kind K1's opening); the head's link; that the later sendings' flags are all false
and what the next code switching reads (Johnson/IMR/GroupKept.lean); the number of messages as a
term of the
list of rounds.
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USERS: kind K2's files; kind K10's files.
The premises are laws' premises: that a fold returns is shown of no proof here. No soundness.
-/
import Johnson.IMR.GroupCount
import Johnson.IMR.GroupTail
import Johnson.Desc.K1.Law.GroupArrays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Cl)

/-- Group number l has just these members with these flags. -/
def Holds (l : Nat) (mem : List Nat) (fl : List Bool) (t : S) : Prop :=
  ∃ G, t.st.groups[l]? = some G ∧ G.members = mem.toArray ∧ G.kept = fl.toArray ∧
    mem.length = fl.length ∧ (∀ o ∈ mem, o < t.st.oracles.size) ∧ mem.Nodup

theorem holds_st {l : Nat} {mem : List Nat} {fl : List Bool} {s t : S} (h : t.st = s.st)
    (H : Holds l mem fl s) : Holds l mem fl t := by
  unfold Holds
  rw [h]
  exact H

/-- The later sending's new numbers are as many as its moment's messages. -/
theorem commit_len {Q : K1.Par} {link moment : Nat} {arrays : Option (List Nat)} {s v : S}
    {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.commitAtS Q link moment arrays : Block S Unit).decide s [r₁, r₂] gs = .ok v)
    {L : LinkCtx} (hL : s.link? = some L) :
    (K1.idsOf Q s.st.oracles.size).toList.length = (K1.flagsAt L.check.frame).length := by
  simp only [K1.commitAtS] at h
  split at h
  · rename_i L₀ F tl hL₀ _ _
    obtain rfl : L₀ = L := Option.some.inj (hL₀.symm.trans hL)
    obtain ⟨y, hy, -⟩ := Keeps.emap_ok h
    obtain ⟨ids, d₁, f', h2, h3⟩ := K1.commitOwn_ok Q link moment arrays _ y _ gs hy
    obtain ⟨-, e, -⟩ := (K1.decideSend_iff Q _ _ d₁ r₁ r₂ ids).1 h2
    unfold Send.joinOwnP at h3
    split at h3
    · rename_i hl
      have k : (L₀.check.frame.atMoment L₀.check.frame.moment).length = ids.size := eq_of_beq hl
      unfold K1.flagsAt
      rw [List.length_map, k, e, Array.length_toList]
      rfl
    · cases h3
  · cases h

/-- **Kind K1's later sending.** -/
theorem holds_commit {Q : K1.Par} {link moment : Nat} {arrays : Option (List Nat)} {s v : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.commitAtS Q link moment arrays : Block S Unit).decide s rs gs = .ok v)
    {L : LinkCtx} (hL : s.link? = some L) {mem : List Nat} {fl : List Bool}
    (H : Holds L.check.frame.group mem fl s) :
    Holds L.check.frame.group (mem ++ (K1.idsOf Q s.st.oracles.size).toList)
      (fl ++ K1.flagsAt L.check.frame) v := by
  obtain ⟨r₁, r₂, rfl⟩ := commitAtS_two h
  obtain ⟨G, hG, em, ek, el, hb, hn⟩ := H
  obtain ⟨Lk, hLk, hA⟩ := K1.laterArrays_commitAtS Q link moment arrays s v _ gs rfl h
  obtain rfl : Lk = L := Option.some.inj (hLk.symm.trans hL)
  have hb' : ∀ o ∈ G.members, o < s.st.oracles.size := fun o ho =>
    hb o (by rw [em] at ho; simpa using ho)
  obtain ⟨G', hG', gr⟩ := hA G hG hb'
  have hsz := (K1.commitAtS_seated Q link moment arrays s v r₁ r₂ gs h).msgs
  refine ⟨G', hG', by rw [gr.1, em]; simp, ?_, ?_, ?_, ?_⟩
  · rw [gr.2 (by rw [ek, em]; simp [el]), ek]
    simp
  · rw [List.length_append, List.length_append, el, commit_len h hL]
  · intro o ho
    rcases List.mem_append.1 ho with ho | ho
    · have := hb o ho
      omega
    · rw [K1.ids_list] at ho
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ho
      have := List.mem_range.1 hi
      omega
  · have k := gr.nodup_ids (by rw [em]; simpa using hn) hb'
    rw [gr.1, em] at k
    simpa using k

/-- **Behind an accept of the code switching at a link, where the statement had l groups.** -/
theorem switch_holds {q : K2.P2} {s m : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hq : q.stands = .link)
    (h : K2.decideWith _root_.Tw.K2.sendByL8 q s rs gs = .ok m) :
    ∃ x : _root_.Tw.K2.Front, _root_.Tw.K2.firstFront s.st s.check.frame = .ok x ∧
      Holds s.st.groups.size ((K2.switchGain x ++ K2.ownGain x).map (·.1))
        ((K2.switchGain x ++ K2.ownGain x).map (·.2)) m := by
  obtain ⟨x, hx, e0, -, -, -, G', hG', m1, m2⟩ := K2.yes_link_groups hq h
  obtain ⟨x', hf, -, -, hs, -⟩ := K2.yes_size h
  obtain rfl : x' = x := by
    rcases hf with ⟨-, k⟩ | ⟨k, -⟩ | ⟨k, -⟩
    · exact Except.ok.inj (k.symm.trans hx)
    · rw [hq] at k
      cases k
    · rw [hq] at k
      cases k
  obtain ⟨L0, G0, S0, g, a⟩ := (_root_.Tw.K2.firstFront_iff _ _ _).1 hx
  have ho : x'.others.size = x'.own.length + 1 := by
    rw [a.out]
    simp [ReqFrame.notices]
  have hN : (_root_.Tw.K2.switchNotices x'.T x'.others).size =
      1 + x'.T.kept.size + x'.others.size := by
    simp [_root_.Tw.K2.switchNotices]
    omega
  have hm1 : (K2.switchGain x').map (·.1) = x'.st.oracles.size ::
      (List.range x'.T.kept.size).map (· + (x'.st.oracles.size + 1)) := by
    unfold K2.switchGain
    rw [List.map_cons, List.map_map]
    congr 1
    exact List.map_fst_zip (by simp)
  have hm2 : (K2.ownGain x').map (·.1) =
      (List.range x'.own.length).map (· + (x'.st.oracles.size + (1 + x'.T.kept.size))) := by
    unfold K2.ownGain
    rw [List.map_map]
    exact List.map_snd_zip (by simp)
  have hP : ((K2.switchGain x' ++ K2.ownGain x').map (·.1)).Pairwise (· < ·) := by
    rw [List.map_append, hm1, hm2, List.cons_append, List.pairwise_cons, List.pairwise_append]
    refine ⟨fun o ho' => ?_, K2.rising_range _ _, K2.rising_range _ _, fun o h1 o' h2 => ?_⟩
    · rcases List.mem_append.1 ho' with k | k <;> obtain ⟨i, -, rfl⟩ := List.mem_map.1 k <;> omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h1
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 h2
      have := List.mem_range.1 hi
      omega
  refine ⟨x', hx, G', hG', m1, m2, by simp, fun o ho' => ?_, hP.imp fun k => Nat.ne_of_lt k⟩
  rw [List.map_append, hm1, hm2] at ho'
  rw [hs, hN, ho]
  rcases List.mem_append.1 ho' with k | k
  · rcases List.mem_cons.1 k with rfl | k
    · omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 k
      have := List.mem_range.1 hi
      omega
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 k
    have := List.mem_range.1 hi
    omega

open Johnson.Desc.First.Walk Johnson.Desc.First.Walk.Seat in
/-- Every row's "opened" leaves the statement. -/
theorem framesOf_st {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} (h : framesOf built first W = .ok fs) : ∀ f ∈ fs, ∀ s t,
    f.opened s = .ok t → t.st = s.st := by
  intro f hf
  unfold framesOf at h
  obtain ⟨l, -, e⟩ := mem_of_mapM_ok _ _ _ h f hf
  dsimp only at e
  split at e
  · split at e
    · cases e
    · cases e
      exact fun s t k => by cases k; rfl
  · split at e
    · split at e
      · cases e
      · cases e
        exact fun s t k => (openLayZero_enters _ _ _ s t k).1
    · split at e
      · cases e
      · cases e
        exact fun s t k => (openAtt_enters _ s t k).1
      · cases e
        exact fun s t k => (openLay_enters _ s t k).1

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- Hearing sub-protocols number 1, 2, 4 and 6 of a link l < 24 are Quiet. -/
theorem hear_quiet (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 24)
    {j : Nat} (hj : j = 1 ∨ j = 2 ∨ j = 4 ∨ j = 6) {Lk : Link S Cl} {b : Block S Cl}
    (eL : c.links[l]? = some Lk) (e : Lk.hear[j]? = some b) : Decides Quiet b := by
  have alone : ∀ {x : Block S Cl} {a : Place}, a.kind ≠ KindName.K7 →
      IM.LaidAlone ProofFile.sameReply b x b.name a → Decides Quiet x → Decides Quiet b :=
    fun hk la D s rs gs t h => D s rs gs t ((IM.yes_alone la hk s t rs gs).1 h).1
  have k3 : ∀ dg : Bool, j = (if dg = true then 6 else 1) → Decides Quiet b := by
    intro dg ej
    obtain ⟨Lk', b', x, eL', e', k3, la⟩ := IM.k3_of hS hR O l (by omega) dg
    have ix : IM.k3Ix l dg = if dg = true then 6 else 1 := by
      show (if dg = true then 6 else 1) + (if l = 24 then 1 else 0) = _
      rw [if_neg (by omega : ¬ l = 24)]
      rfl
    rw [ix, ← ej] at e'
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
    obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
    exact alone (by intro k; cases k) la (theStated_quiet _ _ _ _ _ _ k3).1
  rcases hj with rfl | rfl | rfl | rfl
  · exact k3 false rfl
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
  · rcases Nat.even_or_odd' l with ⟨g, rfl | rfl⟩
    · obtain ⟨Lk', b', Xl, hp, eL', e', -, la, -⟩ := IM.k8_of_layers hS hR O g (by omega)
      obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
      obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
      exact alone (by intro k; cases k) la (k8Whole_quiet _).1
    · obtain ⟨Lk', b', Xl, a, eL', e', -, la, -⟩ := IM.k8_of_attention hS hR O g (by omega)
      obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
      obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
      exact alone (by intro k; cases k) la (k8Whole_quiet _).1
  · exact k3 true rfl

/-- Hearing sub-protocols number 3 and 5 of a link l < 24: kind K1's later sending, then a step that
leaves the statement. -/
theorem hear_commit (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 24)
    {j : Nat} (hj : j = 3 ∨ j = 5) {Lk : Link S Cl} {b : Block S Cl}
    (eL : c.links[l]? = some Lk) (e : Lk.hear[j]? = some b) {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : b.decide s rs gs = .ok t) :
    ∃ (Q : K1.Par) (link moment : Nat) (arrays : Option (List Nat)) (v : S) (rs' : List Fmt.RoundView)
      (gs' : List (List (Nat × List UInt64))),
      (K1.commitAtS Q link moment arrays : Block S Unit).decide s rs' gs' = .ok v ∧
        t.st = v.st := by
  have hk : (kindsBeforeBatching (IM.subAt l) (l == 0))[j]? = some KindName.K1 := by
    unfold IM.subAt
    rw [if_neg (by omega : ¬ l = 24)]
    rcases hj with rfl | rfl <;> split <;> cases (l == 0) <;> rfl
  obtain ⟨Lk', b', Xl, pr, pd, reads, digits, eL', e', -, -, harm⟩ :=
    IM.k1_later O l (IM.subAt l) (IM.subs_scope hS hR O l (by omega)) j hk
      (by rcases hj with rfl | rfl <;> decide)
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
  rcases harm with ⟨-, la⟩ | ⟨-, la⟩
  · have h' : (IM.k1Reads Z Bs.G₀ l Xl pr reads).decide s rs gs = .ok t :=
      ((IM.yes_alone la (by intro k; cases k) s t rs gs).1 h).1
    obtain ⟨v, a1, a2⟩ := andThen_yes h'
    exact ⟨_, _, _, _, v, _, _, a1,
      ((orLoud_whole fun b hb => readsQuietAt_quiet hb).1 v _ _ t a2).1.1⟩
  · exact ⟨_, _, _, _, t, rs, gs, ((IM.yes_alone la (by intro k; cases k) s t rs gs).1 h).1, rfl⟩

/-- **IN FRONT OF THE BATCHING OF LINK l, 1 ≤ l < 24: THE GROUP's MEMBERS AND FLAGS, WRITTEN OUT.**
t₀, t₃, t₅, u: the states in front of the link's first sub-protocol, of its two later sendings and
of its batching. -/
theorem fill_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h1 : 1 ≤ l)
    (h24 : l < 24) {p : ProofFile.InstPub} {R R₀ R₃ R₅ Ru : List Fmt.RoundView}
    {C C₀ C₃ C₅ Cu : List VerifiableInference.Desc.OpenedColumn} {t₀ t₃ t₅ u : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    (f₃ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 5)) (ProofFile.startS Z p) R C = .ok (t₃, R₃, C₃))
    (f₅ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 7)) (ProofFile.startS Z p) R C = .ok (t₅, R₅, C₅))
    (fu : foldBlocks 0 (c.blocksInOrder.take (14 * l + 9)) (ProofFile.startS Z p) R C = .ok (u, Ru, Cu)) :
    ∃ (x : _root_.Tw.K2.Front) (L₃ L₅ : LinkCtx) (Q₃ Q₅ : K1.Par),
      _root_.Tw.K2.firstFront t₀.st t₀.check.frame = .ok x ∧
      t₃.link? = some L₃ ∧ t₅.link? = some L₅ ∧
      (K1.idsOf Q₃ t₃.st.oracles.size).toList.length = (K1.flagsAt L₃.check.frame).length ∧
      (K1.idsOf Q₅ t₅.st.oracles.size).toList.length = (K1.flagsAt L₅.check.frame).length ∧
      Holds l
        ((K2.switchGain x ++ K2.ownGain x).map (·.1) ++
          (K1.idsOf Q₃ t₃.st.oracles.size).toList ++ (K1.idsOf Q₅ t₅.st.oracles.size).toList)
        ((K2.switchGain x ++ K2.ownGain x).map (·.2) ++ K1.flagsAt L₃.check.frame ++
          K1.flagsAt L₅.check.frame) u := by
  obtain ⟨hB, -⟩ := laid_at hS hR O (by omega : l < 25) f₀
  have hc := count_at hS hR O l (by omega) t₀ R₀ C₀ f₀
  obtain ⟨-, fs, hfs, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨Lk, -, -, -, -, eL, hlen, -⟩ := hfr l (by omega)
  rw [if_neg (by omega : ¬ l = 24)] at hlen
  have hearAt : ∀ j < 7, ∃ b, Lk.hear[j]? = some b ∧ c.blocksInOrder[14 * l + 2 + j]? = some b := by
    intro j hj
    obtain ⟨b, e⟩ : ∃ b, Lk.hear[j]? = some b :=
      ⟨_, List.getElem?_eq_getElem (by omega : j < Lk.hear.length)⟩
    refine ⟨b, e, ?_⟩
    have q := IM.hear_at_flat eL e
    rwa [(IM.flatIx_scope hS hR O (by omega : l ≤ 24) j).trans
      (by omega : 14 * l + j + 2 = 14 * l + 2 + j)] at q
  obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_cut (k := 14 * l + 3) 2 f₃
  obtain ⟨t₂, R₂, C₂, f₂⟩ := fold_cut (k := 14 * l + 4) 1 f₃
  obtain ⟨t₄, R₄, C₄, f₄⟩ := fold_cut (k := 14 * l + 6) 1 f₅
  obtain ⟨t₆, R₆, C₆, f₆⟩ := fold_cut (k := 14 * l + 8) 1 fu
  -- the first sub-protocol
  obtain ⟨Lk0, b0, x0, eLk, e0, -, J, hx⟩ := IM.k2_link_sits hS hR O l h1 h24
  obtain rfl : Lk = Lk0 := Option.some.inj (eL.symm.trans eLk)
  obtain ⟨b0', e0', i0⟩ := hearAt 0 (by omega)
  obtain rfl : b0 = b0' := Option.some.inj (e0.symm.trans e0')
  obtain ⟨rs, gs, d⟩ := fold_next i0 f₀ f₁
  obtain ⟨fs', f, m, hfs', hf, y1, -, y3, -, -⟩ := J.yes d
  have y1' : x0.decide t₀ (rs.take x0.retype.rounds.length) (gs.take x0.retype.openings) =
      .ok m := y1
  have H1 : ∃ x, _root_.Tw.K2.firstFront t₀.st t₀.check.frame = .ok x ∧
      Holds l ((K2.switchGain x ++ K2.ownGain x).map (·.1))
        ((K2.switchGain x ++ K2.ownGain x).map (·.2)) m := by
    rcases hx with ⟨-, hm⟩ | ⟨Pp, n, -, -, h3⟩
    · obtain ⟨er, he⟩ := hm t₀ (rs.take x0.retype.rounds.length) (gs.take x0.retype.openings)
      rw [he] at y1'
      cases y1'
    · rcases h3 with ⟨hn, -⟩ | ⟨l', HP, -, -, ex⟩ | ⟨l', -, ex⟩
      · cases hn
      · rw [ex] at y1'
        obtain ⟨v, a1, -⟩ := andThen_yes (n := x0.name) y1'
        obtain ⟨r₁, r₂, a, G', w, roots, -, H⟩ :=
          K2.head_inv (snd := _root_.Tw.K2.sendByL8) rfl a1
        unfold S.atBetween at hB
        rw [H.hHere] at hB
        cases hB
      · rw [ex] at y1'
        have h' : K2.decideWith _root_.Tw.K2.sendByL8
            (IM.k2P Z { chain := 1, link := some l, piece := 1, kind := .K2 } x0.name .link n) t₀
            _ _ = .ok m := y1'
        have k := switch_holds rfl h'
        rwa [hc] at k
  obtain ⟨x, hxf, H1⟩ := H1
  have st1 : t₁.st = m.st := by
    have k := framesOf_st hfs' f (List.mem_of_getElem? hf) m t₁ y3
    exact k
  have stQ : ∀ j, (j = 1 ∨ j = 2 ∨ j = 4 ∨ j = 6) → ∀ s r q s' r' q',
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 2 + j)) (ProofFile.startS Z p) R C = .ok (s, r, q) →
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 2 + j + 1)) (ProofFile.startS Z p) R C = .ok (s', r', q') →
      s'.st = s.st := by
    intro j hj s r q s' r' q' g g'
    obtain ⟨b, e, ib⟩ := hearAt j (by omega)
    obtain ⟨rs', gs', d'⟩ := fold_next ib g g'
    exact (hear_quiet hS hR O h24 hj eL e s rs' gs' s' d').1.1
  have H3 : Holds l _ _ t₃ := holds_st (stQ 2 (by omega) t₂ R₂ C₂ t₃ R₃ C₃ f₂ f₃)
    (holds_st (stQ 1 (by omega) t₁ R₁ C₁ t₂ R₂ C₂ f₁ f₂) (holds_st st1 H1))
  obtain ⟨L₃, hL₃, -, g₃⟩ := group_open hS hR O h24 2 (by omega) t₃ R₃ C₃ f₃
  obtain ⟨L₅, hL₅, -, g₅⟩ := group_open hS hR O h24 4 (by omega) t₅ R₅ C₅ f₅
  obtain ⟨b3, e3, i3⟩ := hearAt 3 (by omega)
  obtain ⟨rs3, gs3, d3⟩ := fold_next i3 f₃ f₄
  obtain ⟨Q₃, lk3, mo3, ar3, v3, rs3', gs3', c3, s3⟩ :=
    hear_commit hS hR O h24 (Or.inl rfl) eL e3 d3
  have H4 : Holds l _ _ t₄ := holds_st s3 (g₃ ▸ holds_commit c3 hL₃ (g₃.symm ▸ H3))
  have H5 : Holds l _ _ t₅ := holds_st (stQ 4 (by omega) t₄ R₄ C₄ t₅ R₅ C₅ f₄ f₅) H4
  obtain ⟨b5, e5, i5⟩ := hearAt 5 (by omega)
  obtain ⟨rs5, gs5, d5⟩ := fold_next i5 f₅ f₆
  obtain ⟨Q₅, lk5, mo5, ar5, v5, rs5', gs5', c5, s5⟩ :=
    hear_commit hS hR O h24 (Or.inr rfl) eL e5 d5
  have H6 : Holds l _ _ t₆ := holds_st s5 (g₅ ▸ holds_commit c5 hL₅ (g₅.symm ▸ H5))
  have n3 : (K1.idsOf Q₃ t₃.st.oracles.size).toList.length =
      (K1.flagsAt L₃.check.frame).length := by
    obtain ⟨r₁, r₂, rfl⟩ := commitAtS_two c3
    exact commit_len c3 hL₃
  have n5 : (K1.idsOf Q₅ t₅.st.oracles.size).toList.length =
      (K1.flagsAt L₅.check.frame).length := by
    obtain ⟨r₁, r₂, rfl⟩ := commitAtS_two c5
    exact commit_len c5 hL₅
  exact ⟨x, L₃, L₅, Q₃, Q₅, hxf, hL₃, hL₅, n3, n5,
    holds_st (stQ 6 (by omega) t₆ R₆ C₆ u Ru Cu f₆ fu) H6⟩

end

#print axioms holds_commit
#print axioms switch_holds
#print axioms hear_commit
#print axioms fill_at

end Meaning.K2
