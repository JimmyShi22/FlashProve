-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/GroupsAtYes.lean: code switching (the kind K2): K2's SHARE OF THE DEAL «GS»:
AT A YES OF THE SWITCH, AT EACH OF ITS THREE SORTS OF PLACE: which group gains which members, with
which flags «kept», in which order; every other group stays; how many groups there are. NO BLOCK
IMPORTS THIS FILE. s, s': the verifier's state in front of the sub-protocol's decision and behind
it. n0: the number of oracle messages of the statement in front. K: the number of the target's
kept shapes.
  switchGain x       what the switch itself joins to its group: its main message, number n0, flag
                     false; then the K kept copies, numbers n0 + 1 …, each with its target's flag
                     «kept again»
  ownGain x          what a later link's first sending joins behind it: the link's own messages of
                     moment 0, numbers n0 + 1 + K …, flag «it has a life»
  ids_cut            a stretch of a sending's numbers (so that K2C/SentIsMade.lean,
                     which stands over Road/K4/Rec/MakerStatement.lean, is imported no
                     more)
  rising_range | _left | _right   numbers c, c + 1, … rise, also zipped with any list
  switch_gains       a yes of the switch at a front whose group has no member yet: GainsAt
                     x.f.group (switchGain x) x.st w.st
  yes_link_groups    AT A LINK: one group more than in front (the front pushes it); every group in
                     front stays; the new group's members and flags are switchGain x ++ ownGain x,
                     in that order
  own_gains · mine_is   the link's own messages join behind the switch, by rising numbers
  yes_head_groups    AT THE HEAD's LINK, the decision at «H:2» alone, where the group that the
                     head's own part of the state names has no member yet: GainsAt a.fr.group
                     (switchGain x) s.st s'.st
  head_place_groups  the whole place «H:2»: the decision, then the quiet step "H.1.quiet", which
                     joins the link's own messages: GainsAt a.fr.group (switchGain x ++ ownGain x)
                     s.st s'.st
  yes_finish_groups  AT THE FINISH, at the state t that the way in hands to the switch: the like
THE FOLD's MASK IS SENT AND NOT JOINED: it is the last of the sending's notices at a link and at
the head; its number is in neither list.
LIMITS. «No member yet» at the head's link and at the finish is a premise here: paid by
headFrontQ_groups (K2C/FrontGroup.lean) with «K7's sub-protocol leaves the statement», and by
finishFrontQ_st | _fr (K2C/FinFront.lean). No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.GroupsStay
import Johnson.Top.H0.K2Hears.Whole
import Johnson.Top.H0.Tw.K2C.HeadNumbers
import Johnson.Top.H0.Tw.K2C.FrontGroup

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (SwIn SwOut switchE switchBehind switchNotices sendByL8 firstFront firstBehind
  joinG)
open VerifiableInference.Desc.LinkJoin

/-- What the switch itself joins to its group. -/
def switchGain (x : _root_.Tw.K2.Front) : List (Nat × Bool) :=
  (x.st.oracles.size, false) ::
    (((List.range x.T.kept.size).map (· + (x.st.oracles.size + 1))).zip x.T.kept.toList).map
      fun p => (p.1, p.2.keptAgain)

/-- What a later link's first sending joins behind the switch. -/
def ownGain (x : _root_.Tw.K2.Front) : List (Nat × Bool) :=
  (x.own.zip ((List.range x.own.length).map
    (· + (x.st.oracles.size + (1 + x.T.kept.size))))).map fun y => (y.2, decide (0 < y.1.life))

/-- A stretch of a sending's numbers. (K2C/SentIsMade.lean has the same sentence as cut_ids; it is
said again here, under another name, so that this file does not stand over that one.) -/
theorem ids_cut (n0 N a k : Nat) (h : a + k ≤ N) :
    (sentIds n0 N).extract a (a + k) = (Array.range k).map (· + (n0 + a)) := by
  unfold sentIds
  apply Array.ext
  · simp
    omega
  · intro i h1 h2
    simp
    omega

theorem rising_range (c : Nat) (n : Nat) : ((List.range n).map (· + c)).Pairwise (· < ·) := by
  rw [List.pairwise_map]
  exact List.pairwise_lt_range.imp fun h => Nat.add_lt_add_right h c

theorem rising_left {β : Type} (c : Nat) (l : List β) :
    (((List.range l.length).map (· + c)).zip l).Pairwise fun a b => a.1 < b.1 := by
  have e : ((((List.range l.length).map (· + c)).zip l).map Prod.fst) =
      (List.range l.length).map (· + c) := List.map_fst_zip (by simp)
  have := rising_range c l.length
  rw [← e, List.pairwise_map] at this
  exact this

theorem rising_right {β : Type} (c : Nat) (l : List β) :
    (l.zip ((List.range l.length).map (· + c))).Pairwise fun a b => a.2 < b.2 := by
  have e : ((l.zip ((List.range l.length).map (· + c))).map Prod.snd) =
      (List.range l.length).map (· + c) := List.map_snd_zip (by simp)
  have := rising_range c l.length
  rw [← e, List.pairwise_map] at this
  exact this

/-- **A yes of the switch itself, at a front whose group has no member yet.** -/
theorem switch_gains {P : _root_.Tw.K2.Par9} {s9 : _root_.Tw.K2.S9} {x : _root_.Tw.K2.Front}
    {r₁ r₂ : Fmt.RoundView} {cols : List _root_.Tw.K2.Col} {w : SwOut} {roots : Nat}
    (hw : switchE switchBehind P sendByL8 s9 x r₁ r₂ cols = .ok (w, roots)) {G : Group}
    (hG : x.st.groups[x.f.group]? = some G) (hm : G.members = #[]) (hk : G.kept = #[]) :
    GainsAt x.f.group (switchGain x) x.st w.st := by
  obtain ⟨y, k⟩ := switchE_inv hw
  obtain ⟨c, Y, S1, S2, S3, rows, hB⟩ := switchBehind_inv k.hBehind
  have hK := sent_ok k.hSend
  have g0 : GS x.st y.st := gs_of_groups hK.groups
  have g1 : GS y.st S1 := by
    have h := hB.hLedger
    split at h
    · exact ledger_gs h
    · cases h
      exact GS.refl _
  have hN : (switchNotices x.T x.others).size = 1 + x.T.kept.size + x.others.size := by
    simp [switchNotices]
    omega
  have hid : y.ids = sentIds x.st.oracles.size (switchNotices x.T x.others).size := hK.ids
  have h0 : y.ids.getD 0 noId = x.st.oracles.size := by
    rw [hid]
    unfold sentIds
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
    rw [if_pos (by omega)]
    simp
  have hkp : y.ids.extract 1 (1 + x.T.kept.size) =
      (Array.range x.T.kept.size).map (· + (x.st.oracles.size + 1)) := by
    rw [hid]
    exact ids_cut _ _ 1 x.T.kept.size (by omega)
  -- the group in front of the joins
  have e1 := (g0.trans g1).2 x.f.group
  rw [hG] at e1
  obtain ⟨G1, hG1, eG1⟩ := Option.map_eq_some_iff.1 e1
  have m1 : G1.members = #[] := (congrArg Prod.fst eG1).trans hm
  have k1 : G1.kept = #[] := (congrArg Prod.snd eG1).trans hk
  have j1 : GainsAt x.f.group [(x.st.oracles.size, false)] S1 S2 := by
    have h := hB.hJoinG
    rw [show (behindArgs P x y r₂ cols).ids.getD 0 noId = x.st.oracles.size from h0] at h
    exact join_gains h hG1 (by simp [m1, k1]) fun m hmm => by rw [m1] at hmm; simp at hmm
  obtain ⟨G1', G2, hG1', hG2, em, ek⟩ := j1.2.2
  obtain rfl : G1' = G1 := Option.some.inj (hG1'.symm.trans hG1)
  have j2 : GainsAt x.f.group
      ((((List.range x.T.kept.size).map (· + (x.st.oracles.size + 1))).zip x.T.kept.toList).map
        fun p => (p.1, p.2.keptAgain)) S2 S3 := by
    have h := hB.hJoinKept
    rw [show (behindArgs P x y r₂ cols).ids.extract 1 (1 + (behindArgs P x y r₂ cols).T.kept.size) =
      (Array.range x.T.kept.size).map (· + (x.st.oracles.size + 1)) from hkp,
      ← Array.foldlM_toList, Array.toList_zip] at h
    simp only [Array.toList_map, Array.toList_range] at h
    refine joins_gains x.f.group (fun p : Nat × KeptTarget => p.1) (fun p => p.2.keptAgain) _ S2 S3
      h ?_ G2 hG2 (by rw [em, ek, m1, k1]; simp) fun m hmm p hp => ?_
    · have := rising_left (x.st.oracles.size + 1) x.T.kept.toList
      rwa [Array.length_toList] at this
    · rw [em, m1] at hmm
      have e : m = x.st.oracles.size := by simpa using hmm
      have h1 := (List.of_mem_zip hp).1
      obtain ⟨i, _, hi⟩ := List.mem_map.1 h1
      show m < p.1
      rw [e, ← hi]
      omega
  exact GainsAt.right (GainsAt.left (g0.trans g1) (j1.trans j2)) (rows_gs hB.hAdded)

/-- **The link's own messages join behind the switch.** Sw: the statement behind the switch. -/
theorem own_gains {x : _root_.Tw.K2.Front} {Sw S' : Statement} {mine : Array Nat} {G : Group}
    (hG : x.st.groups[x.f.group]? = some G) (hm : G.members = #[]) (hk : G.kept = #[])
    (A : GainsAt x.f.group (switchGain x) x.st Sw)
    (hj : (zipT x.own mine.toList).foldlM
      (fun S y => joinG S x.f.group y.2 (decide (0 < y.1.life))) Sw = .ok S')
    (hmine : mine = (Array.range x.own.length).map
      (· + (x.st.oracles.size + (1 + x.T.kept.size)))) :
    GainsAt x.f.group (switchGain x ++ ownGain x) x.st S' := by
  obtain ⟨Ga, Gw, hGa, hGw, wm, wk⟩ := A.2.2
  obtain rfl := Option.some.inj (hGa.symm.trans hG)
  refine A.trans ?_
  rw [OnBytes.zipT_eq, hmine] at hj
  simp only [Array.toList_map, Array.toList_range] at hj
  refine joins_gains x.f.group (fun y : Params.ReqMessage × Nat => y.2)
    (fun y => decide (0 < y.1.life)) _ Sw S' hj (rising_right _ x.own) Gw hGw
    (by rw [wm, wk, hm, hk]; simp [switchGain]) fun m hmm q hq => ?_
  rw [wm, hm] at hmm
  have h2 := (List.of_mem_zip hq).2
  obtain ⟨i, _, hi⟩ := List.mem_map.1 h2
  show m < q.2
  rw [← hi]
  have hmm' : m ∈ (switchGain x).map (·.1) := by simpa using hmm
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hmm'
  unfold switchGain at hz
  rcases List.mem_cons.1 hz with rfl | hz
  · show x.st.oracles.size < _
    omega
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hz
    obtain ⟨j, hj', hju⟩ := List.mem_map.1 (List.of_mem_zip hu).1
    have := List.mem_range.1 hj'
    show u.1 < _
    rw [← hju]
    omega

/-- The numbers of the link's own messages, as the switch returns them. -/
theorem mine_is {x : _root_.Tw.K2.Front} {others : Array Nat}
    (eo : others = (sentIds x.st.oracles.size (switchNotices x.T x.others).size).extract
      (1 + x.T.kept.size) (switchNotices x.T x.others).size)
    (ho : x.others.size = x.own.length + 1) :
    others.extract 0 x.own.length = (Array.range x.own.length).map
      (· + (x.st.oracles.size + (1 + x.T.kept.size))) := by
  have hN : (switchNotices x.T x.others).size = 1 + x.T.kept.size + x.others.size := by
    simp [switchNotices]
    omega
  rw [eo]
  have c1 := ids_cut x.st.oracles.size (switchNotices x.T x.others).size (1 + x.T.kept.size)
    x.others.size (by omega)
  rw [show 1 + x.T.kept.size + x.others.size = (switchNotices x.T x.others).size from
    hN.symm] at c1
  rw [c1]
  apply Array.ext
  · simp
    omega
  · intro i h1 h2
    simp

/-- **At a link.** -/
theorem yes_link_groups {p : P2} {s : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {s' : S} (hp : p.stands = .link) (h : decideWith sendByL8 p s rs gs = .ok s') :
    ∃ x : _root_.Tw.K2.Front, firstFront s.st s.check.frame = .ok x ∧
      x.st.oracles.size = s.st.oracles.size ∧ x.f.group = s.st.groups.size ∧
      s'.st.groups.size = s.st.groups.size + 1 ∧
      (∀ i, i < s.st.groups.size → (s'.st.groups[i]?).map (fun G => (G.members, G.kept)) =
        (s.st.groups[i]?).map (fun G => (G.members, G.kept))) ∧
      ∃ G', s'.st.groups[s.st.groups.size]? = some G' ∧
        G'.members = ((switchGain x ++ ownGain x).map (·.1)).toArray ∧
        G'.kept = ((switchGain x ++ ownGain x).map (·.2)).toArray := by
  obtain ⟨r₁, r₂, x, w, roots, S', f, mine, rfl, k⟩ := link_inv hp h
  obtain ⟨e1, e2⟩ := firstFront_st k.hFront
  obtain ⟨lay, _, _, _, eo⟩ := switch_numbers k.hSwitch
  obtain ⟨mask, bA⟩ := (_root_.Tw.K2.firstBehind_iff _ _ _ _ _ _ _).1 k.hBehind
  obtain ⟨L, G₀, S0, g, a⟩ := (_root_.Tw.K2.firstFront_iff _ _ _).1 k.hFront
  have hfr : x.st.groups[x.f.group]? =
      some (freshGroup s.check.frame.shape.code s.check.frame.shape.maskCode) := by
    rw [e1, e2]
    simp [withFresh]
  have A := switch_gains k.hSwitch hfr rfl rfl
  have ho : x.others.size = x.own.length + 1 := by
    rw [a.out]
    simp [ReqFrame.notices]
  have AB := own_gains hfr rfl rfl A bA.joins (by rw [bA.theOwn]; exact mine_is eo ho)
  have hsz : x.st.groups.size = s.st.groups.size + 1 := by
    rw [e1]
    simp [withFresh]
  refine ⟨x, k.hFront, by rw [e1]; rfl, e2, ?_, fun i hi => ?_, ?_⟩
  · rw [k.hOut]
    exact AB.1.trans hsz
  · rw [k.hOut]
    show (S'.groups[i]?).map _ = _
    rw [AB.2.1 i (by rw [e2]; omega), e1]
    simp [withFresh, Array.getElem?_push, Nat.ne_of_lt hi]
  · obtain ⟨Gx, G', hGx, hG', em, ek⟩ := AB.2.2
    obtain rfl := Option.some.inj (hGx.symm.trans hfr)
    refine ⟨G', ?_, ?_, ?_⟩
    · rw [k.hOut, ← e2]
      exact hG'
    · rw [em]
      simp [freshGroup]
    · rw [ek]
      simp [freshGroup]

/-- **At the head's link**: the decision at «H:2». -/
theorem yes_head_groups {p : P2} {s : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {s' : S} (hp : p.stands = .head) (h : decideWith sendByL8 p s rs gs = .ok s') :
    ∃ (a : HeadOwn) (G₀ : ReqGroup), s.here = .head a ∧
      s.check.frame.groups[s.check.frame.link]? = some G₀ ∧
      ∀ G : Group, s.st.groups[a.fr.group]? = some G → G.members = #[] → G.kept = #[] →
        GainsAt a.fr.group (switchGain (headFrontOf s a G₀.target)) s.st s'.st := by
  obtain ⟨r₁, r₂, a, G₀, w, roots, rfl, k⟩ := head_inv hp h
  refine ⟨a, G₀, k.hHere, k.hGroup, fun G hG hm hk => ?_⟩
  rw [k.hOut]
  exact switch_gains k.hSwitch hG hm hk

/-- **At the head's link, the whole place «H:2»**: the decision, then the quiet step "H.1.quiet",
which joins the link's own messages. -/
theorem head_place_groups {p : P2} {P : HeadPar} {s m s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hp : p.stands = .head)
    (h₁ : decideWith sendByL8 p s rs gs = .ok m) (h₂ : headOpenQ P m = .ok s') :
    ∃ (a : HeadOwn) (G₀ : ReqGroup), s.here = .head a ∧
      s.check.frame.groups[s.check.frame.link]? = some G₀ ∧
      ∀ G : Group, s.st.groups[a.fr.group]? = some G → G.members = #[] → G.kept = #[] →
        GainsAt a.fr.group (switchGain (headFrontOf s a G₀.target) ++
          ownGain (headFrontOf s a G₀.target)) s.st s'.st := by
  obtain ⟨r₁, r₂, a, G₀, w, roots, rfl, k⟩ := head_inv hp h₁
  obtain ⟨lay, _, _, _, eo⟩ := switch_numbers k.hSwitch
  obtain ⟨a2, st, f, mine, L, out, y, cov, s₁, b, q⟩ := (headOpenQ_iff P m s').1 h₂
  have ha2 : a2 = { a with kept := w.out.kept, ids := w.out.others } := by
    have e := q.here
    rw [k.hOut] at e
    injection e with e
    exact e.symm
  have hmc : m.check = s.check := by rw [k.hOut]
  have hms : m.st = w.st := by rw [k.hOut]
  obtain ⟨mask, bA⟩ := (_root_.Tw.K2.firstBehind_iff _ _ _ _ _ _ _).1 q.behind
  refine ⟨a, G₀, k.hHere, k.hGroup, fun G hG hm hk => ?_⟩
  have A := switch_gains k.hSwitch hG hm hk
  have hj := bA.joins
  have hmine := bA.theOwn
  rw [ha2, hmc, hms] at hj
  rw [ha2, hmc] at hmine
  have e' : s'.st = st := by rw [q.out']
  rw [e']
  exact own_gains (x := headFrontOf s a G₀.target) hG hm hk A hj
    (by rw [hmine]; exact mine_is (x := headFrontOf s a G₀.target) eo (by simp [headFrontOf,
      ReqFrame.notices]))

/-- **At the finish**, at the state that the way in hands to the switch. -/
theorem yes_finish_groups {p : P2} {t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {t' : S} (hp : p.stands = .finish)
    (h : decideWith sendByL8 p t rs gs = .ok t') :
    ∃ (a : FinOwn) (G₀ : ReqGroup), t.here = .fin a ∧ a.G = some G₀ ∧
      ∀ G : Group, t.st.groups[a.fr.group]? = some G → G.members = #[] → G.kept = #[] →
        GainsAt a.fr.group (switchGain (finFrontOf t a G₀)) t.st t'.st := by
  obtain ⟨r₁, r₂, a, G₀, w, roots, rfl, k⟩ := finish_inv hp h
  refine ⟨a, G₀, k.hHere, k.hLaid, fun G hG hm hk => ?_⟩
  rw [k.hOut]
  exact switch_gains k.hSwitch hG hm hk

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.switch_gains
#print axioms VerifiableInference.Desc.First.K2.yes_link_groups
#print axioms VerifiableInference.Desc.First.K2.yes_head_groups
#print axioms VerifiableInference.Desc.First.K2.head_place_groups
#print axioms VerifiableInference.Desc.First.K2.yes_finish_groups
