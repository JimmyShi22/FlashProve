-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/HeadSentIs.lean: code switching (the kind K2): THE MAKING OF THE PUBLIC
ITEMS "frame.sentIs" AND "ledger.treesAre" AT THE HEAD's LINK: behind an accept of the kind's
decision in the head's dress, followed by "H.1.quiet" (K2.headOpenQ), their tests
(sentIsB | treesAreB, Johnson/Desc/First/FillSent.lean) accept. The twin, at the head, of
Tw/K2C/SentIsMade.lean and Road/K4/Rec/MakerJoin.lean | MakerAtBorder.lean at a
link. NO BLOCK IMPORTS THIS FILE.
  head_frame_behind   the open link's frame behind the two steps: «next» is «later or close» · its
                      link is P.l · its groups are the head's own part's frame's · keptBefore and
                      own as cuts of the sending's numbers; G is the chain's own frame's group at
                      its link
  head_sentIs         sentIsB (sentDataOf ‹the frame's shape in front› (fun _ => ‹the number of
                      messages in front›) trees) P.l s' = true FROM FOUR FACTS AT THE STATE IN
                      FRONT: hl (the chain's frame's link is P.l) · hg (its groups are reqGroups
                      of its shape) · hA (the head's own part's frame has no own message yet, and
                      its groups are the chain's frame's)
  head_sentIs_at      the same at the term sentDataAt shape N links ps built (by
                      Road/K4/Rec/MakerAtBorder.lean's data_at_border)
  head_treesAre_at    treesAreB (sentDataAt …) m s' = true where the built link m's planned ledger
                      is P.X's
LIMITS. The facts in front are premises. Shown at no value. No soundness is claimed.

-/
import Johnson.Top.H0.Tw.K2C.HeadNumbers
import Johnson.Top.H0.Tw.K2C.HeadLedger
import Johnson.Top.H0.Tw.K2C.SentIsMade
import Johnson.Road.K4.Rec.MakerAtBorder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First (ModelPart Numbers shift)
open _root_.Tw.K2 (SwIn SwOut switchBehind switchNotices sendByL8 firstFront firstBehind)
open Johnson.Desc.First.Walk (firstKept emptySlots weightsAtZero)
open VerifiableInference.Desc.First.FillSent (sentDataOf sentDataAt TreeLook treeLook sentIsB
  treesAreB treesAt looksOf)
open OnBytes.Road.K4.Rec (data_at_border)

theorem head_frame_behind {p : P2} {P : HeadPar} {s m s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hp : p.stands = .head)
    (h₁ : decideWith sendByL8 p s rs gs = .ok m) (h₂ : headOpenQ P m = .ok s') :
    ∃ (a : HeadOwn) (G : ReqGroup) (L : LinkCtx), s.here = .head a ∧
      s.check.frame.groups[s.check.frame.link]? = some G ∧ s'.link? = some L ∧
      L.check.frame.next = .laterOrClose ∧ L.check.frame.link = P.l ∧
      L.check.frame.groups = a.fr.groups ∧
      L.check.frame.keptBefore = (sentIds s.st.oracles.size
        (switchNotices G.target (headFrontOf s a G.target).others).size).extract 1
          (1 + G.target.kept.size) ∧
      L.check.frame.own = a.fr.own ++ ((sentIds s.st.oracles.size
        (switchNotices G.target (headFrontOf s a G.target).others).size).extract
          (1 + G.target.kept.size)
          (switchNotices G.target (headFrontOf s a G.target).others).size).extract 0
            (s.check.frame.atMoment 0).length := by
  obtain ⟨r₁, r₂, a, G, w, roots, _, k⟩ := head_inv hp h₁
  obtain ⟨lay, e1, St, e2, e3⟩ := switch_numbers k.hSwitch
  obtain ⟨a2, st, f, mine, L, out, y, cov, s₁, b, q⟩ := (headOpenQ_iff P m s').1 h₂
  obtain ⟨_, ⟨b', hb', ho⟩, _⟩ := headOpenOpens P m s' h₂
  have ha2 : a2 = { a with kept := w.out.kept, ids := w.out.others } := by
    have e := q.here
    rw [k.hOut] at e
    injection e with e
    exact e.symm
  have hmc : m.check = s.check := by rw [k.hOut]
  obtain ⟨mask, bA⟩ := (_root_.Tw.K2.firstBehind_iff _ _ _ _ _ _ _).1 q.behind
  obtain ⟨_, hlk, hL, _⟩ := Johnson.Desc.First.Walk.Law.front_ok q.front
  have hb2 : b' = { b with
      L := L
      F := emptySlots (weightsAtZero { trees := P.X.Fp.trees }) P.hp.ns } := by
    have e := hb'
    rw [q.out'] at e
    injection e with e
    exact e.symm
  refine ⟨a, G, L, k.hHere, k.hGroup, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold S.link?
    rw [hb']
    simp only [ho, if_true]
    rw [hb2]
  · rw [hL]
    show f.next = _
    rw [bA.frame]
  · rw [hL]
    exact hlk
  · rw [hL]
    show f.groups = _
    rw [bA.frame]
    show a2.fr.groups = _
    rw [ha2]
  · rw [hL]
    show f.keptBefore = _
    rw [bA.frame]
    show a2.kept = _
    rw [ha2]
    exact e2
  · rw [hL]
    show f.own = _
    rw [bA.frame]
    show a2.fr.own ++ mine = _
    rw [bA.theOwn, ha2]
    show a.fr.own ++ w.out.others.extract 0 (m.check.frame.atMoment 0).length = _
    rw [hmc, e3]
    rfl

theorem head_sentIs {p : P2} {P : HeadPar} {s m s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hp : p.stands = .head)
    (h₁ : decideWith sendByL8 p s rs gs = .ok m) (h₂ : headOpenQ P m = .ok s')
    (hl : s.check.frame.link = P.l) (h0 : P.l ≠ 0)
    (hg : s.check.frame.groups = reqGroups s.check.frame.shape)
    (hA : ∀ a, s.here = .head a → a.fr.own = #[] ∧ a.fr.groups = s.check.frame.groups)
    (trees : Nat → List TreeLook) :
    sentIsB (sentDataOf s.check.frame.shape (fun _ => s.st.oracles.size) trees) P.l s' = true := by
  obtain ⟨a, G, L, ha, hG0, hL, e1, e2, e3, k1, k2⟩ := head_frame_behind hp h₁ h₂
  obtain ⟨hO, hAg⟩ := hA a ha
  have hG : (reqGroups s.check.frame.shape)[P.l]? = some G := by
    rw [← hg, ← hl]
    exact hG0
  have hb : G.target.kept.size = G.born.size := born_size _ hG
  have hGd : (reqGroups s.check.frame.shape).getD P.l {} = G := by
    rw [Array.getD_eq_getD_getElem?, hG]
    rfl
  have ho : (headFrontOf s a G.target).others.size = (s.check.frame.atMoment 0).length + 1 := by
    simp [headFrontOf, ReqFrame.notices]
  have hN : (switchNotices G.target (headFrontOf s a G.target).others).size =
      1 + G.target.kept.size + (headFrontOf s a G.target).others.size := by
    simp [switchNotices]
    omega
  have hlen : (s.check.frame.atMoment 0).length =
      (((s.check.frame.shape.link[P.l]?.map (·.messages)).getD []).filter
        fun y => y.moment == 0).length := by
    rw [← hl]
    rfl
  unfold sentIsB
  rw [hL]
  unfold sentDataOf
  simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨e1, e2⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [e3, hAg, hg]
  · rw [k2, hO, if_neg (by simpa using h0), hGd, ← hb, ← hlen]
    have c1 := cut_ids s.st.oracles.size
      (switchNotices G.target (headFrontOf s a G.target).others).size (1 + G.target.kept.size)
      ((headFrontOf s a G.target).others.size) (by omega)
    have e : 1 + G.target.kept.size + (headFrontOf s a G.target).others.size =
        (switchNotices G.target (headFrontOf s a G.target).others).size := hN.symm
    rw [e] at c1
    rw [c1]
    apply Array.ext
    · simp
      omega
    · intro i h1 h2
      simp
  · rw [k1, if_neg (by simpa using h0), hGd, ← hb]
    exact cut_ids _ _ 1 G.target.kept.size (by omega)

section
variable {shape : Params.ReqShape} {N : Numbers} {links : List ModelPart} {ps : List Place}
  {built : Array Stages.LinkH} {pl : Place}

theorem head_sentIs_at {p : P2} {P : HeadPar} {s m s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hp : p.stands = .head)
    (h₁ : decideWith sendByL8 p s rs gs = .ok m) (h₂ : headOpenQ P m = .ok s')
    (hl : s.check.frame.link = P.l) (h0 : P.l ≠ 0)
    (hg : s.check.frame.groups = reqGroups s.check.frame.shape)
    (hA : ∀ a, s.here = .head a → a.fr.own = #[] ∧ a.fr.groups = s.check.frame.groups)
    (hpl : (ps.find? fun q => q.link == some P.l &&
      q.piece == 1 + ((links[P.l]?).map shift).getD 0) = some pl)
    (hn : s.st.oracles.size = N.msgsAt (some pl)) (hsh : s.check.frame.shape = shape) :
    sentIsB (sentDataAt shape N links ps built) P.l s' = true := by
  have h := head_sentIs hp h₁ h₂ hl h0 hg hA (sentDataAt shape N links ps built).trees
  obtain ⟨b1, b2, b3⟩ := data_at_border (built := built) hpl hn hsh
  unfold sentIsB at h ⊢
  rw [b1, b2, b3]
  exact h

theorem head_treesAre_at {P : HeadPar} {m s' : S} (h₂ : headOpenQ P m = .ok s') {k : Nat}
    {X : Stages.LinkH} (hX : built[k]? = some X) (hF : X.Fp.trees = P.X.Fp.trees) :
    treesAreB (sentDataAt shape N links ps built) k s' = true := by
  unfold treesAreB
  rw [headOpenQ_fork h₂]
  simp only [Option.any_some, decide_eq_true_eq]
  show _ = treesAt built k
  unfold treesAt
  rw [hX]
  show _ = looksOf X.Fp
  unfold looksOf
  rw [hF]
  show ((P.X.Fp.trees.map fun T =>
    { T with rows := T.rows.map fun r => { r with L := Array.replicate T.K zeroE } }).toList.map
      treeLook) = _
  rw [Array.toList_map, List.map_map]
  refine List.map_congr_left fun T _ => ?_
  show (T.R, T.K, ((T.rows.map fun r => { r with L := Array.replicate T.K zeroE }).toList.map
    fun r => (r.L0, r.L.size))) = _
  rw [Array.toList_map, List.map_map]
  congr 2
  refine List.map_congr_left fun r _ => ?_
  simp

end

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.head_frame_behind
#print axioms VerifiableInference.Desc.First.K2.head_sentIs
#print axioms VerifiableInference.Desc.First.K2.head_sentIs_at
#print axioms VerifiableInference.Desc.First.K2.head_treesAre_at
