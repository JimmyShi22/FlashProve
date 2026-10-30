-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/MadeK5Reads.lean: code switching (K2): THE THIRD CLAUSE OF "K5.readsThere" AT THE
STATE THAT THE SWITCH LEAVES (r3B, Johnson/P1K2R/MadeK5At.lean: the premise c3 of made_k5_first):
the link's first masked message has a number in the frame behind, the book behind places it, and
the list «own» holds that seat. BROUGHT TO TWO FACTS ON THE SHAPE AND ONE ON THE NUMBERS IN FRONT.
NO BLOCK IMPORTS THIS FILE.
  own_at      behind an accept in a link's dress: the frame's j-th own number is n0 + (1 + K + j)
              (n0: the front's statement's number of messages; K: the target's kept ones), for j
              below the number of the link's messages of moment 0. By K2.yes_link_frame
              (Tw/K2C/LinkNumbers.lean)
  r3_left     r3B own sh l m.check.frame m.book = true FROM: hlk (the frame's link in front is l)
              · hμ (μ is the first message of link l of the shape sh with a mask row: ON THE
              SHAPE) · hμ0 (μ stands below the number of the frame's messages of moment 0 in
              front) · hown (the list holds the seat (trees in front + the lay's tree of notice 1
              + K + μ, the lay's part of it))
  made_k5_firstR   P1K2.made_k5_first with its premise c3 paid so: the two K5 items behind every
                   accept of an attention link's first place
BY: own_at · K2.yes_new_seat (Tw/K2C/NewAtYes.lean) · K2.yes_link_next | yes_link_stays
· ReqFrame.whereIs' text (OnBytes/Iop/Req.lean).
LIMITS. hown is the debt that is left: the promise's numbers against the public data's list. Shown
at no value. No soundness is claimed.
-/
import Johnson.P1K2R.MadeK5At
import Johnson.Top.H0.Tw.K2C.LinkNumbers
import Johnson.Top.H0.Tw.K2C.NewAtYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 decideWith yes_link_next yes_link_stays yes_link_frame
  yes_new_seat sentIds FrontOf)
open _root_.Tw.K2 (sendByL8 firstFront switchNotices)

theorem own_at {p : P2} {s m : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hp : p.stands = .link) (hd : decideWith sendByL8 p s rs gs = .ok m) {j : Nat}
    (hj : j < (s.check.frame.atMoment 0).length) :
    ∃ x : _root_.Tw.K2.Front, firstFront s.st s.check.frame = .ok x ∧
      1 + x.T.kept.size + j < (switchNotices x.T x.others).size ∧
      m.check.frame.own[j]? = some (x.st.oracles.size + (1 + x.T.kept.size + j)) := by
  obtain ⟨x, lay, hx, ho, _, _, _, _, eO, _, hz⟩ := yes_link_frame hp hd
  rw [← ho] at hj
  have hlt : j < m.check.frame.own.size := by rw [hz]; exact hj
  have hlt2 := hlt
  rw [eO] at hlt2
  have hs2 := hlt2
  simp only [Array.size_extract, sentIds, Array.size_map, Array.size_range] at hs2
  refine ⟨x, hx, by omega, ?_⟩
  rw [eO, Array.getElem?_eq_getElem hlt2]
  simp only [Array.getElem_extract, sentIds, Array.getElem_map, Array.getElem_range]
  congr 1
  omega

theorem r3_left {p : P2} {s m : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hp : p.stands = .link) (hd : decideWith sendByL8 p s rs gs = .ok m) {sh : Params.ReqShape}
    {l : Nat} (hlk : s.check.frame.link = l) {μ : Nat}
    (hμ : (((sh.link[l]?.map (·.messages)).getD []).findIdx? fun x =>
      x.shape.maskRows != 0) = some μ)
    (hμ0 : μ < (s.check.frame.atMoment 0).length) {own : List (Nat × Nat)}
    (hown : ∀ (x : _root_.Tw.K2.Front) (lay : TreeLay), firstFront s.st s.check.frame = .ok x →
      layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      own.contains (s.book.trees.size + lay.tree.getD (1 + x.T.kept.size + μ) 0,
        lay.part.getD (1 + x.T.kept.size + μ) 0) = true) :
    r3B own sh l m.check.frame m.book = true := by
  obtain ⟨x, hx, hlt, hO⟩ := own_at hp hd hμ0
  obtain ⟨hn, _⟩ := yes_link_next hp hd
  obtain ⟨_, el, _⟩ := yes_link_stays hp hd
  obtain ⟨x', lay, hF, hlay, hall⟩ := yes_new_seat hd
  have hx' : firstFront s.st s.check.frame = .ok x' := by
    rcases hF with ⟨_, e⟩ | ⟨c, _⟩ | ⟨c, _⟩
    · exact e
    · rw [hp] at c
      cases c
    · rw [hp] at c
      cases c
  obtain rfl : x = x' := Except.ok.inj (hx.symm.trans hx')
  obtain ⟨T, hpl, _⟩ := hall _ hlt
  have hw : m.check.frame.whereIs l μ = some (x.st.oracles.size + (1 + x.T.kept.size + μ)) := by
    unfold ReqFrame.whereIs
    rw [hn, el, hlk]
    simp [hO]
  unfold r3B
  rw [hμ]
  simp only [Option.bind_some, hw, hpl, hown x lay hx hlay, if_true, Option.isSome_some]

section
open VerifiableInference.Desc (Block Place OpenedColumn KindName)
open VerifiableInference.Desc.First (ModelPart Numbers Pub PubData pubAll)
open Johnson.Desc.First.Walk (startFork)
open Johnson.Desc.First.Walk.Seat (pubOf)
open ProofFile (Cl)
open IM (XK Yes linksW placesW subW Joined)

variable {Q : Type}

theorem made_k5_firstR {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {l : Nat} (h1 : 1 ≤ l) (h24 : l < 24)
    {b b' : Block S Cl} (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some l, piece := 1, kind := .K2 })
    (hJ : Joined Z l b b' { chain := 1, link := some l, piece := 1, kind := .K2 })
    (hsub : (ProofFile.subsOf Z)[l]? = some (subW l)) (hatt : subW l = .attention)
    (D : PubData) (base : Pub → Q × S → Bool) (z : Q) (ha : D.d5.isAtt l = true)
    {q : Attention.Plan} (hW : D.d5.W.A[l / 2]? = some q)
    (c1 : ∀ X p, Z.p.built.links[l]? = some X → X.kind = 1 → Z.p.X.A[X.g]? = some p →
      ((startFork (pubOf X) p.ns).trees[q.iU3]?).any (fun T => T.R == 1 && T.K == q.nW) = true)
    {N : Numbers} {E : Nat → S → Bool} {ft : Nat} {s s' : S} (hy : Yes ft b s s')
    (hu : s.failed = none) (hu' : s'.failed = none)
    (hx : XK N linksW placesW E (14 * l + 2) s = true)
    (hsh : s.check.frame.shape = D.d5.shape)
    (hgr : s.check.frame.groups = reqGroups s.check.frame.shape) (hlk : s.check.frame.link = l)
    {lay₀ : Params.ReqLayout} (hlay : s.check.rows.layout = lay₀)
    (c2 : ∀ X, Z.p.built.links[l]? = some X →
      r2B lay₀ D.d5.shape l (pubOf X).arrayOf q.iU3 q.nW = true)
    {μ : Nat}
    (hμ : (((D.d5.shape.link[l]?.map (·.messages)).getD []).findIdx? fun x =>
      x.shape.maskRows != 0) = some μ)
    (hμ0 : μ < (s.check.frame.atMoment 0).length)
    (hown : ∀ (x : _root_.Tw.K2.Front) (lay : TreeLay), firstFront s.st s.check.frame = .ok x →
      layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      (D.d5.ownOf l).contains (s.book.trees.size + lay.tree.getD (1 + x.T.kept.size + μ) 0,
        lay.part.getD (1 + x.T.kept.size + μ) 0) = true) :
    pubAll D base (.more (some l) "K5.liveReq") (z, s') = true ∧
      pubAll D base (.more (some l) "K5.readsThere") (z, s') = true :=
  made_k5_first h1 h24 hlot hpl hJ hsub hatt D base z ha hW c1 hy hu hu' hx hsh hgr hlk hlay c2
    fun _ _ _ _ _ hp hd => r3_left hp hd hlk hμ hμ0 hown

end

end P1K2

#print axioms P1K2.made_k5_firstR
#print axioms P1K2.own_at
#print axioms P1K2.r3_left
