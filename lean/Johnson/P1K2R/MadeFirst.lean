-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/MadeFirst.lean: code switching (K2): hMade, THE PREMISE ON THE MAKINGS OF ITS SHARE
OF e₁ AT A LINK's FIRST PLACE (share_firstP | share_firstQ, Johnson/P1K2R/SharesAtE.lean |
SharesScope.lean), GATHERED: all six | eight public items that the place makes, out of the joins
that lie, under premises that are sorted by what they read. NO BLOCK IMPORTS THIS FILE.
  LinkPlan Z l D          CLOSED ON THE PLAN, at every link: the driver's list has the written
                          sort · the plan's number of slots is the frame's ·
                          madeLookB accepts at the frame's letters, and the plan's state of the
                          smallness test has nothing heard
  K5Plan Z l D N lay₀ q μ  CLOSED ON THE PLAN, at an attention link: the six of
                           Johnson/P1K2R/MadeK5Debts.lean
  K5Front D l lay₀ μ s    AT THE STATE IN FRONT, at an attention link: the frame's shape, groups
                          and link · the layout held · μ stands among the messages of moment 0
  nums_of_yes             where the place's sub-protocol accepts, the lot has made the place's
                          numbers
  hMade_first             hMade, to the letter, at any further Bools E
  share_firstM            share_firstQ with hMade paid so
WHAT STAYS, BY NAME: LinkPlan · (at an attention link) K5Plan and, at the fenced states at which
the promise's tests in front hold, K5Front · «D» (asked by the share anyway) · hSent: THE TWO
ITEMS "frame.sentIs" AND "ledger.treesAre" (other files' to show: done by report
for these links: NOT JOINED HERE: a named premise) · the share's hgrp.
LIMITS. A GATHERING. No premise is shown at a value. No soundness is claimed.

-/
import Johnson.P1K2R.MadeK5Debts

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place OpenedColumn KindName)
open VerifiableInference.Desc.First (S ModelPart Numbers Pub PubData pubAll)
open VerifiableInference.Desc.First.K2 (LinkDebts frameAt madeLookB)
open Johnson.Desc.First.Walk (startFork)
open Johnson.Desc.First.Walk.Seat (pubOf)
open ProofFile (Cl)
open IM (HandsR XK Yes linksW placesW subW Joined)
open _root_.Tw.K2 (firstFront switchNotices)

/-- Closed on the plan, at every link. -/
structure LinkPlan (Z : ProofFile.Pub) (l : Nat) (D : PubData) : Prop where
  hsub : (ProofFile.subsOf Z)[l]? = some (subW l)
  hnsA : ∀ X p, Z.p.built.links[l]? = some X → X.kind = 1 → Z.p.X.A[X.g]? = some p →
    D.nsOf l = some p.ns
  hnsL : ∀ X hp, Z.p.built.links[l]? = some X → X.kind = 0 → Z.p.X.G[X.g]? = some hp →
    D.nsOf l = some hp.ns
  hBA : ∀ X p, Z.p.built.links[l]? = some X → X.kind = 1 → Z.p.X.A[X.g]? = some p →
    madeLookB D.d3 l 2 (pubOf X).arrayOf (pubOf X).Fp.next p.ns = true ∧ p.seam.tl.heard = none
  hBL : ∀ X hp, Z.p.built.links[l]? = some X → X.kind = 0 → Z.p.X.G[X.g]? = some hp →
    madeLookB D.d3 l 2 (pubOf X).arrayOf (pubOf X).Fp.next hp.ns = true ∧ hp.tl.heard = none

/-- Closed on the plan, at an attention link. -/
structure K5Plan (Z : ProofFile.Pub) (l : Nat) (D : PubData) (N : Numbers) (lay₀ : Params.ReqLayout)
    (q : Attention.Plan) (μ : Nat) : Prop where
  ha : D.d5.isAtt l = true
  hW : D.d5.W.A[l / 2]? = some q
  c1 : ∀ X p, Z.p.built.links[l]? = some X → X.kind = 1 → Z.p.X.A[X.g]? = some p →
    ((startFork (pubOf X) p.ns).trees[q.iU3]?).any (fun T => T.R == 1 && T.K == q.nW) = true
  c2 : ∀ X, Z.p.built.links[l]? = some X →
    r2B lay₀ D.d5.shape l (pubOf X).arrayOf q.iU3 q.nW = true
  hμ : (((D.d5.shape.link[l]?.map (·.messages)).getD []).findIdx? fun x =>
    x.shape.maskRows != 0) = some μ
  hOwn : D.d5.ownOf l = N.sent l 0

/-- At the state in front, at an attention link. -/
structure K5Front (D : PubData) (l : Nat) (lay₀ : Params.ReqLayout) (μ : Nat) (s : S) : Prop where
  hsh : s.check.frame.shape = D.d5.shape
  hgr : s.check.frame.groups = reqGroups s.check.frame.shape
  hlk : s.check.frame.link = l
  hlay : s.check.rows.layout = lay₀
  hμ0 : μ < (s.check.frame.atMoment 0).length

theorem nums_of_yes {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {l : Nat} {b b' : Block S Cl}
    (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some l, piece := 1, kind := .K2 })
    (hJ : Joined Z l b b' { chain := 1, link := some l, piece := 1, kind := .K2 }) {ft : Nat}
    {s s' : S} (hy : Yes ft b s s') :
    ∃ P n, prepOf Z G₀ = some P ∧ numsAt P (some l) = some n := by
  obtain ⟨L, hL, hb'⟩ := hlot
  obtain ⟨x, hx', rfl⟩ := IM.lot_K2 hL hb' (by rw [hpl])
  have hi := IM.k2_mem hx'
  rw [show x.place = _ from hpl] at hi
  rcases hi with ⟨_, hm⟩ | ⟨P, n, hP, hn, _⟩
  · obtain ⟨rs, cols, k, e⟩ := hy
    obtain ⟨fs, f, m, _, _, e3, _⟩ := hJ.step e
    exact absurd ⟨rs, cols, k, e3⟩ (never_of_mute hm s m)
  · exact ⟨P, n, hP, hn⟩

variable {Q : Type}

theorem hMade_first {Fk : Nat → S → Prop} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {l : Nat}
    (h1 : 1 ≤ l) (h24 : l < 24) {b b' : Block S Cl}
    (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some l, piece := 1, kind := .K2 })
    (hJ : Joined Z l b b' { chain := 1, link := some l, piece := 1, kind := .K2 })
    (D : PubData) (base : Pub → Q × S → Bool) (z : Q) (Pl : LinkPlan Z l D)
    {N : Numbers} {E : Nat → S → Bool} {ft : Nat} {lay₀ : Params.ReqLayout}
    {q : Attention.Plan} {μ : Nat}
    (P5 : subW l = .attention → K5Plan Z l D N lay₀ q μ)
    (F5 : subW l = .attention → ∀ s, Fk (14 * l + 2) s →
      XK N linksW placesW E (14 * l + 2) s = true → K5Front D l lay₀ μ s)
    (Dd : ∀ P n (s : S) x W lay, prepOf Z G₀ = some P → numsAt P (some l) = some n →
      Fk (14 * l + 2) s → XK N linksW placesW E (14 * l + 2) s = true →
      firstFront s.st s.check.frame = .ok x → frameAt x = some W →
      layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      LinkDebts N l placesW[14 * l + 2]? placesW[14 * l + 3]? s n.positions x W lay)
    (hSent : ∀ s s', Fk (14 * l + 2) s → Yes ft b s s' → s.failed = none → s'.failed = none →
      XK N linksW placesW E (14 * l + 2) s = true →
      pubAll D base (.more (some l) "frame.sentIs") (z, s') = true ∧
        pubAll D base (.more (some l) "ledger.treesAre") (z, s') = true) :
    ∀ s s', Fk (14 * l + 2) s → Yes ft b s s' → s.failed = none → s'.failed = none →
      XK N linksW placesW E (14 * l + 2) s = true →
      ∀ e ∈ madeAt l 2 (decide (subW l = .attention)), pubAll D base e (z, s') = true := by
  intro s s' hf hy hu hu' hx e he
  obtain ⟨g1, g2⟩ := made_ledger_first h24 hJ Pl.hsub D base z Pl.hnsA Pl.hnsL hy
  obtain ⟨g3, g4⟩ := made_look_first h1 h24 hlot hpl hJ Pl.hsub D base z Pl.hBA Pl.hBL hy hu hu' hx
  obtain ⟨g5, g6⟩ := hSent s s' hf hy hu hu' hx
  unfold madeAt at he
  rcases List.mem_append.1 he with h6 | h2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h6
    rcases h6 with rfl | rfl | rfl | rfl | rfl | rfl
    · exact g1
    · exact g4
    · exact g3
    · exact g2
    · exact g5
    · exact g6
  · by_cases hatt : subW l = .attention
    · rw [decide_eq_true hatt, if_pos rfl] at h2
      obtain ⟨P, n, hP, hn⟩ := nums_of_yes hlot hpl hJ hy
      have A := P5 hatt
      have B := F5 hatt s hf hx
      obtain ⟨k1, k2⟩ := made_k5_firstD h1 h24 hlot hpl hJ Pl.hsub hatt D base z A.ha A.hW A.c1 hy
        hu hu' hx B.hsh B.hgr B.hlk B.hlay A.c2 A.hμ B.hμ0 A.hOwn
        (fun x W lay a b c => Dd P n s x W lay hP hn hf hx a b c)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
      rcases h2 with rfl | rfl
      · exact k2
      · exact k1
    · rw [decide_eq_false hatt] at h2
      simp at h2

theorem share_firstM {Fk : Nat → S → Prop} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {l : Nat}
    (h1 : 1 ≤ l) (h24 : l < 24) {b b' : Block S Cl}
    (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some l, piece := 1, kind := .K2 })
    (hJ : Joined Z l b b' { chain := 1, link := some l, piece := 1, kind := .K2 })
    {N : Numbers} {ft : Nat} (D₀ : PubData) (base : Pub → Q × S → Bool) (z : Q)
    (Pl : LinkPlan Z l D₀) {lay₀ : Params.ReqLayout} {q : Attention.Plan} {μ : Nat}
    (P5 : subW l = .attention → K5Plan Z l D₀ N lay₀ q μ)
    (F5 : subW l = .attention → ∀ s, Fk (14 * l + 2) s →
      XK N linksW placesW (EP D₀ base z) (14 * l + 2) s = true → K5Front D₀ l lay₀ μ s)
    (hgrp : ∀ P n, prepOf Z G₀ = some P → numsAt P (some l) = some n → N.groupAt l = n.grp)
    (Dd : ∀ P n (s : S) x W lay, prepOf Z G₀ = some P → numsAt P (some l) = some n →
      Fk (14 * l + 2) s → XK N linksW placesW (EP D₀ base z) (14 * l + 2) s = true →
      firstFront s.st s.check.frame = .ok x → frameAt x = some W →
      layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      LinkDebts N l placesW[14 * l + 2]? placesW[14 * l + 3]? s n.positions x W lay)
    (hSent : ∀ s s', Fk (14 * l + 2) s → Yes ft b s s' → s.failed = none → s'.failed = none →
      XK N linksW placesW (EP D₀ base z) (14 * l + 2) s = true →
      pubAll D₀ base (.more (some l) "frame.sentIs") (z, s') = true ∧
        pubAll D₀ base (.more (some l) "ledger.treesAre") (z, s') = true) :
    HandsR Fk N linksW placesW (EP D₀ base z) ft (14 * l + 2) b :=
  share_firstQ h1 h24 hlot hpl hJ Pl.hsub D₀ base z hgrp Dd
    (hMade_first h1 h24 hlot hpl hJ D₀ base z Pl P5 F5 Dd hSent)

end P1K2

#print axioms P1K2.nums_of_yes
#print axioms P1K2.hMade_first
#print axioms P1K2.share_firstM
