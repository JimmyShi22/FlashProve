-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/MadeFirstSent.lean: code switching (K2): hMade AT THE 23 LINKS' FIRST PLACES, WHOLE:
the last two items ("frame.sentIs" · "ledger.treesAre") laid in by made_sent
(Johnson/Road/K4/Rec/MadeSent.lean): NO ITEM OF hMade IS LEFT WITHOUT A JOIN THERE. NO BLOCK
IMPORTS THIS FILE.
  not_head_of_subs   the built link l is no output head's: out of LinkPlan's hsub
                     (P1K2.kinds_of_subs)
  hMade_firstW       hMade, to the letter, at any further Bools E
  share_firstW       K2's share of e₁ at a link's first place: HandsR … (14 l + 2) b
THE PREMISES, SORTED BY WHAT THEY READ: CLOSED ON THE PLAN: LinkPlan · (attention) K5Plan · hdS
(the public data's SentData is the made datum sentDataAt shape N linksW placesW ‹the built links›)
· AT THE FENCED STATES: hF (MadeSent.lean's SentFence: the frame's groups are reqGroups of its
shape; its shape is «shape») · (attention) K5Front · ON THE NUMBERS: «D» · hgrp.
LIMITS. A GATHERING. e₁ IS NOT PAID: every premise named is still owed; none is shown at a value.
No soundness is claimed.
-/
import Johnson.P1K2R.MadeFirst
import Johnson.Road.K4.Rec.MadeSent

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place OpenedColumn KindName)
open VerifiableInference.Desc.First (S ModelPart Numbers Pub PubData pubAll)
open VerifiableInference.Desc.First.K2 (LinkDebts frameAt)
open VerifiableInference.Desc.First.FillSent (sentDataAt)
open OnBytes.Road.K4.Rec (SentFence made_sent)
open ProofFile (Cl)
open IM (HandsR XK Yes linksW placesW subW Joined)
open _root_.Tw.K2 (firstFront switchNotices)

theorem not_head_of_subs {Z : ProofFile.Pub} {l : Nat} (h24 : l < 24)
    (hsub : (ProofFile.subsOf Z)[l]? = some (subW l)) :
    ∀ X, Z.p.built.links[l]? = some X → X.kind ≠ 2 := by
  intro X hX
  obtain ⟨X₀, hX₀, hk₀, _⟩ := kinds_of_subs h24 hsub
  obtain rfl : X₀ = X := Option.some.inj (hX₀.symm.trans hX)
  exact hk₀

variable {Q : Type}

theorem hMade_firstW {Fk : Nat → S → Prop} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {l : Nat}
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
    {shape : Params.ReqShape} (hdS : D.dS = sentDataAt shape N linksW placesW Z.p.built.links)
    (hF : ∀ s, Fk (14 * l + 2) s → s.failed = none → SentFence shape s) :
    ∀ s s', Fk (14 * l + 2) s → Yes ft b s s' → s.failed = none → s'.failed = none →
      XK N linksW placesW E (14 * l + 2) s = true →
      ∀ e ∈ madeAt l 2 (decide (subW l = .attention)), pubAll D base e (z, s') = true :=
  hMade_first h1 h24 hlot hpl hJ D base z Pl P5 F5 Dd
    (made_sent h1 h24 hlot hpl hJ D base z (not_head_of_subs h24 Pl.hsub) hdS hF)

theorem share_firstW {Fk : Nat → S → Prop} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {l : Nat}
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
    {shape : Params.ReqShape} (hdS : D₀.dS = sentDataAt shape N linksW placesW Z.p.built.links)
    (hF : ∀ s, Fk (14 * l + 2) s → s.failed = none → SentFence shape s) :
    HandsR Fk N linksW placesW (EP D₀ base z) ft (14 * l + 2) b :=
  share_firstM h1 h24 hlot hpl hJ D₀ base z Pl P5 F5 hgrp Dd
    (made_sent h1 h24 hlot hpl hJ D₀ base z (not_head_of_subs h24 Pl.hsub) hdS hF)

end P1K2

#print axioms P1K2.hMade_firstW
#print axioms P1K2.share_firstW
