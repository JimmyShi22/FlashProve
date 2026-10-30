-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/YesTied.lean: THE KIND's OWN DECISION SAYS YES AT ALL 25 PLACES OF
THE CODE SWITCH, AT A STATE THAT IS REACHED IN FRONT OF THE SWITCH, UNDER THE HEAD, AT TWO ROUNDS
AND COLUMNS THAT PASS THE TWO TESTS WHICH `Block.step` RUNS IN FRONT OF EVERY DECISION, AT THE
GROUPS AS IT LAYS THEM: UNDER THE ONE NAMED PREMISE `AllTied` (Returns/ColsFit.lean) BESIDE THESE.
Three statements with their proofs: joins of laws of other files; no definition.

  `link_yes_tied`   in front of the switch into group m + 1, m < 23 (number 14 (m + 1) + 2)
  `head_yes_tied`   in front of the output head's switch (number 339)
  `fin_yes_tied`    behind the last segment (number 353), behind the quiet front's yes

THE PREMISES OF EACH. The head `P5J.AtMgA` and the opening O · the plan's numbers n at the place
(`prepOf`, `numsAt` return) · the state is reached, OVER THE LIST OF THE WRAPPED SUB-PROTOCOLS
(`below`, Johnson/Desc/Sound/ChainRule.lean, which refuse a word that is not below the prime:
narrower than over the description's own list) · the state's own look-ups (the segment and its
group, or where the state stands; the old main code c₀) · at 353 the quiet front's yes · hrf: the
two rounds pass `roundsFit` · hcols: the columns are, in key, position and width, those that the
rounds read · hp: the decision is shown the second round's positions as `Block.step` reads them ·
AND `AllTied`: the plan's list n.read against the book's opened trees, tree for tree: four facts on
each tree that are the verifier's state's alone, and three equations.

By: `call_seven` (Returns/RoundsJoin.lean) · `link_returns_seven`
(Returns/LinkProver.lean), `head_returns_seven`, `fin_returns_seven` (Returns/ArmsProver.lean),
`head_oldCode_reached`, `fin_oldCode_reached` (Returns/ArmsPlan.lean) · another house's
`link_ties_reached` (Johnson/AtFull/Shape/LinkPlanNums.lean), `head_nums_reached`,
`fin_nums_reached` (Johnson/AtFull/Shape/ArmsLeftNums.lean): the three ties of the plan's numbers,
THE FIRST BY NO GENERAL ROAD: by closed tests at the written rows of the full size. THAT HOUSE's OWN
GRADE OF THESE TWO FILES, BY ITS PAPERS, IN THE FORM THAT IT HAS HANDED IN FOR SEALING: ridden of
record over a bare copy of the sealed library · read whole, proofs too, by one reader of that house
who is not their pen, in the form before, and by difference since: comments alone part · `decide
+kernel` stands as code on two and on six lines of them, six of the eight under a raised limit of
recursion · both strike the instance `Inst.Model.Scl.ref`. What lies beneath them, and beneath the
first pen's two joins, is told in these joins' heads.

Limits. `AllTied` IS A PREMISE HERE: at a reached state it is had from `leafOk` of each opened tree
(Returns/TiedReached.lean); Returns/YesLeaf.lean has the three tops so. THE FULL SIZE ALONE: the
head and the ties are of the written plan. AT THE FORMAT's EARLIER HASH ALONE. THE HEAD IS
`P5J.AtMgA`, WHICH ASKS MORE THAN THE `P5J.AtMg` OF THIS FOLDER's OTHER TOPS. "SAYS YES" IS:
`decideWith` RETURNS a state: of the kind's own decision, not of the sub-protocol that a description
seats at the place with what is joined around it, nor of a verifier's program. hrf and hcols are
premises: of a half that has played and whose columns are laid they are the frame's law
(`fits_played`, Johnson/Desc/ProofFile/Honest/Law/Cut.lean), not called here. NO MEMBER: the
premises are shown met together nowhere. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Returns.LinkProver
import Johnson.Desc.K2.Honest.Returns.ArmsProver
import Johnson.Desc.K2.Honest.Returns.RoundsJoin
import Johnson.AtFull.Shape.LinkPlanNums

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (roundsFit groupsOf Block Chain Place)
open VerifiableInference.Desc.First (S HeadOwn FinOwn)
open VerifiableInference.Desc.First.K2 (decideWith rounds flat headFrontOf finFrontOf finishFrontQ)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open Johnson.AtFull.Shape (link_ties_reached head_nums_reached fin_nums_reached)
open P1K2 (Prep Nums numsAt prepOf)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open IM (k2P)
open _root_.Tw.K2 (Col sendByL8)
open ProofFile (Cl)

variable {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {z : ProofFile.InstPub}
  {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **In front of the switch into a later group.** -/
theorem link_yes_tied (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums}
    (hP : prepOf Zp Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * (m + 1) + 2) (z, s))
    (a : Place) (nm : String) (r₁ r₂ : Fmt.RoundView) (ft : Nat) (d₁ d₂ : Fmt.Drawn) (cols : List OpenedColumn)
    (hp : d₂.poss = r₂.drawn.poss)
    (hrf : roundsFit (rounds (k2P Zp a nm .link n)) [r₁, r₂] = true)
    (hcols : cols.map (fun y => (y.1, y.2.1, y.2.2.length)) =
      (groupsOf ft (rounds (k2P Zp a nm .link n)) [d₁, d₂]).flatMap id)
    {L : Params.ReqLink} {Q : ReqGroup} {c₀ : Code}
    (hL : s.check.frame.shape.link[s.check.frame.link]? = some L)
    (hQ : s.check.frame.groups[s.check.frame.link]? = some Q)
    (hc : s.st.codes.base[s.check.frame.shape.code]? = some c₀)
    (hT : AllTied (frontAt s L Q).st (k2P Zp a nm .link n).firstTree
      (Positions.ofDraws c₀.logN r₂.drawn.poss) s.book
      (treesOf (readIn (k2P Zp a nm .link n) s r₁ r₂
        (laidGroups (k2P Zp a nm .link n) ft d₁ d₂ cols) L Q)) n.read) :
    ∃ s', decideWith sendByL8 (k2P Zp a nm .link n) s [r₁, r₂]
      (laidGroups (k2P Zp a nm .link n) ft d₁ d₂ cols) = .ok s' := by
  obtain ⟨t1, t2, t3⟩ := link_ties_reached h O h23 hP hn hr a nm hL hQ hc
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := call_seven (k2P Zp a nm .link n) (frontAt s L Q) s.book
    s.roots r₁ r₂ c₀ ft d₁ d₂ cols hp hrf hcols t1 t2 t3 hT
  exact link_returns_seven h O h23 hP hn hr a nm r₁ r₂ _ hrf hL hQ hc ⟨e1, e2, e3, e4, e5, e6, e7⟩

/-- **In front of the output head's switch.** -/
theorem head_yes_tied (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn : numsAt Pp (some 24) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 339 (z, s))
    (a' : Place) (nm : String) (r₁ r₂ : Fmt.RoundView) (ft : Nat) (d₁ d₂ : Fmt.Drawn) (cols : List OpenedColumn)
    (hp : d₂.poss = r₂.drawn.poss)
    (hrf : roundsFit (rounds (k2P Zp a' nm .head n)) [r₁, r₂] = true)
    (hcols : cols.map (fun y => (y.1, y.2.1, y.2.2.length)) =
      (groupsOf ft (rounds (k2P Zp a' nm .head n)) [d₁, d₂]).flatMap id)
    {a : HeadOwn} {Q : ReqGroup} (here : s.here = .head a)
    (group : s.check.frame.groups[s.check.frame.link]? = some Q)
    {c₀ : Code} (hc : s.st.codes.base[s.check.frame.shape.code]? = some c₀)
    (hT : AllTied (headFrontOf s a Q.target).st (k2P Zp a' nm .head n).firstTree
      (Positions.ofDraws c₀.logN r₂.drawn.poss) s.book
      (treesOf (callIn (k2P Zp a' nm .head n) (headFrontOf s a Q.target) s.book s.roots r₁ r₂
        (flat (k2P Zp a' nm .head n) (laidGroups (k2P Zp a' nm .head n) ft d₁ d₂ cols))))
      n.read) :
    ∃ s', decideWith sendByL8 (k2P Zp a' nm .head n) s [r₁, r₂]
      (laidGroups (k2P Zp a' nm .head n) ft d₁ d₂ cols) = .ok s' := by
  obtain ⟨-, t1, t2, t3⟩ := head_nums_reached h O hP hn hr a' nm here group
  have ho := head_oldCode_reached h.scope h.reads O h.laid.value h.laid.planOk hP hn hr here
    Q.target hc
  rw [Array.getD_eq_getD_getElem?, ho] at t2
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := call_seven (k2P Zp a' nm .head n)
    (headFrontOf s a Q.target) s.book s.roots r₁ r₂ c₀ ft d₁ d₂ cols hp hrf hcols t1 t2 t3 hT
  exact head_returns_seven h O hP hn hr a' nm r₁ r₂ _ hrf here group hc
    ⟨⟨e1, e2, e3, e4, e5⟩, e6, e7⟩

/-- **Behind the last segment.** t: the state behind the quiet front. -/
theorem fin_yes_tied (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn : numsAt Pp none = some n) {s t : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 353 (z, s))
    (hq : finishFrontQ s = .ok t) (a' : Place) (nm : String) (r₁ r₂ : Fmt.RoundView) (ft : Nat)
    (d₁ d₂ : Fmt.Drawn) (cols : List OpenedColumn) (hp : d₂.poss = r₂.drawn.poss)
    (hrf : roundsFit (rounds (k2P Zp a' nm .finish n)) [r₁, r₂] = true)
    (hcols : cols.map (fun y => (y.1, y.2.1, y.2.2.length)) =
      (groupsOf ft (rounds (k2P Zp a' nm .finish n)) [d₁, d₂]).flatMap id)
    {a : FinOwn} {Q : ReqGroup} (here : t.here = .fin a) (laid : a.G = some Q)
    {c₀ : Code} (hc : t.st.codes.base[t.check.frame.shape.code]? = some c₀)
    (hT : AllTied (finFrontOf t a Q).st (k2P Zp a' nm .finish n).firstTree
      (Positions.ofDraws c₀.logN r₂.drawn.poss) t.book
      (treesOf (callIn (k2P Zp a' nm .finish n) (finFrontOf t a Q) t.book t.roots r₁ r₂
        (flat (k2P Zp a' nm .finish n) (laidGroups (k2P Zp a' nm .finish n) ft d₁ d₂ cols))))
      n.read) :
    ∃ s', decideWith sendByL8 (k2P Zp a' nm .finish n) t [r₁, r₂]
      (laidGroups (k2P Zp a' nm .finish n) ft d₁ d₂ cols) = .ok s' := by
  obtain ⟨-, t1, t2, t3⟩ := fin_nums_reached h O hP hn hr hq a' nm here laid
  have h25 := h25_of_hy h.scope O (tests_at_head h.toAtMg O).1
  have ho := fin_oldCode_reached h.scope h.reads O h.laid.value h.laid.planOk h25 hP hn hr hq here
    Q hc
  rw [Array.getD_eq_getD_getElem?, ho] at t2
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := call_seven (k2P Zp a' nm .finish n) (finFrontOf t a Q)
    t.book t.roots r₁ r₂ c₀ ft d₁ d₂ cols hp hrf hcols t1 t2 t3 hT
  exact fin_returns_seven h O hP hn hr hq a' nm r₁ r₂ _ hrf here laid hc
    ⟨⟨e1, e2, e3, e4, e5⟩, e6, e7⟩

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_yes_tied
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_yes_tied
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_yes_tied
