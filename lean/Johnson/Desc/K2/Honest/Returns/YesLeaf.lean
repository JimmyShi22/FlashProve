-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/YesLeaf.lean: THE KIND's OWN DECISION SAYS YES AT ALL 25 PLACES OF
THE CODE SWITCH, AS Returns/YesTied.lean HAS IT, WITH THE NAMED PREMISE `AllTied` STRUCK: IN ITS
STEAD ONE FACT A TREE: `leafOk` OF EACH TREE THAT THE SWITCH OPENS. Three statements with their
proofs: one call of the bridge and one of Returns/YesTied.lean each; no definition.

  `link_yes_leaf`   in front of the switch into group m + 1, m < 23 (number 14 (m + 1) + 2)
  `head_yes_leaf`   in front of the output head's switch (number 339)
  `fin_yes_leaf`    behind the last segment (number 353), behind the quiet front's yes

THE PREMISES OF EACH: those of Returns/YesTied.lean's tops but `AllTied`: the head `P5J.AtMgA` and
the opening · the plan's numbers at the place · the state is reached, OVER THE LIST OF THE WRAPPED
SUB-PROTOCOLS (`below`, Johnson/Desc/Sound/ChainRule.lean: narrower than over the description's own
list) · the state's own look-ups · at 353 the quiet front's yes · hrf · hcols · hp · AND hleaf:
every tree of the book that stands among the opened trees passes `leafOk` at the front's statement.

By: `link_tied_reached`, `head_tied_reached`, `fin_tied_reached` (Returns/TiedReached.lean: the
first pen's: of `AllTied`'s seven things a tree six, at a reached state, under the head) · the three
tops of Returns/YesTied.lean.

Limits. hleaf HAS NO PAYER HERE. NEW BENEATH, AGAINST Returns/YesTied.lean: the twelve files
 of the bridge, with eight decisions by Lean's kernel under a raised limit of recursion (four
closed tests at the written values, each with a control): Returns/TiedReached.lean's Limits name
them. All other Limits of Returns/YesTied.lean stand: THE FULL SIZE AND THE FORMAT's EARLIER HASH
ALONE; "says yes" is: `decideWith` returns, of the kind's own decision; another house's files
 NO MEMBER. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Returns.YesTied
import Johnson.Desc.K2.Honest.Returns.TiedReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (roundsFit groupsOf Block Chain Place)
open VerifiableInference.Desc.First (S HeadOwn FinOwn)
open VerifiableInference.Desc.First.K2 (decideWith rounds flat headFrontOf finFrontOf finishFrontQ)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open P1K2 (Prep Nums numsAt prepOf)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open IM (k2P)
open _root_.Tw.K2 (Col sendByL8 leafOk)
open ProofFile (Cl)

variable {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {z : ProofFile.InstPub}
  {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **In front of the switch into a later group.** -/
theorem link_yes_leaf (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x₀)
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
    (hleaf : ∀ τ ∈ treesOf (readIn (k2P Zp a nm .link n) s r₁ r₂
        (laidGroups (k2P Zp a nm .link n) ft d₁ d₂ cols) L Q), ∀ tree,
      s.book.trees[τ]? = some tree → leafOk (frontAt s L Q).st tree = true) :
    ∃ s', decideWith sendByL8 (k2P Zp a nm .link n) s [r₁, r₂]
      (laidGroups (k2P Zp a nm .link n) ft d₁ d₂ cols) = .ok s' :=
  link_yes_tied h O h23 hP hn hr a nm r₁ r₂ ft d₁ d₂ cols hp hrf hcols hL hQ hc
    (link_tied_reached h.toAtMg O h23 hP hn hr a nm r₁ r₂ _ L Q hc _ hleaf)

/-- **In front of the output head's switch.** -/
theorem head_yes_leaf (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x₀)
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
    (hleaf : ∀ τ ∈ treesOf (callIn (k2P Zp a' nm .head n) (headFrontOf s a Q.target) s.book
        s.roots r₁ r₂
        (flat (k2P Zp a' nm .head n) (laidGroups (k2P Zp a' nm .head n) ft d₁ d₂ cols))),
      ∀ tree, s.book.trees[τ]? = some tree → leafOk (headFrontOf s a Q.target).st tree = true) :
    ∃ s', decideWith sendByL8 (k2P Zp a' nm .head n) s [r₁, r₂]
      (laidGroups (k2P Zp a' nm .head n) ft d₁ d₂ cols) = .ok s' :=
  head_yes_tied h O hP hn hr a' nm r₁ r₂ ft d₁ d₂ cols hp hrf hcols here group hc
    (head_tied_reached h.toAtMg O hP hn hr a' nm r₁ r₂ _ here group hc _ hleaf)

/-- **Behind the last segment.** t: the state behind the quiet front. -/
theorem fin_yes_leaf (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x₀)
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
    (hleaf : ∀ τ ∈ treesOf (callIn (k2P Zp a' nm .finish n) (finFrontOf t a Q) t.book t.roots
        r₁ r₂
        (flat (k2P Zp a' nm .finish n) (laidGroups (k2P Zp a' nm .finish n) ft d₁ d₂ cols))),
      ∀ tree, t.book.trees[τ]? = some tree → leafOk (finFrontOf t a Q).st tree = true) :
    ∃ s', decideWith sendByL8 (k2P Zp a' nm .finish n) t [r₁, r₂]
      (laidGroups (k2P Zp a' nm .finish n) ft d₁ d₂ cols) = .ok s' :=
  fin_yes_tied h O hP hn hr hq a' nm r₁ r₂ ft d₁ d₂ cols hp hrf hcols here laid hc
    (fin_tied_reached h.toAtMg O hP hn hr hq a' nm r₁ r₂ _ Q here hc _ hleaf)

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_yes_leaf
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_yes_leaf
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_yes_leaf
