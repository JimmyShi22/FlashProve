-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/YesReached.lean: THE KIND's OWN DECISION SAYS YES AT ALL 25 PLACES OF
THE CODE SWITCH, AT A STATE THAT IS REACHED IN FRONT OF THE SWITCH, UNDER THE HEAD, AT TWO ROUNDS
AND COLUMNS THAT PASS THE TWO TESTS WHICH `Block.step` RUNS IN FRONT OF EVERY DECISION: WITH NO
PREMISE ON THE BOOK's TREES ANY MORE: Returns/YesLeaf.lean's tops with `leafOk` struck. Three
statements with their proofs: one call of another house's law and one of Returns/YesLeaf.lean each;
no definition.

  `link_yes_reached`   in front of the switch into group m + 1, m < 23 (number 14 (m + 1) + 2)
  `head_yes_reached`   in front of the output head's switch (number 339)
  `fin_yes_reached`    behind the last segment (number 353), behind the quiet front's yes

THE PREMISES OF EACH, ALL OF THEM: the head `P5J.AtMgA` and the opening · the plan's numbers at the
place (`prepOf`, `numsAt` return) · the state is reached, OVER THE LIST OF THE WRAPPED SUB-PROTOCOLS
(`below`, Johnson/Desc/Sound/ChainRule.lean: narrower than over the description's own list) · AT THE
TWO ARMS the state's own look-ups (where it stands; the group that is looked up or laid; the old
main code): at the links these return at a reached state (`link_fields_reached`,
Returns/LinkReached.lean) and are no premises · at 353 the quiet front's yes · hrf, hcols: the two
rounds and the columns pass the two tests · hp: the decision is shown the second round's positions
as `Block.step` reads them.

By: `link_leafOk_all`, `head_leafOk`, `fin_leafOk` (Johnson/AtFull/Shape/LeafOkLinks.lean,
LeafOkArms.lean: `leafOk` of each tree that the switch opens, at a reached state,
in the goals' scope, at an opening: no head is asked there) · the three tops of
Returns/YesLeaf.lean.

WHAT THE THREE DO NOT SAY, NOW THAT NO PREMISE ON THE TREES IS LEFT. (1) THAT ANY STATE IS REACHED
THERE: "reached" asks a run of the wrapped sub-protocols in front of the place, each with its own
yes; none is exhibited here; where none is, the three say nothing. (2) THAT THE HEAD HAS A MEMBER
TOGETHER WITH SUCH A STATE: the library has a head at the name under four premises on the public
files (`P5J.head_exists_at_name`, Johnson/P5J/HeadExistsAtName.lean): not called; it gives no
reached state. (3) ANYTHING ON WHAT THE PROVER SENDS: THE YES HOLDS AT ALL TWO ROUNDS AND COLUMNS OF
THE RIGHT SHAPE: of the rounds and the columns the three ask hrf, hcols and hp and nothing else: at
this step the kind lays claims on and tests nothing of them: SO THE YES IS NO SIGN THAT A MESSAGE IS
HONEST. (4) "SAYS YES" IS: `decideWith` RETURNS A STATE, OF THE KIND's OWN DECISION: NOTHING IS SAID
OF THE SUB-PROTOCOL THAT A DESCRIPTION SEATS AT THE PLACE, with what is joined in front of and
behind the kind's own decision, or of a verifier's program. (5) THAT `leafOk` BITES: as those files
say, where a tree had no sampled part it would accept for nothing, and that the layout
has a sampled member at the written sizes rests on an evaluation in those files alone.

Limits. THE FULL SIZE AND THE FORMAT's EARLIER HASH ALONE. ALL OTHER LIMITS OF Returns/YesLeaf.lean
AND Returns/YesTied.lean STAND, BUT THOSE ON `leafOk` AND `AllTied`, WHICH ARE NO PREMISES HERE
(among those that stand: the head asks more than `P5J.AtMg`; the first tie of the plan's numbers is
had by no general road: closed tests at the written rows). What lies beneath: the twelve files of
the bridge, with eight decisions by Lean's kernel under a raised limit of recursion; six files on
raised limit of recursion, among it); the other house's six files on `leafOk` by its own paper:
built there in a working lane, no ride of record; read whole, proofs too, by one reader of that
house who is not their pen: five of them at other bytes, without some controls, docstrings and
asks, which were read by difference; one at these bytes; by no other house. Nothing on any property.
-/
import Johnson.Desc.K2.Honest.Returns.YesLeaf
import Johnson.AtFull.Shape.LeafOkLinks
import Johnson.AtFull.Shape.LeafOkArms

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
open _root_.Tw.K2 (Col sendByL8)
open Johnson.AtFull.Shape (link_leafOk_all head_leafOk fin_leafOk)
open ProofFile (Cl)

variable {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {z : ProofFile.InstPub}
  {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **In front of the switch into a later group.** -/
theorem link_yes_reached (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums}
    (hP : prepOf Zp Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (14 * (m + 1) + 2) (z, s))
    (a : Place) (nm : String) (r₁ r₂ : Fmt.RoundView) (ft : Nat) (d₁ d₂ : Fmt.Drawn) (cols : List OpenedColumn)
    (hp : d₂.poss = r₂.drawn.poss)
    (hrf : roundsFit (rounds (k2P Zp a nm .link n)) [r₁, r₂] = true)
    (hcols : cols.map (fun y => (y.1, y.2.1, y.2.2.length)) =
      (groupsOf ft (rounds (k2P Zp a nm .link n)) [d₁, d₂]).flatMap id) :
    ∃ s', decideWith sendByL8 (k2P Zp a nm .link n) s [r₁, r₂]
      (laidGroups (k2P Zp a nm .link n) ft d₁ d₂ cols) = .ok s' := by
  obtain ⟨L, Q, c₀, -, -, -, -, hL, hQ, hc, -⟩ := link_fields_reached h.scope h.reads O
    h.laid.value h.laid.planOk h23 hP hn hr a nm
  exact link_yes_leaf h O h23 hP hn hr a nm r₁ r₂ ft d₁ d₂ cols hp hrf hcols hL hQ hc
    (link_leafOk_all h.scope h.reads O h23 hr L Q _ _ _ _)

/-- **In front of the output head's switch.** -/
theorem head_yes_reached (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x₀)
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
    {c₀ : Code} (hc : s.st.codes.base[s.check.frame.shape.code]? = some c₀) :
    ∃ s', decideWith sendByL8 (k2P Zp a' nm .head n) s [r₁, r₂]
      (laidGroups (k2P Zp a' nm .head n) ft d₁ d₂ cols) = .ok s' :=
  head_yes_leaf h O hP hn hr a' nm r₁ r₂ ft d₁ d₂ cols hp hrf hcols here group hc
    (head_leafOk h.scope h.reads O hr here group _ _ _ _ _)

/-- **Behind the last segment.** t: the state behind the quiet front. -/
theorem fin_yes_reached (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x₀)
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
    {c₀ : Code} (hc : t.st.codes.base[t.check.frame.shape.code]? = some c₀) :
    ∃ s', decideWith sendByL8 (k2P Zp a' nm .finish n) t [r₁, r₂]
      (laidGroups (k2P Zp a' nm .finish n) ft d₁ d₂ cols) = .ok s' :=
  fin_yes_leaf h O hP hn hr hq a' nm r₁ r₂ ft d₁ d₂ cols hp hrf hcols here laid hc
    (fin_leafOk h.scope h.reads O hr hq here Q _ _ _ _)

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_yes_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_yes_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_yes_reached
