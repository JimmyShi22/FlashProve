-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/DrawReached.lean: WHAT THE LAWS "THE KIND's OWN DECISION SAYS YES"
ASK OF THE VERIFIER's OWN DRAWS, AT A STATE THAT IS REACHED IN FRONT OF THE SWITCH, IN THE GOALS'
SCOPE, AT THE PLAN's OWN NUMBERS: FROM THE TEST ON ROUNDS THAT `Block.step` RUNS FIRST AND THE FIRST
ENTRY's TEST ON THE PLAN. Statements with their proofs: calls, and one inversion in the library's
own pattern.

WHY. `call_draws_made` (Returns/DrawMade.lean) asks the two equations of the makers' rule at what
the switch announces at the front and at the front's codes. THE LIBRARY PAYS BOTH TIES AT REACHED
STATES: `sw_link`, `sw_head`, `sw_finish` (Johnson/P1K2R/HstReached.lean): the statement's codes are
the numbers' codes; what the switch announces is the numbers' list.

  `numsAt_draws` what the maker `numsAt` (Johnson/Desc/ProofFile/Lot/K2OfPlan.lean) lays into the
                    two counts of draws: the rule's two equations, at its own list and codes
  `draws_of_nums` no state: a place's numbers with these two counts, a front that announces the
                    numbers' list at the numbers' codes, the entry's test, rounds that fit: the five
                    ends of `call_draws_made`
  `link_draws_reached` in front of the switch into group m + 1, m < 23 (number 14 (m + 1) + 2): at a
                    front that the text's own front returns
  `link_draws_plain` the same at the front that `LinkPlain` names (`frontAt s L Q`), with that
                    structure's seven fields on the front in the place of "the text's front
                    returns": THE FORM IN WHICH FIVE OF ITS 32 FIELDS FALL
  `head_draws_reached` in front of the output head's switch (number 339)
  `finish_draws_reached` at the finish (number 353): the state is reached; the decision runs behind
                    the quiet front

By: `call_draws_made` · the library's `sw_link`, `sw_head`, `sw_finish` · `firstFront_st`
(Johnson/Top/H0/Tw/K2C/FrontGroup.lean) · `finishFrontQ_st` (K2C/FinFront.lean) · `frontOf_iff`
(K2C/DebtsState.lean) · `firstFront_returns` (Returns/Front.lean). `numsAt_draws` follows
`numsAt_codes` (Johnson/P1K2R/HstInScope.lean), `numsAt_logN` (Johnson/IMR/K10Pos.lean) and
`numsAt_grp` (K2C/GroupAtNums.lean) line by line.

Limits. "REACHED" IS: OVER THE LIST OF THE WRAPPED SUB-PROTOCOLS, from the description's own start.
THE ENTRY's TEST STAYS A PREMISE: closed on the plan, paid by nobody here (asked at the plan's own
list of announced messages: Returns/LinkReached.lean); the block's own test on the plan does not
hold it; at these numbers and this list its one clause that is not by unfolding says: the number of
samples is the greatest count of answers among the announced messages. AT A SEGMENT's FIRST PLACE
"THE TEXT's FRONT RETURNS x" IS A PREMISE: when it does: `firstFront_returns` (Returns/Front.lean):
six of its seven premises are paid at a reached state in Returns/LinkReached.lean; one (the frame's
next call is a first one) has no payer there that is known here. AT THE HEAD AND AT THE FINISH "THE
TEXT MAKES THE FRONT x" (`frontAt ... = some x`) IS A PREMISE TOO: a look-up, no call: it reads
where the state stands and one entry (the frame's group; what the finish has laid); that it returns
at a reached state is not shown here (for the head the library has `unheard_reached`,
Johnson/Top/H0/Tw/K2C/HeadUnheardReached.lean, and `frame_at_head`,
Johnson/P1K2R/FencesReached.lean: not called). At the finish the quiet front's yes is a premise. THE
FIVE PREMISES IN FRONT (in scope · the files read · the opening · the description returns · its test
on the plan) ARE SHOWN MET TOGETHER BY NOBODY HERE: NO MEMBER. THIS FILE's IMPORTS ARE HEAVY:
Johnson/P1K2R/HstReached.lean brings the folders P1K2R and IMR beneath it; the other files of this
folder are light. Nothing on any property.


-/
import Johnson.Desc.K2.Honest.Returns.DrawMade
import Johnson.P1K2R.HstReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open OnBytes.Params (cubeBitsOf)
open VerifiableInference.Desc (roundsFit Block Chain FileDescription Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 rounds par9 finishFrontQ frontOf_iff firstFront_st
  finishFrontQ_st)
open VerifiableInference.Desc.First.K2Caller (sampledOf)
open VerifiableInference.Desc.First.Send (planOk1)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open P1K2 (Prep Nums numsAt prepOf sw_link sw_head sw_finish)
open IM (k2P)
open _root_.Tw.K2 (Front switchNotices firstFront)
open ProofFile (Cl)

theorem numsAt_draws {Pp : Prep} {link : Option Nat} {n : Nums} (h : numsAt Pp link = some n) :
    n.nonZero = Pp.z.set.samples ∧ n.seeds = Pp.z.set.samples *
      ((sampledOf n.sent.toList).foldl (fun c x => max c (cubeBitsOf n.codes x.shape)) 0 + 1) := by
  unfold numsAt at h
  dsimp only at h
  split at h
  · cases h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨_, _, f, _, lay, _, rd, _, rfl⟩ := h
    exact ⟨rfl, rfl⟩

/-- **No state: the numbers' two counts, list and codes give what the laws ask of the draws.** -/
theorem draws_of_nums (p : P2) (x : Front) (r₁ r₂ : Fmt.RoundView) {Pp : Prep} {link : Option Nat}
    {n : Nums} (hn : numsAt Pp link = some n) (hs : p.seeds = n.seeds)
    (hz : p.nonZero = n.nonZero) (hN : switchNotices x.T x.others = n.sent)
    (hC : x.st.codes = n.codes)
    (he : planOk1 none (switchNotices x.T x.others) (par9 p).eSeed = true)
    (h : roundsFit (rounds p) [r₁, r₂] = true) :
    (∀ q ∈ r₂.drawn.poss, q < 2 ^ p.logN) ∧
      (r₁.drawn.elems.map E.ofTriple).length =
        (sendingAt p x).seeds * ((sendingAt p x).coordinates + 1) ∧
      r₁.drawn.poss = [] ∧ r₁.drawn.trits = [] ∧
      ∀ z ∈ K1.seedsOf (sendingAt p x) r₁, isZeroE z.2 = false := by
  obtain ⟨e1, e2⟩ := numsAt_draws hn
  exact call_draws_made p x r₁ r₂ Pp.z.set.samples (hz.trans e1)
    (by rw [hN, hC]; exact hs.trans e2) he h

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-- **In front of the switch into a later group.** -/
theorem link_draws_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    (a : Place) (nm : String) {x : Front} (hx : firstFront s.st s.check.frame = .ok x)
    (r₁ r₂ : Fmt.RoundView)
    (he : planOk1 none (switchNotices x.T x.others) (par9 (k2P Z a nm .link n)).eSeed = true)
    (h : roundsFit (rounds (k2P Z a nm .link n)) [r₁, r₂] = true) :
    (∀ q ∈ r₂.drawn.poss, q < 2 ^ (k2P Z a nm .link n).logN) ∧
      (r₁.drawn.elems.map E.ofTriple).length = (sendingAt (k2P Z a nm .link n) x).seeds *
        ((sendingAt (k2P Z a nm .link n) x).coordinates + 1) ∧
      r₁.drawn.poss = [] ∧ r₁.drawn.trits = [] ∧
      ∀ w ∈ K1.seedsOf (sendingAt (k2P Z a nm .link n) x) r₁, isZeroE w.2 = false := by
  obtain ⟨Q, hN⟩ := sw_link hS hR O hF hpl h23 hP hn hr
  have hC : x.st.codes = n.codes := by
    rw [(firstFront_st hx).1]
    exact Q.codes
  exact draws_of_nums _ x r₁ r₂ hn rfl rfl (hN x hx) hC he h

/-- **The same at the front that the law on a segment's first place names**, with that law's seven
fields on the front: so five of `LinkPlain`'s 32 fields fall. -/
theorem link_draws_plain (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    (a : Place) (nm : String) {L : Params.ReqLink} {Q : ReqGroup} {c₀ z₀ : Code}
    (first : s.check.frame.next = .first) (later : s.check.frame.link ≠ 0)
    (link : s.check.frame.shape.link[s.check.frame.link]? = some L)
    (group : s.check.frame.groups[s.check.frame.link]? = some Q)
    (code : s.st.codes.base[s.check.frame.shape.code]? = some c₀)
    (maskCode : s.st.codes.mask[s.check.frame.shape.maskCode]? = some z₀)
    (shorter : z₀.logN ≤ c₀.logN) (r₁ r₂ : Fmt.RoundView)
    (he : planOk1 none (switchNotices (frontAt s L Q).T (frontAt s L Q).others)
      (par9 (k2P Z a nm .link n)).eSeed = true)
    (h : roundsFit (rounds (k2P Z a nm .link n)) [r₁, r₂] = true) :
    (∀ q ∈ r₂.drawn.poss, q < 2 ^ (k2P Z a nm .link n).logN) ∧
      (r₁.drawn.elems.map E.ofTriple).length =
        (sendingAt (k2P Z a nm .link n) (frontAt s L Q)).seeds *
          ((sendingAt (k2P Z a nm .link n) (frontAt s L Q)).coordinates + 1) ∧
      r₁.drawn.poss = [] ∧ r₁.drawn.trits = [] ∧
      ∀ w ∈ K1.seedsOf (sendingAt (k2P Z a nm .link n) (frontAt s L Q)) r₁,
        isZeroE w.2 = false :=
  link_draws_reached hS hR O hF hpl h23 hP hn hr a nm (x := frontAt s L Q)
    (firstFront_returns s.st s.check.frame L Q c₀ z₀ first later link group code maskCode shorter)
    r₁ r₂ he h

/-- **In front of the output head's switch.** -/
theorem head_draws_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    {Pp : Prep} {n : Nums} (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some 24) = some n)
    {s : S} (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s))
    (a : Place) (nm : String) {x : Front}
    (hx : VerifiableInference.Desc.First.K2.frontAt (k2P Z a nm .head n) s = some x)
    (r₁ r₂ : Fmt.RoundView)
    (he : planOk1 none (switchNotices x.T x.others) (par9 (k2P Z a nm .head n)).eSeed = true)
    (h : roundsFit (rounds (k2P Z a nm .head n)) [r₁, r₂] = true) :
    (∀ q ∈ r₂.drawn.poss, q < 2 ^ (k2P Z a nm .head n).logN) ∧
      (r₁.drawn.elems.map E.ofTriple).length = (sendingAt (k2P Z a nm .head n) x).seeds *
        ((sendingAt (k2P Z a nm .head n) x).coordinates + 1) ∧
      r₁.drawn.poss = [] ∧ r₁.drawn.trits = [] ∧
      ∀ w ∈ K1.seedsOf (sendingAt (k2P Z a nm .head n) x) r₁, isZeroE w.2 = false := by
  obtain ⟨Q, hN⟩ := sw_head hS hR O hF hpl a nm hP hn hr
  have hC : x.st.codes = n.codes := by
    rcases frontOf_iff.2 hx with ⟨c0, _⟩ | ⟨_, a', G, _, _, rfl⟩ | ⟨c0, _⟩
    · cases c0
    · exact Q.codes
    · cases c0
  exact draws_of_nums _ x r₁ r₂ hn rfl rfl (hN x hx) hC he h

/-- **At the finish**: s is reached; the decision runs at t, behind the quiet front. -/
theorem finish_draws_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (h25 : Z.first.shape.link.length = 25) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp none = some n) {s t : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s)) (hq : finishFrontQ s = .ok t)
    (a : Place) (nm : String) {x : Front}
    (hx : VerifiableInference.Desc.First.K2.frontAt (k2P Z a nm .finish n) t = some x)
    (r₁ r₂ : Fmt.RoundView)
    (he : planOk1 none (switchNotices x.T x.others) (par9 (k2P Z a nm .finish n)).eSeed = true)
    (h : roundsFit (rounds (k2P Z a nm .finish n)) [r₁, r₂] = true) :
    (∀ q ∈ r₂.drawn.poss, q < 2 ^ (k2P Z a nm .finish n).logN) ∧
      (r₁.drawn.elems.map E.ofTriple).length = (sendingAt (k2P Z a nm .finish n) x).seeds *
        ((sendingAt (k2P Z a nm .finish n) x).coordinates + 1) ∧
      r₁.drawn.poss = [] ∧ r₁.drawn.trits = [] ∧
      ∀ w ∈ K1.seedsOf (sendingAt (k2P Z a nm .finish n) x) r₁, isZeroE w.2 = false := by
  obtain ⟨Q, hN⟩ := sw_finish hS hR O hF hpl h25 a nm hP hn hr hq
  have hC : x.st.codes = n.codes := by
    rcases frontOf_iff.2 hx with ⟨c0, _⟩ | ⟨c0, _⟩ | ⟨_, a', G, _, _, rfl⟩
    · cases c0
    · cases c0
    · show t.st.codes = n.codes
      rw [finishFrontQ_st hq]
      exact Q.codes
  exact draws_of_nums _ x r₁ r₂ hn rfl rfl (hN x hx) hC he h

end

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.numsAt_draws
#print axioms VerifiableInference.Desc.K2.Honest.Returns.draws_of_nums
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_draws_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_draws_plain
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_draws_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.finish_draws_reached
