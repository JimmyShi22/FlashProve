-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K10/Honest/KeepsStep.lean: THE CLOSING OF A SEGMENT (K10): `K10Keeps`
(Johnson/Desc/K10/Honest/Keeps.lean) PAID FROM THE WHOLE MEMBER's ACCEPTING STEP (`StepYes`,
Johnson/Top/H0/Walk/Reach.lean): the one line from that step to the member's decision, laid over
Johnson/Desc/K10/Honest/KeepsSeat.lean; AND THREE THINGS THAT FOLLOW FROM ITS FIRST HALF,
`K10Turns`, in the forms in which other authors' laws take them. Lemmas on the verifier's own
text; no honest side's frame in them; none of the library's goals.

  `keeps_of_stepYes`   of any block each of whose decision's yeses gives `K10Keeps`: so does each
                       accepting step: by the library's `stepYes_decide`
                       (Johnson/Top/H0/Walk/ReachInv.lean)
    `putLive_head`, `keeps_head`   from `K10Turns`: where the state in front stands in the head's
                   own part a, the state behind stands in a part a' with a'.x = a.x, a'.t = a.t,
                   a'.wo = a.wo
      `beside_own`, `keeps_own`, `keeps_out`   from `K10Turns`: what a layers' link's own rounds
                   returned (`S.own?`) is behind as in front: the library's `SameOwn`, by its
                   `putLink_own`, `putFork_own` and `K9.putRec_keeps`; so are the chain's results
                   so far (`S.out`): a clause of `turns_six` (Keeps.lean) by name
  `keeps_step_link`    under the library's one head (`P5J.AtMgA`), at each link l < 25: whichever
                       block stands at the library's number `LPFK10.ixK10 l` of the first chain's
                       flat list: each of its accepting steps gives `K10Keeps`
    `keeps_step_place`   the like BY PLACES: at a number k whose place in `P5J.At.ps` is of the
                   kind K10; and the block's own place is that place

Limits. AT `OnBytes.secondHashFunction` ALONE, IN SCOPE, as KeepsSeat.lean. THE HEAD IS MET, UNDER FOUR
PREMISES ON THE THREE PUBLIC FILES, by the library's `P5J.head_exists_at_name`
(Johnson/P5J/HeadExistsAtName.lean); that these four hold at any public files is not shown here.
`keeps_head`, `keeps_own`, `keeps_out` have no member here; `keeps_head` bites at the closing in
the head's link alone. Called by no line of this folder. The same line from `StepYes` to the
decision stands in the library at the bare retyped closing, to another end, in elder files
(Johnson/LPFK10R/RoomClose.lean, OwnInAt.lean: they call `stepYes_decide` too). Of this folder it
stands over Keeps.lean and KeepsSeat.lean. Nothing on soundness, completeness or hiding of the
protocol.

-/
import Johnson.Desc.K10.Honest.KeepsSeat
import Johnson.Top.H0.Walk.ReachInv
import Johnson.Desc.First.Link.Law.OwnStay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.YesFree
open OnBytes VerifiableInference.Desc VerifiableInference.Desc.First.Close
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied (StepYes stepYes_decide)

/-- From the decision's yeses to the accepting steps. -/
theorem keeps_of_stepYes {Cl : Type} {b : Block S Cl}
    (h : ∀ t t' rs gs, b.decide t rs gs = .ok t' → K10Keeps t t') {ft : Nat} {s s' : S}
    (hy : StepYes ft b s s') : K10Keeps s s' := by
  obtain ⟨rs, gs, e⟩ := stepYes_decide hy
  exact h _ _ _ _ e

/-- Writing the live copy leaves three fields of the head's own part: what its rounds heard, the
tables, what the merge laid. Inside the head's open link it does turn that part (the link's
context). -/
theorem putLive_head (t : S) (c : Model.ChainCheck) (a : VerifiableInference.Desc.First.HeadOwn)
    (h : t.here = .head a) :
    ∃ a', (t.putLive c).here = .head a' ∧ a'.x = a.x ∧ a'.t = a.t ∧ a'.wo = a.wo := by
  cases ho : a.opened with
  | false =>
    have hl : t.link? = none := by
      unfold VerifiableInference.Desc.First.S.link?
      rw [h]
      simp [ho]
    refine ⟨a, ?_, rfl, rfl, rfl⟩
    unfold VerifiableInference.Desc.First.S.putLive
    rw [hl]
    exact h
  | true =>
    have hl : t.link? = some a.L := by
      unfold VerifiableInference.Desc.First.S.link?
      rw [h]
      simp [ho]
    refine ⟨{ a with L := { a.L with check := c } }, ?_, rfl, rfl, rfl⟩
    unfold VerifiableInference.Desc.First.S.putLive
    rw [hl]
    show (t.putLink { a.L with check := c }).here = _
    unfold VerifiableInference.Desc.First.S.putLink
    rw [h]
    simp [ho]

/-- **WHAT A YES LEAVES OF THE HEAD's OWN PART**: in the form that the other authors' riders on
that part take: "the part behind is the part in front" does not hold at the closing in the head's
open link, where the link's context is written (the text of `S.putLink`; no lemma here says it). -/
theorem keeps_head {t t' : S} (h : K10Turns t t') (a : VerifiableInference.Desc.First.HeadOwn)
    (ha : t.here = .head a) :
    ∃ a', t'.here = .head a' ∧ a'.x = a.x ∧ a'.t = a.t ∧ a'.wo = a.wo := by
  obtain ⟨a', e, hx⟩ := putLive_head t { t.live with frame := (K9.recOf t').frame } a ha
  refine ⟨a', ?_, hx⟩
  rw [h.2]
  exact e

/-- What a layers' link's own rounds returned is a reader that does not see what K9's blocks and
the closing write: by the library's two laws (`LinkJoin.putLink_own`, `putFork_own`,
Johnson/Desc/First/Link/Law/StretchParts.lean). General: it serves at every block for which the
library has a law on `K9.Beside` (Johnson/Desc/First/Batch/Law/Keeps.lean). -/
theorem beside_own : K9.Beside (·.own?) :=
  ⟨LinkJoin.putLink_own, LinkJoin.putFork_own, fun _ _ _ => rfl, fun _ _ => rfl⟩

/-- **A YES LEAVES WHAT A LAYERS' LINK's OWN ROUNDS RETURNED**: the library's `SameOwn`
(Johnson/Desc/First/Link/Law/OwnStay.lean). -/
theorem keeps_own {t t' : S} (h : K10Turns t t') : LinkJoin.SameOwn t t' := by
  show t'.own? = t.own?
  rw [h.2]
  exact K9.putRec_keeps beside_own t _

/-- **AND THE CHAIN's RESULTS SO FAR** (the pending claims and the reply among them): the fourth
clause of `turns_six` (Keeps.lean), by name. -/
theorem keeps_out {t t' : S} (h : K10Turns t t') : t'.out = t.out := (turns_six h).2.2.2.1

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE PAYER, BY LINKS.** -/
theorem keeps_step_link (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    ∀ blk, cF.blocksInOrder[LPFK10.ixK10 l]? = some blk →
      ∀ ft s s', StepYes ft blk s s' → K10Keeps s s' := by
  obtain ⟨_, _, _, b, _, _, _, _, hn, _, hk⟩ := seated_at_headK10 h l hl
  intro blk hb ft s s' hy
  rw [number_is, hn] at hb
  obtain rfl := Option.some.inj hb
  exact keeps_of_stepYes hk hy

/-- **THE PAYER, BY PLACES.** -/
theorem keeps_step_place (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (k : Nat) (p : Place)
    (hp : P5J.At.ps[k]? = some p) (hK : p.kind = KindName.K10) :
    ∀ blk, cF.blocksInOrder[k]? = some blk →
      blk.place = p ∧ ∀ ft s s', StepYes ft blk s s' → K10Keeps s s' := by
  obtain ⟨b, h1, h2, hk⟩ := keeps_at_place h k p hp hK
  intro blk hb
  rw [h1] at hb
  obtain rfl := Option.some.inj hb
  exact ⟨h2, fun ft s s' hy => keeps_of_stepYes hk hy⟩

end ProofFile.Honest.K10.YesFree

#print axioms ProofFile.Honest.K10.YesFree.keeps_head
#print axioms ProofFile.Honest.K10.YesFree.beside_own
#print axioms ProofFile.Honest.K10.YesFree.keeps_own
#print axioms ProofFile.Honest.K10.YesFree.keeps_out
#print axioms ProofFile.Honest.K10.YesFree.keeps_of_stepYes
#print axioms ProofFile.Honest.K10.YesFree.keeps_step_link
#print axioms ProofFile.Honest.K10.YesFree.keeps_step_place
