-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/DrawAtHead.lean: the smallness test's draw at its seat in the proof file's own
first chain, at all 25 links: the member of the flat list has one step on the chain's shape, with
both laws at the seated block's own decision. Under the head `P5J.AtMgA`; nothing is evaluated.

Main names.
* `putTl_keeps`, `draw_keeps`: a yes of the draw's decision leaves the mark of failure and what goes
  out.
* `drawNo`: the smallness test's number among a link's hearing sub-protocols: 5 at the head's link,
  4 at every other. (Johnson/AtFull/Shape/BehindAtHead.lean has the same function under the name
  `k8No`; this file does not import it, and so has a name of its own.)
* `drawGS p n`: the step at the seat: no mark, then `K8.drawG p n`
  (Johnson/Desc/First/K8/HearChain.lean).
* `draw_at`: for l < 25: with Bs what the maker's own `ProofFile.baseOf` returns at the public part, and
  Xl the link as built in its ground Bs.G₀: the member b at number 14 l + drawNo (subAt l) + 2 of
  cF.blocksInOrder is such that: where b says yes on one round, `drawGS` at that round's number of entries
  returns at the state's shape, and returns the shape behind; and where `drawGS` returns at the
  state's shape, at whichever number n, b says yes on any one round.
* `drawN p`: the number of entries that the place's own declared round counts: columns x tau
  (`K8.round`, Johnson/Desc/First/K8/Hear.lean). `drawStep p`: `drawGS p (drawN p)`: THE STEP AS A
  FUNCTION OF THE SHAPE ALONE.
* `draw_step_at`: with the same letters, tied as there: the member's declared rounds are the one
  round `K8.round p`; a yes of b on whatever list of rounds is a yes on one round; if that round has
  `drawN p` entries, `drawStep p` returns at the state's shape, and returns the shape behind; and
  where `drawStep p` returns at the state's shape, b says yes on any one round.

How. `IM.k8_alone` (Johnson/IMR/K8Seat.lean: the seat holds the kind's own block, whole, alone; its
decision is the draw's by definition), `IM.subs_scope` (Johnson/IMR/LinkSeat.lean), `IM.yes_alone`
(Johnson/IMR/SeatForm.lean: the seated yes is the block's yes, no mark, the reply as it was),
`IM.hear_at_flat` and `IM.flatIx_scope` (the number in the flat list); then `draw_carries` and
`draw_returns`.

Limits. The decision alone: the frame's tests in front of it (the round's form) and the member's
runs of claims and of what comes after are not here. In `draw_at`'s second law the number n is free
of the round: the decision asks nothing of the number of entries. That a round which the run hands
the member has `drawN p` entries is the frame's test on the rounds' form: a premise of
`draw_step_at`'s first law, paid nowhere here. In neither second law is the step's value tied to the
shape behind the yes: with the first law that follows where the step's number is the round's number
of entries (in `draw_step_at`: where the round has `drawN p` entries). OF THE HEAD THE PROOFS SPEND
THREE FIELDS ALONE (scope, reads, laid.opened): the others are idle here, and the letters Z, D, r,
Np and x stand in no conclusion. The first law is of the strong form (a yes gives the step's
return); the merge's and the reads' laws are of the weaker one (a yes AND the step's return give the
shape behind), and their steps return an Option, this one an Except. No law ties drawNo to k8No. No
state is shown at which `drawGS` returns. At the format's second hash function. Nothing on soundness,
completeness or hiding.
-/
import Johnson.Desc.First.K8.HearChain
import Johnson.IMR.K8Seat
import Johnson.IMR.LinkSeat
import Johnson.IMR.FlatScope
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link KindName)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open VerifiableInference.Desc.First.Shape
open OnBytes.Maker (WholeD)
open IM (subAt)
open P5J (AtMgA F0T)

/-! ## 1 What the draw leaves -/

/-- Laying the test's record leaves the mark of failure and what goes out. -/
theorem putTl_keeps (s : S) (tl : HTailF2) :
    (s.putTl tl).failed = s.failed ∧ (s.putTl tl).out = s.out := by
  unfold S.putTl
  split
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- A yes of the draw's decision leaves the mark and what goes out. -/
theorem draw_keeps {Cl : Type} {p : VerifiableInference.Desc.First.K8.Par} {s t : S} {r : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (VerifiableInference.Desc.First.K8.approximateRangeProofDrawKind (Cl := Cl)
      VerifiableInference.Desc.First.K8.atS p).decide s [r] gs = .ok t) :
    t.failed = s.failed ∧ t.out = s.out := by
  obtain ⟨-, tl, -, rfl⟩ := (VerifiableInference.Desc.First.K8.draw_iff p s t r gs).1 h
  exact putTl_keeps _ _

/-! ## 2 The draw at its seat, at all 25 links -/

/-- The smallness test's number among a link's hearing sub-protocols. -/
def drawNo : ModelPart → Nat
  | .head => 5
  | _ => 4

/-- At that number the link's list of kinds has the smallness test. (BehindAtHead.lean's k8_index
says the same of k8No.) -/
theorem drawNo_index (sub : ModelPart) (first : Bool) :
    (kindsBeforeBatching sub first)[drawNo sub]? = some KindName.K8 := by
  cases sub <;> cases first <;> rfl

/-- **The step at the seat.** -/
def drawGS (p : VerifiableInference.Desc.First.K8.Par) (n : Nat) (a : ChainSh) :
    Except String ChainSh :=
  if a.marked then .error "the draw: the state bears a mark"
  else VerifiableInference.Desc.First.K8.drawG p n a

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The draw at its seat, at all 25 links**: both laws at the seated block's own decision: a yes
on one round gives the step's return at that round's number of entries, to the shape behind; the
step's return, at whichever number, gives a yes on any one round. -/
theorem draw_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    ∃ (Bs : ProofFile.PureBase) (Xl : Stages.LinkH) (b : Block S ProofFile.Cl),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      Bs.G₀.built[l]? = some Xl ∧
      cF.blocksInOrder[14 * l + drawNo (subAt l) + 2]? = some b ∧
      (∀ s rd gs t, b.decide s [rd] gs = .ok t →
        drawGS (ProofFile.k8Par Zp Bs.G₀ Xl l) rd.drawn.trits.length (chainSh s) = .ok (chainSh t)) ∧
      ∀ s n rd gs u, drawGS (ProofFile.k8Par Zp Bs.G₀ Xl l) n (chainSh s) = .ok u →
        ∃ t, b.decide s [rd] gs = .ok t := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hi : 2 ≤ drawNo (subAt l) + 1 ∧ drawNo (subAt l) + 1 ≤ 9 := by
    cases subAt l <;> exact ⟨by decide, by decide⟩
  obtain ⟨Lk, b, Xl, eL, eb, hX, -, la⟩ :=
    IM.k8_alone O l (subAt l) (IM.subs_scope h.scope h.reads O l hl) (drawNo (subAt l))
      (drawNo_index _ _) hi
  have hy := IM.yes_alone la (by intro k; cases k)
  have q := IM.hear_at_flat eL eb
  rw [IM.flatIx_scope h.scope h.reads O (by omega : l ≤ 24) (drawNo (subAt l))] at q
  refine ⟨Bs, Xl, b, O.made, hX, q, fun s rd gs t hd => ?_, fun s n rd gs u hg => ?_⟩
  · obtain ⟨hd', hf, -⟩ := (hy s t [rd] gs).1 hd
    have hd'' : (VerifiableInference.Desc.First.K8.approximateRangeProofDrawKind (Cl := ProofFile.Cl)
        VerifiableInference.Desc.First.K8.atS (ProofFile.k8Par Zp Bs.G₀ Xl l)).decide s [rd] gs =
        .ok t := hd'
    have hs : s.failed = none := (draw_keeps hd'').1.symm.trans hf
    have hm : (chainSh s).marked = false := by
      show s.failed.isSome = false
      rw [hs]
      rfl
    unfold drawGS
    rw [hm]
    exact VerifiableInference.Desc.First.K8.draw_carries hd''
  · unfold drawGS at hg
    split at hg
    · cases hg
    · rename_i hm
      obtain ⟨t, ht⟩ := VerifiableInference.Desc.First.K8.draw_returns (Cl := ProofFile.Cl)
        (ProofFile.k8Par Zp Bs.G₀ Xl l) n s rd gs hg
      obtain ⟨k1, k2⟩ := draw_keeps ht
      have hf : s.failed = none := by
        have h1 : (chainSh s).marked = false := by simpa using hm
        have h2 : s.failed.isSome = false := h1
        simpa using h2
      refine ⟨t, (hy s t [rd] gs).2 ⟨ht, k1.trans hf, ?_⟩⟩
      unfold ProofFile.sameReply
      rw [k2]
      exact beq_self_eq_true _

/-! ## 3 The step as a function of the shape alone -/

/-- The number of entries that the place's own declared round counts. -/
def drawN (p : VerifiableInference.Desc.First.K8.Par) : Nat :=
  VerifiableInference.Desc.First.K8.columns p * p.tau

/-- **The step at the seat, at the plan's number.** -/
def drawStep (p : VerifiableInference.Desc.First.K8.Par) (a : ChainSh) : Except String ChainSh :=
  drawGS p (drawN p) a

/-- **The same with the step as a function of the shape alone**: at the plan's number of entries,
which the first law takes as a premise on the round. -/
theorem draw_step_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    ∃ (Bs : ProofFile.PureBase) (Xl : Stages.LinkH) (b : Block S ProofFile.Cl),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      Bs.G₀.built[l]? = some Xl ∧
      cF.blocksInOrder[14 * l + drawNo (subAt l) + 2]? = some b ∧
      b.rounds = [VerifiableInference.Desc.First.K8.round (ProofFile.k8Par Zp Bs.G₀ Xl l)] ∧
      (∀ s rs gs t, b.decide s rs gs = .ok t → ∃ rd, rs = [rd] ∧
        (rd.drawn.trits.length = drawN (ProofFile.k8Par Zp Bs.G₀ Xl l) →
          drawStep (ProofFile.k8Par Zp Bs.G₀ Xl l) (chainSh s) = .ok (chainSh t))) ∧
      ∀ s rd gs u, drawStep (ProofFile.k8Par Zp Bs.G₀ Xl l) (chainSh s) = .ok u →
        ∃ t, b.decide s [rd] gs = .ok t := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hi : 2 ≤ drawNo (subAt l) + 1 ∧ drawNo (subAt l) + 1 ≤ 9 := by
    cases subAt l <;> exact ⟨by decide, by decide⟩
  obtain ⟨Lk, b, Xl, eL, eb, hX, -, la⟩ :=
    IM.k8_alone O l (subAt l) (IM.subs_scope h.scope h.reads O l hl) (drawNo (subAt l))
      (drawNo_index _ _) hi
  have hy := IM.yes_alone la (by intro k; cases k)
  have q := IM.hear_at_flat eL eb
  rw [IM.flatIx_scope h.scope h.reads O (by omega : l ≤ 24) (drawNo (subAt l))] at q
  obtain ⟨Bs', Xl', b', e1, e2, e3, c1, c2⟩ := draw_at h l hl
  obtain rfl : Bs' = Bs := Except.ok.inj (e1.symm.trans O.made)
  obtain rfl : Xl' = Xl := Option.some.inj (e2.symm.trans hX)
  obtain rfl : b' = b := Option.some.inj (e3.symm.trans q)
  refine ⟨Bs', Xl', b', e1, e2, e3, IM.alone_rounds la, fun s rs gs t hd => ?_,
    fun s rd gs u hg => c2 s _ rd gs u hg⟩
  have hd' : (VerifiableInference.Desc.First.K8.approximateRangeProofDrawKind (Cl := ProofFile.Cl)
      VerifiableInference.Desc.First.K8.atS (ProofFile.k8Par Zp Bs'.G₀ Xl' l)).decide s rs gs = .ok t :=
    ((hy s t rs gs).1 hd).1
  obtain ⟨rd, rfl⟩ := VerifiableInference.Desc.First.K8.decide_one _ _ s t rs gs hd'
  refine ⟨rd, rfl, fun hn => ?_⟩
  unfold drawStep
  rw [← hn]
  exact c1 s rd gs t hd

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.putTl_keeps
#print axioms Johnson.AtFull.Shape.draw_keeps
#print axioms Johnson.AtFull.Shape.drawNo_index
#print axioms Johnson.AtFull.Shape.draw_at
#print axioms Johnson.AtFull.Shape.draw_step_at
#print axioms Johnson.AtFull.Shape.drawNo
#print axioms Johnson.AtFull.Shape.drawGS
#print axioms Johnson.AtFull.Shape.drawN
#print axioms Johnson.AtFull.Shape.drawStep
