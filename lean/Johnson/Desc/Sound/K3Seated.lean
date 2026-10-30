-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/K3Seated.lean: FROM THE LAW OF THE KIND "LOOKUP" AT ITS MAKER TO THE LAW AT WHAT
IS SEATED: the piece that holds `below B`, B the value of `K3.theStated` at an address
(Johnson/Desc/First/Look/K3Stated.lean). Two theorems; a carriage: nothing of the kind is proved
here.

Why. A law needs an object: the constant of the seated text that it speaks of. The kind's law is
proved at `below (K3.Law.blockVia seat piece laid before p [])`, at letters. At a place of the first
chain sits `theStated … a`'s value: that maker at the address's own arguments, with one conjunct
more in its test on the plan, at four of six sorts of place a step without a round behind it, and at
two a list of claims more.

Main names:
  **`k3_stated_goodIn`**: B := the value of `theStated` at a, ITS TEST ON THE PLAN SAYS YES; p a
    piece with `p.b = below B`. GIVEN (law) for the address's own link i, `digits`, place, list of
    what must be sent and count of padding places, AND THAT THE MAKER's OWN TEST ON THE PLAN SAYS
    YES THERE: the piece with `below (Law.blockVia (seatOfLookupOnDigitsOrCalls claim digits) a.piece laid sent P [])`
    in B's place owes `GoodIn on on' R R'`; (hq) where `quietAt` gives a step f at the address: f's
    law in the form of Johnson/Desc/Sound/MergeQuiet.lean; (hn) where it gives none: on' gives on'',
    and a witness of R'' is one of R'. THEN `p.GoodIn on on'' R R''`.
  `k3_seated_goodIn`: the same for a piece that holds `below B'`, B' any block that narrows B: what
    a seat lays: its tests behind B's `decide`, another name.

Limits: law, hq and hn are premises: the first is the lookup's files' to pay, the second rests on
Johnson/Desc/First/Look/K3QuietLaws.lean and on what on' and R' say. THAT A SEAT's BLOCK NARROWS B
is a premise of the second theorem: by `bind_narrows` (Johnson/Desc/Sound/MergeNarrow.lean) for each
test that a seat lays behind `decide`. The lift over the public part, outside `below`, is not joined
here. `GoodIn` alone: nothing on what rides past. Nothing on acceptance; nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.MergeQuiet
import Johnson.Desc.Sound.MergeSameMakers
import Johnson.Desc.Sound.MergeNarrowMakers
import Johnson.Desc.Sound.GoodInStretch
import Johnson.Desc.First.Look.K3OwnIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Maker OnBytes.Flat KObj
open OnBytes.Model (Aff)
open _root_.Run.PQ (CK SgX)

variable {Cl W : Type} {C : CK} {F : Frame}

/-- **The kind's law at its maker gives the law at the seated block.** -/
theorem k3_stated_goodIn (claim : Aff → Cl) (readers : Nat → Option (K3.Readers First.S))
    (X : Model.Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place)
    (B : Block First.S Cl) (h : K3.theStated claim readers X codes shape a = some B)
    (hOk : B.planOk = true) (p : Piece C F First.S Cl W) (hp : p.b = below B)
    (on on' on'' : First.S × F.E.Str → Prop) (R R' R'' : First.S × F.E.Str → W → Prop)
    (law : ∀ i digits P sent laid, a.link = some i → a.piece = K3.pieceAt X i digits →
      First.Look.placeAt X i digits = some P →
      First.Look.beforeAt codes shape i digits = some sent →
      First.Look.laidAt X i digits = some laid →
      (K3.Law.blockVia (K3.seatOfLookupOnDigitsOrCalls claim digits) a.piece laid sent P []).planOk = true →
      ({ p with b := below (K3.Law.blockVia (K3.seatOfLookupOnDigitsOrCalls claim digits) a.piece laid sent P []) } :
        Piece C F First.S Cl W).GoodIn on on' R R')
    (hq : ∀ f, (a.link.bind fun i => K3.quietAt X i (a.piece == K3.pieceAt X i true)) = some f →
      ∀ s' t y, f s' = .ok t → on' (s', y) →
        on'' (t, y) ∧ ∀ w, R'' (t, y) w → R' (s', y) w)
    (hn : (a.link.bind fun i => K3.quietAt X i (a.piece == K3.pieceAt X i true)) = none →
      (∀ b, on' b → on'' b) ∧ ∀ b w, R'' b w → R' b w) :
    p.GoodIn on on'' R R'' := by
  obtain ⟨B₁, hB₁, e1, e2, -, e4⟩ := K3.theStated_is claim readers X codes shape a B h
  obtain ⟨b, hb, hW⟩ := K3.theWhole_is claim true X codes shape a B₁ hB₁
  obtain ⟨i, digits, P, sent, laid, hi, hpc, hP, hs, hl, r1, r2, -, r4⟩ :=
    K3.theOwn_is claim true X codes shape a b hb
  have hbOk : b.planOk = true := by
    rw [e4] at hOk
    rcases hW with ⟨-, rfl⟩ | ⟨f, -, rfl⟩
    · exact hOk
    · exact ((Bool.and_eq_true _ _).mp hOk).1
  have g := law i digits P sent laid hi hpc hP hs hl (r4 hbOk)
  have sV : (K3.Law.blockVia (K3.seatOfLookupOnDigitsOrCalls claim digits) a.piece laid sent P []).Same b :=
    ⟨r1.symm, r2.symm⟩
  have sB : B₁.Same B := ⟨e1.symm, e2.symm⟩
  rcases hW with ⟨hnone, rfl⟩ | ⟨f, hf, rfl⟩
  · -- no step behind the kind's rounds
    obtain ⟨n1, n2⟩ := hn hnone
    refine goodIn_weaken p on on on' on'' R R R' R'' (fun _ x => x) n1 n2 (fun _ _ x => x) ?_
    refine goodIn_of_same p _ ?_ on on' R R' g
    rw [hp]
    exact (sV.trans sB).below
  · -- a step behind them
    have g2 := goodIn_below_thenQuiet
      ({ p with b := below (K3.Law.blockVia (K3.seatOfLookupOnDigitsOrCalls claim digits) a.piece laid sent P []) } :
        Piece C F First.S Cl W)
      (K3.Law.blockVia (K3.seatOfLookupOnDigitsOrCalls claim digits) a.piece laid sent P []) rfl b.name
      (b.name ++ ": behind it") 1 a.link a.piece f on on' on'' R R' R'' g (hq f hf)
    refine goodIn_of_same p _ ?_ on on'' R R'' g2
    rw [hp]
    exact ((sV.andThen (Block.Same.refl _) b.name b.name).trans sB).below

/-- **At what a seat lays**: a block B' that narrows `theStated`'s value (the seat's tests behind
its `decide`, one around the other; another name): the piece that holds `below B'` owes the same. -/
theorem k3_seated_goodIn (claim : Aff → Cl) (readers : Nat → Option (K3.Readers First.S))
    (X : Model.Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place)
    (B B' : Block First.S Cl) (h : K3.theStated claim readers X codes shape a = some B)
    (hOk : B.planOk = true) (hN : B'.Narrows B) (p : Piece C F First.S Cl W)
    (hp : p.b = below B')
    (on on' on'' : First.S × F.E.Str → Prop) (R R' R'' : First.S × F.E.Str → W → Prop)
    (law : ∀ i digits P sent laid, a.link = some i → a.piece = K3.pieceAt X i digits →
      First.Look.placeAt X i digits = some P →
      First.Look.beforeAt codes shape i digits = some sent →
      First.Look.laidAt X i digits = some laid →
      (K3.Law.blockVia (K3.seatOfLookupOnDigitsOrCalls claim digits) a.piece laid sent P []).planOk = true →
      ({ p with b := below (K3.Law.blockVia (K3.seatOfLookupOnDigitsOrCalls claim digits) a.piece laid sent P []) } :
        Piece C F First.S Cl W).GoodIn on on' R R')
    (hq : ∀ f, (a.link.bind fun i => K3.quietAt X i (a.piece == K3.pieceAt X i true)) = some f →
      ∀ s' t y, f s' = .ok t → on' (s', y) →
        on'' (t, y) ∧ ∀ w, R'' (t, y) w → R' (s', y) w)
    (hn : (a.link.bind fun i => K3.quietAt X i (a.piece == K3.pieceAt X i true)) = none →
      (∀ b, on' b → on'' b) ∧ ∀ b w, R'' b w → R' b w) :
    p.GoodIn on on'' R R'' := by
  refine goodIn_of_narrows p (below B) ?_ on on'' R R'' ?_
  · rw [hp]
    exact hN.below
  · exact k3_stated_goodIn claim readers X codes shape a B h hOk
      ({ p with b := below B } : Piece C F First.S Cl W) rfl on on' on'' R R' R'' law hq hn

#print axioms k3_stated_goodIn
#print axioms k3_seated_goodIn

end VerifiableInference.Desc.Sound
