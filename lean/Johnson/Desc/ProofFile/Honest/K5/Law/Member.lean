-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Member.lean: CONDITIONAL: which sub-protocol stands in the
first chain's flat list at the place of an attention segment's own rounds (kind K5), and how it
decides: as the kind's own decision (`decide seatSO p`, Johnson/Desc/First/Att/K5AttentionKind.lean, SeatO.lean)
with two tests more: the state behind bears no mark of failure, and it holds the reply that stood in
front.

  `parAt Zp g a`   the public numbers of the kind's place of the group g of layers, a the group's
                   attention plan
  `DecidesAs p blk`   blk stands at the kind's place of segment p.link; its rounds and its (empty)
                   lists of oracle messages are the kind's at p; the kind's test on the plan says
                   yes; blk's decision is the kind's, with the two tests
  `PlanAt Zp g a`   five facts on the public plan at group g
  `decidesAs_of_alone`   GENERAL in the public parameters: a sub-protocol that is the kind's own
                   one, wrapped alone as the description's maker wraps it, decides so
  `k5_member`      CONDITIONAL, under the one hypothesis `P5J.AtMgA` that ties the library's letters
                   to the proof file's description, at the format's second hash function and the full size:
                   for each group g below 12 the member number 14 (2 g + 1) + 4 decides so

By: the library's `k5_alone` (Johnson/H2K5R/LawAtEntry.lean), `k5_seat_of_open`
(Johnson/H2K5R/SeatAtOpen.lean) and `IM.yes_alone` (Johnson/IMR/SeatForm.lean).

Limits. `P5J.AtMgA` is A HYPOTHESIS of every statement that names it: where it is not met,
`k5_member` says nothing. It can be met: at the full-size public files as Ladder/Stored.lean spells
them the head has a member with no premise (`headMember_zFull`,
AtFullSide/Top/HeadMemberAtFull.lean: one example, in a side library; these three files are tied to
the package's files by no theorem). The library also has `P5J.head_exists_at_name`
(Johnson/P5J/HeadExistsAtName.lean): a head is there under four premises on the public files. This
file calls neither. No yes of any decision is concluded here.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Seated
import Johnson.P5J.MgAtAll
import Johnson.H2K5R.SeatAtOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Chain Claim First.S)
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.First.Att.P
open P5J (AtMgA TS)

/-- The public numbers of the kind's place of group g; a: the group's attention plan. -/
def parAt (Zp : ProofFile.Pub) (g : Nat) (a : Attention.Plan) : Par :=
  parO (P5J.At.X Zp) (2 * g + 1) a ((H2K5.k5Before? Zp ("A" ++ toString g)).getD [])

/-- **blk decides as the kind's own decision at the numbers p, with two tests more.** It is a
definition: the form in which `decidesAs_of_alone` and `k5_member` of this file end, and a premise's
form for the laws that stand above it. -/
structure DecidesAs (p : Par) (blk : Block First.S Claim) : Prop where
  /-- it stands at the kind's place of the segment -/
  place : blk.place = ⟨1, some p.link, 3, .K5⟩
  /-- no round has an oracle message -/
  oracles : blk.oracles = (rounds p).map fun _ => []
  /-- its rounds are the kind's -/
  rounds : blk.rounds = rounds p
  /-- the kind's test on the plan says yes: a fact on p alone, kept here because every law on the
  decision spends it -/
  plan : planOk p = true
  /-- its yes is the kind's yes, no mark behind, and the reply as in front -/
  decides : ∀ (t t' : First.S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
    blk.decide t rs gs = .ok t' ↔
      decide seatSO p t rs = .ok t' ∧ t'.failed = none ∧ ProofFile.sameReply t t' = true

/-- Facts on the public plan at group g. fits: the ledger of the segment has room for the slots of
the lookup on the calls and of the segment's own rounds. -/
structure PlanAt (Zp : ProofFile.Pub) (g : Nat) (a : Attention.Plan) : Prop where
  planIs : PlanIs (P5J.At.X Zp)
  p4 : (P5J.At.X Zp).p4 = true
  plan : (P5J.At.X Zp).A[g]? = some a
  look : ∃ x₁, lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁
  fits : Forest.elems a.fs + slotsOf (script a.own) ≤ a.ns

/-- **The kind's sub-protocol, wrapped alone, decides so.** General in the public parameters W, the
segment's number l and the group g. ok': one more conjunct in the test on the plan. CONDITIONAL: b'
is the kind's sub-protocol off the plan, its test on the plan says yes, and blk is b' wrapped alone:
the description's maker is meant to pay these. -/
theorem decidesAs_of_alone {W : Verify.Public} {l g : Nat} {before : List (Nat × Nat)}
    {b' blk : Block First.S Claim} {a : Attention.Plan} {ok' : Bool} {n : String}
    (hat : k5AtN W l g before = some b') (ha : W.A[g]? = some a) (hok : b'.planOk = true)
    (hla : IM.LaidAlone ProofFile.sameReply blk { b' with planOk := b'.planOk && ok' } n
      ⟨1, some l, 3, .K5⟩) : DecidesAs (parO W l a before) blk := by
  obtain ⟨a', ea', eb⟩ := k5AtN_is _ _ _ _ _ hat
  obtain rfl : a' = a := Option.some.inj (ea'.symm.trans ha)
  subst eb
  exact
    { place := IM.alone_place hla
      rounds := IM.alone_rounds hla
      oracles := IM.alone_oracles hla
      plan := (Bool.and_eq_true_iff.1 hok).1
      decides := fun t t' rs gs => IM.yes_alone hla (fun e => nomatch e) t t' rs gs }

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The member at the kind's border of group g.** CONDITIONAL: under the hypothesis that ties the
library's letters to the proof file's description: a hypothesis here; on whether it can be met see
the head's Limits. -/
theorem k5_member (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : Nat} (hg : g < 12) :
    ∃ blk a, cF.blocksInOrder[borderOf g]? = some blk ∧ PlanAt Zp g a ∧ DecidesAs (parAt Zp g a) blk := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hW : Bs.G₀.W = P5J.At.X Zp := O.W
  obtain ⟨h4, g', hg', e⟩ := att_only O.pub O.blank (IM.subs_att h.scope h.reads O.pub O.blank hg)
  obtain rfl : g' = g := by omega
  obtain ⟨Lk, Eb, b', e1, e2, hat, hla⟩ := k5_alone O h4 hg'
  have e3 := IM.flatIx_scope h.scope h.reads O (l := 2 * g' + 1) (by omega) 2
  have hfl : cF.blocksInOrder[14 * (2 * g' + 1) + 4]? = some Eb := by
    have hfl0 := IM.hear_at_flat e1 e2
    rw [e3, show 14 * (2 * g' + 1) + 2 + 2 = 14 * (2 * g' + 1) + 4 by omega] at hfl0
    exact hfl0
  obtain ⟨blk, -, a, x₁, xd, -, -, -, -, hP, -, ea, hx, -, Pn, hat', hok, -⟩ :=
    k5_seat_of_open h.scope h.reads O h.laid.planOk h.laid.asks hg
  obtain rfl : b' = blk := Option.some.inj (hat.symm.trans hat')
  have Dc := decidesAs_of_alone hat ea hok hla
  have hf := Pn.fits
  rw [hW] at Dc hP h4 ea hx
  exact ⟨Eb, a, hfl, ⟨hP, h4, ea, ⟨x₁, hx⟩, by omega⟩, Dc⟩

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.decidesAs_of_alone
#print axioms ProofFile.Honest.K5.k5_member
