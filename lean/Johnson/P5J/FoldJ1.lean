-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/FoldJ1.lean: FIVE FIELDS OF FoldFacts (Johnson/Desc/First/FoldFacts.lean: the facts on
the verifier's state that the laws take from "reached") AT THE LETTERS OF THE COMPOSED MEANING'S
HEAD: weightsOk, reqIs, tidy, room, roomEarly: each a theorem from the head h : P5J.AtMg ...,
general in a condition Rch that gives the description's own "reached" (hR): at_ := fun a => a.1,
d := At.foldD Zp cF Ld, reqW := At.reqW, links := At.links, ps := At.ps. The statements are those of
the table of joints, to the letter, at o := OnBytes.secondHashFunction (the table's
letter for the whole join).

  flat_ok           every sub-protocol of the first chain's flat list passes its test on the plan
  weightsOk_at_head, reqIs_at_head   by weights_at_open, req_at_open (Johnson/LTPileR/AtGate.lean)
  tidy_at_head      by tidy_at_open (Johnson/Desc/AtSeats/Fit/TidyAtOpen.lean)
  room_at_head, roomEarly_at_head    by room_at_fill_below, roomEarly_at_fill_below
                    (RoomAtFill.lean), where the public test FillP1.startB accepts (hs)
  foldFacts_of_j1   A STRUCTURE LITERAL of FoldFacts at these letters: the five by the theorems
                    above, the other twenty-one fields as premises in the fields' own text: so Lean
                    holds that the five ends are the fields' own types

Limits. At the second hash function (OnBytes.secondHashFunction): the opening's seats are shown there. Laws from
accepts: where Rch never holds every sentence is idle. hs is a premise. No soundness statement.

-/
import Johnson.P5J.AtMg
import Johnson.P5J.FoldAt
import Johnson.P5J.RchIsReach
import Johnson.IMR.PlanAt
import Johnson.LTPileR.AtGate
import Johnson.Desc.AtSeats.Fit.TidyAtOpen
import Johnson.P1L20R.RoomAtFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.K12.Door (Laid msgsOfChain)
open OnBytes.Maker (WholeD)
open Johnson.Desc.First.Walk.Tied (Reach RchAt reach_raw)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl}

/-- Every sub-protocol of the first chain's flat list passes its test on the plan. -/
theorem flat_ok (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) : ∀ b ∈ cF.blocksInOrder, b.planOk = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact IM.plan_flat O h.laid.planOk

section
variable (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {Str : Type}
  (Rch : ℕ → ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) × Str → Prop)
  (hR : ∀ k a, Rch k a → RchAt (F0T OnBytes.secondHashFunction Zp Np cF) k a)
include h hR

/-- **weightsOk.** -/
theorem weightsOk_at_head : ∀ k a, Rch k a → a.1.2.failed = none → weightsB a.1.2 = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  intro k a hr _
  exact Meaning.K2.weights_at_open O (flat_ok h) 0 k a.1
    (reach_raw (hRch_at OnBytes.secondHashFunction Zp Np cF Rch hR k a hr))

/-- **reqIs.** -/
theorem reqIs_at_head : ∀ k a, Rch k a → a.1.2.failed = none → a.1.2.req = At.reqW a.1.1 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  intro k a hr hm
  exact Meaning.K2.req_at_open O (flat_ok h) 0 k a.1
    (reach_raw (hRch_at OnBytes.secondHashFunction Zp Np cF Rch hR k a hr)) hm

/-- **tidy.** -/
theorem tidy_at_head : ∀ k a, Rch k a → a.1.2.failed = none →
    OnBytes.Means.tidy4B a.1.2.st = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  intro k a hr hm
  exact Meaning.K2.tidy_at_open h.laid.value h.laid.planOk O k a.1
    (hRch_at OnBytes.secondHashFunction Zp Np cF Rch hR k a hr) hm

/-- **room.** -/
theorem room_at_head (Ld : Laid)
    (hs : FillP1.startB Zp (msgsOfChain Zp.made.proof.1) (At.N Zp cF).indexNo = true) :
    ∀ k a p m, Rch k a → a.1.2.failed = none → At.ps[k]? = some p → p.link = some m →
      2 ≤ p.piece → Johnson.Desc.First.Walk.Tied.roomIsB (At.foldD Zp cF Ld).free0
        (At.foldD Zp cF Ld).fvs m a.1.2 = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact P1L20.room_at_fill_below h.scope h.reads O (flat_ok h) (Rch := Rch)
    (at_ := fun a => a.1)
    (hRch_at OnBytes.secondHashFunction Zp Np cF Rch hR) hs

/-- **roomEarly.** -/
theorem roomEarly_at_head (Ld : Laid)
    (hs : FillP1.startB Zp (msgsOfChain Zp.made.proof.1) (At.N Zp cF).indexNo = true) :
    ∀ k a p m, Rch k a → a.1.2.failed = none → At.ps[k]? = some p → p.link = some m →
      p.piece < 2 → 0 < m → Johnson.Desc.First.Walk.Tied.roomIsB (At.foldD Zp cF Ld).free0
        (At.foldD Zp cF Ld).fvs m a.1.2 = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact P1L20.roomEarly_at_fill_below h.scope h.reads O (flat_ok h) (Rch := Rch)
    (at_ := fun a => a.1)
    (hRch_at OnBytes.secondHashFunction Zp Np cF Rch hR) hs

/-- **THE FIT, HELD BY LEAN**: FoldFacts at the head's letters: the five by the theorems above, the
other twenty-one fields as premises in the fields' own text. -/
theorem foldFacts_of_j1 (Ld : Laid)
    (hs : FillP1.startB Zp (msgsOfChain Zp.made.proof.1) (At.N Zp cF).indexNo = true)
    (bookInOrder' : ∀ k a, Rch k a → a.1.2.failed = none →
      K12.Door.atFirstBook (At.foldD Zp cF Ld).ft a.1.2 = true)
    (seatsCarried' : ∀ k a, Rch k a → a.1.2.failed = none →
      K12.Door.atFirstSeats (At.foldD Zp cF Ld).L a.1.2 = true)
    (bookFits' : ∀ k a, Rch k a → a.1.2.failed = none → K12.Door.atFirstFits a.1.2 = true)
    (msgShapes' : ∀ k a, Rch k a → a.1.2.failed = none →
      K12.Door.atFirstShapes (At.foldD Zp cF Ld).M a.1.2 = true)
    (pileMasks' : ∀ k a, Rch k a → a.1.2.failed = none → K13.pileMasksC a.1.2 = true)
    (pileWithin' : ∀ k a, Rch k a → a.1.2.failed = none → K13.pileWithinC a.1.2 = true)
    (oneRow' : ∀ k a, Rch k a → a.1.2.failed = none → K13.oneRowC a.1.2 = true)
    (codes' : ∀ k a, Rch k a → a.1.2.failed = none →
      a.1.2.st.codes = (At.foldD Zp cF Ld).sent.codes)
    (shape' : ∀ k a, Rch k a → a.1.2.failed = none →
      a.1.2.check.frame.shape = (At.foldD Zp cF Ld).sent.shape)
    (layout' : ∀ k a, Rch k a → a.1.2.failed = none →
      a.1.2.check.rows.layout = (At.foldD Zp cF Ld).sent.layout)
    (liveShape' : ∀ k a, Rch k a → a.1.2.failed = none →
      a.1.2.live.frame.shape = (At.foldD Zp cF Ld).sent.shape)
    (liveLayout' : ∀ k a, Rch k a → a.1.2.failed = none →
      a.1.2.live.rows.layout = (At.foldD Zp cF Ld).sent.layout)
    (groups' : ∀ k a, Rch k a → a.1.2.failed = none →
      a.1.2.check.frame.groups = reqGroups a.1.2.check.frame.shape)
    (liveGroups' : ∀ k a, Rch k a → a.1.2.failed = none →
      a.1.2.live.frame.groups = reqGroups a.1.2.live.frame.shape)
    (frameShape' : ∀ k a, Rch k a → a.1.2.failed = none →
      a.1.2.frame.shape = (At.foldD Zp cF Ld).sent.shape)
    (frameGroups' : ∀ k a, Rch k a → a.1.2.failed = none →
      a.1.2.frame.groups = reqGroups a.1.2.frame.shape)
    (ownIs' : ∀ k a p l, Rch k a → a.1.2.failed = none → At.ps[k]? = some p → p.kind = .K3 →
      p.link = some l → Look.OwnIs (At.foldD Zp cF Ld).sent l a.1.2)
    (groupIs' : ∀ k a p m L, Rch k a → a.1.2.failed = none → At.ps[k]? = some p → p.link = some m →
      a.1.2.link? = some L → L.check.group = (At.foldD Zp cF Ld).groupAt m
        ∧ L.check.frame.group = (At.foldD Zp cF Ld).groupAt m)
    (frameIs' : ∀ k a p m L, Rch k a → a.1.2.failed = none → At.ps[k]? = some p → p.link = some m →
      a.1.2.link? = some L →
      L.check.frame.moment = momentAt (shiftAt At.links m) p.piece ∧
        L.check.frame.own = (At.foldD Zp cF Ld).ownAt m (momentAt (shiftAt At.links m) p.piece) ∧
        L.check.frame.keptBefore = (At.foldD Zp cF Ld).keptAt m ∧
        (p.piece ≤ 11 + 2 * shiftAt At.links m →
          L.check.frame.link = m ∧ L.check.frame.next = .laterOrClose))
    (rowsSent' : ∀ k a, Rch k a → a.1.2.failed = none →
      ∀ o ∈ OnBytes.singleRowsOracles a.1.2.live.frame.rows, o < a.1.2.book.place.size)
    (replyNat' : ∀ k a, Rch k a → a.1.2.failed = none → ∀ g, a.1.2.out.reply = some g →
      OnBytes.Model.ofNat g.c0.toNat = g) :
    FoldFacts Rch (fun a => a.1) (At.foldD Zp cF Ld) At.reqW At.links At.ps where
  bookInOrder := bookInOrder'
  seatsCarried := seatsCarried'
  bookFits := bookFits'
  msgShapes := msgShapes'
  weightsOk := weightsOk_at_head h Rch hR
  pileMasks := pileMasks'
  pileWithin := pileWithin'
  oneRow := oneRow'
  tidy := tidy_at_head h Rch hR
  codes := codes'
  shape := shape'
  layout := layout'
  liveShape := liveShape'
  liveLayout := liveLayout'
  groups := groups'
  liveGroups := liveGroups'
  frameShape := frameShape'
  frameGroups := frameGroups'
  ownIs := ownIs'
  groupIs := groupIs'
  frameIs := frameIs'
  rowsSent := rowsSent'
  reqIs := reqIs_at_head h Rch hR
  replyNat := replyNat'
  room := room_at_head h Rch hR Ld hs
  roomEarly := roomEarly_at_head h Rch hR Ld hs

end

end P5J

#print axioms P5J.weightsOk_at_head
#print axioms P5J.reqIs_at_head
#print axioms P5J.tidy_at_head
#print axioms P5J.room_at_head
#print axioms P5J.roomEarly_at_head
#print axioms P5J.foldFacts_of_j1
