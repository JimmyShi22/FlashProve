-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/StandsAt.lean: the honest side of the kind "lookup"
(K3): behind the accepting step of the description's own member at a lookup on the calls, what was
heard meets the library's structure of end values at the step's own rounds (`Fo.HeardIs`,
OnBytes/Tie/Pv/Lookup/Port/FoHeard.lean): so it "stands for some rounds" (`K3Stands`,
Johnson/Top/H/K3RowOut.lean), without which the items of the lookup's row out say nothing. Theorems;
each is a call of a theorem of the library.

Terms. Honest/K3/GLOSSARY.md. In this file: the older text of the lookup's sub-protocol is
`K3.block` (Johnson/Desc/First/Look/K3Lookup.lean).

What is shown.
  `older_yes`: where the member accepts, the decision of the older text of the lookup's sub-protocol
    accepts on the same rounds, with the same state behind: the library's swap of the two texts, at
    the member.
  `heardIs_at`: what was heard meets the structure of end values at these very rounds, at every
    number lm.
  `stands_at`: hence it stands for some rounds.
  `heardIs_lay`: the sentence of `heardIs_at`, in the form in which the theorems on the layers' own
    kind take it: of the field fo and the ledger of a layers' link.

Hypotheses that remain.
  The hypotheses of `calls_state` (Honest/K3/Law/Thread/StateBehind.lean): `O`, `hs`, `hd`, `hb`,
    `hbs`, `hm`, `hmp`, `hpk`, `h`.
  `hfv`: the library's test `fitsVia` (Johnson/Desc/First/Look/Via/Via.lean) on the parameters
    accepts.
  `hok`: (from `heardIs_at` on) the rounds' words are below the prime (`okRoundsE`,
    Johnson/Top/H/K3LawKind.lean: what the fold asks of a whole view). At an accepting step on the
    thread `okRounds_moved` (Honest/K3/Law/Thread/OkPlayed.lean) shows it; that call is not made
    here.
  `hin`: (from `heardIs_at` on) the lookup's promise in front holds (`k3OnIn`,
    Johnson/Desc/First/Look/K3Borders.lean).

How the proof goes. The proofs call the library's `decide_mk`, `hearVia_hear`
(Johnson/Top/H/K3Via/Blocks.lean) and `k3DecideHears_calls` (Johnson/Top/H/K3DecideHearsAt.lean),
and `calls_state`. The library states the same law of the seated text itself
(`k3DecideHears_via_calls`, Johnson/Top/H/K3Via/DecideHearsVia.lean), under that sub-protocol's
whole test on the plan at its own letters; the way taken here asks `fitsVia` alone, which is a test
of `k3Tests` (Honest/K3/SeatFits.lean) by name.

Users. Honest/K3/Law/Thread/StandsBehind.lean imports this file; it says the like at either sort of
lookup.

Limits. Conditional on the hypotheses above. On the calls alone. No instance of these hypotheses is
exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.PutFo
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.Front
import Johnson.Top.H.K3Via.DecideHearsVia
import Johnson.Top.H.K3RowOut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Aff Fork Reading)
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn)
open VerifiableInference.Desc.K3 (seatCalls k3OnIn)
open VerifiableInference.Desc.K3.Law (hearVia fitsVia decide_mk hearVia_hear)
open VerifiableInference.OnPublicFiles (okRoundsE k3DecideHears_calls K3Stands)

local notation "FS" => VerifiableInference.Desc.First.S

section
variable (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub) (Bs : PureBase)
  (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat) (B : SecondSeat)
  (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site) (hs : s ∈ lookSites Z)
  (hd : s.digits = false) (lot m : Block FS ProofFile.Cl) (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀)
  (hbs : lot.place = s.at_.place) (hm : m ∈ ch.blocksInOrder) (hmp : m.place = lot.place)
  (hpk : m.planOk = true) (ft : Nat) (sj sj' : FS) (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn)
  (h : m.step ft sj rs c = .ok (sj', n)) (hfv : fitsVia s.p = true)

include O hs hd hb hbs hm hmp hpk h hfv

/-- **Where the member accepts, the decision of the older text of the sub-protocol accepts on the
same rounds, with the same state behind.** Conditional on the hypotheses of `calls_state`, and on
`fitsVia` accepting. -/
theorem older_yes (piece : Nat) (laid : Array Nat) (before : List (Nat × Nat))
    (guests : List (VerifiableInference.Desc.First.Look.Guest FS ProofFile.Cl))
    (gs : List (List (Nat × List UInt64))) :
    (VerifiableInference.Desc.K3.block (seatCalls K3Lot.ofForm) piece laid before s.p
      guests).decide sj rs gs = .ok sj' := by
  obtain ⟨F, H, G, a1, a2, a3, a4, a5, e, _⟩ := calls_state o pol lay KL Fd Z Bs base ch A B O s hs
    hd lot m hb hbs hm hmp hpk ft sj sj' n rs c h
  unfold fitsVia at hfv
  cases hp : s.p.shape with
  | none =>
    rw [hp] at hfv
    exact nomatch hfv
  | some sh =>
    rw [hp] at hfv
    have hf' : (VerifiableInference.Desc.K3.entriesFit (VerifiableInference.Desc.K3.faceOf sh)
        (s.p.entries.getD []) && (s.p.entries.getD []).all
          VerifiableInference.Desc.K3.staticT) = true := hfv
    rw [Bool.and_eq_true] at hf'
    rw [e]
    exact decide_mk ⟨a1, a2, a3, a4⟩ (hearVia_hear (fun h1 e1 => by
      obtain rfl : sh = h1 := Option.some.inj (hp.symm.trans e1)
      exact hf'.1) hf'.2 a5)

variable (hok : okRoundsE rs = true) (hin : k3OnIn s.p sj = true)

include hok hin

/-- **What was heard meets the library's structure of end values at the step's own rounds.**
Conditional on the hypotheses that the head of this file lists. No instance of these hypotheses is
exhibited in this file. -/
theorem heardIs_at (lm : Nat) :
    ∃ F' g, sj'.fork? = some F' ∧ sj'.lookHeard? = some g ∧
      _root_.Fo.HeardIs Reading.gl g F' (_root_.Fo.endsOf g.shape lm s.p.first
        (rs.map (_root_.Fo.rdRV Reading.gl))) := by
  obtain ⟨F, F', g, f1, f2, f3, _, f5⟩ := k3DecideHears_calls K3Lot.ofForm 0 #[] [] s.p []
    OnBytes.Slice.GE Reading.gl lm sj sj' rs [] hok
    (older_yes o pol lay KL Fd Z Bs base ch A B O s hs hd lot m hb hbs hm hmp hpk ft sj sj' n rs c h
      hfv 0 #[] [] [] [])
  obtain ⟨_, F₁, _, _, _, a4, a5, a6, a7⟩ := onIn_parts hin
  obtain ⟨b1, _, _⟩ := ledger_of a6 a7
  obtain rfl : F₁ = F := Option.some.inj (a4.symm.trans f1)
  refine ⟨F', g, f2, f3, ?_⟩
  rw [← a5]
  exact (f5 b1).2.2

/-- **Hence it stands for some rounds.** Conditional on the same hypotheses. -/
theorem stands_at (lm : Nat) :
    ∃ F' g, sj'.fork? = some F' ∧ sj'.lookHeard? = some g ∧
      K3Stands g.shape lm s.p.first Reading.gl g F' := by
  obtain ⟨F', g, f2, f3, hI⟩ := heardIs_at o pol lay KL Fd Z Bs base ch A B O s hs hd lot m hb hbs
    hm hmp hpk ft sj sj' n rs c h hfv hok hin lm
  exact ⟨F', g, f2, f3, _, hI⟩

/-- **In the form in which the theorems on the layers' own kind take it.** Conditional on the same
hypotheses. -/
theorem heardIs_lay (lm : Nat) :
    ∀ a fo, sj'.here = .lay a → a.fo = some fo →
      _root_.Fo.HeardIs Reading.gl fo a.F (_root_.Fo.endsOf fo.shape lm s.p.first
        (rs.map (_root_.Fo.rdRV Reading.gl))) := by
  intro a fo ha hfo
  obtain ⟨F', g, f2, f3, hI⟩ := heardIs_at o pol lay KL Fd Z Bs base ch A B O s hs hd lot m hb hbs
    hm hmp hpk ft sj sj' n rs c h hfv hok hin lm
  obtain ⟨_, H, G, _, _, _, hC, _⟩ := calls_here o pol lay KL Fd Z Bs base ch A B O s hs hd lot m hb
    hbs hm hmp hpk ft sj sj' n rs c h
  obtain ⟨e1, _⟩ := fo_of_here hC a ha
  rcases hC with ⟨a0, _, rfl⟩ | ⟨a0, _, rfl⟩ | ⟨a0, _, _, rfl⟩
  · obtain rfl : _ = a := VerifiableInference.Desc.First.Here.lay.inj ha
    obtain rfl : H = fo := Option.some.inj hfo
    obtain rfl : G = F' := Option.some.inj f2
    obtain rfl : H = g := Option.some.inj f3
    exact hI
  · exact nomatch ha
  · exact nomatch ha

end

#print axioms ProofFile.Honest.K3.Law.AtThr.older_yes
#print axioms ProofFile.Honest.K3.Law.AtThr.heardIs_at
#print axioms ProofFile.Honest.K3.Law.AtThr.stands_at
#print axioms ProofFile.Honest.K3.Law.AtThr.heardIs_lay

end ProofFile.Honest.K3.Law.AtThr
