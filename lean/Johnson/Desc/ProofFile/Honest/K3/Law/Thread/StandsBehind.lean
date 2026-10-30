-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/StandsBehind.lean: the honest side of the kind "lookup"
(K3): behind the accepting step of the description's own member at a lookup, on the calls or on the
digits, what the seat reads as heard meets the library's structure of end values at the step's own
rounds (`Fo.HeardIs`, OnBytes/Tie/Pv/Lookup/Port/FoHeard.lean), at the ledger that the seat reads
there: also behind the step without a round that the lot joins to the lookup. So it "stands for some
rounds" (`K3Stands`, Johnson/Top/H/K3RowOut.lean). Theorems, for either sort of lookup.

Terms. Honest/K3/GLOSSARY.md. In this file: the lookups' form is `FormAt`
(Honest/K3/Law/MemberOne.lean).

What is shown. Each at every number lm.
  `heardIs_form`: the title's sentence at a sub-protocol of the lookups' form, at either sort.
  `heardIs_member`: the same at the description's own member at a site.
  `stands_member`: hence what was heard stands for some rounds there.
To a later ledger: the library's own `heardIsLater` and `k3StandsLater`
(Johnson/Top/H/K3LeftLater.lean). Honest/K3/Law/Thread/StandsAt.lean says the like on the calls
alone.

Hypotheses that remain.
  `Fm`: the form; or, at the member:
  `O`: the description returns (`IM.Open`, Johnson/IMR/SeatOpen.lean).
  `hs`: s is a site of the public part (`lookSites Z`).
  `hb`, `hbs`: lot is one of the lookups' own sub-protocols (`(K3Lot.lot Z).blocks`); it stands at
    the site's place.
  `hm`, `hmp`, `hpk`: the member is in the first chain's flat list; it stands at that place; it
    passes its own test on the plan (planOk).
  `h`: the step accepts.
  `hfv`: the library's test `fitsVia` (Johnson/Desc/First/Look/Via/Via.lean) on the parameters
    accepts.
  `hok`: the rounds' words are below the prime (`okRoundsE`, Johnson/Top/H/K3LawKind.lean). At an
    accepting step on the thread `okRounds_moved` (Honest/K3/Law/Thread/OkPlayed.lean) shows it;
    that call is not made here.
  `hin`: the lookup's promise in front holds (`k3OnIn`, Johnson/Desc/First/Look/K3Borders.lean).

How the proof goes. The proofs call the library's `decide_mk`, `hearVia_hear`
(Johnson/Top/H/K3Via/Blocks.lean), `k3DecideHears_calls`, `k3DecideHears_digits`
(Johnson/Top/H/K3DecideHearsAt.lean), `heardIsLater` (Johnson/Top/H/K3LeftLater.lean) and
`later_planClaims` (Johnson/Desc/First/Look/K3DigitsKeeps.lean); and `form_state`
(Honest/K3/Law/Thread/StateBehind.lean) and `behind_hands` (Honest/K3/Law/BehindHands.lean).

Users. `lays_stands` (Honest/K3/Law/Thread/LaysStands.lean) and `stands_link`
(Honest/K3/Law/Thread/AtLink.lean) call `stands_member`.

Limits. Conditional on the hypotheses above. The statements speak of the state right behind the
member's step: that the members behind keep what was heard, and only add to the ledger, is for the
files on those members to show. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.StandsAt
import Johnson.Desc.ProofFile.Honest.K3.Law.BehindHands
import Johnson.Top.H.K3LeftLater
import Johnson.Desc.First.Look.K3DigitsKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Aff Fork Reading)
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn)
open VerifiableInference.Desc.K3 (k3OnIn)
open VerifiableInference.Desc.K3.Law (hearVia fitsVia decide_mk hearVia_hear)
open VerifiableInference.Desc.First.Look (P)
open VerifiableInference.OnPublicFiles (okRoundsE k3DecideHears_calls k3DecideHears_digits K3DecideHears
        K3Stands heardIsLater later_planClaims)

local notation "FS" => VerifiableInference.Desc.First.S

/-- **At a sub-protocol of the lookups' form, at either sort.** Conditional on the form, the
accepting step, `fitsVia`, the rounds' words, and the lookup's promise in front. -/
theorem heardIs_form {Cl : Type} {claim : Aff → Cl} {X : OnBytes.Model.Verify.Public} {i : Nat}
    {d : Bool} {p : P} {b : Block FS Cl} (Fm : FormAt claim X i d p b) (hfv : fitsVia p = true)
    (ft : Nat) (s t : FS) (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn)
    (h : b.step ft s rs c = .ok (t, n)) (hok : okRoundsE rs = true) (hin : k3OnIn p s = true)
    (lm : Nat) :
    ∃ F' g, (seatOf claim d).fork t = some F' ∧ (seatOf claim d).heard t = some g ∧
      _root_.Fo.HeardIs Reading.gl g F' (_root_.Fo.endsOf g.shape lm p.first
        (rs.map (_root_.Fo.rdRV Reading.gl))) := by
  obtain ⟨F, H, G, a1, a2, a3, a4, a5, hQ⟩ := form_state Fm ft s t n rs c h
  have hold : (VerifiableInference.Desc.K3.block (seatOf claim d) 0 #[] [] p []).decide s rs [] =
      .ok ((seatOf claim d).put s H G) := by
    unfold fitsVia at hfv
    cases hp : p.shape with
    | none =>
      rw [hp] at hfv
      exact nomatch hfv
    | some sh =>
      rw [hp] at hfv
      have hf' : (VerifiableInference.Desc.K3.entriesFit (VerifiableInference.Desc.K3.faceOf sh)
          (p.entries.getD []) && (p.entries.getD []).all
            VerifiableInference.Desc.K3.staticT) = true := hfv
      rw [Bool.and_eq_true] at hf'
      exact decide_mk ⟨a1, a2, a3, a4⟩ (hearVia_hear (fun h1 e1 => by
        obtain rfl : sh = h1 := Option.some.inj (hp.symm.trans e1)
        exact hf'.1) hf'.2 a5)
  have law : K3DecideHears (seatOf claim d).fork (seatOf claim d).heard p.calls p.pub p.lid
      (VerifiableInference.Desc.K3.block (seatOf claim d) 0 #[] [] p []).decide := by
    cases d with
    | false => exact k3DecideHears_calls claim 0 #[] [] p []
    | true => exact k3DecideHears_digits claim 0 #[] [] p []
  obtain ⟨F0, F1, g, f1, f2, f3, _, f5⟩ := law OnBytes.Slice.GE Reading.gl lm s _ rs [] hok hold
  obtain rfl : F0 = F := Option.some.inj (f1.symm.trans a1)
  obtain ⟨_, F₁, _, _, _, b4, b5, b6, b7⟩ := onIn_parts hin
  obtain ⟨c1, _, _⟩ := ledger_of b6 b7
  have a1' : s.fork? = some F0 := by cases d <;> exact a1
  obtain rfl : F₁ = F0 := Option.some.inj (b4.symm.trans a1')
  obtain ⟨k1, cl, k2⟩ := behind_hands claim hQ f2
  refine ⟨_, g, k2, k1.trans f3, ?_⟩
  rw [← b5]
  exact heardIsLater OnBytes.Slice.GE Reading.gl g F1 _ _ (later_planClaims F1 cl) (f5 c1).2.2

section
variable (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub) (Bs : PureBase)
  (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat) (B : SecondSeat)
  (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site) (hs : s ∈ lookSites Z)
  (lot m : Block FS ProofFile.Cl) (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀)
  (hbs : lot.place = s.at_.place) (hm : m ∈ ch.blocksInOrder) (hmp : m.place = lot.place)
  (hpk : m.planOk = true) (ft : Nat) (sj sj' : FS) (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn)
  (h : m.step ft sj rs c = .ok (sj', n)) (hfv : fitsVia s.p = true)
  (hok : okRoundsE rs = true) (hin : k3OnIn s.p sj = true)

include O hs hb hbs hm hmp hpk h hfv hok hin

/-- **At the description's own member at a site, of either sort.** Conditional on the hypotheses
that the head of this file lists. No instance of these hypotheses is exhibited in this file. -/
theorem heardIs_member (lm : Nat) :
    ∃ F' g, (seatOf K3Lot.ofForm s.digits).fork sj' = some F' ∧
      (seatOf K3Lot.ofForm s.digits).heard sj' = some g ∧
      _root_.Fo.HeardIs Reading.gl g F' (_root_.Fo.endsOf g.shape lm s.p.first
        (rs.map (_root_.Fo.rdRV Reading.gl))) := by
  obtain ⟨Fm, _⟩ := site_block o pol lay KL Fd Z Bs base ch A B O s hs lot m hb hbs hm hmp hpk
  obtain ⟨_, _, _, _, hst⟩ := memberAtSite o pol lay KL Fd Z Bs base ch A B O lot hb m hm hmp
  exact heardIs_form Fm hfv ft sj sj' n rs c ((hst ft sj sj' n rs c).1 h).1 hok hin lm

/-- **Hence what was heard stands for some rounds there.** Conditional on the same hypotheses. -/
theorem stands_member (lm : Nat) :
    ∃ F' g, (seatOf K3Lot.ofForm s.digits).fork sj' = some F' ∧
      (seatOf K3Lot.ofForm s.digits).heard sj' = some g ∧
      K3Stands g.shape lm s.p.first Reading.gl g F' := by
  obtain ⟨F', g, f2, f3, hI⟩ := heardIs_member o pol lay KL Fd Z Bs base ch A B O s hs lot m hb hbs
    hm hmp hpk ft sj sj' n rs c h hfv hok hin lm
  exact ⟨F', g, f2, f3, _, hI⟩

end

#print axioms ProofFile.Honest.K3.Law.AtThr.heardIs_form
#print axioms ProofFile.Honest.K3.Law.AtThr.heardIs_member
#print axioms ProofFile.Honest.K3.Law.AtThr.stands_member

end ProofFile.Honest.K3.Law.AtThr
