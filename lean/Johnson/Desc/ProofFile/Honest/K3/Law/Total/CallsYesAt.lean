-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Total/CallsYesAt.lean: the kind "lookup" (K3). Conditional:
three bridges from what the library's `IM.MadeOwed` gives (Johnson/IMR/MadeOwed.lean: "the debt of a
kind's authors at one of its places") to the hypotheses of Honest/K3/Law/Total/CallsBehindAll.lean,
at the lookup on a link's calls. In the goals' scope, wherever the proof file's description returns
(`IM.Open`, Johnson/IMR/SeatOpen.lean). Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: the lookup on the calls of link l stands at the number
`k3K l false` of the flat list (Johnson/Desc/First/Look/K3Base.lean). The step's acceptance alone
from s to s' is `IM.Yes 0 b s s'` (Johnson/IMR/HandsDef.lean). A public test is open or tied in
front of border k if it is in `frontAtK mgMore k`, and behind if it is in `behindAtK mgMore k p`
(Johnson/Desc/Sound/MgAt/K3CallsTable.lean).

What is shown.
  `calls_hd_of_yes`: the acceptance alone of the step of the first chain's member at the calls'
    number is an acceptance of the decision of `K3.block` (Johnson/Desc/First/Look/K3Lookup.lean) at the
    place's own parameters, at some rounds, whatever their words; and the address's piece is the
    public structure's.
  `front_of_xk`: the debt's test in front (`IM.XK`, HandsDef.lean, at the public items' test
    `IM.EAt`, MadeOwed.lean) holds every public test that is open or tied in front.
  `behind_of_made`: what the debt asks behind is among what stands open or tied behind: the debt's
    filter "does not ride" is dropped.
The statements speak of no thread, prover, coin or string.

Hypotheses that remain.
  `hS`, `hR`, `O`, `hF`: (in `calls_hd_of_yes`) the goals' scope (`VerifierAndGoals.InScope`); the reading of
    the files (`VerifierAndGoals.readFiles`); the return of the description; the description's test on the
    plan.
  `hl`, `hb`, `hy`: (there) the link is below 25; b is the member at the number; the acceptance
    alone of its step from s to s'.
  `hx`: (in `front_of_xk`) the debt's test holds at s.
  `hq`: (in `behind_of_made`) q is one of the items that the debt asks (`Meaning.Ride.madeAtK`).

Imported. Files of the library alone. MadeOwed.lean imports a module under Johnson/Goal/
(Johnson/Goal/Meaning/QuietRide.lean), and the statement of `behind_of_made` names a definition of
that module (`Meaning.Ride.madeAtK`). No module of that folder is imported here directly.

How the proof goes. By calls of the library's own lemmas alone. The first bridge: at all 25 links
the chain's member is the kind's own sub-protocol at its address, laid alone (`IM.k3_of`,
Johnson/IMR/K3Seat.lean); member number j of a link's hearing is number 14 l + 2 + j of the flat
list (`hear_flat`, Johnson/IMR/FrameAt.lean; `hear_flat24`, Johnson/IMR/FrameAll.lean); a step's
acceptance is the decision's (`step_ok_iff`, Johnson/Desc/Sound/RunIsDecide.lean); the acceptance of
the sub-protocol that is laid alone is the kind's own (`IM.k3_yes`, K3Seat.lean); its test on the
plan follows from the description's (`IM.blocksOk_of_planOk`, Johnson/IMR/PlanOkFlat.lean); and the
stated sub-protocol's acceptance is that of `K3.block` (`theStated_yes_calls`,
Johnson/Desc/First/Link/Law/K4AtFront.lean). The two others: the written lists are the full ones
(`IM.linksW_full`, `IM.placesW_full`, Johnson/IMR/K8Owed.lean); the two closed lists of extra public
tests are one by their texts.

Users. `madeOwed_calls_lay` and `madeOwed_calls_att` (Honest/K3/Law/Total/MadeOwedCalls.lean)
combine these bridges with CallsBehindAll.lean. What whoever combines the two must mind: the first
bridge speaks of the public structure Bs.G₀.W, that file of the X of the composed meaning's data. In
the two others the public test is the library's `pubAll` (Johnson/Desc/First/PubAll.lean) at the
letters D and base, in that file the composed meaning's field pub; by the library the two are one by
`rfl` at D := the data's pubD and base := the pub of the meaning beneath. The first bridge's
parameters P' are that file's `P.ofPlace … x` where the public structure has the place x (`placeAt`,
Johnson/Desc/First/Look/LookKind.lean, unfolds). The debt's list stands at `IM.keepsAt p`
(MadeOwed.lean); the third bridge is general in that list.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
In particular no state is exhibited at which a member's step accepts. At the full size alone.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.IMR.MadeOwed
import Johnson.IMR.K8Owed
import Johnson.IMR.K3Seat
import Johnson.IMR.FrameAt
import Johnson.IMR.FrameAll
import Johnson.IMR.PlanOkFlat
import Johnson.IMR.EndFivePaid
import Johnson.P5K3R.SitsRounds
import Johnson.Desc.Sound.RunIsDecide
import Johnson.Desc.Sound.MoreAll
import Johnson.Desc.Sound.MgAt.K3CallsTable
import Johnson.Desc.First.Look.K3Base
import Johnson.Desc.First.Link.Law.K4AtFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Total
open VerifiableInference VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block Chain FileDescription Place)
open VerifiableInference.Desc.First (S PubData Numbers Rdr pubAll ePubAt_mem)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.Sound (moreAll mgMore)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The acceptance alone of the step of the chain's member at the calls' number is an acceptance
of the decision of `K3.block`.** Conditional on the goals' scope, the reading of the files, the
return of the description, its test on the plan, b being the member at the number, and the
acceptance of its step from s to s'. No instance of these hypotheses is exhibited in this file.
sent, laid, rs and gs are bound by "∃" and held by what functions return at them alone: some values:
not said to be the step's own. -/
theorem calls_hd_of_yes (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hF : F.planOk = true) {l : ℕ}
    (hl : l < 25) {b : Block S ProofFile.Cl} (hb : c.blocksInOrder[k3K l false]? = some b) {s s' : S}
    (hy : IM.Yes 0 b s s') :
    (IM.k3Place l false).piece = Desc.K3.pieceAt Bs.G₀.W l false ∧
      ∃ P' sent laid rs gs, placeAt Bs.G₀.W l false = some P' ∧
        (Desc.K3.block (Desc.K3.seatCalls K3Lot.ofForm) (IM.k3Place l false).piece laid sent P'
          []).decide s rs gs = .ok s' := by
  obtain ⟨Lk, b0, b', e1, e2, hat, hla⟩ := IM.k3_of hS hR O l hl false
  have hbb : b0 = b := by
    by_cases h24 : l = 24
    · subst h24
      obtain ⟨Lk', e1', -, hj⟩ := Meaning.K2.hear_flat24 hS hR O
      obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
      obtain ⟨b1, f1, f2⟩ := hj 2 (by decide)
      have g1 : b0 = b1 := Option.some.inj (e2.symm.trans f1)
      exact g1.trans (Option.some.inj (f2.symm.trans hb))
    · obtain ⟨Lk', e1', hj⟩ := Meaning.K2.hear_flat hS hR O (l := l) (by omega)
      obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
      obtain ⟨b1, f1, f2⟩ := hj 1 (by decide)
      have hix : IM.k3Ix l false = 1 := by
        show (if false = true then 6 else 1) + (if l = 24 then 1 else 0) = 1
        rw [if_neg h24]
        rfl
      have hk : k3K l false = 14 * l + 2 + 1 := by
        show 14 * l + IM.k3Ix l false + 2 = _
        rw [hix]
      rw [hix] at e2
      rw [hk] at hb
      have g1 : b0 = b1 := Option.some.inj (e2.symm.trans f1)
      exact g1.trans (Option.some.inj (f2.symm.trans hb))
  subst hbb
  obtain ⟨rs, cols, n, hst⟩ := hy
  have hd0 := ((Desc.Sound.step_ok_iff 0 b0 s s' rs cols n).1 hst).2.2.2
  obtain ⟨hd1, -, -⟩ := (IM.k3_yes hla s s' _ _).1 hd0
  have hOkb : b0.planOk = true :=
    Meaning.K2.planOk_of_blocksOk (IM.blocksOk_of_planOk O hF) b0 (List.mem_of_getElem? hb)
  have hOk' : b'.planOk = true := by
    rw [← IM.alone_planOk hla]
    exact hOkb
  obtain ⟨hpcX, -⟩ := K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt Bs.G₀.W) Bs.G₀.W Z.first.codes
    Z.first.shape l false b' hat
  obtain ⟨P', sent, laid, n', gs', hP, hyes⟩ := Desc.LinkJoin.theStated_yes_calls K3Lot.ofForm
    (K3Lot.readersAt Bs.G₀.W) Bs.G₀.W Z.first.codes Z.first.shape (IM.k3Place l false) b' hat hOk' l
    rfl hpcX s s' _ _ hd1
  exact ⟨hpcX, P', sent, laid, _, gs', hP, hyes⟩

end

/-- **The debt's test in front holds every public test that is open or tied in front.** Conditional
on that test at s. No instance of these hypotheses is exhibited in this file. -/
theorem front_of_xk {Q : Type} (N : Numbers) (D : PubData)
    (base : Desc.First.Pub → Q × S → Bool) (z : Q) (k : ℕ) (s : S)
    (hx : IM.XK N IM.linksW IM.placesW (IM.EAt D base IM.linksW IM.placesW z) k s = true) :
    ∀ q ∈ frontAtK mgMore k, pubAll D base q (z, s) = true := by
  intro q hq
  have h5 := (IM.xk_parts hx).2.2.2.2
  unfold IM.EAt at h5
  rw [IM.linksW_full, IM.placesW_full] at h5
  exact ePubAt_mem (pubAll D base) moreAll _ _ k (z, s) h5 q (List.mem_append.1 hq)

/-- **What the debt asks behind stands open or tied behind.** Conditional on the item being one of
the debt's. No instance of these hypotheses is exhibited in this file. -/
theorem behind_of_made (D : PubData) (keeps : List Rdr) (k : ℕ) (p : Place)
    (q : Desc.First.Pub)
    (hq : q ∈ Meaning.Ride.madeAtK D keeps moreAll IM.linksW IM.placesW k p) :
    q ∈ behindAtK mgMore k p := by
  unfold Meaning.Ride.madeAtK at hq
  have h1 := (List.mem_filter.1 hq).1
  rw [IM.linksW_full, IM.placesW_full] at h1
  exact h1

end ProofFile.Honest.K3.Law.Total

#print axioms ProofFile.Honest.K3.Law.Total.calls_hd_of_yes
#print axioms ProofFile.Honest.K3.Law.Total.front_of_xk
#print axioms ProofFile.Honest.K3.Law.Total.behind_of_made
