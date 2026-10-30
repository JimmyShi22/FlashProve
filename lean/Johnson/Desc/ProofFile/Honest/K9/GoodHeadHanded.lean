-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/GoodHeadHanded.lean: "GOOD" (`goodW`, Honest/K9/GateArms.lean) AT THE STATE THAT THE
FRAME's FIELD HANDS IN FRONT OF THE OUTPUT HEAD's SEGMENT's BATCHING, FROM THE SILENCE OF THE LISTED MARKS AND ONE
SENTENCE ON THAT STATE. A joining of other houses' lemmas with ours; statements and proofs; no definition; no goal is
stated.
  `readers_head_form` whatever readers the lot lays at segment 24 (`K3Lot.readersAt X 24`) are the output head's
      caller's, at some number: by the lot's text alone
  **`goodW_head_handed_of_k6`** under the head · hB · the lookups' marks (`k3Marks Zp G₀`), the
      smallness test's (`P1K8.part1Marks Zp Bs.G₀`) and the fit's among the marks asked · the walk's premises at A.length = 347 · K9's
      seat at 24 · **hK: `K6GoodAt … 1995 2168 s'`** (the invariant of the output head's own rounds,
      Honest/K6/GoodLaw/Runs.lean, AT THE STATE HANDED): `goodW p ‹the segment's gatherer› s' w.2.2.filled`: THE END OF
      THE PREMISE hPr24 OF `k9_fallDebt_form_head_with` (Honest/K9/FallFormHeadWith.lean), to the sign. HOW:
      `goodW_head_nums` at Kp := `K6GoodAt … 1995 2168`, its eight premises by that sub-protocol's own lemmas:
      `good_across_draw` · `k6GoodAt_of_frontLater` at the sealed `all_runs_at_head` · `own_live_at_head` ·
      `own_plain_at_head` · `own_unnamed_at_head` · `callerKeys_slotsIn` · `callerBits_noSlot` · `callerPins_noSlot`
      (through the lookups' `keysClear_of_slotsIn` · `bitsClear_of_none` · `pinsClear_of_none`) · JC | JD:
      `P1K8.headClauses_handed` · `MergeLive`: `mergeLive_handed` · sv + 1 = 2168: `sV_of_good`
WHAT IS NOT CLAIMED. **hK IS A PREMISE HERE**: Honest/K9/K6GoodHanded.lean (`k6Good_handed`) has it at the walk from the
silence of listed marks, and GoodHeadHandedMarks.lean lays it in. THAT hK HOLDS AT ANY STATE IS SHOWN NOWHERE. hPr24 at
any Pr. (For a condition that is paid at the frame's field the smallness test has the link from the field to the
walk's premises; it is not called here.) That any walk returns.
ARGUED, STATED IN NO THEOREM: AT A FILLING WITH NO SIDE OF THE CLOSING (K10), AS `widerFillAt` (`k10_ten`,
Honest/K10/AtFill.lean), NO STEP IS TAKEN BEHIND NUMBER 12; THE PREMISES HERE STAND AT 347: AT SUCH A FILLING THE
THEOREM SPEAKS OF NOTHING. At the shipped filling (onlineFilling), which has the closings, nothing here
shows the premises met. NO MEMBER. K9's BOUND AT THIS SEGMENT IS EXCHANGED BY THIS, NOT PAID. IT STANDS OVER MANY FILES
OF OTHER HOUSES THAT ARE NO PART OF THE SEALED LIBRARY (laws.11): Honest/K6/GoodLaw/ · the lookups' Honest/K3/Good/ ·
Honest/K11/Mark/ · Johnson/Desc/K11/Front/ and Live/ · Johnson/Desc/K8/Honest/ · Johnson/P1K8R/ · the frame's Honest/Law/,
and all that these import. u is a letter, read by nothing in the conclusion. Called by Honest/K9/GoodHeadHandedMarks.lean
alone. At the full size and the format's second hash function alone, as h. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.GoodHeadNums
import Johnson.Desc.ProofFile.Honest.K9.MergeLiveHanded
import Johnson.P1K8R.ClausesAtLinks
import Johnson.P1K9R.AreadyClosed
import Johnson.Desc.ProofFile.Honest.K6.GoodLaw.Rides.Members
import Johnson.Desc.ProofFile.Honest.K6.GoodLaw.Rides.OwnShares
import Johnson.Desc.ProofFile.Honest.K6.GoodLaw.Rides.Draw
import Johnson.Desc.ProofFile.Honest.K6.GoodLaw.CallerSlots
import Johnson.Desc.ProofFile.Honest.K6.GoodLaw.Window

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin VerifiableInference.Desc.K9L VerifiableInference.Desc.PhiAll
open ProofFile.Honest (Lay Mid Step walk Mark marksQuiet drawsFit)
open ProofFile.Honest.K3.Good (k3Marks)
open ProofFile.Honest.K3.Good.Live (keysClear_of_slotsIn bitsClear_of_none pinsClear_of_none)
open ProofFile.Honest.K6.GoodLaw (K6GoodAt k6GoodAt_of_frontLater good_across_draw own_live_at_head own_plain_at_head
  own_unnamed_at_head callerKeys_slotsIn callerBits_noSlot callerPins_noSlot sV_of_good)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {W Y : Type}

/-- **Whatever readers the lot lays at segment 24 are the output head's caller's**, at some number. -/
theorem readers_head_form {X : Verify.Public} {rd : Desc.K3.Readers S} (h : K3Lot.readersAt X 24 = some rd) :
    ∃ iU3, rd = Kinds.Head.callerReaders (Kinds.Head.planesAt iU3) := by
  unfold K3Lot.readersAt at h
  by_cases hH : Desc.K3.isHead X 24 = true
  · simp only [hH, if_true] at h
    obtain ⟨i, -, e⟩ := Option.map_eq_some_iff.1 h
    exact ⟨i, e.symm⟩
  · exfalso
    have hH' : Desc.K3.isHead X 24 = false := by simpa using hH
    cases hp : X.p4 <;> simp [hH', hp] at h

/-- **"GOOD" AT THE STATE THAT THE FRAME's FIELD HANDS IN FRONT OF THE HEAD's SEGMENT's BATCHING, FROM THE SILENCE OF
THE LISTED MARKS AND ONE SENTENCE ON THE STATE**: `hK`: the output head's own rounds' invariant stands at that state. -/
theorem goodW_head_handed_of_k6 (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (G₀ : ProofFile.Ground) (ms : List Mark)
    (hsub : ∀ mk ∈ k3Marks Zp G₀, mk ∈ ms) (hsub1 : ∀ mk ∈ P1K8.part1Marks Zp Bs.G₀, mk ∈ ms)
    {A t : List (Block S ProofFile.Cl)} {b : Block S ProofFile.Cl} (hall : cF.blocksInOrder = A ++ b :: t)
    (hfit : ∀ d ∈ A, (⟨d.place,
      fun _ own => if drawsFit d.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ : Mark) ∈ ms)
    (hA : A.length = 347) (hpos : 0 < b.rounds.length)
    (L : Lay) (hft : L.firstTree = 0) {a₀ z : ProofFile.Honest.ChainProgress S ProofFile.Cl W Y} {zp : ProofFile.InstPub} {s' : S}
    {m₀ : Option (Mid W Y)} {ss : List (Step W Y)} {fr : List Fmt.Drawn}
    (hm : m₀.isSome = true)
    (ha : ProofFile.Honest.ChainProgress.start L cF.blocksInOrder m₀ (some (ProofFile.startS Zp zp)) [] = .ok a₀)
    (hn : fr.length = (A.flatMap (·.rounds)).length) (hq : marksQuiet ms A [] fr = true)
    (hz : walk L ss fr a₀ = .ok z) (hv : z.ver = some s')
    {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (Sd : SeatedFree cF Zp 24 kk Lk p w) (u : HTailF2)
    (hK : K6GoodAt (P5J.At.X Zp).hS (Kinds.Head.Law.readsOf (P5J.At.X Zp))
      (Kinds.Head.parOf (P5J.At.X Zp).hS (Kinds.Head.Law.workOf (P5J.At.X Zp))) 1995 2168 s') :
    goodW p (claimsInBy Lk.each Lk.hear Lk.order) s' w.2.2.filled := by
  obtain ⟨pC, pD, hC, hD⟩ := P1K9.bothPlaces_at_head h 24 (by omega)
  obtain ⟨JC, JD⟩ := P1K8.headClauses_handed h G₀ hC hD ms hsub hall hfit hA hpos L hft hm ha hn hq hz hv
  obtain ⟨a', xh, hsa, hxa, hML⟩ := mergeLive_handed h hB ms hsub1 hall hfit hA hpos L hft hm ha hn hq hz hv
  have esv : xh.sV + 1 = 2168 := sV_of_good _ _ _ hK a' xh hsa hxa
  exact goodW_head_nums h Sd u hC hD
    (K6GoodAt (P5J.At.X Zp).hS (Kinds.Head.Law.readsOf (P5J.At.X Zp))
      (Kinds.Head.parOf (P5J.At.X Zp).hS (Kinds.Head.Law.workOf (P5J.At.X Zp))) 1995 2168)
    (fun t y t₁ hd k => good_across_draw p t t₁ y hd k)
    (fun o ho run hr m t z k hz' =>
      k6GoodAt_of_frontLater (Kinds.Head.Law.Five.all_runs_at_head h Sd.link o ho run hr m t z hz') k)
    (fun j h1 h2 => own_live_at_head h Sd.link 1995 2168 j h1 h2)
    (own_plain_at_head h Sd.link)
    (fun j hj => own_unnamed_at_head h Sd.link 1995 2168 j hj)
    (fun t k j hj => keysClear_of_slotsIn _ t (callerKeys_slotsIn _ _ _ 1995 2168 t k) (Or.inl hj))
    (fun rd hrd t j => by
      obtain ⟨i, rfl⟩ := readers_head_form hrd
      exact bitsClear_of_none _ t (callerBits_noSlot i t) j)
    (fun rd hrd t j => by
      obtain ⟨i, rfl⟩ := readers_head_form hrd
      exact pinsClear_of_none _ t (callerPins_noSlot i t) j)
    esv s' hML hK JC JD

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.readers_head_form
#print axioms ProofFile.Honest.K9.goodW_head_handed_of_k6
