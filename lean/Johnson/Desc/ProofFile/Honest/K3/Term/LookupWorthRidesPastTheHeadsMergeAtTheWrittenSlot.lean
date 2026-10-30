-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AT `lettersHead`'s THREAD (Honest/Thread/FirstHead.lean), under the library's hypothesis
`P5J.AtMgA`: the prover H, the Script Q, the rider Rd, the clauses of keeps Kp, the clause Said and
the thread's other letters are variables.
Johnson/Desc/ProofFile/Honest/K3/Term/LookupWorthRidesPastTheHeadsMergeAtTheWrittenSlot.lean: the
honest side of the kind "lookup" (K3): the law of
Honest/K3/Term/LookupWorthRidesPastTheHeadsMerge.lean (worth 24 8 "planes" and worth 24 8 "keys"
pass over the member number 346), with its hypothesis on the public data paid and its hypothesis
on the rider in two forms that name no place of the public data by a letter: at the written number
2168, and at the first slot of whatever place the public data hold. Theorems, conditional; no
definition.

What is shown.
  `firstSlotOfTheDigitsPlaceIsThePublicPlaces`   where `digAt` holds a place x at a link, the
      first slot of the parameters that `placeAt` holds there on the digits is x.F.next. Public
      data alone.
  `headsDigitsFirstSlotAtThePublicPlaceIs2168`   under `P5J.AtMgA`: the parameters that `placeAt`
      holds at link 24 on the digits have the first slot 2168
  `headsDigitsFirstSlotIs2168`   under `P5J.AtMgA`: the place that `digAt` holds at link 24 has
      F.next = 2168
  `lookupWorthRidesPastTheHeadsMergeAtTheWrittenSlot`   the law, from the rider's clause at 2168
  `lookupWorthRidesPastTheHeadsMergeAtThePublicPlace`   the law, from the rider's clause at the
      first slot of every place that `placeAt` holds at link 24 on the digits
  `borderOfTheHeadsDigitsIs345`   the library's number of the border in front of the head's lookup
      on the digits (`borderOf`, Johnson/Desc/Sound/MgAt/K3Open.lean) is 345

Hypotheses that remain, in the two laws. `P5J.AtMgA`.
  keepsLeavesTheTailAndExtendsTheLedger: what the clause of keeps of the member number 346 gives.
    For the files on that member to show.
  riderHoldsThatTheHeardRecordStands: the rider at 346 holds that what the lookup on the digits has
    heard stands for some rounds (`StandsHere`, Honest/K3/Law/Thread/LaysStands.lean), at the number
    5 and at the first slot named above.

Limits. Nothing here shows that a thread's rider has such a clause, nor that the member's keeps
gives what is asked. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupWorthRidesPastTheHeadsMerge
import Johnson.Desc.Kinds.Law.K6PubInScope
import Johnson.Desc.Sound.MgAt.K3Open
import Johnson.P5T.DigAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open OnBytes.Model (HTailF2)
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.First.Look (digAt placeAt)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (digits_place)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead WtF Script)
open ProofFile.Honest.K3.Law.AtThr (StandsHere)

local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place
local notation "ParametersL" => VerifiableInference.Desc.First.Look.P

/-! ## 1 The first slot -/

/-- **Where `digAt` holds a place at a link, the first slot of the parameters that `placeAt` holds
there on the digits is that place's next free slot.** -/
theorem firstSlotOfTheDigitsPlaceIsThePublicPlaces {X : OnBytes.Model.Verify.Public} {link : Nat}
    {digitsPlace : PlaceL} {tl : HTailF2}
    (publicDataHoldTheDigitsPlace : digAt X link = some (digitsPlace, tl)) {p : ParametersL}
    (publicDataHoldTheParameters : placeAt X link true = some p) :
    p.first = digitsPlace.F.next := by
  unfold digAt at publicDataHoldTheDigitsPlace
  obtain ⟨x', placeRead, rest⟩ := Option.bind_eq_some_iff.1 publicDataHoldTheDigitsPlace
  obtain ⟨tl', -, rest⟩ := Option.bind_eq_some_iff.1 rest
  obtain ⟨shape, -, rest⟩ := Option.map_eq_some_iff.1 rest
  obtain ⟨rfl, -⟩ := Prod.mk.inj rest
  unfold placeAt at publicDataHoldTheParameters
  rw [placeRead] at publicDataHoldTheParameters
  obtain rfl := Option.some.inj publicDataHoldTheParameters
  rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : PlaceL}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

include h in
/-- **Under `P5J.AtMgA` the parameters at link 24 on the digits have the first slot 2168.** -/
theorem headsDigitsFirstSlotAtThePublicPlaceIs2168 {p : ParametersL}
    (publicDataHoldTheParameters : placeAt Zp.p.X 24 true = some p) : p.first = 2168 := by
  obtain ⟨p', placeRead, -, firstIs⟩ :=
    digits_place h.toAtMg.scope h.toAtMg.reads h.toAtMg.pubOne
  have placeRead' : placeAt Zp.p.X 24 true = some p' := placeRead
  obtain rfl : p' = p := Option.some.inj (placeRead'.symm.trans publicDataHoldTheParameters)
  exact firstIs

include h in
/-- **Under `P5J.AtMgA` the place that `digAt` holds at link 24 has the next free slot 2168.** -/
theorem headsDigitsFirstSlotIs2168 {digitsPlace : PlaceL} {tl : HTailF2}
    (publicDataHoldTheDigitsPlace : digAt Zp.p.X 24 = some (digitsPlace, tl)) :
    digitsPlace.F.next = 2168 := by
  obtain ⟨p, placeRead, -, firstIs⟩ :=
    digits_place h.toAtMg.scope h.toAtMg.reads h.toAtMg.pubOne
  have placeRead' : placeAt Zp.p.X 24 true = some p := placeRead
  rw [← firstSlotOfTheDigitsPlaceIsThePublicPlaces publicDataHoldTheDigitsPlace placeRead']
  exact firstIs

/-! ## 2 The law -/

variable {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

local notation "LH" => lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w

/-- **CONDITIONAL ON `P5J.AtMgA` and on two hypotheses more: worth 24 8 "planes" and worth 24 8
"keys" pass over the member number 346**: from the rider's clause at the written slot 2168. No
instance of these hypotheses is exhibited in this file. -/
theorem lookupWorthRidesPastTheHeadsMergeAtTheWrittenSlot
    (keepsLeavesTheTailAndExtendsTheLedger : ∀ s s', (LH).thread.keeps 346 s s' →
      s'.tl? = s.tl? ∧ ∀ F, s.fork? = some F → ∃ F', s'.fork? = some F' ∧ _root_.Fo.Later F F')
    (riderHoldsThatTheHeardRecordStands : ∀ v s, (LH).thread.rides 346 v s →
      StandsHere true 5 2168 s)
    {what : String} (whatIsPlanesOrKeys : what = "planes" ∨ what = "keys") :
    RidesPastAtS (LH).thread Said 346 (Item.worth 24 8 what) := by
  obtain ⟨digitsPlace, tl, publicDataHoldTheDigitsPlace, -⟩ :=
    h.k9_dig 24 (by decide) (fun _ => 0)
  refine lookupWorthRidesPastTheHeadsMerge h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
    publicDataHoldTheDigitsPlace keepsLeavesTheTailAndExtendsTheLedger (fun v s rider => ?_)
    whatIsPlanesOrKeys
  rw [headsDigitsFirstSlotIs2168 h publicDataHoldTheDigitsPlace]
  exact riderHoldsThatTheHeardRecordStands v s rider

/-- **The same from the rider's clause at the first slot of every place that the public data hold at
link 24 on the digits.** CONDITIONAL ON `P5J.AtMgA` and on two hypotheses more. No instance of these
hypotheses is exhibited in this file. -/
theorem lookupWorthRidesPastTheHeadsMergeAtThePublicPlace
    (keepsLeavesTheTailAndExtendsTheLedger : ∀ s s', (LH).thread.keeps 346 s s' →
      s'.tl? = s.tl? ∧ ∀ F, s.fork? = some F → ∃ F', s'.fork? = some F' ∧ _root_.Fo.Later F F')
    (riderHoldsThatTheHeardRecordStands : ∀ v s, (LH).thread.rides 346 v s →
      ∀ p, placeAt Zp.p.X 24 true = some p → StandsHere true 5 p.first s)
    {what : String} (whatIsPlanesOrKeys : what = "planes" ∨ what = "keys") :
    RidesPastAtS (LH).thread Said 346 (Item.worth 24 8 what) := by
  obtain ⟨p, placeRead, -, firstIs⟩ :=
    digits_place h.toAtMg.scope h.toAtMg.reads h.toAtMg.pubOne
  have placeRead' : placeAt Zp.p.X 24 true = some p := placeRead
  refine lookupWorthRidesPastTheHeadsMergeAtTheWrittenSlot h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp
    w Said keepsLeavesTheTailAndExtendsTheLedger (fun v s rider => ?_) whatIsPlanesOrKeys
  rw [← firstIs]
  exact riderHoldsThatTheHeardRecordStands v s rider p placeRead'

/-! ## 3 The border's number -/

/-- The library's number of the border in front of the head's lookup on the digits. -/
theorem borderOfTheHeadsDigitsIs345 : borderOf 24 true = 345 := by decide

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.firstSlotOfTheDigitsPlaceIsThePublicPlaces
#print axioms ProofFile.Honest.K3.Term.headsDigitsFirstSlotAtThePublicPlaceIs2168
#print axioms ProofFile.Honest.K3.Term.headsDigitsFirstSlotIs2168
#print axioms ProofFile.Honest.K3.Term.lookupWorthRidesPastTheHeadsMergeAtTheWrittenSlot
#print axioms ProofFile.Honest.K3.Term.lookupWorthRidesPastTheHeadsMergeAtThePublicPlace
#print axioms ProofFile.Honest.K3.Term.borderOfTheHeadsDigitsIs345
