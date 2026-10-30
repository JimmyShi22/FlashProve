-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5WrittenPlans.lean: kind K5: **A PAYMENT BENEATH THE KIND's NAMED CONDITION: WHERE TWO COMPARISONS WITH WRITTEN VALUES ACCEPT, THE CONDITION's TWO TESTS ON THE PLAN's SEATS AND SHAPES FOLLOW FROM BOOLS
WITHOUT A LETTER**, one pair for each of the twelve groups. It turns nothing of the condition (K5CondAt, Door/Law/K5LeftOfCond.lean).
The two comparisons (madeRow Zp · the written cut of the first chain) ARE PREMISES HERE, as in Door/Law/K5Written.lean: the verifier's list of entry tests asks them: they stand in its prefix that Johnson/Desc/Laid/ProofAsksFirstThirteenTests.lean pins (asksAt2).
The road: the tests "at every member" give the tests at the members that are read (Door/Law/K5PlansAll.lean), and read of what the planner sends the request's shape alone (Door/Law/K5PlansBy.lean): no map from trees to arrays' names, no
radius; the seats, the numbers by place and the listed seats are the written ones (Door/Law/K5Written.lean).

Main names:
  sentW · numsW · laidW · msgsW: what the planner sends (with no map of names), the table's numbers, the listed seats and the messages' shapes, at the written values. No letter.
  seatsAtW g L · seatsAllW g · shapesAllW g: the Bools. No letter (but g; L is the written list's own value).
  isCall_shape | seatCalls_shape: the seat of a member of the caller's list (P6T.seatCallsT, Johnson/P5T/SeatsAt.lean) reads of what the planner sends the request's shape alone.
  **seatsPlan_of_written | shapesPlan_of_written**: under the head, the two comparisons, the place x₁ of the group's lookup argument and the listed seats L: seatsAllW g = true | shapesAllW g = true → the condition's field, text for text.
  k5Tests_of_written: so K5Tests at the condition's closed letters, from the two Bools and its other two fields.
IS IT EMPTY HERE? Implications from Bools without a letter. THAT THEY ARE true IS NOT SHOWN: THESE TERMS HAVE BEEN EVALUATED NOWHERE. A MEMBER OF THE HEAD IS PROVED AT storedPublicFiles AND zGap ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5Written
import Johnson.Desc.First.Att.Door.Law.K5PlansBy
import Johnson.Desc.First.Att.Door.Law.K5LeftOfCond

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K5.Door
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (Sent lookAt sigListCalls keptAt bornAt)
open VerifiableInference.Desc.First.Att.P (psOf qsOf seatsPlanB shapesPlanB readMsgs)
open VerifiableInference.Desc.First.FillSent (sentDataOf baseAt treesAt)
open VerifiableInference.Desc.K12.Door (Laid laidAtCodes msgsOfChain)
open VerifiableInference.PlanWritten (madeRow cutFirstFull proofSizedFull)
open Johnson.G (proofSendsFull layoutFull)
open P5J (AtMg AtMgA TS)

/-- What the planner sends, at the written values, with no map from trees to arrays' names. -/
def sentW : Sent := ⟨proofSizedFull.codes, proofSizedFull.request, layoutFull, #[]⟩

/-- The table's numbers at the written values. -/
def numsW : Numbers := (P5T.numbersOf pseatsW).withTold P5J.At.ps toldW

/-- The listed seats at the written values. -/
def laidW : Option Laid := laidAtCodes proofSizedFull.codes proofSendsFull.1

/-- The messages' shapes at the written values. -/
def msgsW : List OracleShape := msgsOfChain proofSendsFull.1

/-- The test on the seats at every member, at the written values and a list of seats. -/
def seatsAtW (g : ℕ) (L : Laid) : Bool :=
  seatsAllBy proofSizedFull.request (baseAt numsW P5J.At.links P5J.At.ps) (fun _ => []) sentW (fun _ => 0)
    (fun k => P6T.seatCallsT pseatsW sentW (2 * g + 1) k) (numsW.sent (2 * g + 1) 0) (numsW.msgsAt (some ⟨1, some (2 * g + 1), 3, .K5⟩)) (2 * g + 1) L

/-- **The test on the seats of group g, at the written values.** -/
def seatsAllW (g : ℕ) : Bool := laidW.any (seatsAtW g)

/-- **The test on the shapes of group g, at the written values.** -/
def shapesAllW (g : ℕ) : Bool :=
  shapesAllBy proofSizedFull.request (baseAt numsW P5J.At.links P5J.At.ps) (fun _ => []) sentW (fun _ => 0)
    (numsW.msgsAt (some ⟨1, some (2 * g + 1), 3, .K5⟩)) (2 * g + 1) msgsW

theorem isCall_shape {D D' : Sent} (h : D.shape = D'.shape) (l j : ℕ) : P6T.isCall D l j = P6T.isCall D' l j := by
  funext p
  unfold P6T.isCall P6T.keptN bornAt keptAt
  rw [h]

/-- The seat of a member of the caller's list reads of what the planner sends the request's shape alone. -/
theorem seatCalls_shape {D D' : Sent} (h : D.shape = D'.shape) (ps : List P5T.PSeat) (l j : ℕ) :
    P6T.seatCallsT ps D l j = P6T.seatCallsT ps D' l j := by
  unfold P6T.seatCallsT P6T.callAt
  rw [isCall_shape h]

section
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

theorem shape_written (hm : madeRow Zp = true) : P5J.At.shape Zp = proofSizedFull.request := (made_row_gives hm).1.2.2.1

theorem sentAt_shape (hm : madeRow Zp = true) : (P5J.At.sentAt Zp).shape = sentW.shape := shape_written hm

theorem sent_written (h : AtMg o Z D r Zp Np cF) (hm : madeRow Zp = true) : (P5J.At.N Zp cF).sent = numsW.sent := by
  show (P5T.numbersOf (P5J.At.pseats Zp)).sent = (P5T.numbersOf pseatsW).sent
  rw [pseats_written h hm]

theorem msgsAt_written (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull) : (P5J.At.N Zp cF).msgsAt = numsW.msgsAt := by
  show (fun p => msgsTold (P5J.At.told cF) (borderOf P5J.At.ps p)) = fun p => msgsTold toldW (borderOf P5J.At.ps p)
  rw [told_written hc]

theorem base_written (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull) :
    baseAt (P5J.At.N Zp cF) P5J.At.links P5J.At.ps = baseAt numsW P5J.At.links P5J.At.ps := by
  funext m
  unfold baseAt
  rw [msgsAt_written hc]

theorem laid_written (hm : madeRow Zp = true) : P5J.At.laid? Zp = laidW := by
  show laidAtCodes Zp.first.codes Zp.made.proof.1 = laidAtCodes proofSizedFull.codes proofSendsFull.1
  rw [(made_row_gives hm).1.1, (made_row_gives hm).2]

theorem msgs_written (hm : madeRow Zp = true) (L : Laid) : (P5J.At.d12 Zp L).M = msgsW := by
  show msgsOfChain Zp.made.proof.1 = msgsOfChain proofSendsFull.1
  rw [(made_row_gives hm).2]

/-- The test on the seats at every member, at the composed meaning's letters (P5J.At, Johnson/P5J/LettersAt.lean), is the one at the written values. -/
theorem seatsAll_written (h : AtMg o Z D r Zp Np cF) (hm : madeRow Zp = true)
    (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull) (g : ℕ) (tr : ℕ → List FillSent.TreeLook) (rd : OracleShape → ℕ) (L : Laid) :
    seatsAllBy (P5J.At.shape Zp) (baseAt (P5J.At.N Zp cF) P5J.At.links P5J.At.ps) tr (P5J.At.sentAt Zp) rd
      (fun k => P6T.seatCallsT (P5J.At.pseats Zp) (P5J.At.sentAt Zp) (2 * g + 1) k) ((P5J.At.N Zp cF).sent (2 * g + 1) 0)
      ((P5J.At.N Zp cF).msgsAt (some ⟨1, some (2 * g + 1), 3, .K5⟩)) (2 * g + 1) L = seatsAtW g L := by
  have hσ : (fun k => P6T.seatCallsT (P5J.At.pseats Zp) (P5J.At.sentAt Zp) (2 * g + 1) k) =
      fun k => P6T.seatCallsT pseatsW sentW (2 * g + 1) k := by
    funext k
    rw [pseats_written h hm, seatCalls_shape (sentAt_shape hm)]
  unfold seatsAtW
  rw [seatsAllBy_reads (sentAt_shape hm) _ _ tr (fun _ => []) rd (fun _ => 0), hσ, shape_written hm, base_written hc, sent_written h hm,
    msgsAt_written hc]

/-- The like for the shapes. -/
theorem shapesAll_written (hm : madeRow Zp = true) (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull) (g : ℕ)
    (tr : ℕ → List FillSent.TreeLook) (rd : OracleShape → ℕ) (L : Laid) :
    shapesAllBy (P5J.At.shape Zp) (baseAt (P5J.At.N Zp cF) P5J.At.links P5J.At.ps) tr (P5J.At.sentAt Zp) rd
      ((P5J.At.N Zp cF).msgsAt (some ⟨1, some (2 * g + 1), 3, .K5⟩)) (2 * g + 1) (P5J.At.d12 Zp L).M = shapesAllW g := by
  unfold shapesAllW
  rw [shapesAllBy_reads (sentAt_shape hm) _ _ tr (fun _ => []) rd (fun _ => 0), shape_written hm, base_written hc, msgsAt_written hc,
    msgs_written hm]

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- The field on the seats at a letter i for the link's number. -/
theorem seatsPlan_at (hm : madeRow Zp = true) (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull) {g : ℕ} {L : Laid}
    (hL : P5J.At.laid? Zp = some L) (hW : seatsAllW g = true) (i : ℕ) (e : i = 2 * g + 1) (ks : List ℕ) :
    seatsPlanB h.𝔇.pubD.dS (2 * g + 1) (keptAt h.𝔇.sent i).length L
      (psOf (sigListCalls h.𝔇.sent h.𝔇.l3.rad i) (fun j => h.𝔇.l3.seat i false j.1) ks) (h.𝔇.pubD.N.sent i 0)
      (h.𝔇.pubD.N.msgsAt (some ⟨1, some (2 * g + 1), 3, .K5⟩)) = true := by
  subst e
  have hA : seatsAtW g L = true := by
    unfold seatsAllW at hW
    rw [← laid_written hm, hL] at hW
    exact hW
  rw [← seatsAll_written h.toAtMg hm hc g (treesAt Zp.made.p.built.links) (P5J.At.rad3At Zp Z.lay) L] at hA
  exact seatsAllBy_gives hA ks

/-- The field on the shapes at a letter i for the link's number. -/
theorem shapesPlan_at (hm : madeRow Zp = true) (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull) {g : ℕ} (L : Laid)
    (hW : shapesAllW g = true) (i : ℕ) (e : i = 2 * g + 1) (ks : List ℕ) :
    shapesPlanB h.𝔇.pubD.dS (2 * g + 1) (keptAt h.𝔇.sent i).length (P5J.At.d12 Zp L).M (qsOf (sigListCalls h.𝔇.sent h.𝔇.l3.rad i) ks)
      (h.𝔇.pubD.N.msgsAt (some ⟨1, some (2 * g + 1), 3, .K5⟩)) = true := by
  subst e
  rw [← shapesAll_written hm hc g (treesAt Zp.made.p.built.links) (P5J.At.rad3At Zp Z.lay) L] at hW
  exact shapesAllBy_gives hW ks

/-- **THE CONDITION's FIELD seatsPlan, FROM A BOOL WITHOUT A LETTER.** -/
theorem seatsPlan_of_written (hm : madeRow Zp = true) (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull) {g : ℕ}
    {a : Attention.Plan} {x₁ : Look.Place} (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {L : Laid} (hL : P5J.At.laid? Zp = some L)
    (hW : seatsAllW g = true) :
    seatsPlanB h.𝔇.pubD.dS (2 * g + 1) (keptAt h.𝔇.sent x₁.link).length L
      (psOf (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link) (seatAll h x₁) (readMsgs h.𝔇.sent x₁ a.seam.tl)) (h.𝔇.pubD.N.sent x₁.link 0)
      (h.𝔇.pubD.N.msgsAt (some ⟨1, some (2 * g + 1), 3, .K5⟩)) = true :=
  seatsPlan_at h hm hc hL hW x₁.link (VerifiableInference.OnPublicFiles.lookAt_link hx) _

/-- **THE CONDITION's FIELD shapesPlan, FROM A BOOL WITHOUT A LETTER.** -/
theorem shapesPlan_of_written (hm : madeRow Zp = true) (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull) {g : ℕ}
    {a : Attention.Plan} {x₁ : Look.Place} (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) (L : Laid) (hW : shapesAllW g = true) :
    shapesPlanB h.𝔇.pubD.dS (2 * g + 1) (keptAt h.𝔇.sent x₁.link).length (P5J.At.d12 Zp L).M
      (qsOf (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link) (readMsgs h.𝔇.sent x₁ a.seam.tl)) (h.𝔇.pubD.N.msgsAt (some ⟨1, some (2 * g + 1), 3, .K5⟩)) = true :=
  shapesPlan_at h hm hc L hW x₁.link (VerifiableInference.OnPublicFiles.lookAt_link hx) _

/-- **K5Tests at the condition's closed letters, from the two Bools and its other two fields.** -/
theorem k5Tests_of_written (hm : madeRow Zp = true) (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull) {g : ℕ}
    {a : Attention.Plan} {x₁ : Look.Place} (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {L : Laid} (hL : P5J.At.laid? Zp = some L)
    (hs : seatsAllW g = true) (hq : shapesAllW g = true) (hsent : ∀ i, seatAll h x₁ i ∈ h.𝔇.pubD.N.sent (2 * g + 1) 0)
    (hsome : ∀ i, ∃ y ∈ h.𝔇.ms, Alike y (⟨⟨sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link, seatAll h x₁⟩, i⟩ : Mem)) :
    K5Tests h.𝔇.pubD h.𝔇.sent h.𝔇.ms L (P5J.At.d12 Zp L).M g a x₁ ⟨1, some (2 * g + 1), 3, .K5⟩ h.𝔇.l3.rad (seatAll h x₁) where
  seatsPlan := seatsPlan_of_written h hm hc hx hL hs
  shapesPlan := shapesPlan_of_written h hm hc hx L hq
  sent := hsent
  someMem := hsome

end

end H2K5.Door

#print axioms H2K5.Door.seatCalls_shape
#print axioms H2K5.Door.laid_written
#print axioms H2K5.Door.seatsAll_written
#print axioms H2K5.Door.shapesAll_written
#print axioms H2K5.Door.seatsPlan_of_written
#print axioms H2K5.Door.shapesPlan_of_written
#print axioms H2K5.Door.k5Tests_of_written
