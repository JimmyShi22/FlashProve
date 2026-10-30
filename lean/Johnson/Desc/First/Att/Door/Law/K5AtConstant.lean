-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5AtConstant.lean: kind K5: WHERE THE KIND's LAW AT THE TABLE MEETS THE COMPOSED MEANING's CLOSED CONSTANT (Johnson/P5J/MgAtAll.lean: mgAtAll h := mgAll h.𝔇 mgBase, under the one head
AtMgA o Z D r Zp Np cF x) AND THE OPENING OF THE MAKER (IM.Open) AT WHICH THE KIND's FACTS ON THE DESCRIPTION STAND.

Typed by reading the constant's files: P5J/MgAtAll.lean · LettersAll.lean · LettersAt.lean ·
LettersAt4.lean · Rad3Seat3At.lean · AtMg.lean · LaidOpens.lean · IMR/SeatOpen.lean · ProofFile/LinkAt.lean · Law/LinkAtLaw.lean · ProofFile/Pub.lean.

Why. The kind's facts on the description (which sub-protocol sits at the segment, its test on the plan, its runs, the readers) are shown from an opening O : IM.Open … Z Bs base c …, at W := Bs.G₀.W ·
Dn := sentOfBuilt Z.first Z.p.built · the links c.links[m]?. The law at the table ends at the constant's letters At.X Zp · h.𝔇.sent · At.lk Zp. Three ties make the two sides one.

Main names:
  `open_all`: FROM THE HEAD ALONE there is an opening at Z := Zp · c := cF · F := F0T o Zp Np cF, and its W is At.X Zp (LaidAt.opened · IM.Open.W).
  `sent_meets`: h.𝔇.sent = sentOfBuilt Zp.first Zp.p.built (rfl). `links_meet`: h.𝔇.links is the written list of the segments' sorts (rfl).
  `chain_meets`, `lk_meets`: ProofFile.onlineFirstChainAt Zp = .ok cF from the opening (after the proof of ProofFile.Law.descPure_chain) · At.lk Zp m = cF.links[m]? (ProofFile.Law.linkAt_of).
  `dataIs_all`, `dataSent_all`, `mgGains_all`, `hpub_all`, `more_all`, `runsIs_all`, `mHIs_all`, `rdIs_all`, `constrIs_all`: K5AtMgAll.lean's, called at h.𝔇 and mgBase.
  `planIs_all`: PlanIs (At.X Zp), from the head's field pubOne.
NOT HERE: MgIs · baseP · nsOf · lkAt as a field (it follows from lk_meets and the opening's own equation c.links[2 g + 1]? = some Lk).
Is it empty here? Under the head: A MEMBER OF THAT HEAD IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.P5J.MgAtAll
import Johnson.Desc.ProofFile.Law.LinkAtLaw
import Johnson.Desc.First.Att.K05PublicOfBuilt
import Johnson.Desc.First.Att.Door.Law.K5AtMgAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.First.Att.P (PlanIs planIs_public sentOfBuilt)
open Desc.K14.Law (secondAt seatZ)
open P5J (AtMgA mgAtAll F0T TS)

section
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA o Z D r Zp Np cF x)

include h in
/-- **From the head alone: the opening of the maker, at the constant's own letters; its W is the constant's X.** -/
theorem open_all : ∃ Bs base, IM.Open o Z.pol Z.lay Z.KL (F0T o Zp Np cF) Zp Bs base cF (seatZ Zp Np) (secondAt Zp Np) ∧
    Bs.G₀.W = P5J.At.X Zp := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact ⟨Bs, base, O, O.W⟩

/-- **What the planner sends: one term on both sides.** -/
theorem sent_meets : h.𝔇.sent = sentOfBuilt Zp.first Zp.p.built := rfl

/-- The segments' sorts: the written list. -/
theorem links_meet : h.𝔇.links = (List.range 12).flatMap (fun _ => [ModelPart.layers, ModelPart.attention]) ++ [.head] := rfl

include h in
/-- PlanIs at the constant's public parameters. -/
theorem planIs_all : PlanIs (P5J.At.X Zp) := planIs_public h.pubOne

omit h in
/-- **The chain off the public part is the opening's.** -/
theorem chain_meets {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Zp Bs base cF A B) : ProofFile.onlineFirstChainAt Zp = .ok cF := by
  show ProofFile.chainOfSeat Zp (ProofFile.pureSeat ProofFile.emptySecondHashFunction Zp) = .ok cF
  rw [ProofFile.Law.chainOfSeat_older Zp ProofFile.emptySecondHashFunction o]
  unfold ProofFile.chainOfSeat ProofFile.partsOf
  rw [O.made]
  show ((ProofFile.partsAt (ProofFile.pureSeat o Zp) Bs).base.bind fun base =>
    ProofFile.chainBy Zp base (ProofFile.partsAt (ProofFile.pureSeat o Zp) Bs).frames (ProofFile.partsAt (ProofFile.pureSeat o Zp) Bs).road) = .ok cF
  rw [O.places]
  exact O.chain

omit h in
/-- **The constant's links are the opening's chain's.** -/
theorem lk_meets {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Zp Bs base cF A B) (m : ℕ) :
    P5J.At.lk Zp m = cF.links[m]? := ProofFile.Law.linkAt_of Zp cF (chain_meets O) m

/-! ## K5AtMgAll.lean's, at the constant -/

theorem dataIs_all (m : ℕ) : DataIs h.𝔇.pubD (P5J.At.X Zp) h.𝔇.links m := dataIs_any h.𝔇 m

theorem dataSent_all : DataSent h.𝔇.pubD h.𝔇.cs h.𝔇.sent := dataSent_any h.𝔇

theorem hpub_all : (mgAtAll h).pub = pubAll h.𝔇.pubD (mgBase (P := ProofFile.InstPub)
    (W := Wit (CellsQ OnBytes.Flat.numsFull.rows (P5J.colsAt OnBytes.Flat.numsFull)) P5J.At.Tok MsgT)).pub := hpub_any h.𝔇 mgBase

/-- The constant's list of extra public tests is the closed one. -/
theorem more_all : (mgAtAll h).more = mgMore := mgAll_more_base h.𝔇

theorem runsIs_all : h.𝔇.pubD.runs = runsAt h.𝔇.links := rfl

theorem mHIs_all : h.𝔇.pubD.mH = (if (P5J.At.X Zp).p4 then 2 else 1) * (P5J.At.X Zp).NGr := rfl

theorem rdIs_all : h.𝔇.pubD.Rd = K9.readersAt (P5J.At.lk Zp) (P5J.At.X Zp) h.𝔇.pubD.mH := rfl

theorem mgGains_all {g : ℕ} {a : Attention.Plan} {x₁ : Look.Place} (h4 : (P5J.At.X Zp).p4 = true) (ha : (P5J.At.X Zp).A[g]? = some a)
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) :
    MgGains (mgAtAll h) h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.Rd h.𝔇.runs h.𝔇.St h.𝔇.N h.𝔇.wt (2 * g + 1) x₁ a.S a.seam.tl h.𝔇.sent h.𝔇.l3.rad
      (fun j => h.𝔇.l3.seat x₁.link false j.1) h.𝔇.l3.arr := mgGains_any h.𝔇 mgBase (planIs_all h) h4 ha hx

theorem constrIs_all : ∀ n p a₁ y w, (mgAtAll h).constr n p a₁ y w ↔
    if p = .lookDigits then h.𝔇.digitsPart n a₁ y w
    else (p = .small → h.𝔇.H.base n w) ∧
      ∀ M i, h.𝔇.decT y.cell a₁ = some M → VerifiableInference.OnPublicFiles.Flat.Holds M i → bodyAll h.𝔇 n p i a₁ y w :=
  constrIs_any h.𝔇 mgBase

end

end H2K5.Door

#print axioms H2K5.Door.open_all
#print axioms H2K5.Door.sent_meets
#print axioms H2K5.Door.links_meet
#print axioms H2K5.Door.planIs_all
#print axioms H2K5.Door.chain_meets
#print axioms H2K5.Door.lk_meets
#print axioms H2K5.Door.dataIs_all
#print axioms H2K5.Door.dataSent_all
#print axioms H2K5.Door.hpub_all
#print axioms H2K5.Door.more_all
#print axioms H2K5.Door.runsIs_all
#print axioms H2K5.Door.mHIs_all
#print axioms H2K5.Door.rdIs_all
#print axioms H2K5.Door.mgGains_all
#print axioms H2K5.Door.constrIs_all
