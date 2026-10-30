-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K2/HeardAtSwitches.lean: the kind "the code switch" (K2): HOW FAR THE FILLING's DATA HAVE
HEARD AT THE MESSAGES THAT A SWITCH CARRIES: at each pair of switches, neighbouring or not, at each
address of a message of a segment in front of the first, the joined filling `withSwitchData` at the
shared sending's data has heard no more challenges than stand in front of the switch in front: the
premise hD1 of `msgs_at_lot_data` (MsgsAtLotData.lean of this folder) and of `k2_exchange_full`.
Public data alone. Five definitions; one closed fact by evaluation in Lean's kernel, with a control;
three laws.

  `zzHeard`, `heardAll`   what a seat's address has heard, by the seats of "U3" and "BZ" and the
                    rounds "RNG"; `heard_le`: the joined filling hears no more, at any seats
  `sentW`, `addrsW_mem`   an address of `addrsW` is one that the written segment has sent
  `heardRngW`, `heardFrontB`, `heardFrontW`   BY LEAN's KERNEL: at each written switch and each
                    earlier segment
  `heard_at_switches`   THE END

By: `seats_at_head`, `first_at_head` (Johnson/HonestTrace/U3Fit/SeatsAtHead.lean) · `addrs_written`
(Honest/K2/Law/LightWritten.lean) · `roundsTo_at_head` (MsgsAtJoin.lean of this folder) ·
`entries_at_head`, `roundNumbers_entries`, `places_at_head` (Honest/K2/Law/PlacesWritten.lean,
sealed).

Limits. THE HEAD AND THE OPENING ARE HYPOTHESES: THIS FILE SHOWS THEM MET BY NOTHING: WHERE NOTHING
MEETS THEM THE END HOLDS EMPTILY. A CLOSED FACT BY LEAN's KERNEL, REPLAYED BY NO INDEPENDENT
CHECKER. It says how many challenges are read, of no message what it holds. The end holds at each
input and needs no validity. NOT IN FRONT OF A LAW OVER COINS. The full size and the format's
second hash function alone. Nothing on any property.
-/
import AtFullSide.K2.MsgsAtJoin
import Johnson.HonestTrace.U3Fit.SeatsAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.LightWritten
import Johnson.Desc.ProofFile.Honest.K1.LotData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open VerifiableInference.Desc (Block Chain)
open OnBytes.HonestTrace (Seat seatsOf heardOf pairOf mineOf)
open OnBytes.HonestTrace.U3.Fit (seatsW seats_at_head first_at_head)
open OnBytes.Params (ReqLayout)
open Johnson.G (layoutFull)
open Johnson.AtFull.Desc (spotsWritten)
open P5J (AtMgA TS F0T)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest
open ProofFile.Honest.K2
open ProofFile.Honest.K2.Law

/-- What the filling of "ZZ" has heard at an address: the round "RNG" of its segment, and one. A
second text of `zzDataAt`'s heardAt (Honest/K8/ZzData.lean): `heard_le` ties the two, by unfolding.
-/
def zzHeard (lay : ReqLayout) (seats : List Seat) (rng : List Nat) (a : MsgAddr) : Nat :=
  match (ProofFile.Honest.K8.bearsZz lay (pairOf seats) a).bind fun x => rng[x.1]? with
  | some n => n + 1
  | none => 0

/-- The largest of the three. -/
def heardAll (u3 bz : List Seat) (lay : ReqLayout) (rng : List Nat) (a : MsgAddr) : Nat :=
  max (heardOf u3 a) (max (heardOf bz a) (zzHeard lay bz rng a))

/-- **The joined filling hears no more than that.** -/
theorem heard_le (S₀ : OnBytes.HonestTrace.Sz) (Z : ProofFile.Pub) (G : ProofFile.Ground) (x : ProofFile.Inst)
    (a : MsgAddr) :
    (withSwitchData S₀ (K1.lotData S₀) Z G x).heardAt a ≤
      heardAll (seatsOf Z G "U3") (seatsOf Z G "BZ") G.first.layout
        (roundNumbers Z.D.1 "RNG") a := by
  show (if (switchSeat Z G a).isSome = true then (switchData S₀ Z G).heardAt a
    else (K1.lotData S₀ Z G x).heardAt a) ≤ _
  split
  · exact Nat.zero_le _
  · show (if (a.sender == K1.firstAddr) = true then _ else
      (if mineOf (seatsOf Z G "BZ") a = true then (K1.digitsFill Z G _).heardAt a else
        (OnBytes.HonestTrace.U3.u3RowsOf Z G x).heardAt a)) ≤ _
    split
    · exact Nat.zero_le _
    · split
      · exact Nat.le_trans (Nat.le_refl _) (Nat.le_max_right _ _)
      · exact Nat.le_max_left _ _

/-- The addresses that the written segment s has sent. -/
def sentW (s : Nat) : List MsgAddr :=
  match IM.prepW with
  | some P =>
    (sentBy { shape := P.z.request, groups := OnBytes.reqGroups P.z.request } spotsWritten s).map
      fun x => ⟨x.1, x.2.1⟩
  | none => []

/-- **An address of `addrsW` is one that the written segment has sent.** -/
theorem addrsW_mem {s m : Nat} {a : MsgAddr} (h : addrsW s m = some a) : a ∈ sentW s := by
  unfold addrsW at h
  unfold sentW
  cases hP : IM.prepW with
  | none =>
    rw [hP] at h
    cases h
  | some P =>
    rw [hP] at h
    unfold addrOf ProofFile.Honest.K2.addrIn at h
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 h
    exact List.mem_map.2 ⟨y, List.mem_of_getElem? hy, rfl⟩

/-- The rounds "RNG", written. -/
def heardRngW : List Nat := entryNumbers P5T.esFull.1 "RNG"

/-- **The test.** sh: 0 is the test; a control's is large. -/
def heardFrontB (sh : Nat) : Bool :=
  placesW.all fun p₀ => (List.range p₀.link).all fun s => (sentW s).all fun a =>
    decide (heardAll (seatsW "U3") (seatsW "BZ") layoutFull heardRngW a + sh ≤
      roundsCutW (switchNo p₀))

set_option maxRecDepth 1000000 in
/-- **Its yes, and a control.** -/
theorem heardFrontW : heardFrontB 0 = true ∧ heardFrontB 100000 = false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- **THE PREMISE hD1, AT EVERY INPUT.** -/
theorem heard_at_switches (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (S₀ : OnBytes.HonestTrace.Sz) :
    ∀ p₀ ∈ switchPlaces Zp Bs.G₀, ∀ p ∈ switchPlaces Zp Bs.G₀, ∀ (x : ProofFile.Inst) (s m : Nat)
      (a : MsgAddr), s < p₀.link → p.addrs s m = some a →
      (withSwitchData S₀ (K1.lotData S₀) Zp Bs.G₀ x).heardAt a ≤
        0 + roundsTo cF.blocksInOrder (switchNo p₀) := by
  intro p₀ hp₀ p hp x s m a hs ha
  have hp₀W : p₀ ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp₀
  have hpW : p ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp
  rw [addrs_written p hpW] at ha
  have t := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 heardFrontW.1 p₀ hp₀W) s
    (List.mem_range.2 hs)) a (addrsW_mem ha)
  have t' := of_decide_eq_true t
  rw [Nat.zero_add, roundsTo_at_head h O]
  refine Nat.le_trans (heard_le S₀ Zp Bs.G₀ x a) ?_
  rw [seats_at_head h O.blank "U3", seats_at_head h O.blank "BZ",
    (first_at_head h O.blank).2.2, roundNumbers_entries, entries_at_head h.toAtMg O]
  exact t'

end AtFullSide.K2

#print axioms AtFullSide.K2.zzHeard
#print axioms AtFullSide.K2.heardAll
#print axioms AtFullSide.K2.heard_le
#print axioms AtFullSide.K2.sentW
#print axioms AtFullSide.K2.addrsW_mem
#print axioms AtFullSide.K2.heardRngW
#print axioms AtFullSide.K2.heardFrontB
#print axioms AtFullSide.K2.heardFrontW
#print axioms AtFullSide.K2.heard_at_switches
