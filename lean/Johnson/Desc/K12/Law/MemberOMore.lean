-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.MemberO
import Johnson.Desc.K12.Law.MasksPlan
import Johnson.Desc.K12.Law.BatNone
import Johnson.Desc.K12.Law.FirstBelow
import Johnson.Desc.K12.Law.CodesJoh
import Johnson.Desc.K12.Law.BatPriceLaw
import Johnson.Desc.K12.Law.OwnSeat
/-
Johnson/Desc/K12/Law/MemberOMore.lean: WHAT ELSE IS CLOSED AT THE SAME LITERALS: at the proximity test O of the SMALL stored proof of a build that is not in this repository (LitO.lean; MemberO.lean). Statements and proofs. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  o_firstNe · o_last · o_alone: by the kernel: no tree of nums.first is the own mask's · at the record behind the beginning: the last of D.ts is D.fresh.t · no member stands at the mask's place. (They read gpOf alone; the row that passes is Lean's default: gpOf does not read it.)
  o_roots: tO.roots = piO.nums.free (both 5): by rfl.
  o_price: batPriceOk piO rO 128 = true, by the kernel. o_below128: with batBelow_of_ok (BatPriceLaw.lean): RoundBelow 768 ("BAT"'s written round) (2⁻¹ ^ 128), closed.
  fields_O: WHICH FIELDS OF AtPlaceOwn (Johnson/Desc/K12/Coin/OwnArm.lean) ARE CLOSED AT piO, IN PLAIN LETTERS (its definitions unfolded by hand): early · answers · planOk · spend · deal · codes (at the letters lstJ · flC · flZ · flZ and the radii rO) · the first half of like, with «the written "BAT" sends no tree» (so batNone follows from like) · own1 · trees (through TreesOwnP). NINE OF THIRTEEN, one of them by half.
  NOT CLOSED HERE: like's second half · wants · numOwn · bears: they speak of the stretch's data (dB · dt), the frame F, num, base and εt.
  masks_O: MasksFixed piO.

-/
set_option autoImplicit false
set_option maxRecDepth 100000
namespace H2K.Member
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (johOk batV0 spendOk pubOk writtenOf WR chainFrom Letters sgOf CodesAt batPriceOk)
open H2K.First (batOneOk dealOk ownN lastOk aloneAt)
open H2K.Made (firstNe MasksFixed TreesOwnP)

/-- The record behind the batching's beginning, with Lean's default row for what passes. -/
def tOb : T12 := { tO with st := begun tO.st tO.g gO, pass := .claim default lyO }

theorem o_firstNe : firstNe piO = true := by decide +kernel
theorem o_last : lastOk piO tOb = true := by decide +kernel
theorem o_maskNone : tO.mask = none := by decide +kernel
theorem o_alone : aloneAt piO tOb = some true := by decide +kernel
theorem o_price : batPriceOk piO rO 128 = true := by decide +kernel

/-- The record's count of roots is the plan's count of roots in front of "BAT". -/
theorem o_roots : tO.roots = piO.nums.free := rfl

theorem masks_O : MasksFixed piO := H2K.Made.masksFixed_of_planOk piO member_O.2.2.1

/-- **The fields of AtPlaceOwn that are closed at piO, in plain letters.** -/
theorem fields_O :
    piO.early = true ∧ piO.answers = 1 ∧ (proximityTestKind guardedProximityTestParts piO : Block T12 Unit).planOk = true ∧
    spendOk piO = true ∧ dealOk piO = true ∧
    CodesAt Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => rO s.st) piO.nums.stages ∧
    (∃ w0 l, writtenOf piO.nums = some (w0 :: l) ∧ w0.tree = none) ∧ ownN piO = 1 ∧
    (∀ (X : Letters) a rest w0 l (c : OnBytes.Slice.Chain (sgOf a)), piO.nums.stages = a :: rest →
      writtenOf piO.nums = some (w0 :: l) → chainFrom X rest a l = some c → TreesOwnP c) := by
  obtain ⟨_, _, hp, he, ha, ho, hj, _, hsp, _, _⟩ := member_O
  obtain ⟨_, _, _, w0, w, _, hw, _, _⟩ := masks_O.made
  exact ⟨he, ha, hp, hsp, H2K.Made.dealOk_of_planOk guardedProximityTestParts piO hp,
    H2K.Pub.codes_of_johOk rO piO hj, ⟨w0, w, hw, H2K.Made.written_bat _ w0 w hw⟩,
    masks_O.own1 ho, fun X a rest w0 l c hs hw hc => masks_O.treesOwn ho X a rest w0 l c hs hw hc⟩

/-- "BAT"'s price, closed. -/
theorem o_below128 : ∃ w0 l, writtenOf piO.nums = some (w0 :: l) ∧
    RoundBelow 768 w0.rd ((2 : ENNReal)⁻¹ ^ 128) := by
  obtain ⟨a, b, rest, w0, w, hs, hw, _, _⟩ := masks_O.made
  have h := H2K.Pub.batBelow_of_ok piO rO 128 a (b :: rest) hs w0 w hw o_price
  rw [o_v0] at h
  exact ⟨w0, w, hw, h⟩

end H2K.Member

#print axioms H2K.Member.o_firstNe
#print axioms H2K.Member.o_last
#print axioms H2K.Member.o_alone
#print axioms H2K.Member.o_price
#print axioms H2K.Member.o_roots
#print axioms H2K.Member.masks_O
#print axioms H2K.Member.fields_O
#print axioms H2K.Member.o_below128
