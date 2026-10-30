-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K03ReachedAt.lean: WHAT THE LOOKUP ON THE CALLS HAS LEFT, AT EVERY STATE THAT IS "REACHED" (RchAt, Johnson/Top/H0/Walk/ReachAt.lean) AT THE BORDER IN FRONT OF AN ATTENTION SEGMENT's OWN SUB-PROTOCOL, at the proof file's own IOP as written in Lean: two joins of three lines:
rch_pure_fold (Johnson/Top/H0/Walk/ReachPure.lean: "reached" gives the fold's return, in the first chain's own letters), then the theorem along the fold.
  k3Ix_att: the index: 14 * (2 * g + 1) + 2 + IM.k3Ix (2 * g + 1) false + 1 = 14 * (2 * g + 1) + 4.
  reached_rowsBare: by rowsBare_reached (Johnson/Desc/First/Look/K03RowsBare.lean).
  reached_leftAt: by leftAt_reached (Johnson/Desc/First/Look/K03LeftQ.lean: no premise on the sumcheck's marks).
  leftItem_reached: THE ITEM left l's OWN SENTENCE (k3LeftItemAt, Johnson/Desc/First/Look/K3LeftItem.lean) AT THE STATE THAT IS REACHED BEHIND THE LOOKUP ON THE CALLS, at the 24 links in front of the head's: leftAt_reached's own six lines, with the lookup argument's files' k3_calls_leftItem_anyWords
    (Johnson/Top/H/Keep/K3LeftAnyWords.lean: the item is made at every accept; no premise on the rounds' words) in k3_calls_leftAt's place. reached_leftItem: the same under RchAt, at an attention segment.
k3Ix_att's three lines are calls_reached's own (K03LeftQ.lean).
USER: whoever must hand a fence along the fold (IM.HandsR's Fk): "what was left by the lookup on the calls" in all three forms. And kind K5's bridge: the first two's conclusions are the premises hRB | hLA of hbare_of_reached | hleft_of_reached (Johnson/Desc/First/Att/Door/Law/K5ReachedPlus.lean) at Rch := RchAt ‹the description› · get := fun u => u · k := 14 * (2 * g + 1) + 4.
THE DESCRIPTION STANDS WRITTEN OUT (IM.Open's field desc says that onlineDescription's value is this term): with a letter F the state's type F.S₁ would not be S before a substitution.
READ FROM: K03RowsBare.lean · K03LeftQ.lean · ReachPure.lean · Johnson/IMR/SeatOpen.lean's structure Open.
IS IT EMPTY HERE? Implications. No state is shown to be reached.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K03RowsBare
import Johnson.Desc.First.Look.K03LeftQ
import Johnson.Top.H0.Walk.ReachPure
import Johnson.Top.H.Keep.K3LeftAnyWords

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain)
open VerifiableInference
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.FillBare (leftAtB)
open Johnson.Desc.First.Walk.Tied (RchAt rch_pure_fold)

theorem k3Ix_att (g : ℕ) : 14 * (2 * g + 1) + 2 + IM.k3Ix (2 * g + 1) false + 1 = 14 * (2 * g + 1) + 4 := by
  have hix : IM.k3Ix (2 * g + 1) false = 1 := by
    show (if false = true then 6 else 1) + (if 2 * g + 1 = 24 then 1 else 0) = _
    rw [if_neg (show ¬ 2 * g + 1 = 24 by omega)]
    rfl
  rw [hix]

/-- **THE ITEM left l's SENTENCE AT THE STATE THAT IS REACHED BEHIND THE LOOKUP ON THE CALLS.** -/
theorem leftItem_reached {Pf : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : VerifiableInference.Desc.FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) (hOk : F.planOk = true)
    (l : ℕ) (hl : l < 24) {s₀ t : S} {R R' : List Fmt.RoundView} {C C' : List Desc.OpenedColumn}
    (h : Desc.foldBlocks 0 (c.blocksInOrder.take (14 * l + 2 + IM.k3Ix l false + 1)) s₀ R C = .ok (t, R', C')) :
    k3LeftItemAt Bs.G₀.W l t := by
  obtain ⟨s, G, p, piece, laid, sent, rs, gs, hp, hG, hQ, hpl, hd⟩ :=
    calls_reached hS hR O hOk l hl h
  have hpl' : Desc.K3.planOk p laid ([] : List (Desc.First.Look.Guest S ProofFile.Cl)) = true := hpl
  unfold Desc.K3.planOk at hpl'
  rw [Bool.and_eq_true] at hpl'
  obtain ⟨hs, hsh, -⟩ := planOk_room hpl'.1
  exact ⟨p, hp, k3_calls_leftItem_anyWords K3Lot.ofForm piece laid sent p [] s t rs gs hsh hd hG hQ⟩

section
variable {Pf : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

theorem reached_rowsBare (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c) Z Bs base c A B)
    (hOk : (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c).planOk = true) (g : ℕ) (hg : g < 12) {Str : Type} :
    ∀ a : (ProofFile.InstPub × S) × Str, RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c) (14 * (2 * g + 1) + 4) a →
      ∃ g₁, a.1.2.lookHeard? = some g₁ ∧ ∀ f ∈ g₁.rows.toList, f.ents = #[] := by
  intro a hr
  obtain ⟨_, rs, cols, hf⟩ := rch_pure_fold hr
  exact rowsBare_reached hS hR O hOk (2 * g + 1) (by omega) false (by rw [k3Ix_att]; exact hf)

theorem reached_leftAt (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c) Z Bs base c A B)
    (hOk : (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c).planOk = true) (g : ℕ) (hg : g < 12) {Str : Type} :
    ∀ a : (ProofFile.InstPub × S) × Str, RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c) (14 * (2 * g + 1) + 4) a →
      ∃ g₁ G, a.1.2.lookHeard? = some g₁ ∧ a.1.2.fork? = some G ∧ leftAtB g₁ G = true := by
  intro a hr
  obtain ⟨_, rs, cols, hf⟩ := rch_pure_fold hr
  exact leftAt_reached hS hR O hOk (2 * g + 1) (by omega) (by rw [k3Ix_att]; exact hf)

theorem reached_leftItem (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c) Z Bs base c A B)
    (hOk : (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c).planOk = true) (g : ℕ) (hg : g < 12) {Str : Type} :
    ∀ a : (ProofFile.InstPub × S) × Str, RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c) (14 * (2 * g + 1) + 4) a →
      k3LeftItemAt Bs.G₀.W (2 * g + 1) a.1.2 := by
  intro a hr
  obtain ⟨_, rs, cols, hf⟩ := rch_pure_fold hr
  exact leftItem_reached hS hR O hOk (2 * g + 1) (by omega) (by rw [k3Ix_att]; exact hf)

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.reached_rowsBare
#print axioms VerifiableInference.OnPublicFiles.reached_leftAt
#print axioms VerifiableInference.OnPublicFiles.leftItem_reached
#print axioms VerifiableInference.OnPublicFiles.reached_leftItem
