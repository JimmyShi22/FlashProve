-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K03PlanOf.lean: THE KIND "LOOKUP" (K3): `K3Plan` AT THE PROOF FILE: the
structure that, with the door's row on the digits, gives `K3PlanR` (Johnson/P5J/K03PlanAt.lean),
`k03_law_ofR`'s premise, "what is asked of the plan alone" (K3Means.lean), SHOWN AT THE PUBLIC DATA
(the structure `Verify.Public`) OF THE DESCRIPTION THAT `ProofFile.onlineDescription` RETURNS, in the goals' scope.
A JOINING: one lemma a field, each from its own kind's files. Theorems with their proofs.

THE STATEMENT IS THE LOOKUP's FILES', to the letter.

  `headLink_scope`: in scope the head's link is number 24 (by `Meaning.scope_plans`).
  `k03_const_ok`: in scope, where the description's test on the plan says yes: at each of the fifty
    places `K3.theStated` answers at the driver's address, and ITS VALUE's test on the plan says yes
    (the three lines of `k03_pieces_of`, K3PiecesOf.lean, field planOk: `IM.k3_of`,
    `IM.hear_at_flat`, `IM.alone_planOk`, `Keeps.planOk_blocks`).
  **`k03_plan_of`**: the six fields: dig: the door's row on the digits: the lookups' `asks_digB`
    with `links_25`; att: the lookups' `attAt_scope`; lay: the lookups' `layAt_scope`; head: the
    door's row on the head: the lookups' `asks_head`; its test on the planes' packing by
    `stated_entries` at the head's address, `placeAt_headAt` and `headAt_shape`; head24:
    `headLink_scope`; entries: the lookups' `stated_entries` at `k03_const_ok`'s value, with
    `k03_place` (Johnson/P5K3R/SitsRounds.lean).

PREMISES: the goals' scope (hS, hR); the description's letters, each by the call that made it (O:
`IM.Open`, Johnson/IMR/SeatOpen.lean); TWO ROWS OF THE PROOF FILE's DOOR, Bools on the public data
(hDig, hHead); the description's test on the plan (hOk). L is free: every radius.

Limits. Nothing on soundness. On the public data alone: no view, no witness, no meaning. THAT THE
FIVE PREMISES HOLD TOGETHER ANYWHERE IS NOT SHOWN HERE: `onlineDescription` returns at the goals' full-size
files by a ride; the two rows were ridden too, once in a build apart.
`K3Pieces` and `K3MeanR` stay premises of `k03_law_ofR`, beside hS, hR, O, hT and hE.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Look.K3Means
import Johnson.Desc.First.Look.K3AsksDoorLaw
import Johnson.Desc.First.Look.K3AsksPlan
import Johnson.Desc.First.Look.K3PlanOfOk
import Johnson.Desc.First.Look.K3PlanLay
import Johnson.Desc.First.Look.K3PlanAtt
import Johnson.P5K3R.SitsRounds
import Johnson.Desc.PlanPasses

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look

/-- In scope the head's link is number 24. -/
theorem headLink_scope {Pf : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : Verify.Public} (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (h : Verify.publicOf Pf.pol Pf.KL lay = .ok X) : headLink X = 24 := by
  obtain ⟨hp4, hN, -, -⟩ := Meaning.scope_plans hS hR h
  unfold headLink
  rw [if_pos hp4, hN]

section
variable {Pf : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : Desc.FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Desc.Block Desc.First.S ProofFile.Cl)}
  {c : Desc.Chain Desc.First.S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- At each of the fifty places the kind's stated block is there, and its own test on the plan says
yes. -/
theorem k03_const_ok (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) (hOk : F.planOk = true)
    (l : ℕ) (hl : l < 25) (d : Bool) :
    ∃ b', Desc.K3.theStated K3Lot.ofForm (K3Lot.readersAt Bs.G₀.W) Bs.G₀.W Z.first.codes
        Z.first.shape (IM.k3Place l d) = some b' ∧ b'.planOk = true := by
  obtain ⟨Lk, b, b', h1, h2, h3, h4⟩ := IM.k3_of hS hR O l hl d
  have h5 := IM.hear_at_flat h1 h2
  refine ⟨b', h3, ?_⟩
  rw [← IM.alone_planOk h4]
  have hp : (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z)
      c).planOk = true := O.desc ▸ hOk
  exact (Desc.Keeps.planOk_blocks _ hp).1 b (List.mem_of_getElem? h5)

/-- **`K3Plan` AT THE PROOF FILE.** -/
theorem k03_plan_of (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B)
    (hDig : Desc.K3Asks.digRow Z.p.X (Desc.K3Asks.sentOf Z) = true)
    (hHead : Desc.K3Asks.headRow Z.p.X = true) (hOk : F.planOk = true) {Cells Tok : Type}
    (L : K3Letters Cells Tok) :
    @K3Plan (Desc.Kinds.Head.Law.sizesOf Bs.G₀.W.hS) Cells Tok Bs.G₀.W (Desc.K3Asks.sentOf Z).up L
      Cb.Gl.p (OnBytes.Model.Head.keyFloor Bs.G₀.W.hS) := by
  have hX := O.public
  have h24 := headLink_scope hS hR hX
  rw [← O.W] at hDig hHead
  have ent : ∀ l < 25, ∀ p, placeAt Bs.G₀.W l false = some p →
      p.entries.isSome = true ∧
        ∃ hs, p.shape = some hs ∧ (Forest.planeCols hs p.lm).toBool = true := by
    intro l hl p hp
    obtain ⟨b', h3, hk⟩ := k03_const_ok hS hR O hOk l hl false
    exact Desc.K3.stated_entries _ _ _ _ _ _ b' h3 hk l false rfl
      (K3Lot.k03_place _ _ _ _ _ l false b' h3).1 p hp
  refine @K3Plan.mk (Desc.Kinds.Head.Law.sizesOf Bs.G₀.W.hS) _ _ _ _ _ _ _ (fun l hl => ?_)
    (fun l hl h1 => ?_) (fun l hl h0 => layAt_scope hS hR hX hl h0) ?_ h24
    fun l hl p hp => (ent l hl p hp).1
  · exact Desc.K3Asks.asks_digB hDig L.rad l (by rw [Desc.K3Asks.links_25 h24]; exact hl)
  · obtain ⟨x, a, -, -, e, H, -⟩ := attAt_scope hS hR hX hl h1 (Desc.K3Asks.sentOf Z).up L.rad
    exact ⟨x, _, _, e, H⟩
  · obtain ⟨x, e, hb, -⟩ := Desc.K3Asks.asks_head hHead
    refine ⟨x, e, hb, ?_⟩
    have hp := @placeAt_headAt (Desc.Kinds.Head.Law.sizesOf Bs.G₀.W.hS)
      (Desc.Kinds.Head.Law.policyOf Bs.G₀.W.hS) ⟨fun _ => 0, 0, 0⟩ _ _ e
    rw [h24] at hp
    obtain ⟨-, hs, e₁, e₂⟩ := ent 24 (by omega) _ hp
    obtain rfl : x.fs = hs := Option.some.inj ((Desc.K3Asks.headAt_shape e).symm.trans e₁)
    exact e₂

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.headLink_scope
#print axioms VerifiableInference.OnPublicFiles.k03_const_ok
#print axioms VerifiableInference.OnPublicFiles.k03_plan_of
