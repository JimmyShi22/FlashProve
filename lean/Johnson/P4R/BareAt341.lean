-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P4R/BareAt341.lean, BESIDE P4R/LeavesFilledAt341.lean: ONE MORE FACT ON THE VERIFIER'S STATE
THAT IS REACHED AT BORDER 341 OF THE FIRST CHAIN, IN THE GOALS' SCOPE: none of the rows that the lookup
argument on the output head's calls left as heard names an entry of an array. Border 341 stands right
behind the accept of that lookup argument, which makes the fact: so nothing has to keep it. Statements
and proofs: four calls.
  P4.back_341 (P4R/Back341N.lean): "reached at 341" is the outcome of three accepts · placeH2_free
  (Law/HeadLedgerMade.lean), at the second: in front of the lookup argument a ledger is there, with its
  sizes · blockVia_decide (Johnson/Top/H/K3Via/Blocks.lean), at the third, under the test on the list of
  rounds (P4.plan_at) · calls_rowsBare (Johnson/Top/H/Keep/RowsBare.lean): the fact behind.
  **bare_341**     at Reach 0 c.blocksInOrder start 341 (z, s0).
  **bare_rchAt**   at RchAt (FD Z A B c) 341 a: in the letters in which the law's premises stand.
WHY NOT FROM THE TABLE's PROMISE: its sentence "what the lookup on the calls left" speaks of the rows'
VALUES in every world (HeardIs.rows: RowIs); that a row NAMES no entry is a fact on the form's text.
WHAT IS LEFT: hOk : F.planOk = true.
Every letter under "there is": none in the conclusions.
What it does not say. "No mark" is not asked (it stands in the law's binder: idle). Nothing on soundness.

-/
import Johnson.P4R.K6AtRchAt
import Johnson.Top.H.Keep.RowsBare

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P4

open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head.Law (placeH2_free)
open VerifiableInference.OnPublicFiles (calls_rowsBare)
open Johnson.Desc.First.Walk.Tied (Reach RchAt)
open ProofFile (Cl)
open Inst.Model (ScalesAndPolicy)

variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat} {Str : Type}

/-- **Made by the accept right in front of border 341.** -/
theorem bare_341 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {XP : Type} {start : XP → S} {z : XP} {s0 : S} (h : Reach 0 c.blocksInOrder start 341 (z, s0)) :
    ∀ g, s0.lookHeard? = some g → ∀ f ∈ g.rows.toList, f.ents = #[] := by
  obtain ⟨_, _, s340, -, -, ⟨p, n, HP, rs, gs, a2⟩, b3, Q, sent, laid, rs3, gs3, f3, hv, hp⟩ :=
    back_341 hS hR O h
  obtain ⟨G, hG, hs, -, -⟩ := placeH2_free a2
  obtain ⟨g0, hg0, hb⟩ := calls_rowsBare K3Lot.ofForm 3 laid sent Q [] s340 s0 rs3 gs3
    (VerifiableInference.Desc.K3.Law.blockVia_decide (hp (plan_at O hOk 340 b3 f3)) hv) hG hs
  intro g hg
  obtain rfl : g0 = g := Option.some.inj (hg0.symm.trans hg)
  exact hb

/-- **The same at the family that counts.** -/
theorem bare_rchAt (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true) :
    ∀ a : (ProofFile.InstPub × S) × Str, RchAt (FD Z A B c) 341 a → a.1.2.failed = none →
      ∀ g, a.1.2.lookHeard? = some g → ∀ f ∈ g.rows.toList, f.ents = #[] :=
  fun _ h _ => bare_341 hS hR O hOk (reach_of_rchAt h)

end P4

#print axioms P4.bare_341
#print axioms P4.bare_rchAt
