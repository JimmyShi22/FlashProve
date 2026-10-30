-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ReadersPaid.lean: k01_fifty_atBase's BINDER hRd (what a run's reader answers in
front of a later sub-protocol of kind K1 it answers behind), TO THE LETTER, WITH ALL THAT IS PAID LAID
IN: all 24 segments in front of the output head, at both later places; of the output head's segment
the lookup's "objects" and "guests" at both places and the approximate range proof's run. A statement
with its proof: calls.

  headLink_open       in scope the opened description's output head's link is number 24
                      (Meaning.scope_plans at IM.Open.public).
  runsHead            [by evaluation] the written list at link 24.
  hRd_paid            **hRd.** From Johnson/Desc/K1/Law/ReadersSeated.lean's hRd_seated, with hW :=
                      headLink_open, hK4 := k4Block_respects (RespectsK4Q.lean), and in hHead the
                      two runs of ReadersHead.lean's fwd_head_look.
PREMISES THAT STAY, BY NAME.
  hS hR O hDlk        binders that the top has.
  hlk                 ON THE LETTER Dm.lk: it is the opened chain's list of links. (At the closed
                      constant: ProofFile.Law.linkAt_of, Johnson/Desc/ProofFile/Law/LinkAtLaw.lean.)
  hX                  a test on public values: headLink XV = 24. (At the closed constant:
                      headLink_in_scope.)
  hHead5              **FIVE RUNS OF THE OUTPUT HEAD's SEGMENT**: (3, norm) (3, policy) (3, logits)
                      (2, planes) (3, join), at both later places, as Fwd, behind
                      the accept and the promise in front.
What is not claimed. hHead5. That a sub-protocol accepts. Nothing on soundness, on an honest prover
or on hiding.

-/
import Johnson.Desc.K1.Law.ReadersHead
import Johnson.Desc.K1.Law.RespectsK4Q

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open Cb Johnson.Pack
open VerifiableInference.Desc (Block Chain Link FileDescription Place)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More PubData flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull runsAt MsgT MgData CellsQ mgAll d13 mgBase)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.K13.Law (openAt)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.K9 (Readers LinkHoles statesOfLink readersOfLink holesAt)
open VerifiableInference.Reads.Pass (Fwd)
open OnBytes.Model.Stages (LinkH)
open IM (k1Ix)
open ProofFile (Cl)

theorem runsHead : runsL 24 false = [(2, "objects"), (2, "guests"), (3, "norm"), (3, "policy"),
    (3, "logits"), (2, "planes"), (3, "join")] := by decide +kernel

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- In scope the output head's link is number 24. -/
theorem headLink_open (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) : headLink Bs.G₀.W = 24 := by
  obtain ⟨p4, ng, -⟩ := Meaning.scope_plans hS hR O.public
  unfold headLink
  rw [p4, ng]
  rfl

/-- **hRd, to the letter, with all that is paid laid in.** -/
theorem hRd_paid (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hDlk : Dm.links = linksFull)
    (hlk : ∀ l, l < 25 → Dm.lk l = c.links[l]?) (hX : headLink XV = 24)
    (hHead5 : ∀ d : Bool, ∀ X arrs, Bs.G₀.built[24]? = some X → ∀ lk, c.links[24]? = some lk →
      ∀ x x' y, YesOf (blkL Z Bs.G₀ 24 d X arrs) x x' →
      InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)) linksFull (flatPlacesOf linksFull true)
        (noL 24 d) x y →
      ∀ p ∈ [(3, "norm"), (3, "policy"), (3, "logits"), (2, "planes"), (3, "join")],
        Fwd (readersOfLink (holesAt XV (headLink XV) 24 lk) lk) p.1 p.2 x.2 x'.2) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y m j r, YesOf (blkL Z Bs.G₀ l d X arrs) x x' → InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)) linksFull (flatPlacesOf linksFull true) (noL l d) x y → (Pub.formsIn m j r ∈ (First.pubSets (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)).more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++ First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) ∨ Pub.formsInT m j r ∈ (First.pubSets (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)).more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++ First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d))) → ReadersStay (dK Dm.pubD Dm.sent) m j r x.2 x'.2 := by
  refine hRd_seated Dm dk hS hR O hDlk hlk hX (headLink_open hS hR O)
    (fun x _ => k4Block_respects x) ?_
  intro d X arrs hXb lk elk x x' y hy hIn p hp
  rw [runsHead] at hp
  rcases List.mem_cons.1 hp with rfl | hp
  · exact fwd_head_look hS hR O XV hX d X arrs lk elk x x' hy "objects" (Or.inl rfl)
  rcases List.mem_cons.1 hp with rfl | hp
  · exact fwd_head_look hS hR O XV hX d X arrs lk elk x x' hy "guests" (Or.inr rfl)
  exact hHead5 d X arrs hXb lk elk x x' y hy hIn p hp

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.runsHead
#print axioms VerifiableInference.Desc.K1.headLink_open
#print axioms VerifiableInference.Desc.K1.hRd_paid
