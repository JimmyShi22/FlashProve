-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/K11R/SpeaksPaid.lean: a payment beneath the kind K11's conditions (the merge of the claims on
the committed table): THE FIELD speaks OF `K11Cond` (LawAtMg.lean), FROM ONE FACT ON THE STATE
IN FRONT. One theorem: a call.

What is said. `speaks_paid`: at the constant's own head h and an opening O at its letters, for every
Rch: if at every state with the table's condition at 346 that is reached and bears no mark the
reads' tables that lie in the state are the ones that the readers' second arm would lay
(`TablesLaid`, Johnson/Top/H0/MergeLaw/SpeaksOfTables.lean), then K11Cond's field speaks holds, to
the letter. It is `speaks_at_front` (SpeaksAtFront.lean) at the constant;
the link by `linkAt_of_open` (Johnson/ToldDescR/PureChainOfOpen.lean); the head's segment's
number from the scope.

Limits. `TablesLaid` is a premise here. It is shown at every reached state at 346, from the scope
and an opening, in TablesAt346.lean; CondOfTight.lean joins the two.
The field speaks has been evaluated true at an honest state at 346, at two sizes (in runs
outside this file, not shown here); `TablesLaid` itself has been
evaluated nowhere. Nothing on soundness.

-/
import Johnson.K11R.LawAtMg
import Johnson.Top.H0.MergeLaw.SpeaksAtFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace K11

open OnBytes.Maker OnBytes.Flat OnBytes.Slice
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.Desc.First.MergeLaw
open P5J (AtMgA mgAtAll TS)
open ProofFile (Cl)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {F : FileDescription ProofFile.Inst} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

set_option maxRecDepth 100000 in
/-- **The field speaks of `K11Cond`, from `TablesLaid` at the reached states in front.** -/
theorem speaks_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A B) {Fr : Frame}
    (Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop)
    (ht : ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str),
      onQ h.𝔇.N (mgAtAll h) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
      Rch 346 ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      TablesLaid (VerifiableInference.Desc.K9.phAt (P5J.At.X Zp) 24) a.1) :
    ∀ l, cF.links[24]? = some l → ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str),
      onQ h.𝔇.N (mgAtAll h) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
      Rch 346 ((z, a.1), a.2) → ¬ a.1.failed ≠ none → Speaks l a.1 := by
  intro l hl z a ha hR hm
  have hH : VerifiableInference.OnPublicFiles.headLink (P5J.At.X Zp) = 24 := by
    obtain ⟨p4, ng, -⟩ := Meaning.scope_plans h.scope h.reads h.pubOne
    unfold VerifiableInference.OnPublicFiles.headLink
    rw [p4, ng]
    rfl
  exact speaks_at_front h.𝔇 mgBase rfl rfl hH h.𝔇.N z a ha (Classical.not_not.1 hm)
    ((ToldDesc.linkAt_of_open O 24).trans hl) (ht z a ha hR hm)

end K11

#print axioms K11.speaks_paid
