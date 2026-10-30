-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/FreshAtProof.lean: the kind "the code switch" (K2): THE SECOND
STATEMENT IS PROVED, IN ITS FORM FOR EACH SPENDER (`SwitchFreshAt`, Honest/K2/FreshAt.lean) AND SO
IN ITS FIRST FORM (`SwitchFresh`, Honest/K2/Fresh.lean): IMPLICATIONS FROM THEIR NAMED PREMISES; AND
WHERE NOTHING IS SPENT AT AN ADDRESS THE FRAME's SENTENCE HOLDS THERE WITH NO PREMISE: SO WHAT IS
OWED FOR THE FRAME's FIELD `fresh` SHRINKS TO THE ADDRESSES THAT SPEND OF THIS SIDE's COINS.
Statements with their proofs.

  `switchFreshAt`   THE IMPLICATION, AT ALL ITS LETTERS: `FreshAsksAt` at an address gives
                    `FreshOfAt` there, by the equation of Honest/K2/Law/FreshProof.lean
  `switchFresh`     THE IMPLICATION OF Honest/K2/Fresh.lean: `FreshAsks` gives `FreshOf`: from
                    `switchFreshAt` at every address: ONE PROOF TEXT FOR BOTH
  `idle_eq`         a tool: where the list of entries that are spent is empty the two sides of the
                    frame's equation are one law
  `fresh_idle`      at any side, book and order, at ONE member: nothing spent at an address of that
                    member's coins: the frame's equation at that member and address, with no premise
  `freshOfAt_idle`  so, if that is so of every member: `FreshOfAt` there, with no premise
  `freshOf_of_spenders`   so `FreshOf` follows from `FreshOfAt` at the addresses that spend of this
                    side's coins
  `freshOf_noSpender`   and where no address spends of them `FreshOf` holds with no premise at all
  `switchFresh_of_spenders`   for the switch: `FreshAsksAt` at these addresses alone gives `FreshOf`

Limits. IMPLICATIONS: the premises of `FreshAsksAt` are shown here at no address. What
Honest/K2/Fresh.lean's limits say of `SendFreshLaw`, `book` and `bookFits` holds here. Nothing here
says what the statements would mean for any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.FreshProof
import Johnson.Desc.ProofFile.Honest.K2.FreshAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Oracle Block Place)

variable {S Cl W₀ Rc Xi Tr X : Type}

/-- **THE IMPLICATION, FOR EACH SPENDER.** -/
theorem switchFreshAt (Sd : Sender) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (ok : Xi → Bool)
    (rounds : List (Fmt.DeclaredRound × List Oracle)) (bs : List (Block S Cl)) (fs : List (Fall S))
    (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) (Bk : ProverCoinCounts) (ord : List Place)
    (q : Addr) : SwitchFreshAt Sd D readers closing p ok rounds bs fs σ Bk ord q := by
  intro h u hu sp ca m ds asks hd hbud _
  obtain ⟨⟨d₁, o₁⟩, ⟨d₂, o₂⟩, rfl⟩ := List.length_eq_two.1 h.two
  obtain ⟨b, hfind, rfl⟩ := Option.map_eq_some_iff.1 h.seated
  have hpl : b.place = p.place := seated_place hfind
  rw [switch_members Sd D readers closing p ok (d₁, o₁) (d₂, o₂) b _ h.blocks] at hu
  obtain rfl := List.mem_singleton.1 hu
  obtain ⟨x₁, x₂, rfl, hx₁⟩ := draws_two d₁ d₂ ds hd
  have hseeds : seedsFit p.sizes.codes (switchSent p.sizes p.others) x₁.elems :=
    h.seeds (d₁, o₁) rfl x₁ hx₁
  have hasks : asksWithin p.sizes.codes (switchSent p.sizes p.others) ((asks[0]?).getD []) := by
    have h0 : asksWithin p.sizes.codes (switchSent p.sizes p.others) (asks.headD []) := hbud
    rwa [headD_get] at h0
  have hbook := h.book
  have hsend := h.sendFresh
  rw [← hpl] at hbook hsend
  exact fresh_at Sd D readers closing p d₁ d₂ o₁ o₂ b.name ⟨b.place, 0⟩ (some m.st.input)
    (Bk.spentBy ⟨b.place, 0⟩ q) (Bk.knownBy ord ⟨b.place, 0⟩ q) sp ca m x₁ x₂ asks
    (fun data => hsend h.fits h.oneRow hbook data x₁.elems ((asks[0]?).getD []) hseeds hasks)

/-- **THE IMPLICATION OF Honest/K2/Fresh.lean**: from the form for each spender, at every
address. -/
theorem switchFresh (Sd : Sender) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (ok : Xi → Bool)
    (rounds : List (Fmt.DeclaredRound × List Oracle)) (bs : List (Block S Cl)) (fs : List (Fall S))
    (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) (Bk : ProverCoinCounts) (ord : List Place) :
    SwitchFresh Sd D readers closing p ok rounds bs fs σ Bk ord :=
  switchFresh_of_at Sd D readers closing p ok rounds bs fs σ Bk ord
    (switchFreshAt Sd D readers closing p ok rounds bs fs σ Bk ord)

theorem idle_eq {d : Due} {β γ : Type} (es : List Ahead) (hes : es = []) (f : Cs d → β)
    (g : Cs d → γ) :
    (Prob.unif (Cs d)).map (fun c => (cutAll c es, f c, g c)) =
      (Prob.unif (CsAll (es.map Ahead.named) × Cs d)).map fun a => (some a.1, f a.2, g a.2) := by
  subst hes
  have e : (fun a : CsAll (([] : List Ahead).map Ahead.named) × Cs d =>
      ((some a.1 : Option (CsAll (([] : List Ahead).map Ahead.named))), f a.2, g a.2)) =
      (fun c : Cs d => (cutAll c ([] : List Ahead), f c, g c)) ∘ Prod.snd := by
    funext a
    rfl
  rw [e, ← PMF.map_comp, Prob.map_snd_unif]

/-- **Nothing spent at an address of one member's coins: the frame's equation there, with no
premise.** -/
theorem fresh_idle (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) (Bk : ProverCoinCounts)
    (ord : List Place) (q : Addr) (u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (h₀ : Bk.spentBy ⟨σ.block.place, u.number⟩ q = []) (sp : CsAll u.part.spends)
    (ca : CsAll u.part.carries) (m : Mid (Local W₀ Rc Xi Tr) X) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))) :
    (Prob.unif (Cs u.part.takes)).map (fun c =>
        (cutAll c (Bk.spentBy ⟨σ.block.place, u.number⟩ q), σ.shows .own u (c, sp, ca) m ds asks,
          cutAll c (Bk.knownBy ord ⟨σ.block.place, u.number⟩ q))) =
      (Prob.unif (CsAll ((Bk.spentBy ⟨σ.block.place, u.number⟩ q).map Ahead.named) ×
          Cs u.part.takes)).map fun a =>
        (some a.1, σ.shows .own u (a.2, sp, ca) m ds asks,
          cutAll a.2 (Bk.knownBy ord ⟨σ.block.place, u.number⟩ q)) :=
  idle_eq _ h₀ (fun c => σ.shows .own u (c, sp, ca) m ds asks)
    (fun c => cutAll c (Bk.knownBy ord ⟨σ.block.place, u.number⟩ q))

/-- So of every member: the frame's sentence at that address, with no premise. -/
theorem freshOfAt_idle (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) (Bk : ProverCoinCounts)
    (ord : List Place) (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) (q : Addr)
    (h₀ : ∀ u ∈ σ.members, Bk.spentBy ⟨σ.block.place, u.number⟩ q = []) :
    FreshOfAt σ Bk ord bud q := by
  intro u hu sp ca m ds asks _ _ _
  exact fresh_idle σ Bk ord q u (h₀ u hu) sp ca m ds asks

/-- So the frame's field follows from its sentences at the addresses that spend of this side's
coins. -/
theorem freshOf_of_spenders (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (Bk : ProverCoinCounts) (ord : List Place) (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
    (h : ∀ q, (∃ u ∈ σ.members, Bk.spentBy ⟨σ.block.place, u.number⟩ q ≠ []) →
      FreshOfAt σ Bk ord bud q) : FreshOf σ Bk ord bud := by
  refine (freshOf_iff σ Bk ord bud).2 fun q => ?_
  by_cases hq : ∃ u ∈ σ.members, Bk.spentBy ⟨σ.block.place, u.number⟩ q ≠ []
  · exact h q hq
  · refine freshOfAt_idle σ Bk ord bud q fun u hu => ?_
    by_contra hne
    exact hq ⟨u, hu, hne⟩

/-- Where no address spends of this side's coins the field holds with no premise at all. -/
theorem freshOf_noSpender (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (Bk : ProverCoinCounts) (ord : List Place) (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
    (h₀ : ∀ q, ∀ u ∈ σ.members, Bk.spentBy ⟨σ.block.place, u.number⟩ q = []) :
    FreshOf σ Bk ord bud :=
  freshOf_of_spenders σ Bk ord bud fun q ⟨u, hu, hne⟩ => absurd (h₀ q u hu) hne

/-- **For the switch: the premises at the addresses that spend of its coins alone.** -/
theorem switchFresh_of_spenders (Sd : Sender) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing) (p : SwitchPlace) (ok : Xi → Bool)
    (rounds : List (Fmt.DeclaredRound × List Oracle)) (bs : List (Block S Cl)) (fs : List (Fall S))
    (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) (Bk : ProverCoinCounts) (ord : List Place)
    (h : ∀ q, (∃ u ∈ σ.members, Bk.spentBy ⟨σ.block.place, u.number⟩ q ≠ []) →
      FreshAsksAt Sd D readers closing p ok rounds bs fs σ Bk ord q) :
    FreshOf σ Bk ord (switchBud p) :=
  freshOf_of_spenders σ Bk ord (switchBud p) fun q hq =>
    switchFreshAt Sd D readers closing p ok rounds bs fs σ Bk ord q (h q hq)

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.switchFreshAt
#print axioms ProofFile.Honest.K2.Law.switchFresh
#print axioms ProofFile.Honest.K2.Law.idle_eq
#print axioms ProofFile.Honest.K2.Law.fresh_idle
#print axioms ProofFile.Honest.K2.Law.freshOfAt_idle
#print axioms ProofFile.Honest.K2.Law.freshOf_of_spenders
#print axioms ProofFile.Honest.K2.Law.freshOf_noSpender
#print axioms ProofFile.Honest.K2.Law.switchFresh_of_spenders
