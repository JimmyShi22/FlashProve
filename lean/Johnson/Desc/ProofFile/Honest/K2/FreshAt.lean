-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/FreshAt.lean: the kind "the code switch" (K2): THE SECOND STATEMENT
(Honest/K2/Fresh.lean) IN A FORM FOR EACH SPENDER: ONE SENTENCE AT ONE ADDRESS, FROM PREMISES AT
THAT ADDRESS. A STATEMENT, PROVED IN Honest/K2/Law/FreshAtProof.lean (`switchFreshAt`). Definitions;
and lines that hold the cut forms against the whole ones. The statement is none of the library's
goals.

WHY. `FreshAsks` asks its test on the book, and the sender's second law, AT EVERY ADDRESS: one
address at which the test says no leaves `SwitchFresh` silent at all. Here each address stands for
itself.

  `FreshOfAt`       the field `fresh` of `Good` (`FreshOf`, Honest/K2/Fresh.lean), at one address
  `freshOf_iff`     the field holds just if it holds at every address
  `FreshAsksAt`     ALL PREMISES, by name: seated · blocks · two · fits · seeds · oneRow, as in
                    `FreshAsks`; book · sendFresh: at the one address
  `FreshAsks.at_`   the whole list of premises gives the list at each address
  `SwitchFreshAt`   THE STATEMENT, AT ALL ITS LETTERS: `FreshAsksAt` gives `FreshOfAt` at
                    `switchBud`
  `switchFresh_of_at`   the statement at every address gives `SwitchFresh`

Limits. THE STATEMENT IS NOT PROVED HERE. Its premises are shown here at no address. `FreshAsks`,
which gives them at every address (`FreshAsks.at_`), is had at the switches of even link, under the
library's head, the opened description and a return of `bookWhole`: `freshAsks_at_switch`
(AtFullSide/K2/BookAtSwitches.lean). What Honest/K2/Fresh.lean's limits say of `SendFreshLaw`,
`book` and `bookFits` holds here. Nothing here says what the statement would mean for any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Fresh

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open VerifiableInference.Desc (Oracle Block Place)

variable {W₀ Rc Xi Tr X S Cl : Type}

/-- The field `fresh` of `Good`, at one address. -/
def FreshOfAt (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) (Bk : ProverCoinCounts)
    (ord : List Place) (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) (p : Addr) :
    Prop :=
  ∀ u ∈ σ.members, ∀ sp ca m ds asks,
    drawsFit (u.rounds.map (·.1)) ds = true → bud u.number ds asks →
    u.part.stopAt (Face.own.sees m.st.input) m.loc ds ≠ some .hid →
    (Prob.unif (Cs u.part.takes)).map (fun c =>
        (cutAll c (Bk.spentBy ⟨σ.block.place, u.number⟩ p), σ.shows .own u (c, sp, ca) m ds asks,
          cutAll c (Bk.knownBy ord ⟨σ.block.place, u.number⟩ p))) =
      (Prob.unif (CsAll ((Bk.spentBy ⟨σ.block.place, u.number⟩ p).map Ahead.named) ×
          Cs u.part.takes)).map fun a =>
        (some a.1, σ.shows .own u (a.2, sp, ca) m ds asks,
          cutAll a.2 (Bk.knownBy ord ⟨σ.block.place, u.number⟩ p))

/-- The field holds just if it holds at every address. -/
theorem freshOf_iff (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) (Bk : ProverCoinCounts)
    (ord : List Place) (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) :
    FreshOf σ Bk ord bud ↔ ∀ p, FreshOfAt σ Bk ord bud p :=
  ⟨fun h p u hu sp ca m ds asks => h u hu p sp ca m ds asks,
    fun h u hu p sp ca m ds asks => h p u hu sp ca m ds asks⟩

/-- **All premises**, at one address. -/
structure FreshAsksAt (Sd : Sender) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (ok : Xi → Bool)
    (rounds : List (Fmt.DeclaredRound × List Oracle)) (bs : List (Block S Cl)) (fs : List (Fall S))
    (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) (Bk : ProverCoinCounts) (ord : List Place)
    (q : Addr) : Prop where
  seated : Side.seated bs p.place (switchRow Sd D readers closing p ok rounds) fs = some σ
  blocks : σ.block.rounds.zip σ.block.oracles = rounds
  two : rounds.length = 2
  fits : K1.sendFits (sendingPar p.sizes.codes (switchSent p.sizes p.others))
    (rideOf (switchSent p.sizes p.others) (switchFresh p.sizes p.others p.foldVars)) = true
  seeds : ∀ r ∈ rounds.head?, ∀ d : Fmt.Drawn, drawFit r.1 d = true →
    seedsFit p.sizes.codes (switchSent p.sizes p.others) d.elems
  oneRow : ∀ x ∈ switchFresh p.sizes p.others p.foldVars,
    ((switchSent p.sizes p.others).getD x.1 default).shape.maskRows = 1
  book : bookFits p.sizes.codes (switchSent p.sizes p.others)
    (switchFresh p.sizes p.others p.foldVars) (Bk.spentBy ⟨p.place, 0⟩ q)
    (Bk.knownBy ord ⟨p.place, 0⟩ q) = true
  sendFresh : SendFreshLaw Sd p.sizes.codes (switchSent p.sizes p.others)
    (switchFresh p.sizes p.others p.foldVars) (Bk.spentBy ⟨p.place, 0⟩ q)
    (Bk.knownBy ord ⟨p.place, 0⟩ q)

/-- The whole list of premises gives the list at each address. -/
theorem FreshAsks.at_ {Sd : Sender} {D : RowDataOf Xi} {readers : Local W₀ Rc Xi Tr → Readers}
    {closing : Closing} {p : SwitchPlace} {ok : Xi → Bool}
    {rounds : List (Fmt.DeclaredRound × List Oracle)} {bs : List (Block S Cl)} {fs : List (Fall S)}
    {σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi} {Bk : ProverCoinCounts} {ord : List Place}
    (h : FreshAsks Sd D readers closing p ok rounds bs fs σ Bk ord) (q : Addr) :
    FreshAsksAt Sd D readers closing p ok rounds bs fs σ Bk ord q :=
  ⟨h.seated, h.blocks, h.two, h.fits, h.seeds, h.oneRow, h.book q, h.sendFresh q⟩

/-- **THE STATEMENT**, meant at all its letters. Not proved here: `switchFreshAt`,
Honest/K2/Law/FreshAtProof.lean. -/
def SwitchFreshAt (Sd : Sender) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (ok : Xi → Bool)
    (rounds : List (Fmt.DeclaredRound × List Oracle)) (bs : List (Block S Cl)) (fs : List (Fall S))
    (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) (Bk : ProverCoinCounts) (ord : List Place)
    (q : Addr) : Prop :=
  FreshAsksAt Sd D readers closing p ok rounds bs fs σ Bk ord q →
    FreshOfAt σ Bk ord (switchBud p) q

/-- The statement at every address gives the statement of Honest/K2/Fresh.lean. -/
theorem switchFresh_of_at (Sd : Sender) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing) (p : SwitchPlace) (ok : Xi → Bool)
    (rounds : List (Fmt.DeclaredRound × List Oracle)) (bs : List (Block S Cl)) (fs : List (Fall S))
    (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) (Bk : ProverCoinCounts) (ord : List Place)
    (h : ∀ q, SwitchFreshAt Sd D readers closing p ok rounds bs fs σ Bk ord q) :
    SwitchFresh Sd D readers closing p ok rounds bs fs σ Bk ord :=
  fun a => (freshOf_iff σ Bk ord (switchBud p)).2 fun q => h q (a.at_ q)

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.freshOf_iff
#print axioms ProofFile.Honest.K2.FreshAsks.at_
#print axioms ProofFile.Honest.K2.switchFresh_of_at
