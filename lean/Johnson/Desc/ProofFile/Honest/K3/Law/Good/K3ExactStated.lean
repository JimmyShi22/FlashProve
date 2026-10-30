-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Good/K3ExactStated.lean: THE FIELDS exact AND fresh OF THE
FRAME'S `Good` AT THE LOOKUP'S ROW: TWO STATEMENTS. Their terms lie in
Honest/K3/Law/Good/K3Exact.lean [not in this library]. Definitions of sentences; no theorem; one
example, by unfolding, on which side is meant.

  `RowStated f σ` THE PREMISES BY NAME, at the side's own members: at each stage of the row that has
    a sumcheck: the library's test on ITS shape; the member's own declared rounds state just the
    call's scalars and no oracle message; they mark Y's challenge as never 0. At each stage that
    sends nothing: its one round states nothing
  `OwnsNone Bk σ` by the book no part spends a run of coins of a part of this row
  `ExactK3` the field exact, in its own text at one member (`ExactMember`, Honest/Small/Field.lean),
    at every member of the row's own side (the frame's `Side.seated` at the site's place and
    `rowPairs`: the side that `k3Lettered` yields), at On and bud laid as "true", under `RowStated`
  `FreshK3` the field fresh likewise (`FreshMember`), under `OwnsNone`
The face, the book, the order of places, the chain's number and its first tree are variables.

HOW THE TERMS GO: by cases on the member. A stage with a sumcheck: the masked sumcheck's part,
lifted, beside its simulator: Honest/SumLaw/SumExact.lean: `exact_sumPart_field`. A stage that sends
nothing: Honest/Small/Quiet.lean: `quietPart_exact_lift`, with Honest/K3/RowQuietIs.lean. The second
sentence: Honest/Law/ToyLaw.lean: `fresh_of_nil`. Calls alone.

WHAT MAY BE SAID of the two sentences and of their terms is not this file's
to say. The riders and limits of the laws that are called stand in the heads of the files
that hold them, in their writers' words: Honest/SumLaw/SumExact.lean, Honest/Small/Quiet.lean,
Honest/Law/ToyLaw.lean.

Limits. Nothing is shown here, nor whether the premises hold at a site. On := "true" and bud :=
"true" are laid in `k3Lettered`, not earned. No instance of these hypotheses is exhibited in this
file. Nothing on any property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Good.K3Lettered
import Johnson.Desc.ProofFile.Honest.SumLaw.Fits
import Johnson.Desc.ProofFile.Honest.SumLaw.BetaMarked
import Johnson.Desc.ProofFile.Honest.Small.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.Part.MaskedSum (shapeOk)
open ProofFile.Honest.SumLaw (StatedBy betaMarked)
open ProofFile.Honest.Small (ExactMember FreshMember statedOf)

variable {Bk : ProverCoinCounts} {S Cl V W X Pb : Type}

/-- **The premises by name, at the side's own members.** f: the lookup's face. A member's number is
its stage's number in the row. -/
structure RowStated (f : LFace) (σ : Side S Cl V W X Pb) : Prop where
  /-- at a stage that has a sumcheck -/
  sums : ∀ u ∈ σ.members, ∀ st k, (stages f)[u.number]? = some st → st.call f = some k →
    shapeOk k = true ∧ StatedBy (scalarsOf k) u.rounds ∧ betaMarked k u.rounds = true
  /-- at a stage that sends nothing -/
  quiets : ∀ u ∈ σ.members, ∀ st, (stages f)[u.number]? = some st → st.call f = none →
    statedOf u.rounds = [([], [])]

/-- By the book no part spends a run of coins of a part of this row. -/
def OwnsNone (Bk : ProverCoinCounts) (σ : Side S Cl V W X Pb) : Prop :=
  ∀ u ∈ σ.members, ∀ p, Bk.spentBy ⟨σ.block.place, u.number⟩ p = []

/-- **THE FIELD exact AT THE LOOKUP'S ROW.** A statement; its term: `exact_k3`. -/
def ExactK3 (φ : Face V W Pb) (chain firstTree : Nat) (A : Fill W) (s : Site)
    (bs : List (Block S Cl)) (fs : List (Fall S)) : Prop :=
  ∀ σ : Side S Cl V W X Pb, Side.seated bs s.at_.place (rowPairs A s) fs = some σ →
    RowStated s.at_.face σ → ∀ u ∈ σ.members,
      ExactMember φ σ chain firstTree (fun _ _ _ _ => True) (fun _ _ _ => True) u

/-- **THE FIELD fresh AT THE LOOKUP'S ROW.** A statement; its term: `fresh_k3`. -/
def FreshK3 (φ : Face V W Pb) (Bk : ProverCoinCounts) (ord : List Place) (A : Fill W) (s : Site)
    (bs : List (Block S Cl)) (fs : List (Fall S)) : Prop :=
  ∀ σ : Side S Cl V W X Pb, Side.seated bs s.at_.place (rowPairs A s) fs = some σ →
    OwnsNone Bk σ → ∀ u ∈ σ.members, FreshMember φ σ Bk ord (fun _ _ _ => True) u

/-- The side of which the two sentences speak is the side that `k3Lettered` yields, at whatever
letters A', B'; its On and bud are the two that stand in them. By unfolding. -/
example (A : Fill W) (s : Site) (A' B' : Coins Bk → S → Mid W X → Env → Prop)
    (bs : List (Block S Cl)) (fs : List (Fall S)) :
    (k3Lettered (Cl := Cl) (V := V) (Pb := Pb) A s A' B').side bs fs =
        Side.seated bs s.at_.place (rowPairs A s) fs ∧
      (k3Lettered (Cl := Cl) (V := V) (Pb := Pb) A s A' B').On = (fun _ _ _ _ => True) ∧
      (k3Lettered (Cl := Cl) (V := V) (Pb := Pb) A s A' B').bud = (fun _ _ _ => True) :=
  ⟨rfl, rfl, rfl⟩

end ProofFile.Honest.K3.Law
