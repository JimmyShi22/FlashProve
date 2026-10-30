-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/T3/KindPaysCore.lean: KindPays G κ: what is asked of one kind, with light imports: the library's honest frame alone, so that every kind's files can state it without the
compiler's files. The rest of the way from the kinds to Owed is in Johnson/T3/OwedOfKinds.lean, which imports this file. No value of KindPays is given here.
-/
import Johnson.Desc.ProofFile.Honest.Owed

set_option autoImplicit false

namespace VerifiableInference.Compilation
open ProofFile.Honest (ProverCoinCounts Sides Good orderOf preOf earlierOf)
open VerifiableInference.Desc (FileDescription KindName)

section Kinds
variable {Xi W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}

/-- **What is asked of one kind**: at every list of parts that stands at a place of that kind, in each of the three chains, the list fits its
block; each part has a simulator that is exact; each owner is fresh. These are Good's fields fits, exact and fresh; plays and acc are
completeness's: at A' := False they hold for nothing, so the existentials leave them unasked. -/
def KindPays (G : Sides F Bk W₀ Rc Ky Tr X₀ X) (κ : KindName) : Prop :=
  (∀ L ∈ G.first, L.place.kind = κ → ∀ σ, L.side F.first.blocksInOrder G.falls₁ = some σ →
      ∃ A' B', Good (preOf 0 0 (earlierOf F 0) F.first.blocksInOrder L.place) .own σ Bk (orderOf F) 0 0 A' B'
        L.On L.bud) ∧
  (∀ L ∈ G.shared, L.place.kind = κ → ∀ σ, L.side F.shared.blocksInOrder G.falls₂ = some σ →
      ∃ A' B', Good (preOf 1 0 (earlierOf F 1) F.shared.blocksInOrder L.place) .shared σ Bk (orderOf F) 1 0
        A' B' L.On L.bud) ∧
  (∀ L ∈ G.second, L.place.kind = κ → ∀ σ, L.side F.second.blocksInOrder G.falls₃ = some σ →
      ∃ A' B', Good (preOf 2 F.lastChainFirstTreeNumber (earlierOf F 2) F.second.blocksInOrder L.place) .own σ Bk
        (orderOf F) 2 F.lastChainFirstTreeNumber A' B' L.On L.bud)

end Kinds

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.KindPays
