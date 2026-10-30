-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Hears/OfFit.lean: rounds that pass the step's own test on the
rounds are heard, with the sealed digests struck, from a ledger with room. One statement with its
proof ON THE VERIFIER's TEXT; no prover is in this file, and no goal is stated.

  `hears_of_fit`    **`roundsFit` at the table's declared rounds, a well laid ledger with room, and
                    lt coordinates of the lookup's point on the positions: the head's hearing
                    returns on the rounds with the digests struck**, with what `hears_shaped` says
                    of the ledger behind and of the five lengths

Limits. CONDITIONAL, as Honest/K6/Hears/Shaped.lean: on the ledger's make, on room and on zt's
length; and on the test's yes: THAT THE HONEST SIDE's ROUNDS PASS THE TEST IS NOT SHOWN HERE. It
lays two theorems together and adds nothing: `hears_shaped` (Shaped.lean) and `shapedNZ_of_fit` with
`rounds_noSeeds` (Johnson/Desc/Kinds/Law/K06FitsShape.lean, Law/K06EveryList.lean). The
declared rounds are written as the seated block has them (`blockAt_rounds`, Law/K06HonestStep.lean,
at the sizes and the work of the block's public numbers); that equation is not called here. Nothing
on the decision's other tests or on the step.
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K6.Hears.Shaped
import Johnson.Desc.Kinds.Law.K06FitsShape

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace ProofFile.Honest.K6.Hears
open OnBytes.Model (Fork)
open VerifiableInference.Desc (roundsFit noDigest)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head (HeardAll)
open VerifiableInference.Desc.Kinds.Head.Law (WellLaid Fresh)

variable [Head.Sizes] [Head.Policy] [Head.Request] [Head.Token] [FinalNorm.In] [Head.In]

/-- **ROUNDS THAT PASS THE STEP's TEST ARE HEARD, WITH THE DIGESTS STRUCK.** work: the bits of work
in the declared rounds' entries. -/
theorem hears_of_fit (work : Nat) {F : Fork} {m : Nat} (hW : WellLaid F)
    (hF : Fresh F (41 + 8 * Norm.lt + 4 * Norm.lPd + m)) (hzt : (FinalNorm.zt).size = Norm.lt)
    (rs : List Fmt.RoundView)
    (hf : roundsFit ((Head.rounds : List Round).map fun R =>
      ({ entry := R.entry work } : Fmt.DeclaredRound)) rs = true) :
    ∃ (H : HeardAll) (G : Fork), Head.hear F (rs.map noDigest) = some (H, G, []) ∧ WellLaid G ∧
      Fresh G m ∧ G.next = F.next + (41 + 8 * Norm.lt + 4 * Norm.lPd) ∧ G.ns = F.ns ∧
      H.1.pV.size = Norm.lt ∧ H.1.squares.r.size = Norm.lPd + Norm.lt ∧
      H.1.products.r.size = Norm.lt ∧ H.2.1.normed.r.size = Norm.lt ∧
      H.2.2.logits.r.size = Norm.lt + Norm.lPd :=
  hears_shaped hW hF hzt _ (Head.Law.shapedNZ_of_fit work rs _ Head.Law.rounds_noSeeds hf)

#print axioms hears_of_fit

end ProofFile.Honest.K6.Hears
