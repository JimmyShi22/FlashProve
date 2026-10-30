-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Top/PubPlainLedger.lean: THE MASTER LEDGER, THE SEAM BETWEEN THE PLANNER's RETURN AND
    THE PUBLIC PART's: A LEDGER FOR `ProofFile.pubBy` (Johnson/Desc/ProofFile/Pub.lean): IT PAYS NOTHING:
    it names the six steps that stand between
`ProofFile.PlainG.madeOf … = .ok m` (where another file's `madeOf_of_madeAt` ends) and `ProofFile.pubPlain … =
    .ok Zq` (where `descPure_of_parts`, `laid_of_rows` and `rowsRead_of_live` begin).
  `pubOfParts`: the value that `pubBy` returns, from its parts: the text of its last step.
  `pubBy_of_parts`: the planner returns m · the codes' lengths are powers of two · declPOf m ·
      toldOf m · depthOf m return · the first chain's given rounds are cut · the first state is made
      ⟹ pubBy returns that value. General in the planner and
    the starts.
  **`pubPlain_of_parts`**: at the plain road, from the key file's two returns (hX · hm): the
      planner's value is `blankM m`.
  `blank_X`, `blank_chains`, `blank_proof`, `blank_key`: blanking the segments' routines leaves the
      field X, the chains and the sends: rfl. `pub_X` … : so the public part's X IS X₀'s
      letter m.p.X.
The laws on `pubBy` (pubBy_fields · pubBy_make · pubBy_made · pubBy_start · pubBy_cuts ·
    pubBy_par · pubBy_entries) all go the other way: from its return to its parts.
Limits. No premise is shown to be met. No soundness follows.

-/
import Johnson.AtFull.Top.OnePlanner
import Johnson.Desc.ProofFile.OnlineDescriptionPublicPart

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFull.Top
open ProofFile
open VerifiableInference.PlanWritten (publicOfO)
open VerifiableInference.Desc.Key (madeAt fixedDigest)

/-- The value that `pubBy` returns, from its parts. -/
def pubOfParts (st : Starts) (pol KL : ByteArray) (m : Johnson.G.OfPlan.Made)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (told : List Root × List Root × List Root) (depth : Nat)
    (cuts : List VerifiableInference.Desc.First.Cut) (s₀ : VerifiableInference.Desc.First.S) : Pub
        :=
  { pol := pol, KL := KL, made := m, P := st.par m.p.chains.proof.first, cuts := cuts, D := D
    told := told, depth := depth, s₀ := s₀ }

/-- **`pubBy` returns.** -/
theorem pubBy_of_parts
    {made : ByteArray → ByteArray → ByteArray → Except String Johnson.G.OfPlan.Made} {st : Starts}
    {pol lay KL : ByteArray} {m : Johnson.G.OfPlan.Made}
    {D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound}
    {told : List Root × List Root × List Root} {depth : Nat}
    {cuts : List VerifiableInference.Desc.First.Cut} {s₀ : VerifiableInference.Desc.First.S}
    (u₁ : made pol lay KL = .ok m)
    (u₂ : m.p.chains.proof.first.codes.lengthsOk = true)
    (u₃ : Johnson.G.OfPlan.declPOf m = .ok D)
    (u₄ : toldOf m = .ok told)
    (u₅ : Johnson.G.OfPlan.depthOf m = .ok depth)
    (u₆ : VerifiableInference.Desc.First.cutOf m.p.chains.proof.first.given.rounds = some cuts)
    (u₇ : st.start (st.par m.p.chains.proof.first) m.p.chains.proof.first = some s₀) :
    pubBy made st pol lay KL = .ok (pubOfParts st pol KL m D told depth cuts s₀) := by
  unfold pubBy pubOfParts
  simp only [u₁, u₂, u₃, u₄, u₅, u₆, u₇, atCall, orSay, Except.mapError, Option.elim, bind,
    Except.bind, pure, Except.pure, Bool.not_true, Bool.false_eq_true, if_false]

theorem blank_X (m : Johnson.G.OfPlan.Made) : (ProofFile.Law.blankM m).p.X = m.p.X := rfl
theorem blank_chains (m : Johnson.G.OfPlan.Made) : (ProofFile.Law.blankM m).p.chains = m.p.chains := rfl
theorem blank_proof (m : Johnson.G.OfPlan.Made) : (ProofFile.Law.blankM m).proof = m.proof := rfl
theorem blank_key (m : Johnson.G.OfPlan.Made) : (ProofFile.Law.blankM m).key = m.key := rfl

/-- **`pubPlain` returns**, from the key file's two returns and the six steps. -/
theorem pubPlain_of_parts {o : SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {X₀ : OnBytes.Model.Verify.Public} {m : Johnson.G.OfPlan.Made}
    {D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound}
    {told : List Root × List Root × List Root} {depth : Nat}
    {cuts : List VerifiableInference.Desc.First.Cut} {s₀ : VerifiableInference.Desc.First.S}
    (hX : publicOfO o pol KL (some lay) = .ok X₀) (hm : madeAt X₀ lay fixedDigest = .ok m)
    (u₂ : m.p.chains.proof.first.codes.lengthsOk = true)
    (u₃ : Johnson.G.OfPlan.declPOf (ProofFile.Law.blankM m) = .ok D)
    (u₄ : toldOf (ProofFile.Law.blankM m) = .ok told)
    (u₅ : Johnson.G.OfPlan.depthOf (ProofFile.Law.blankM m) = .ok depth)
    (u₆ : VerifiableInference.Desc.First.cutOf m.p.chains.proof.first.given.rounds = some cuts)
    (u₇ : plainStarts.start (plainStarts.par m.p.chains.proof.first) m.p.chains.proof.first =
      some s₀) :
    pubPlain o pol lay KL =
      .ok (pubOfParts plainStarts pol KL (ProofFile.Law.blankM m) D told depth cuts s₀) :=
  pubBy_of_parts (FlashProve.madeOf_of_madeAt hX hm) u₂ u₃ u₄ u₅ u₆ u₇

/-- The public part's X is the planner's. -/
theorem pub_X (st : Starts) (pol KL : ByteArray) (m : Johnson.G.OfPlan.Made)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (told : List Root × List Root × List Root) (depth : Nat)
    (cuts : List VerifiableInference.Desc.First.Cut) (s₀ : VerifiableInference.Desc.First.S) :
    (pubOfParts st pol KL (ProofFile.Law.blankM m) D told depth cuts s₀).made.p.X = m.p.X := rfl

end AtFull.Top

#print axioms AtFull.Top.pubBy_of_parts
#print axioms AtFull.Top.blank_X
#print axioms AtFull.Top.blank_chains
#print axioms AtFull.Top.blank_proof
#print axioms AtFull.Top.blank_key
#print axioms AtFull.Top.pubPlain_of_parts
#print axioms AtFull.Top.pub_X
