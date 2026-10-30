-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/BlindAtAll.lean: KIND K11 (THE MERGE): AT THE CLOSED CONSTANT'S STRUCTURE OF
LETTERS THE TWO READERS OF THE VERIFIER'S STATE DO NOT READ WHAT THE MERGE WRITES. Two statements
with their proofs, and the two together. NO SOUNDNESS.

Several of the merge's laws take two premises on the filling's readers (hdec, hsmp: `merge_hcb`,
Johnson/Top/H0/MergeLaw/CtxBack.lean; `merge_tiedAtR`, TiesReached.lean; the second tie at the
composed meaning, SecondTieAt.lean): the decoder of the stored table and the reader of samples give
the same at a state s and at s with the two fields laid that an accepting merge writes (rowsOwed,
here). Here both are paid at the structure of letters of the closed constant
(`AtMgA.𝔇 h`, Johnson/P5J/MgAtAll.lean), at every h.
  `blind_decT`: hdec to the letter: its decoder reads no state at all (`P5J.At.noRec_decT`,
    Johnson/P5J/LettersAt.lean).
  `blind_smp`: hsmp to the letter: its reader of samples is `smpNamed`, which reads the state's
    statement alone (`smpNamed_same`, Johnson/Desc/Sound/SmpNamed.lean), and the two fields are not
    the statement.
  `blind_atAll`: both.
Limits. h : AtMgA … stands under "for all": that such an h exists is shown nowhere here: if none
does, the statements are empty. Nothing on what the two readers give. AT THE CONSTANT AS IMPORTED: a
text that lays another decoder or reader owes these again (the proofs then break). Of
completeness's kind: no error term; nothing on soundness; nothing on hiding.

-/
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.Sound (smpNamed_same)
open P5J (AtMgA TS)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **hdec at the constant**: the decoder does not read what the merge writes. -/
theorem blind_decT (h : AtMgA o Z D r Zp Np cF x) :
    ∀ z c (s : S) (a' : HeadOwn),
      h.𝔇.decT c (z, { s with rowsOwed := none, here := .head a' }) =
        h.𝔇.decT c (z, s) :=
  fun z c _ _ => P5J.At.noRec_decT o Zp Np cF (P5J.At.EAt Z) h.plan.shape c z _ _

/-- **hsmp at the constant**: nor does the reader of samples. -/
theorem blind_smp (h : AtMgA o Z D r Zp Np cF x) :
    ∀ z (s : S) (a' : HeadOwn),
      h.𝔇.smp (z, { s with rowsOwed := none, here := .head a' }) = h.𝔇.smp (z, s) := by
  intro z s a'
  funext t i
  exact smpNamed_same (P5J.At.cs Zp) (P5J.At.seats Zp) (z, s)
    (z, { s with rowsOwed := none, here := .head a' }) rfl t i

/-- Both. -/
theorem blind_atAll (h : AtMgA o Z D r Zp Np cF x) :
    (∀ z (s : S) (a' : HeadOwn),
      h.𝔇.smp (z, { s with rowsOwed := none, here := .head a' }) = h.𝔇.smp (z, s)) ∧
    ∀ z c (s : S) (a' : HeadOwn),
      h.𝔇.decT c (z, { s with rowsOwed := none, here := .head a' }) =
        h.𝔇.decT c (z, s) :=
  ⟨blind_smp h, blind_decT h⟩

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.blind_decT
#print axioms VerifiableInference.Desc.First.MergeLaw.blind_smp
#print axioms VerifiableInference.Desc.First.MergeLaw.blind_atAll
