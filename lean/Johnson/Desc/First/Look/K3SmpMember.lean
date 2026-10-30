-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3SmpMember.lean: THE TYPE OF SAMPLES OF A SIGNATURE HAS A MEMBER: so the
letter σ₀ of the lookups' laws (k3_digits_seated_kept and its like) can always be filled. Two
statements with their proofs.
Why it holds: the library's record Sample (Cb/Gen/OodDec.lean:132-136) bears «the seeds' type is not
empty» AS A FIELD (ne : Nonempty D); a member's sample is a seed with its answers (OMsg.Smp := Z.D ×
(Z.S → E), Cb/Ld/LdSig.lean:181); a signature's is one for each member (:245).
  smp_nonempty: for every signature S over a type with a zero.  digSmp_nonempty: at the digits'
  lookup's signature.
OBJECT: Cb.Sig.Smp. LETTERS: general in S; x, D, rad.
Used by K3CallsMeanOf.lean, K3CallsMeanR.lean, K3DigitsRestR.lean (Johnson/Desc/First/Look/) and 1
  more.
Limits. A member by choice: nothing on which sample a record holds. Nothing on soundness.

-/
import Johnson.Desc.First.Look.K3Caller

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.First.Look

theorem smp_nonempty {E : Type} [Zero E] (S : Cb.Sig E) : Nonempty S.Smp :=
  ⟨fun a => (Classical.choice (S.om a).Z.ne, fun _ => 0)⟩

theorem digSmp_nonempty (x : Desc.First.Look.Place) (D : Desc.First.Look.Sent)
    (rad : OnBytes.OracleShape → ℕ) : Nonempty (digSg x D rad).Smp :=
  smp_nonempty _

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.smp_nonempty
#print axioms VerifiableInference.OnPublicFiles.digSmp_nonempty
