-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/SeatedM4.lean: WHAT ONE SENDING LAYS INTO THE RECORD's BOOK, WHOLE
(`K1.SeatedBy`, Johnson/Desc/K1/Law/SeatedAtRecord.lean), AT W's COMMITMENT WITH KIND K13's BLOCK
BEHIND IT. One statement with its proof. A file of its own, so that whoever calls it imports no
table of joints.
  `atM4_seated`: kind K13's block behind the sending leaves the book, the count of roots and the
    number of messages.
What is not claimed. Nothing beyond `K1.SeatedBy`'s own words. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.AtRecord
import Johnson.Desc.K1.Law.SeatedAtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice
open VerifiableInference.Desc.First (S)

variable {Cl : Type}

/-- **W's commitment with the kind's block behind it.** -/
theorem atM4_seated {P : Where} {P' : K1.Par} {s s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (atM4 (Cl := Cl) P (K1.sendAtS P')).decide s [r₁, r₂] gs = .ok s') :
    K1.SeatedBy P' s.book s.st.oracles.size s.roots s'.book s'.st.oracles.size s'.roots := by
  obtain ⟨s₁, g₁, rs₂, g₂, h1, h2⟩ := atM4_mid h
  have hb := K1.sendAtS_seated P' s s₁ r₁ r₂ g₁ h1
  have hn := sameAll_size (rowsB_same h2)
  obtain ⟨m₀, l, o, owed, _, _, _, rfl⟩ := rowsB_at h2
  exact ⟨hb.lay, hb.seated, hb.roots, hn.trans hb.msgs⟩

end VerifiableInference.Desc.K13.Law
