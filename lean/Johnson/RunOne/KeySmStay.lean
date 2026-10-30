-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeySmStay.lean: THE SENDING KIND's SmpStay (Johnson/Desc/K1/Law/SmpStay.lean: the codes stay; every SAMPLED message of A stands in B with its shape, mark and sample rows) GIVES SampleAlike (Johnson/RunOne/KeySmOnly.lean) AT EVERY SAMPLED MESSAGE: so a row's files that hold SmpStay across its block state NOTHING OF THEIR OWN on the record's fields: under BaseSt.SmOnly the tables' reading's sample at a seat whose message is sampled is unturned.
OBJECT: B.h₁.smp | B.h₂.smp · USER: rows 1.15 and 2.9 | 2.10; whoever walks a chain by SmpStay · LETTERS: T (the base).
  sampleAlike_of_smpStay   PROVED: glue: SmpStay's own text, leg by leg. KIN: rows_stay | smpAt_stay | smpS_held (Johnson/Desc/K1/Law/SmpHeldAt.lean): the like at THE SENDING KIND's FILES' OWN smpAt | smpS; none at BaseSt.smAt [by search].
  smp₁_of_smpStay | smp₂_of_smpStay   PROVED
SampleAlike SAYS MORE THAN SmpStay WHERE A MESSAGE IS NOT SAMPLED (it asks «sampled» alike there too): the ground's admitP | elsewhereP turn an unsampled message to sampled: SO AT AN UNSAMPLED MESSAGE SampleAlike CAN FAIL ACROSS A BLOCK: THESE LEMMAS SPEAK OF SAMPLED MESSAGES ALONE, which every open pin's message is.
Nothing on soundness.
-/
import Johnson.RunOne.KeySmOnly
import Johnson.Desc.K1.Law.SmpStay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key
open VerifiableInference.Desc.K1 (SmpStay)

theorem sampleAlike_of_smpStay (A B : Statement) (h : SmpStay A B) (o : Nat) (x : OnBytes.Oracle) (hx : A.oracles[o]? = some x) (hs : x.sampled = true) :
    SampleAlike A B o := by
  obtain ⟨x', hx', e1, e2, e3⟩ := h.2 o x hx hs
  exact ⟨h.1, Or.inr ⟨x, x', hx, hx', e1, e2.trans hs.symm, e3⟩⟩

variable {Cells M Smp Rec : Type} (T : BaseSt Cells M Smp Rec)

theorem smp₁_of_smpStay (h : T.SmOnly) (a a' : Xi × FirstState) (j t : Nat) (hS : SmpStay a.2.d.st a'.2.d.st)
    (hs : ∀ o, T.orc₁ (T.arr j t) = some o → ∃ x, a.2.d.st.oracles[o]? = some x ∧ x.sampled = true) : T.h₁.smp a' j t = T.h₁.smp a j t :=
  smp₁_of_only T h a a' j t fun o ho => by
    obtain ⟨x, hx, hm⟩ := hs o ho
    exact sampleAlike_of_smpStay _ _ hS o x hx hm

theorem smp₂_of_smpStay (h : T.SmOnly) (a a' : P₂ × St₂) (j t : Nat) (h1 : a'.1 = a.1) (hS : SmpStay a.2.st a'.2.st)
    (hs : ∀ o, orc₂ (T.arr j t) = some o → ∃ x, a.2.st.oracles[o]? = some x ∧ x.sampled = true) : T.h₂.smp a' j t = T.h₂.smp a j t :=
  smp₂_of_only T h a a' j t (fun o _ => by rw [h1]; exact sampleAlike_refl _ o) fun o ho => by
    obtain ⟨x, hx, hm⟩ := hs o ho
    exact sampleAlike_of_smpStay _ _ hS o x hx hm

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.sampleAlike_of_smpStay
#print axioms Johnson.RunOne.KeyRows23.smp₁_of_smpStay
#print axioms Johnson.RunOne.KeyRows23.smp₂_of_smpStay
