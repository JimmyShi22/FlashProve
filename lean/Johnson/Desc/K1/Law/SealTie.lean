--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/SealTie.lean: what a sealed message gives to a table that reads the statement
alone, with no seed in sight: of the messages in the library's list of the word sent, at most one
meets the first sample row that the statement holds of the message (read as a linear form on the
message's entries, formsAt, with its target, ansAt: GoodSendForms.lean).

Main names:
  MeetsAt      a message of the library's code meets the statement's first sample row of number o.
  sealed_one   at a sealed message two members of the list that meet it are one.
  sealed_noClash   the second half of Sealed in the general form of a list and a map of answers.
  sealed_unfolded  the same, with the answer as a map on the sample map's one place.

What is not claimed. One answer a message. The encoding randomness is not pinned: the list is of
messages, under "there is an encoding randomness". That a message is in the list of the word sent,
and which word that is, is said nowhere here. Nothing on soundness of a protocol, on an honest
prover or on hiding.

-/
import Johnson.Desc.K1.Law.GoodSendForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Johnson.Pack Cb Cb.Ood

/-- A message meets the first sample row that the statement holds of message number o. -/
def MeetsAt (cs : Codes) (s : OracleShape) (St : Statement) (o : Nat)
    (u : (portCode cs s).J → GE) : Prop :=
  ∃ φ v, formsAt cs s St o = some φ ∧ ansAt St o = some v ∧
    ∑ j : (Fin s.mainRows × Fin (pMain cs s).ell) ⊕ (Fin s.maskRows × Fin (pMask cs s).ell),
      φ () j * u j = v ()

/-- **At a sealed message two members of the list that meet the statement's row are one.** -/
theorem sealed_one (cs : Codes) (s : OracleShape) (e : Nat) (f : (portOmZ cs s e).Str)
    (St : Statement) (o : Nat) (hT : Tie cs s) (h : Sealed cs s e f St o)
    (u u' : (portCode cs s).J → GE) (hl : (portOmZ cs s e).InList f u)
    (hl' : (portOmZ cs s e).InList f u') (hm : MeetsAt cs s St o u)
    (hm' : MeetsAt cs s St o u') : u = u' := by
  obtain ⟨ρ, y, hs, hno⟩ := h
  obtain ⟨h1, h2⟩ := forms_of_seedIs cs s e St o ρ y hT hs
  obtain ⟨φ, v, a1, a2, a3⟩ := hm
  obtain ⟨φ', v', b1, b2, b3⟩ := hm'
  obtain rfl := Option.some.inj (a1.symm.trans h1)
  obtain rfl := Option.some.inj (a2.symm.trans h2)
  obtain rfl := Option.some.inj (b1.symm.trans h1)
  obtain rfl := Option.some.inj (b2.symm.trans h2)
  by_contra hne
  exact hno ⟨u, u', hl, hl', hne, funext fun _ => a3.trans b3.symm⟩

/-- The second half of Sealed, in the general form of a list and a map of answers. -/
theorem sealed_noClash (cs : Codes) (s : OracleShape) (e : Nat) (f : (portOmZ cs s e).Str)
    (St : Statement) (o : Nat) (h : Sealed cs s e f St o) :
    ∃ ρ y, SeedIs cs s St o ρ y ∧
      ¬ Cb.Ood.Clash ((portOmZ cs s e).InList f) (portOmZ cs s e).Z.val ρ := by
  obtain ⟨ρ, y, hs, hno⟩ := h
  exact ⟨ρ, y, hs, fun ⟨m, m', c1, c2, c3, c4⟩ => hno ⟨m, m', c1, c2, c3, c4⟩⟩

/-- The same with the answer as a map on the sample map's one place: the form in which a table that
has one letter for the answers of the map and of the record takes it. -/
theorem sealed_unfolded (cs : Codes) (s : OracleShape) (e : Nat) (f : (portOmZ cs s e).Str)
    (St : Statement) (o : Nat) (h : Sealed cs s e f St o) :
    ∃ (ρ : (Fin (bitsZ cs s) → GE) × GEˣ) (v : Unit → GE),
      (∃ y, SeedIs cs s St o ρ y ∧ v = fun _ => y) ∧
        ¬ Cb.Ood.Clash ((portOmZ cs s e).InList f) (portOmZ cs s e).Z.val ρ := by
  obtain ⟨ρ, y, hs, hno⟩ := sealed_noClash cs s e f St o h
  exact ⟨ρ, fun _ => y, ⟨y, hs, rfl⟩, hno⟩

/-- A try: at a statement without the message nothing meets. -/
theorem not_meets_empty (cs : Codes) (s : OracleShape) (St : Statement) (o : Nat)
    (u : (portCode cs s).J → GE) (h : St.oracles[o]? = none) : ¬ MeetsAt cs s St o u := by
  rintro ⟨_, _, a, _⟩
  simp [formsAt, h] at a

end VerifiableInference.Desc.K1
