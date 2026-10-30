-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqJohnSubNo.lean: a finding, as a theorem: under a standard layout an oracle message
whose format is over a proper subfield holds neither data nor free entries. (not all hypotheses are
named here: see `Spec.ld_subfield_noData`)

Two statements and their proofs. Generic.
`Y : N.StdL Fp` (Cb/Ld/LdSendStdL.lean): a standard layout of the family N, with the pads' field Fp:
each member's entries are data, free entries or pads.

Why: Cb/Req1/LdReqJohnSub.lean has the case "an oracle message over a subfield K, below the Johnson
radius" (`o.JohnF K d L`), whose clause "fmt" says: every word as sent, read under the
transformation, is over K. The standard sender of a family (Cb/Ld/LdSendStdL.lean) is made from a
layout Y whose data and free entries are elements of E, all of them: `Y.msgOf a` takes any vector
over E, and `Y.OK`'s clause "lay" says that it stands in the message as it is. So the sender can be
made to send an encoding of any vector over E, and by the lemma of Cb/Req1/LdReqJohnSub.lean
(`ld_subfield_member`), under its hypotheses, all its entries lie in K.

Main names:
  `Spec.ld_subfield_noData`: `Y.OK t`; of the member a: laws, distance d as read, its radius below
    d, the generator over K, the format over K; a place n of data or of a free entry of the member a
    ⇒ every element of E lies in K. At any radius below the distance, within unique decoding too. Of
    `Y.OK` only "enc" and "lay" are used.
  `Spec.ld_subfield_noDataJ`: the same, with `(N.om a).JohnF K d L` in place of the five conditions
    on the member a.

What it means: in every record that asks a standard layout in order (`LdSendD.IsStd`,
Cb/Req1/LdReqProtoStd.lean; `LdSendD.IsStdJ`, Cb/Req1/LdReqJohn.lean; the object's seven senders;
weights-formedness) all oracle messages are words over E, offline and online: a format over a proper
subfield can be met only by a member that holds pad entries alone (under the further hypotheses of
`Spec.ld_subfield_noData`: laws, distance d as read, the radius below d, the generator over K). Only
the pads may lie in a subfield (plain format: `OMsg.plain`, Cb/Ld/LdSig.lean), which "evades"
(`OMsg.Evades`, Cb/Ld/LdSig.lean) allows within unique decoding (`OMsg.Half`,
Cb/Req1/LdReqJohn.lean). The standard sender does not cover messages over the base field: not for
want of the lemma on lists, but by the type of its data. This protocol's technical report
(lean/CREDITS.md) has such messages
(rows over the base field, pads in the base field, encoding randomness over the base field). What
would cover them: a layout whose data, free entries, pads and randomness lie in a field chosen
member by member.

Limits: this file says nothing on senders that are not standard. The lemma on members of a list
(`ld_subfield_member`) does not hang on layouts and stands as it is.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdReqJohnSub
import Cb.Ld.LdSendStdL

set_option autoImplicit false

namespace Cb
open Prob Iop Hiop Cb.Ood

def Spec.ld_subfield_noData : Prop :=
  ∀ (K Fp E : Type) [Field K] [Field Fp] [Fintype Fp] [Field E] [Fintype E] [Algebra K E]
      [Algebra Fp E] (N : Sig E) (Y : N.StdL Fp) (t : N.O → ℕ) (a : N.O) (d : ℕ),
    Y.OK t → (N.om a).C.Laws → (N.om a).C.Dist d → (N.om a).e < d →
    (N.om a).C.GenIn K → (∀ f : (N.om a).Str, (N.om a).C.LongIn K ((N.om a).upW f)) →
    (Y.Dt a ⊕ Y.Fr a) → ∀ x : E, x ∈ Set.range (algebraMap K E)

def Spec.ld_subfield_noDataJ : Prop :=
  ∀ (K Fp E : Type) [Field K] [Field Fp] [Fintype Fp] [Field E] [Fintype E] [Algebra K E]
      [Algebra Fp E] (N : Sig E) (Y : N.StdL Fp) (t : N.O → ℕ) (a : N.O) (d L : ℕ),
    Y.OK t → (N.om a).JohnF K d L → (Y.Dt a ⊕ Y.Fr a) → ∀ x : E, x ∈ Set.range (algebraMap K E)

theorem ld_subfield_noData : Spec.ld_subfield_noData := by
  intro K Fp E _ _ _ _ _ _ _ N Y t a d hY hL hD hlt hG hfmt n x
  obtain ⟨r⟩ := (Y.En a).neRnd
  have hf := hfmt ((Y.En a).enc (Y.msgOf a (fun _ => x) 0) r)
  rw [hY.enc] at hf
  have hN : (N.om a).C.Near (N.om a).e
      ((N.om a).C.enc (Y.upM a (Y.msgOf a (fun _ => x) 0)) (Y.upR a r))
      ((N.om a).C.enc (Y.upM a (Y.msgOf a (fun _ => x) 0)) (Y.upR a r)) := by
    show cnt _ ≤ _
    rw [cnt_false fun _ hne => hne rfl]
    exact Nat.zero_le _
  have hm := (ld_subfield_member K E (N.om a).P (N.om a).C d (N.om a).e hL hD hlt hG _ _ _ hf hN).1
    ((Y.ν a).symm (Sum.inl n))
  rw [hY.lay] at hm
  exact hm

theorem ld_subfield_noDataJ :
    Spec.ld_subfield_noDataJ := fun K Fp E _ _ _ _ _ _ _ N Y t a d _ hY h =>
  ld_subfield_noData K Fp E N Y t a d hY h.laws h.dist (ldJohn_lt _ _ _ h.inJ) h.gen h.fmt

end Cb
