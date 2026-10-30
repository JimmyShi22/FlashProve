-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/OneWitness.lean: how a block's law enters a table whose claim is ONE "there is a
witness" over all open items. A tool; no protocol occurs here.

The matter. A table of joints says at each border which items are open; its claim there is
L := "there is a witness w at which EVERY open item holds". A block's row closes some items (they
are open in front and not behind), opens others, and lets the rest ride. A law of the form
"a witness behind gives a witness in front" (`Know.toLeads` gives that form: it drops the
extractor) speaks of the block's own items; the riders hold at the witness BEHIND, not at the one
that the law returns. So such a law does not give `Keeps` at the table's claims.

The form that does: A MAP ON WITNESSES THAT IS NAMED: Q a b := the promise behind ∧ for every w:
all that is open behind holds at w → (what is wanted in front) holds at E a b w. E lays the parts
of the witness that the block's row closes (behind the block nothing constrains them any more) and
leaves the rest; where a row closes no such part E is the identity.

  `Leads.glueBy`: the block's law at E, for the items that it closes, and the riders' riding from w
    to E a b w, which is owed FOR CERTAIN (at whatever the verifier puts out), give the law for all
    items open in front. The riding costs no error: it enters by `Leads.conseq`, the frame rule.
  `Leads.glue`: the case E := the same witness.
  `Leads.keepsOfMap`, `Leads.keepsOfSame`: the law at E gives `Keeps` at the two claims
    "there is a w".

Limits. Rules: as empty as their premises. Nothing on soundness.

-/
import Johnson.Desc.Plain.Leads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Iop
namespace Reduction

variable {A B I W : Type} [DecidableEq I] {K : Reduction A B} {on : A → Prop} {on' : B → Prop}
  {ε : Err K.shape}

/-- **The law for the closed items and the riders' riding give the law for all items.** O, O': what
is open in front, behind. hA i a w, hB i b w: item i holds at the statement and the witness. -/
theorem Leads.glue (O O' : List I) (hA : I → A → W → Prop) (hB : I → B → W → Prop)
    (law : K.Leads on
      (fun a b => on' b ∧ ∀ w, (∀ i ∈ O', hB i b w) → ∀ i ∈ O, i ∉ O' → hA i a w) ε)
    (ride : ∀ a τ b, on a → K.out a τ = some b → ∀ w i, i ∈ O → i ∈ O' → hB i b w → hA i a w) :
    K.Leads on (fun a b => on' b ∧ ∀ w, (∀ i ∈ O', hB i b w) → ∀ i ∈ O, hA i a w) ε :=
  law.conseq (fun _ h => h) fun a τ b ha hb hQ =>
    ⟨hQ.1, fun w hw i hi =>
      if h : i ∈ O' then ride a τ b ha hb w i hi h (hw i h) else hQ.2 w hw i hi h⟩

/-- The same with a map on witnesses. -/
theorem Leads.glueBy (E : A → B → W → W) (O O' : List I) (hA : I → A → W → Prop)
    (hB : I → B → W → Prop)
    (law : K.Leads on
      (fun a b => on' b ∧ ∀ w, (∀ i ∈ O', hB i b w) → ∀ i ∈ O, i ∉ O' → hA i a (E a b w)) ε)
    (ride : ∀ a τ b, on a → K.out a τ = some b →
      ∀ w i, i ∈ O → i ∈ O' → hB i b w → hA i a (E a b w)) :
    K.Leads on (fun a b => on' b ∧ ∀ w, (∀ i ∈ O', hB i b w) → ∀ i ∈ O, hA i a (E a b w)) ε :=
  law.conseq (fun _ h => h) fun a τ b ha hb hQ =>
    ⟨hQ.1, fun w hw i hi =>
      if h : i ∈ O' then ride a τ b ha hb w i hi h (hw i h) else hQ.2 w hw i hi h⟩

omit [DecidableEq I] in
/-- **The law at a map gives `Keeps` at the claims "there is a witness".** -/
theorem Leads.keepsOfMap (E : A → B → W → W) (RA : A → W → Prop) (RB : B → W → Prop)
    (h : K.Leads on (fun a b => on' b ∧ ∀ w, RB b w → RA a (E a b w)) ε) :
    K.Keeps on on' (fun a => ∃ w, RA a w) (fun b => ∃ w, RB b w) ε :=
  h.conseq (fun _ h => h) fun a _ b _ _ hQ => ⟨hQ.1, fun ⟨w, hw⟩ => ⟨E a b w, hQ.2 w hw⟩⟩

omit [DecidableEq I] in
/-- The case of the same witness. -/
theorem Leads.keepsOfSame (RA : A → W → Prop) (RB : B → W → Prop)
    (h : K.Leads on (fun a b => on' b ∧ ∀ w, RB b w → RA a w) ε) :
    K.Keeps on on' (fun a => ∃ w, RA a w) (fun b => ∃ w, RB b w) ε :=
  h.conseq (fun _ h => h) fun _ _ _ _ _ hQ => ⟨hQ.1, fun ⟨w, hw⟩ => ⟨w, hQ.2 w hw⟩⟩

end Reduction
end Iop

#print axioms Iop.Reduction.Leads.glue
#print axioms Iop.Reduction.Leads.glueBy
#print axioms Iop.Reduction.Leads.keepsOfMap
#print axioms Iop.Reduction.Leads.keepsOfSame
