-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartAllotRule.lean: "allotted ⇒ pending", for arbitrary parameters: one rule on a family
of free entries in the place of one derivation for each masked block.

In standard terms: book-keeping on entries of oracle messages (an entry: one coordinate of the
message that an oracle message encodes). `LdPend.Rule` is a condition on a set X of records, a
reading (Rd, Rr) and a family of entries; the statements say how it is got from one sending, cut
down and joined.
Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Part/LdPartAllotRuleProofs.lean.
Generic: any stage, any sending, any finite field. Nothing assumed beyond the hypotheses of the
statements and whatever the arguments hold as proofs. No top theorem of its own.
A stage is an `LdStage`, a sending an `LdSendD` (Cb/Req1/LdSegKit.lean), a pending block an
`LdPend` (Cb/Ld/LdMia.lean), a layout a `Sig.StdL` (Cb/Ld/LdSendStdL.lean; `Fr`: its free entries).

Why: the records on masks (Cb/Ld/LdLayDKit.lean) ask, for each masked block
of a request, that "its masks are a pending block": a member of a set X of pending blocks that is
closed on data (`LdPend.JD`: two blocks as one; a smaller reading; another type for the same masks;
the same entries written otherwise). For a request with a hundred blocks in a segment nobody can
give a hundred derivations. Here the derivation is given once, for a family at' : Nm → entries of
free entries and every way to cut a block out of it.
The rule is meant as the invariant on masks of a builder's joint: "the free entries that are out
and unused at this stage obey the rule for the set of blocks that are pending here".



Main names:
  `β.Recast β'`: β' is β at a smaller reading that holds the own entries, with another type for the
    same masks, own entries and values written otherwise (`Spec.ldRule_recast`: a set that is
    closed on data holds β' with β).
  `LdPend.JStable X`: X is closed on data: it contains its closure `LdPend.JD X`.
  `LdPend.Rule X Rd Rr at'`: inj: the places differ; rd: they are in the reading; pend: for every
    finite injective family nm of names, every type Mk of masks (finite, not empty) and every
    bijection vf from Mk onto the vectors on the family, the block (reading Rd, Rr; own entries: the
    places of the family; masks Mk; values: vf M at the places) is in X.
  `Spec.ldRule_castMany`, `Spec.ldRule_castOne`: under the hypotheses of their statements, the two
    forms of a block that a standard sending lays (masks in whichever new members; masks in one new
    member) recast to "places, values at places", at every reading within theirs.
  `Spec.ldRule_many`: under the hypotheses of its statement (among them `Q d.N d.t F Y`,
    `LdPend.JStable X`, `∀ β, d.LaysD Q β → X β`): a standard sending lays the rule, masks in
    whichever new members: for pl injective into the layout's free entries; at every reading that
    shows no pad and no encoding randomness of a new member.
  `Spec.ldRule_one`: the same for free entries of one new member o; at every reading that shows no
    pad and not the encoding randomness of o: pads and encoding randomness of the other new members
    may be seen (the form that can cross a closing of other members of the same sending).
  `Spec.ldRule_pair`: under `LdPend.JStable X`: two rules at one reading, at places that are apart,
    are one rule on the sum of the names: a block may take its masks from both families (so the
    batching with a value shown: hiding coefficients from the segment's mask rows, the inner entry
    from the request's first sending).
  `Spec.ldRule_less`, `Spec.ldRule_sub`, `Spec.ldRule_mono`: under the hypotheses of their
    statements, the rule passes to a smaller reading; a part of the names; a larger X.

Limits: this file does not say that a sending is standard, or that its layout has what Q asks:
premises. The rule speaks of sets of pending blocks, not of provers: it does not say that the masks
of a pending block are uniform given what has been shown.



`ldRule_pair` asks one reading of both rules: two rules from different sendings come at different
readings and are first shrunk (`ldRule_less`); the common reading must still hold what the block
reads.
Three states of a mask entry (from a write-up of ours (lean/CREDITS.md), which we
follow; by reading, not machine-checked): waiting
(beside the oracle message that holds it and the answers of that message's sample, nothing that has
been sent or claimed so far depends on it); spent (it has masked its one block's messages); and from
then on data of rows (a row reads mask entries of the block that made it and of earlier blocks;
later blocks take such rows as incoming forms; the entry stays in every later reading). The rule is
for the first state only: at a stage it is to be stated for the names that have been neither used
nor read by any relation or message so far (for each name: beside the oracle message that holds it
and the answers of that message's sample). Nothing here tracks the state: what tracks it is X (a
block is pending only if every link so far has let it pass); the same fact from the rows' side ("no
place of a pending row is an own entry of a pending block") is not said here.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdLayDKit

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

section
variable {E Kc : Type} [Field E] [Fintype E]

/-- An entry of the old messages, of the new ones, among the entries after a sending. -/
def Sig.atOld (S N : Sig E) (n : S.Ent) : (S.sum N).Ent := ⟨.inl n.1, n.2⟩
def Sig.atNew (S N : Sig E) (n : N.Ent) : (S.sum N).Ent := ⟨.inr n.1, n.2⟩

/-- β' is β at a smaller reading, with another type for the same masks, written otherwise. -/
def LdPend.Recast {a : LdStage E Kc} (β β' : LdPend a) : Prop :=
  (∀ n, β'.Rd n → β.Rd n) ∧
  (∀ o, β'.Rr o → β.Rr o) ∧
  (∀ n, β'.own n → β'.Rd n) ∧
  (∀ n, β.own n ↔ β'.own n) ∧
  ∃ e : β.Mk ≃ β'.Mk, ∀ M n, β.own n → β.val M n = β'.val (e M) n

/-- Closed on data. -/
def LdPend.JStable {a : LdStage E Kc} (X : LdPend a → Prop) : Prop := ∀ β, LdPend.JD X β → X β

/-- The rule. -/
structure LdPend.Rule {a : LdStage E Kc} (X : LdPend a → Prop) (Rd : a.S.Ent → Prop)
    (Rr : a.S.O → Prop) {Nm : Type} (at' : Nm → a.S.Ent) : Prop where
  inj  : Function.Injective at'
  rd   : ∀ x, Rd (at' x)
  pend : ∀ (Ix : Type) [Fintype Ix] (nm : Ix → Nm), Function.Injective nm →
    ∀ (Mk : Type) [Fintype Mk] [Nonempty Mk] (vf : Mk → Ix → E), Function.Bijective vf →
      X ⟨Rd, Rr, plOwn fun x => at' (nm x), Mk, plVal (fun x => at' (nm x)) vf⟩

end

namespace Spec
section
variable (E Kc : Type) [Field E] [Fintype E]

def ldRule_jd : Prop := ∀ (a : LdStage E Kc) (X : LdPend a → Prop), LdPend.JStable (LdPend.JD X)

def ldRule_recast : Prop :=
  ∀ (a : LdStage E Kc) (X : LdPend a → Prop) (β β' : LdPend a),
    LdPend.JStable X → X β → β.Recast β' → X β'

/-- A block laid in whichever new members, as "places, values at places". -/
def ldRule_castMany : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [Algebra F E] (a : LdStage E Kc) (d : LdSendD a)
      (Y : d.N.StdL F) (Ix : Type) [Fintype (Ix → E)] [Nonempty (Ix → E)] (pl : Ix → Σ o, Y.Fr o),
    Function.Injective pl →
    ∀ (Rd : d.tgt.S.Ent → Prop) (Rr : d.tgt.S.O → Prop), (∀ n, Rd (a.S.atNew d.N n) → Y.NoPad n) →
      (∀ o, ¬ Rr (.inr o)) → (∀ x, Rd (a.S.atNew d.N (Y.entF (pl x)))) →
      ∀ (Mk : Type) [Fintype Mk] [Nonempty Mk] (vf : Mk → Ix → E), Function.Bijective vf →
        (d.pendMany Y pl (fun n => Rd (a.S.atOld d.N n)) fun o => Rr (.inl o)).Recast
          ⟨Rd, Rr, plOwn fun x => a.S.atNew d.N (Y.entF (pl x)), Mk,
            plVal (fun x => a.S.atNew d.N (Y.entF (pl x))) vf⟩

/-- A block laid in one new member, as "places, values at places". -/
def ldRule_castOne : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [Algebra F E] (a : LdStage E Kc)
      (d : LdSendD a) (Y : d.N.StdL F) (o : d.N.O) (Ix : Type) [Fintype (Ix → E)]
      [Nonempty (Ix → E)] (pl : Ix → Y.Fr o),
    Function.Injective pl →
    ∀ (Rd : d.tgt.S.Ent → Prop) (Rr : d.tgt.S.O → Prop), (∀ n, Rd (a.S.atNew d.N n) → Y.rdBut o n) →
      ¬ Rr (.inr o) → (∀ x, Rd (a.S.atNew d.N (Y.entO o (pl x)))) →
      ∀ (Mk : Type) [Fintype Mk] [Nonempty Mk] (vf : Mk → Ix → E), Function.Bijective vf →
        (d.pendOne Y o pl (fun n => Rd (a.S.atOld d.N n)) fun o' => Rr (.inl o')).Recast
          ⟨Rd, Rr, plOwn fun x => a.S.atNew d.N (Y.entO o (pl x)), Mk,
            plVal (fun x => a.S.atNew d.N (Y.entO o (pl x))) vf⟩

/-- Under the hypotheses below, a standard sending lays the rule: masks in whichever new members. -/
def ldRule_many : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [Algebra F E] (a : LdStage E Kc) (d : LdSendD a) (Q : LdLayQ E)
      (Y : d.N.StdL F) (dat : a.S.Wit × a.Wp → ∀ i, Y.Dt i → E) (rst : a.Wp → d.Wp')
      (bk₀ : (∀ i, Y.Dt i → E) → d.Wp' → a.Wp) (w0 : a.S.Wit × a.Wp),
    d.StdAt F Y dat rst bk₀ w0 → Q d.N d.t F Y →
    ∀ (Nm : Type) (pl : Nm → Σ o, Y.Fr o), Function.Injective pl →
      ∀ X : LdPend d.tgt → Prop, LdPend.JStable X → (∀ β, d.LaysD Q β → X β) →
        ∀ (Rd : d.tgt.S.Ent → Prop) (Rr : d.tgt.S.O → Prop),
          (∀ n, Rd (a.S.atNew d.N n) → Y.NoPad n) → (∀ o, ¬ Rr (.inr o)) →
          (∀ x, Rd (a.S.atNew d.N (Y.entF (pl x)))) →
          LdPend.Rule X Rd Rr fun x => a.S.atNew d.N (Y.entF (pl x))

/-- Under the hypotheses below, a standard sending lays the rule: masks in one new member. -/
def ldRule_one : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [Algebra F E] (a : LdStage E Kc) (d : LdSendD a) (Q : LdLayQ E)
      (Y : d.N.StdL F) (dat : a.S.Wit × a.Wp → ∀ i, Y.Dt i → E) (rst : a.Wp → d.Wp')
      (bk₀ : (∀ i, Y.Dt i → E) → d.Wp' → a.Wp) (w0 : a.S.Wit × a.Wp),
    d.StdAt F Y dat rst bk₀ w0 → Q d.N d.t F Y →
    ∀ (o : d.N.O) (Nm : Type) (pl : Nm → Y.Fr o), Function.Injective pl →
      ∀ X : LdPend d.tgt → Prop, LdPend.JStable X → (∀ β, d.LaysD Q β → X β) →
        ∀ (Rd : d.tgt.S.Ent → Prop) (Rr : d.tgt.S.O → Prop),
          (∀ n, Rd (a.S.atNew d.N n) → Y.rdBut o n) → ¬ Rr (.inr o) →
          (∀ x, Rd (a.S.atNew d.N (Y.entO o (pl x)))) →
          LdPend.Rule X Rd Rr fun x => a.S.atNew d.N (Y.entO o (pl x))

/-- Under the hypotheses below, two rules at places that are apart are one. -/
def ldRule_pair : Prop :=
  ∀ (a : LdStage E Kc) (X : LdPend a → Prop) (Rd : a.S.Ent → Prop) (Rr : a.S.O → Prop)
      (Nm₁ Nm₂ : Type) (at₁ : Nm₁ → a.S.Ent) (at₂ : Nm₂ → a.S.Ent),
    LdPend.JStable X → LdPend.Rule X Rd Rr at₁ → LdPend.Rule X Rd Rr at₂ →
    (∀ x y, at₁ x ≠ at₂ y) → LdPend.Rule X Rd Rr (Sum.elim at₁ at₂)

def ldRule_less : Prop :=
  ∀ (a : LdStage E Kc) (X : LdPend a → Prop) (Rd Rd' : a.S.Ent → Prop) (Rr Rr' : a.S.O → Prop)
      (Nm : Type) (at' : Nm → a.S.Ent),
    LdPend.JStable X → LdPend.Rule X Rd Rr at' → (∀ n, Rd' n → Rd n) → (∀ o, Rr' o → Rr o) →
    (∀ x, Rd' (at' x)) → LdPend.Rule X Rd' Rr' at'

def ldRule_sub : Prop :=
  ∀ (a : LdStage E Kc) (X : LdPend a → Prop) (Rd : a.S.Ent → Prop) (Rr : a.S.O → Prop)
      (Nm Nm' : Type) (at' : Nm → a.S.Ent) (f : Nm' → Nm),
    LdPend.Rule X Rd Rr at' → Function.Injective f → LdPend.Rule X Rd Rr fun x => at' (f x)

def ldRule_mono : Prop :=
  ∀ (a : LdStage E Kc) (X X' : LdPend a → Prop) (Rd : a.S.Ent → Prop) (Rr : a.S.O → Prop)
      (Nm : Type) (at' : Nm → a.S.Ent),
    (∀ β, X β → X' β) → LdPend.Rule X Rd Rr at' → LdPend.Rule X' Rd Rr at'

/-- A block of the rule, written otherwise. -/
def ldRule_as : Prop :=
  ∀ (a : LdStage E Kc) (X : LdPend a → Prop) (Rd : a.S.Ent → Prop) (Rr : a.S.O → Prop)
      (Nm : Type) (at' : Nm → a.S.Ent),
    LdPend.JStable X → LdPend.Rule X Rd Rr at' →
    ∀ (Ix : Type) [Fintype Ix] (nm : Ix → Nm), Function.Injective nm →
      ∀ (Mk : Type) [Fintype Mk] [Nonempty Mk] (vf : Mk → Ix → E), Function.Bijective vf →
        ∀ (own : a.S.Ent → Prop) (val : Mk → a.S.Ent → E), (∀ n, own n ↔ ∃ x, at' (nm x) = n) →
          (∀ M x, val M (at' (nm x)) = vf M x) → X ⟨Rd, Rr, own, Mk, val⟩

end
end Spec
end Cb
