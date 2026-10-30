-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Join1/LinkHole.lean: the link's item on knowledge soundness (`Hiop.LinkKnowR`,
Hiop/RecSubs.lean), from round-by-round soundness of a link record by record. General, over letters:
no protocol, no code and no size occurs.

Why. A link between two encoded indices with records may be had in two forms. The item `LinkKnowR`
speaks of ONE reduction whose explicit statement is the pair of records. A written link whose
decision is made at two keys that hold the records is A FAMILY of proofs on one shape of rounds, one
for each pair of records, each with the trivial statement, and its soundness is stated record by
record, for a language with ways out. Both say: outside the language the prover is doomed to
rejection, statement by statement. This file carries the second form to the first.

Main names:
  `linkOf s bl er rd acc`: a family of decisions on the shape s, as one reduction to the trivial
    statement.
  `linkOf_out`: it gives out a statement exactly where the decision is yes. `linkOf_local`: it is
    local if the decisions are.
  `linkOf_know`: from soundness decision by decision to knowledge soundness, nothing extracted.
  `link_know`: THE ITEM, from soundness record by record for a language Lg, if on the statements of
    which the item speaks (`ConfigurationWithOutOfDomainSample.onEq`) Lg gives the link's relaxed relation (`ConfigurationWithOutOfDomainSample.ReqR`).
  `link_know_ior`: the item of ANY reduction that decides as the family does: the item reads of a
    reduction its rounds and its verifier's output alone.
  `Lang4 C Ag`: the language in four clauses: the first word does not decode with its record; it has
    a collision at its record's seed; the further word has; both decode to messages that agree.
  `lang4_req`: that premise at `Lang4`, IF MESSAGES THAT AGREE HOLD THE SAME INDEX.
  `link_know4`: the item from these two.

Limits: nothing on an honest prover: none of the items of `Hiop.LinkListR`. No error is bounded: the
list ε is handed through as it is. The item speaks of fewer statements than the language: where the
first word decodes to a message that holds no index, `ConfigurationWithOutOfDomainSample.onEq` fails and nothing is said. That
any family of decisions is sound is a hypothesis here. Nothing is declared of sources and ties in
`linkOf`.
Terms: lean/GLOSSARY.md.

-/
import Hiop.RecSubs
import Ior.Know

set_option autoImplicit false

namespace OnBytes.Join1
open Iop Prob Hiop

/-- **A family of decisions on one shape of rounds, as one reduction to the trivial statement.**
acc: for each explicit statement x, each implicit instance y and each transcript: accept or not. bl,
er, rd: which oracles are blinded; the positions that the verifier reads. It has no new implicit
instance, and nothing is declared of sources and ties. -/
def linkOf {X : Type} {E : ExtSpec} (s : Shape) (bl : OPos s → Bool) (er : Rho s → Finset E.Pos)
    (rd : Rho s → Finset (OPos s)) (acc : X → E.Str → Tr s → Bool) : IOR X E Unit extNone where
  shape := s
  blinded := bl
  extReads := er
  reads := rd
  out := fun x y τ => if acc x y τ then some () else none
  imp := fun _ _ => ()
  srcE := fun _ _ => ∅
  srcO := fun _ _ => ∅
  tie := fun _ _ => ∅

section
variable {X : Type} {E : ExtSpec} (s : Shape) (bl : OPos s → Bool) (er : Rho s → Finset E.Pos)
  (rd : Rho s → Finset (OPos s)) (acc : X → E.Str → Tr s → Bool)

/-- It gives out a statement exactly where the decision is yes. -/
theorem linkOf_out (a : X × E.Str) (τ : Tr s) (b : Unit × extNone.Str) :
    (linkOf s bl er rd acc).red.out a τ = some b ↔ acc a.1 a.2 τ = true := by
  show (Option.map _ (if acc a.1 a.2 τ then some () else none)) = some b ↔ _
  by_cases h : acc a.1 a.2 τ = true
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]
    constructor
    · intro h'
      cases h'
    · intro h'
      exact absurd h' h

/-- **It is local, if the decisions are**: each depends on the implicit instance and on the prover's
oracles only at the positions er and rd. -/
theorem linkOf_local
    (h : ∀ x y y' (τ τ' : Tr s), τ.rho = τ'.rho → τ.plains = τ'.plains →
      (∀ p ∈ er τ.rho, E.rd y p = E.rd y' p) → (∀ p ∈ rd τ.rho, τ.read p = τ'.read p) →
      acc x y τ = acc x y' τ') : (linkOf s bl er rd acc).IsLocal where
  out := fun x y y' τ τ' h1 h2 h3 h4 => by
    show (if acc x y τ then some () else none : Option Unit) = if acc x y' τ' then some () else none
    rw [h x y y' τ τ' h1 h2 h3 h4]
  imp := fun _ _ _ _ q => q.elim

/-- **From soundness decision by decision to knowledge soundness of the one reduction, nothing being
extracted.** Lg: a language of pairs. If outside Lg the prover is doomed to rejection with the
errors ε, and on the statements with `on` the language gives the relation RA, then the reduction is
round-by-round knowledge sound on these statements, from RA to the trivial relation. -/
theorem linkOf_know (Lg : X → E.Str → Prop) (ε : Err s) (on : X × E.Str → Prop)
    (RA : X × E.Str → Unit → Prop)
    (hS : ∀ x y, ¬ Lg x y → Doomed s ε fun τ => acc x y τ = false)
    (hL : ∀ x y, on (x, y) → Lg x y → RA (x, y) ()) :
    (linkOf s bl er rd acc).red.Know on RA (fun _ _ => True) (fun _ _ (_ : Unit) => ()) ε := by
  intro a ha
  by_cases hl : Lg a.1 a.2
  · exact Doomed.of_forall _ _ fun _ _ _ _ _ => hL a.1 a.2 ha hl
  · refine Doomed.mono _ _ (fun τ hτ b _ hb _ => ?_) (hS a.1 a.2 hl)
    have h1 := (linkOf_out s bl er rd acc a τ b).1 hb
    rw [hτ] at h1
    cases h1

end

section
variable (C : ConfigurationWithOutOfDomainSample) (s : Shape) (bl : OPos s → Bool)
  (er : Rho s → Finset (twoExternalStrings C.n C.Sg).Pos) (rd : Rho s → Finset (OPos s))
  (acc : C.Rec × C.Rec → (twoExternalStrings C.n C.Sg).Str → Tr s → Bool)

/-- **THE LINK'S ITEM ON KNOWLEDGE SOUNDNESS** (`Hiop.LinkKnowR`, Hiop/RecSubs.lean), from soundness
record by record: acc holds the pair of records in its first argument. -/
theorem link_know (Lg : C.Rec × C.Rec → (twoExternalStrings C.n C.Sg).Str → Prop) (ε : Err s)
    (hS : ∀ r y, ¬ Lg r y → Doomed s ε fun τ => acc r y τ = false)
    (hL : ∀ r y, C.onEq (r, y) → Lg r y → C.ReqR (r, y) ()) :
    LinkKnowR (C := C) (linkOf s bl er rd acc) ε :=
  linkOf_know s bl er rd acc Lg ε C.onEq C.ReqR hS hL

/-- **THE ITEM OF ANY REDUCTION THAT DECIDES AS THE FAMILY DOES.** The item reads of a reduction its
rounds and its verifier's output alone: so it holds of every Q on whose rounds the verifier gives
out the trivial statement exactly where acc' says yes, whatever Q declares of positions read,
sources and ties. -/
theorem link_know_ior (Q : IOR (C.Rec × C.Rec) (twoExternalStrings C.n C.Sg) Unit extNone)
    (acc' : C.Rec × C.Rec → (twoExternalStrings C.n C.Sg).Str → Tr Q.shape → Bool)
    (hout : ∀ r y τ, Q.out r y τ = if acc' r y τ then some () else none)
    (Lg : C.Rec × C.Rec → (twoExternalStrings C.n C.Sg).Str → Prop) (ε : Err Q.shape)
    (hS : ∀ r y, ¬ Lg r y → Doomed Q.shape ε fun τ => acc' r y τ = false)
    (hL : ∀ r y, C.onEq (r, y) → Lg r y → C.ReqR (r, y) ()) : LinkKnowR (C := C) Q ε := by
  intro a ha
  by_cases hl : Lg a.1 a.2
  · exact Doomed.of_forall _ _ fun _ _ _ _ _ => hL a.1 a.2 ha hl
  · refine Doomed.mono _ _ (fun τ hτ b _ hb _ => ?_) (hS a.1 a.2 hl)
    have h1 : (Q.out a.1 a.2 τ).map (fun xo => (xo, Q.imp a.2 τ)) = some b := hb
    rw [hout, hτ] at h1
    cases h1

/-- **The language of a link with records, in four clauses**: the first word does not decode with
its record; the first word has a collision at its record's seed; the further one has; or both
decode, each with its own record, to messages that agree (Ag u₁ u₀). -/
def Lang4 (Ag : C.Msg → C.Msg → Prop) (r : C.Rec × C.Rec) (y : (twoExternalStrings C.n C.Sg).Str) : Prop :=
  C.dcd y.1 r.1 = none ∨ C.coll y.1 r.1.1 ∨ C.coll y.2 r.2.1 ∨
    ∃ u₀ u₁, C.dcd y.1 r.1 = some u₀ ∧ C.dcd y.2 r.2 = some u₁ ∧ Ag u₁ u₀

/-- **On the statements of which the link's item speaks, the language in four clauses gives the
link's relaxed relation, IF MESSAGES THAT AGREE HOLD THE SAME INDEX.** The item's condition shuts
the first three clauses. -/
theorem lang4_req (Ag : C.Msg → C.Msg → Prop)
    (hheld : ∀ u₁ u₀, Ag u₁ u₀ → C.held u₁ = C.held u₀) (r : C.Rec × C.Rec)
    (y : (twoExternalStrings C.n C.Sg).Str) (hon : C.onEq (r, y)) (hl : Lang4 C Ag r y) : C.ReqR (r, y) () := by
  obtain ⟨h0, h1⟩ := hon
  have hc0 : ¬ C.coll y.1 r.1.1 := by
    intro hc
    have : C.D y.1 r.1 = none := by
      unfold ConfigurationWithOutOfDomainSample.D
      rw [if_pos hc]
    rw [show C.D (r, y).2.1 (r, y).1.1 = C.D y.1 r.1 from rfl, this] at h0
    cases h0
  have hD0 : C.D y.1 r.1 = (C.dcd y.1 r.1).bind C.held := by
    unfold ConfigurationWithOutOfDomainSample.D
    rw [if_neg hc0]
  have hD1 : C.D y.2 r.2 = (C.dcd y.2 r.2).bind C.held := by
    unfold ConfigurationWithOutOfDomainSample.D
    rw [if_neg h1]
  rcases hl with hn | hc | hc | ⟨u₀, u₁, e0, e1, ha⟩
  · rw [show C.D (r, y).2.1 (r, y).1.1 = C.D y.1 r.1 from rfl, hD0, hn] at h0
    cases h0
  · exact absurd hc hc0
  · exact absurd hc h1
  · show C.D y.2 r.2 = C.D y.1 r.1
    rw [hD0, hD1, e0, e1]
    exact hheld u₁ u₀ ha

/-- **THE LINK'S ITEM, from soundness record by record for the language in four clauses, and the one
law on the configuration.** -/
theorem link_know4 (Ag : C.Msg → C.Msg → Prop) (ε : Err s)
    (hheld : ∀ u₁ u₀, Ag u₁ u₀ → C.held u₁ = C.held u₀)
    (hS : ∀ r y, ¬ Lang4 C Ag r y → Doomed s ε fun τ => acc r y τ = false) :
    LinkKnowR (C := C) (linkOf s bl er rd acc) ε :=
  link_know C s bl er rd acc (Lang4 C Ag) ε hS fun r y => lang4_req C Ag hheld r y

end
end OnBytes.Join1

#print axioms OnBytes.Join1.linkOf_out
#print axioms OnBytes.Join1.linkOf_local
#print axioms OnBytes.Join1.linkOf_know
#print axioms OnBytes.Join1.link_know
#print axioms OnBytes.Join1.link_know_ior
#print axioms OnBytes.Join1.lang4_req
#print axioms OnBytes.Join1.link_know4
