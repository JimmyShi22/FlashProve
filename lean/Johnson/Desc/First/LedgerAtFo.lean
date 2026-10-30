-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/LedgerAtFo.lean: `RanAtOfLink` | `RanAtToSettling`
(Johnson/Desc/Sound/FoldSteps.lean) AT THE LIBRARY's OWN LEDGER:
the type `Fork`, the order `Fo.Later` (OnBytes/Tie/Pv/Lookup/Forest/FoForm.lean) and the test
`OnBytes.PscRun.Sized` (OnBytes/Tie/Pv/Psc/PscFork.lean); what is heard: `Forest.Heard`. Statements,
written as `def … : Prop`, and their proofs: one call each, with `Fo.Later.refl` and
`Fo.Later.trans`. And the carried record's two readings.

Why. The lookups' files' statement on the kind "lookup" asks, of each of the kind's three runs of
claims, a record of three fields: what was heard still stands at the record at which the run is
called; that record's ledger is a later one than the hearing's, with its sizes; the run went on and
left a ledger G; and, beside these, that G is earlier than, or is, the ledger H at which the claims
are judged. `RanAt` at these letters has those three fields, under the same names and in the same
order, as `K3RanAt` (Johnson/Top/H/K3OutStatement.lean, lines
60-65; the three "Later": line 96): so a value of the one should be a value of the other by
⟨h.heard, h.later, h.ran⟩. BY READING, NOT BY LEAN.


  `CarriesFo fork heard`: the relation that each block and each run of the link owes.
    `carriesFoOfLater`: it is had from the library's other order, `OnBytes.PscRun.Later`.
  `RanAtOfLinkFo`, `ranAtOfLinkFo` · `RanAtToSettlingFo`, `ranAtToSettlingFo`: general in the record
    S, the two readings and the batching's letter Q. `RanAtOfLinkAtFo`, `RanAtToSettlingAtFo`: the
    same, asking `CallsAt` alone.
  `carriesSame`, `carriesPut`: at the carried record of the first chain
    (Johnson/Desc/First/State.lean), with fork := `S.fork?` and heard := `S.lookHeard?`:
    Johnson/Desc/First/StateLedger.lean's two laws at this order.
  `carriesPaid`, `carriesTook`: two real turns of the ledger carry: a debt marked as paid
    (`Fork.paid`); slots taken (`took`).

Limits. Those of FoldSteps.lean: `Steps`, `RunsStep` and `Calls` are premises: one law a block, one
a run, one for the batching: NO BLOCK OF THE PROTOCOL HAS THEM YET. AT WHICH LEDGER THE LINK's ONE
EQUATION SPEAKS is the batching's and the closing's law to say. What the calling kinds owe on their
forms is not touched. The reading of the lookup on the digits (`s.tl?.bind (·.heard)`) has no law
here. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.FoldStepsProofs
import Johnson.Desc.First.StateLedger
import OnBytes.Tie.Pv.Lookup.Forest.FoForm
import OnBytes.Tie.Pv.Psc.PscLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc
open OnBytes OnBytes.Model

/-- What was heard stands; the ledger only grows, with its sizes: at the library's order. -/
abbrev CarriesFo {S : Type} (fork : S → Option Fork) (heard : S → Option Forest.Heard) :
    S → S → Prop :=
  Carries fork heard _root_.Fo.Later OnBytes.PscRun.Sized

/-- **From the library's other order** (`OnBytes.PscRun.Later`, OnBytes/Tie/Pv/Psc/PscLater.lean: it
holds "the sizes are kept" as a field): what was heard stays heard, and the ledger behind is later
in that order: then the step carries. FOR A KIND WHOSE LAWS ON ITS OWN TEXT END IN THAT ORDER. -/
theorem carriesFoOfLater {S : Type} (fork : S → Option Fork) (heard : S → Option Forest.Heard)
    (s s' : S) (hh : ∀ g, heard s = some g → heard s' = some g)
    (hf : ∀ F, fork s = some F → ∃ G, fork s' = some G ∧ OnBytes.PscRun.Later F G) :
    CarriesFo fork heard s s' :=
  ⟨hh, fun F hF hs => by
    obtain ⟨G, hG, l⟩ := hf F hF
    exact ⟨G, hG, ⟨l.next, l.ns, l.keep⟩, l.sized hs⟩⟩

/-- **Who pays "the run ran at a later record" and "later" to the ledger behind the link's claims.**
-/
def RanAtOfLinkFo : Prop :=
  ∀ (S Cl : Type) (fork : S → Option Fork) (heard : S → Option Forest.Heard)
    (Q : S → List Fmt.RoundView → S → List Cl → S → S → Prop)
    (L : Link S Cl) (h₁ h₂ : List (Block S Cl)) (b : Block S Cl), L.hear = h₁ ++ b :: h₂ →
    (∀ c ∈ h₂, c.Steps (CarriesFo fork heard)) →
    (∀ c ∈ L.hear, c.RunsStep (CarriesFo fork heard)) →
    Calls (CarriesFo fork heard) Q L.batch →
    ∀ (ft : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn),
      foldBlocks ft L.blocksInOrder s rs cols = .ok out →
      ∃ t t₁ u₀ z u e cls, Traced (CarriesFo fork heard) Q L h₁ b ft s rs cols t t₁ u₀ z u e cls ∧
        RanUpTo fork heard _root_.Fo.Later OnBytes.PscRun.Sized L h₁ b t₁ e cls

theorem ranAtOfLinkFo : RanAtOfLinkFo := fun S Cl fork heard Q =>
  ranAtOfLink S Cl Fork Forest.Heard fork heard _root_.Fo.Later OnBytes.PscRun.Sized Q
    _root_.Fo.Later.refl fun _ _ _ => _root_.Fo.Later.trans

/-- **The like, on to the settling**: at the record in front of the decision of d, a place of the
closing. -/
def RanAtToSettlingFo : Prop :=
  ∀ (S Cl : Type) (fork : S → Option Fork) (heard : S → Option Forest.Heard)
    (Q : S → List Fmt.RoundView → S → List Cl → S → S → Prop)
    (L : Link S Cl) (h₁ h₂ c₁ c₂ : List (Block S Cl)) (b d : Block S Cl),
    L.hear = h₁ ++ b :: h₂ → L.close = c₁ ++ d :: c₂ →
    (∀ c ∈ h₂, c.Steps (CarriesFo fork heard)) →
    (∀ c ∈ L.hear, c.RunsStep (CarriesFo fork heard)) →
    Calls (CarriesFo fork heard) Q L.batch →
    (∀ c ∈ L.hear, c.AfterStep (CarriesFo fork heard)) →
    (∀ c ∈ c₁, c.Steps (CarriesFo fork heard)) →
    ∀ (ft : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn),
      foldBlocks ft L.blocksInOrder s rs cols = .ok out →
      ∃ t t₁ u₀ z u e cls w w₁,
        Traced (CarriesFo fork heard) Q L h₁ b ft s rs cols t t₁ u₀ z u e cls ∧
        (∃ c, foldBlocks ft (L.upTo c₁) s rs cols = .ok (w, behindOf (L.upTo c₁) rs, c)) ∧
        (∃ gs, d.decide w (shownAt (L.upTo c₁) d rs) gs = .ok w₁) ∧
        RanUpTo fork heard _root_.Fo.Later OnBytes.PscRun.Sized L h₁ b t₁ w cls

theorem ranAtToSettlingFo : RanAtToSettlingFo := fun S Cl fork heard Q =>
  ranAtToSettling S Cl Fork Forest.Heard fork heard _root_.Fo.Later OnBytes.PscRun.Sized Q
    _root_.Fo.Later.refl fun _ _ _ => _root_.Fo.Later.trans

/-- The same, asking less of the batching (`CallsAt`). -/
def RanAtOfLinkAtFo : Prop :=
  ∀ (S Cl : Type) (fork : S → Option Fork) (heard : S → Option Forest.Heard)
    (Q : S → List Fmt.RoundView → S → List Cl → S → S → Prop)
    (L : Link S Cl) (h₁ h₂ : List (Block S Cl)) (b : Block S Cl), L.hear = h₁ ++ b :: h₂ →
    (∀ c ∈ h₂, c.Steps (CarriesFo fork heard)) →
    (∀ c ∈ L.hear, c.RunsStep (CarriesFo fork heard)) →
    CallsAt (CarriesFo fork heard) Q L.batched (claimsInBy L.each L.hear L.order) →
    ∀ (ft : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn),
      foldBlocks ft L.blocksInOrder s rs cols = .ok out →
      ∃ t t₁ u₀ z u e cls, Traced (CarriesFo fork heard) Q L h₁ b ft s rs cols t t₁ u₀ z u e cls ∧
        RanUpTo fork heard _root_.Fo.Later OnBytes.PscRun.Sized L h₁ b t₁ e cls

theorem ranAtOfLinkAtFo : RanAtOfLinkAtFo := fun S Cl fork heard Q =>
  ranAtOfLinkAt S Cl Fork Forest.Heard fork heard _root_.Fo.Later OnBytes.PscRun.Sized Q
    _root_.Fo.Later.refl fun _ _ _ => _root_.Fo.Later.trans

/-- The same, asking less of the batching (`CallsAt`). -/
def RanAtToSettlingAtFo : Prop :=
  ∀ (S Cl : Type) (fork : S → Option Fork) (heard : S → Option Forest.Heard)
    (Q : S → List Fmt.RoundView → S → List Cl → S → S → Prop)
    (L : Link S Cl) (h₁ h₂ c₁ c₂ : List (Block S Cl)) (b d : Block S Cl),
    L.hear = h₁ ++ b :: h₂ → L.close = c₁ ++ d :: c₂ →
    (∀ c ∈ h₂, c.Steps (CarriesFo fork heard)) →
    (∀ c ∈ L.hear, c.RunsStep (CarriesFo fork heard)) →
    CallsAt (CarriesFo fork heard) Q L.batched (claimsInBy L.each L.hear L.order) →
    (∀ c ∈ L.hear, c.AfterStep (CarriesFo fork heard)) →
    (∀ c ∈ c₁, c.Steps (CarriesFo fork heard)) →
    ∀ (ft : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn),
      foldBlocks ft L.blocksInOrder s rs cols = .ok out →
      ∃ t t₁ u₀ z u e cls w w₁,
        Traced (CarriesFo fork heard) Q L h₁ b ft s rs cols t t₁ u₀ z u e cls ∧
        (∃ c, foldBlocks ft (L.upTo c₁) s rs cols = .ok (w, behindOf (L.upTo c₁) rs, c)) ∧
        (∃ gs, d.decide w (shownAt (L.upTo c₁) d rs) gs = .ok w₁) ∧
        (∃ c, foldBlocks ft (L.upTo c₁ ++ [d]) s rs cols =
          .ok (w₁, behindOf (L.upTo c₁ ++ [d]) rs, c)) ∧
        RanUpTo fork heard _root_.Fo.Later OnBytes.PscRun.Sized L h₁ b t₁ w cls

theorem ranAtToSettlingAtFo : RanAtToSettlingAtFo := fun S Cl fork heard Q =>
  ranAtToSettlingAt S Cl Fork Forest.Heard fork heard _root_.Fo.Later OnBytes.PscRun.Sized Q
    _root_.Fo.Later.refl fun _ _ _ => _root_.Fo.Later.trans

namespace First

theorem carriesSame (s s' : S) (hf : s'.fork? = s.fork?) (hl : s'.lookHeard? = s.lookHeard?) :
    CarriesFo S.fork? S.lookHeard? s s' :=
  carriesOfSame _root_.Fo.Later.refl s s' hf hl

theorem carriesPut (s : S) (G : Fork)
    (h : ∀ F, s.fork? = some F → OnBytes.PscRun.Sized F →
      _root_.Fo.Later F G ∧ OnBytes.PscRun.Sized G) :
    CarriesFo S.fork? S.lookHeard? s (s.putFork G) :=
  carriesPutFork s G h

/-- Marking a debt as paid leads to a later ledger. -/
theorem paid_later (F : Fork) (i : Nat) : _root_.Fo.Later F (F.paid i) :=
  ⟨Nat.le_refl _, rfl, fun _ h => ⟨h, rfl, rfl⟩⟩

/-- **A real turn of the ledger**: the ledger in front with a debt marked as paid, laid by
`putFork`. -/
theorem carriesPaid (s : S) (F : Fork) (i : Nat) (hF : s.fork? = some F) :
    CarriesFo S.fork? S.lookHeard? s (s.putFork (F.paid i)) :=
  carriesPut s _ fun F' hF' hs => by
    obtain rfl : F = F' := Option.some.inj (hF.symm.trans hF')
    exact ⟨paid_later F i, OnBytes.PscRun.paid_sized i hs⟩

/-- **Another**: slots taken. -/
theorem carriesTook (s : S) (F : Fork) (n : Nat) (hF : s.fork? = some F) :
    CarriesFo S.fork? S.lookHeard? s (s.putFork (OnBytes.PscRun.took F n)) :=
  carriesPut s _ fun F' hF' hs => by
    obtain rfl : F = F' := Option.some.inj (hF.symm.trans hF')
    exact ⟨_root_.Fo.took_later F n, OnBytes.PscRun.took_sized n hs⟩

end First

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.carriesFoOfLater
#print axioms VerifiableInference.Desc.ranAtOfLinkFo
#print axioms VerifiableInference.Desc.ranAtToSettlingFo
#print axioms VerifiableInference.Desc.ranAtOfLinkAtFo
#print axioms VerifiableInference.Desc.ranAtToSettlingAtFo
#print axioms VerifiableInference.Desc.First.carriesSame
#print axioms VerifiableInference.Desc.First.carriesPut
#print axioms VerifiableInference.Desc.First.carriesPaid
#print axioms VerifiableInference.Desc.First.carriesTook
