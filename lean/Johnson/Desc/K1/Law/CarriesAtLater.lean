-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/CarriesAtLater.lean: K1's LATER BLOCKS' DECISIONS STEP: b.Steps (CarriesFo
S.fork? S.lookHeard?) (Johnson/Desc/Sound/FoldSteps.lean · Johnson/Desc/First/LedgerAtFo.lean): a
yes of the decision leaves what the
lookup was heard to return, and leaves the link's ledger a later one with its sizes. At a later
moment's sending (commitAtS; laterAt: a link's digits, its reads' own sending), and at ANY block of
the form
«that sending, with a block q joined behind it that leaves both readers» (the reads' place's joined
block), with q's premise PAID at the quiet step of a layers' link, of the head's and of an attention
link.
WITHOUT the premise planOk; at any list of rounds.
THE LEDGER's HALF IS CALLED: Johnson/Desc/First/LedgerLater.lean: K1.commitAtS_later :
Decides LaterS (commitAtS …): LaterS is, to the letter, carriesFoOfLater's premise on the ledger.
THE HEARD HALF IS NEW HERE: a yes of commitAtS lays ((laid s w).putLink L').putFork F'
(commitAtS_next gives that form): by Johnson/Desc/First/StateLedger.lean's look_putFork |
look_putLink.
  commitAtS_heard                 what the lookup was heard to return is left
  commitAtS_stepsFo · laterAt_stepsFo **the sending**
  SameReaders q                   a yes of q leaves S.fork? and S.lookHeard?
  same_layers | same_head | same_att | same_blockAt      the three quiet steps
    (K8/ReadsQuietLaws.lean's layers_ok | head_ok; readsAtSO_eq)
  andThen_stepsFo                   **the sending with such a q joined behind**
Nothing on soundness.
-/
import Johnson.Desc.K1.KeepsNext
import Johnson.Desc.K1.Places
import Johnson.Desc.First.LedgerLater
import Johnson.Desc.First.LedgerAtFo
import Johnson.Desc.K8.ReadsQuietAt
import Johnson.Desc.K8.ReadsQuietLaws
import Johnson.Goal.Meaning.RecReadsAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Model OnBytes.Params Desc.Plain
open VerifiableInference.Desc.First (S)

/-- **What the lookup was heard to return is left.** -/
theorem commitAtS_heard {Cl : Type} {P : Par} {link moment : Nat} {arrays : Option (List Nat)}
    {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (commitAtS (Cl := Cl) P link moment arrays).decide s rs gs = .ok s') :
    s'.lookHeard? = s.lookHeard? := by
  obtain ⟨L, F, tl, y, _, _, _, rfl, _⟩ := commitAtS_next h
  rw [S.look_putFork, S.look_putLink]
  rfl

/-- **A LATER MOMENT's SENDING's DECISION STEPS.** -/
theorem commitAtS_stepsFo {Cl : Type} (P : Par) (link moment : Nat) (arrays : Option (List Nat)) :
    (commitAtS (Cl := Cl) P link moment arrays).Steps (CarriesFo S.fork? S.lookHeard?) :=
  fun s rs gs s' h => carriesFoOfLater _ _ s s' (fun g hg => by rw [commitAtS_heard h]; exact hg)
    (commitAtS_later P link moment arrays s rs gs s' h)

theorem laterAt_stepsFo {Cl : Type} (q : Params.First) (gp : GPar) (link piece moment : Nat)
    (arrays : Option (List Nat)) :
    (laterAt (Cl := Cl) q gp link piece moment arrays).Steps (CarriesFo S.fork? S.lookHeard?) :=
  commitAtS_stepsFo _ link moment arrays

/-- A yes leaves both readers. -/
def SameReaders {Cl : Type} (q : Block S Cl) : Prop :=
  ∀ s s' rs gs, q.decide s rs gs = .ok s' → s'.fork? = s.fork? ∧ s'.lookHeard? = s.lookHeard?

theorem same_layers (P : K8.ReadsQuiet.PG) : SameReaders (K8.ReadsQuiet.layers P) := by
  intro s s' rs gs h
  obtain ⟨a, own, tl', ha, _, _, rfl⟩ := K8.ReadsQuiet.layers_ok h
  exact ⟨S.fork_lay s a _ ha rfl, S.look_lay s a _ ha rfl⟩

theorem same_head (P : K8.ReadsQuiet.PH) : SameReaders (K8.ReadsQuiet.head P) := by
  intro s s' rs gs h
  obtain ⟨a, cov, x, t, tl', ha, ho, _, _, _, _, rfl⟩ := K8.ReadsQuiet.head_ok h
  exact ⟨S.fork_head s a _ ha rfl rfl, S.look_head s a _ ha rfl rfl⟩

theorem same_att {W : Verify.Public} {l g : Nat} {q : Block S Unit}
    (hq : First.Att.readsAtO W l g = some q) : SameReaders q := by
  unfold First.Att.readsAtO at hq
  obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 hq
  intro s s' rs gs h
  obtain ⟨a, t, tl, ha, rfl⟩ := Meaning.K2.readsAtSO_eq h
  exact ⟨S.fork_att s a _ ha rfl, S.look_att s a _ ha rfl⟩

theorem same_blockAt {G : Array Layer.HPlan2} {hS : Head.Shape} {HLy : Head.HL}
    {H : Head.HPlanH2} {kinds : List (Nat × Nat)} {l : Nat} {q : Block S Unit}
    (h : K8.ReadsQuiet.blockAt G hS HLy H kinds l = some q) : SameReaders q := by
  unfold K8.ReadsQuiet.blockAt at h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain ⟨hp, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact same_layers _
  · split at h
    · obtain rfl := Option.some.inj h
      exact same_head _
    · cases h

/-- **THE SENDING WITH A BLOCK JOINED BEHIND IT THAT LEAVES BOTH READERS.** -/
theorem andThen_stepsFo {Cl : Type} (P : Par) (link moment : Nat) (arrays : Option (List Nat))
    (name : String) (q : Block S Cl) (hq : SameReaders q) :
    ((commitAtS (Cl := Cl) P link moment arrays).andThen name q).Steps
      (CarriesFo S.fork? S.lookHeard?) := by
  intro s rs gs s' h
  have h' : ((commitAtS (Cl := Cl) P link moment arrays).decide s
      (rs.take (commitAtS (Cl := Cl) P link moment arrays).rounds.length)
      (gs.take (commitAtS (Cl := Cl) P link moment arrays).openings)).bind (fun s₁ =>
      q.decide s₁ (rs.drop (commitAtS (Cl := Cl) P link moment arrays).rounds.length)
        (gs.drop (commitAtS (Cl := Cl) P link moment arrays).openings)) = .ok s' := h
  cases h1 : (commitAtS (Cl := Cl) P link moment arrays).decide s
      (rs.take (commitAtS (Cl := Cl) P link moment arrays).rounds.length)
      (gs.take (commitAtS (Cl := Cl) P link moment arrays).openings) with
  | error e =>
    rw [h1] at h'
    cases h'
  | ok s₁ =>
    rw [h1] at h'
    have h2 : q.decide s₁ _ _ = .ok s' := h'
    obtain ⟨e1, e2⟩ := hq _ _ _ _ h2
    refine carriesFoOfLater _ _ s s' (fun g hg => by rw [e2, commitAtS_heard h1]; exact hg)
      fun F hF => ?_
    obtain ⟨G, hG, hl⟩ := commitAtS_later P link moment arrays s _ _ s₁ h1 F hF
    exact ⟨G, by rw [e1]; exact hG, hl⟩

end VerifiableInference.Desc.K1
