-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/KeptWLegs.lean: KeptW (Johnson/Desc/Kinds/Law/WeightAtSame.lean: what a
sub-protocol of the output head's segment must leave so that the sentence WeightAt can be carried
over it) AT THREE BARE SUB-PROTOCOLS THAT STAND BEHIND THE HEAD'S OWN ROUNDS: the segment's second
sending with the quiet step that lays the head's tables; the approximate range proof; a later
sending. Each from a law on that sub-protocol's decision.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law).
  KeptW.trans; keptW_tables (laying the head's tables); keptW_putTl (laying the approximate range
      proof's own part of the state): tools.
  keptW_reads_laid: an accept of "K1.laterAt ... andThen ReadsQuiet.head P": over
      Johnson/Desc/Kinds/Law/ReadsLaidAlike.lean (reads_laid_later).
  keptW_range: an accept of the approximate range proof's "approximateRangeProofDrawKind atS p": over
      Johnson/Desc/First/K8/LawLeaves.lean (decide_atS: it turns the state by putTl alone).
  keptW_sending: an accept of "K1.laterAt ...": over Johnson/Desc/Kinds/Law/SendingKeeps.lean
      (sending_alike).

Every letter under "there is": none in the statements (KeptW's own o, o' are pinned by the two
states' field here).
What it does not say. THESE ARE THE BARE SUB-PROTOCOLS' DECISIONS. That the piece which the IOP as
written in Lean holds at a place accepts only where the bare sub-protocol decides so, is each
sub-protocol's authors' to say. Nothing on the lookup on the digits (its authors have that leg).
Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.WeightAtSame
import Johnson.Desc.Kinds.Law.ReadsLaidAlike
import Johnson.Desc.Kinds.Law.SendingKeeps
import Johnson.Desc.First.K8.LawLeaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes OnBytes.Model
open OnBytes.PscRun (Later)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K8

theorem KeptW.trans {s s' s'' : S} (a : KeptW s s') (b : KeptW s' s'') : KeptW s s'' := by
  obtain ⟨o, o', ho, ho', a1, a2, a3, a4, a5, a6, aL⟩ := a
  obtain ⟨p, p', hp, hp', b1, b2, b3, b4, b5, b6, bL⟩ := b
  obtain rfl : o' = p := by
    have e := ho'.symm.trans hp
    simpa using e
  exact ⟨o, p', ho, hp', b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5,
    b6.trans a6, aL.trans bL⟩

/-- Laying the head's tables. -/
theorem keptW_tables {s : S} {a : HeadOwn} (ha : s.here = .head a)
    (tt : Option OnBytes.Model.Head.Tables) :
    KeptW s { s with here := .head { a with t := tt } } :=
  ⟨a, _, ha, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Later.refl _⟩

/-- Laying the approximate range proof's own part of the state. -/
theorem keptW_putTl {s : S} {a : HeadOwn} (ha : s.here = .head a) (tl : HTailF2) :
    KeptW s (s.putTl tl) := by
  cases hop : a.opened with
  | true =>
    have e : s.putTl tl = { s with here := .head { a with tl := tl } } := by
      unfold S.putTl
      rw [ha]
      simp [hop]
    rw [e]
    exact ⟨a, _, ha, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Later.refl _⟩
  | false =>
    have e : s.putTl tl = s := by
      unfold S.putTl
      rw [ha]
      simp [hop]
    rw [e]
    exact ⟨a, a, ha, ha, rfl, rfl, rfl, rfl, rfl, rfl, Later.refl _⟩

/-- **The segment's second sending with the quiet step that lays the tables.** -/
theorem keptW_reads_laid {q : Params.First} {gp : _root_.Desc.Plain.GPar}
    {link piece moment : Nat} {arrays : Option (List Nat)} {P : ReadsQuiet.PH} {name : String}
    {s s' : S} {a : HeadOwn} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (ha : s.here = .head a)
    (h : ((K1.laterAt q gp link piece moment arrays : Block S Unit).andThen name
      (ReadsQuiet.head P)).decide s rs gs = .ok s') : KeptW s s' := by
  obtain ⟨_, _, tt, _, _, _, _, _, _, al, _⟩ := reads_laid_later ha h
  exact (keptW_tables ha (some tt)).trans (KeptW.of_alike al)

/-- **The approximate range proof.** -/
theorem keptW_range {Cl : Type} (p : First.K8.Par) {s s' : S} {a : HeadOwn} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (ha : s.here = .head a)
    (h : (First.K8.approximateRangeProofDrawKind (Cl := Cl) First.K8.atS p).decide s rs gs = .ok s') : KeptW s s' := by
  obtain ⟨tl, rfl⟩ := First.K8.decide_atS p s s' rs gs h
  exact keptW_putTl ha tl

/-- **A later sending.** -/
theorem keptW_sending {Cl : Type} {q : Params.First} {gp : _root_.Desc.Plain.GPar}
    {link piece moment : Nat} {arrays : Option (List Nat)} {s s' : S} {a : HeadOwn}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))} (ha : s.here = .head a)
    (h : (K1.laterAt q gp link piece moment arrays : Block S Cl).decide s rs gs = .ok s') :
    KeptW s s' :=
  KeptW.of_alike (sending_alike ha h)

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.KeptW.trans
#print axioms VerifiableInference.Desc.Kinds.Head.Law.keptW_putTl
#print axioms VerifiableInference.Desc.Kinds.Head.Law.keptW_reads_laid
#print axioms VerifiableInference.Desc.Kinds.Head.Law.keptW_range
#print axioms VerifiableInference.Desc.Kinds.Head.Law.keptW_sending
