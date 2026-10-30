-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/Fit/QuietK9.lean: KIND K9's BATCHING AND ITS ONE EQUATION,
at every GroundQuiet R: drawAlone_byQ · adds_byQ · batch_byQ · takeN_byQ · asRow_byQ · door_byQ ·
oneEquation_byQ.
CARRIED BY PROGRAM out of Johnson/Goal/Meaning/RecGrows.lean:
each declaration that is needed for the top and names GroundKeeps | StKeeps is copied
under its own name with a letter behind it (Q), with GroundQuiet | StQuiet in that word's place; its
docstrings are struck (they are that file's); where a proof opens the word itself it is turned by
hand. THE ORIGINAL IS IMPORTED AND NOT TURNED: what names neither word is called from it. IF THE
ORIGINAL ITSELF IS WIDENED INSTEAD, THIS FILE FALLS.
What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Goal.Meaning.RecGrows
import Johnson.Desc.GroundQuiet
import Johnson.ToldDescR.K2KeepsQuiet
import Johnson.Desc.AtSeats.Fit.QuietK2Sends

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.Ground (GroundKeeps GroundQuiet By groundKeeps_grows)
open VerifiableInference.Desc.K9
open Johnson.Desc.First.Walk

variable {Cl : Type} {R : Statement → Statement → Prop}

theorem drawAlone_byQ (hr : ∀ T, R T T) (p : Where) :
    Decides (ByS R) (drawAlone (Cl := Cl) atS p) := by
  intro s rs gs s' h
  simp only [drawAlone] at h
  split at h
  · obtain ⟨q, hq, h⟩ := bindE h
    obtain ⟨chi, _, h⟩ := bindE h
    obtain ⟨o, ho, h⟩ := bindE h
    cases h
    show R s.st q.d.st
    rw [(atS_get (there_some hq)).2]
    exact hr _
  · cases h

theorem adds_byQ (p : Where) (piece : Nat) (what : String)
    {claims : S → Except String (List Claim × S)} (hcl : FnCl (ByS R) claims) :
    Decides (ByS R) (adds (Cl := Cl) atS p piece what claims) := by
  intro s rs gs s' h
  simp only [adds] at h
  obtain ⟨s₀, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨x, hx, h⟩ := bindE h
  obtain ⟨q, hq, h⟩ := bindE h
  obtain ⟨F, _, h⟩ := bindE h
  cases h
  show R s.st q.d.st
  rw [(atS_get (there_some hq)).2]
  exact hcl s x hx

theorem batch_byQ (H : GroundQuiet R) (p : Where)
    {claims : S → Except String (List Claim × S)} (hcl : FnCl (ByS R) claims) :
    Decides (ByS R) (batch atS p claims) := by
  intro s rs gs s' h
  simp only [batch] at h
  obtain ⟨t₁, h1, h⟩ := bindE h
  exact H.trans (drawAlone_byQ H.refl p s rs gs t₁ h1)
    (adds_byQ p p.piece "the segment's" hcl t₁ [] [] s' h)

theorem takeN_byQ {X : Type} (H : GroundQuiet R) (o : Nat) : ∀ (n : Nat) (d : St X)
    (acc : List Nat) (y : List Nat × St X), takeN o n d acc = .ok y → R d.st y.2.st
  | 0, d, acc, y, h => by
    cases h
    exact H.refl _
  | n + 1, d, acc, y, h => by
    unfold takeN at h
    obtain ⟨x, hx, h⟩ := bindE h
    exact H.trans (H.takeMask d x.2 o x.1 (there_some hx)) (takeN_byQ H o n x.2 _ y h)

theorem asRow_byQ {X : Type} (H : GroundQuiet R) {Rw : ReqRows} {f : ReqFrame} {q : Equation}
    {d : St X} {y : Row × St X} (h : asRow Rw f q d = .ok y) : R d.st y.2.st := by
  unfold asRow at h
  obtain ⟨row, _, h⟩ := bindE h
  dsimp only at h
  split at h
  · cases h
    exact H.refl _
  · obtain ⟨m, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨o, _, h⟩ := bindE h
    obtain ⟨x, hx, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    cases h
    exact takeN_byQ H o _ d [] x hx

theorem door_byQ {X : Type} (H : GroundQuiet R) {owed : RowsOwed} {laid : Option Nat}
    {L : LinkCtx} {F : Fork} {d : St X} {o : Out X} (h : door owed laid L F d = .ok o) :
    R d.st o.d.st := by
  unfold door at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨x, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨y, hy, h⟩ := bindE h
  obtain ⟨d', hd, h⟩ := bindE h
  cases h
  exact H.trans (asRow_byQ H hy) (H.addRow y.2 d' _ y.1 (there_some hd))

theorem oneEquation_byQ (H : GroundQuiet R) (p : Where) :
    Decides (ByS R) (oneEquation (Cl := Cl) atS p) := by
  intro s rs gs s' h
  simp only [oneEquation] at h
  obtain ⟨q, hq, h⟩ := bindE h
  obtain ⟨o, ho, h⟩ := bindE h
  cases h
  show R s.st o.d.st
  rw [← (atS_get (there_some hq)).2]
  exact door_byQ H ho

end Meaning.K2
