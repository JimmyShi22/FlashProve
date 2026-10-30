-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/Tries.lean: the form of the law on what a sending's decision asks and writes,
general in the decision; the kind's own decision meets it; a decision that says yes to all and one
that says no to all fail it.

Main names: Dec, WritesLaw, writesLaw, writesLaw_unique (whatever meets the law says yes where the
kind's decision does, with the same value); yesAll, noAll, yesAll_fails, noAll_fails; a small place
with one sampled message: toyP, toyD, toyR₁, toyR₂, toy_plan, toy_fit, toy_asks.

What is not claimed. The small place has one entry, which is its pad, and no coordinate: it refutes
the two silly decisions and tries no weight of a point. Nothing on soundness, on an honest prover or
on hiding.

-/
import Johnson.Desc.K1.Law.Writes3
import Johnson.Desc.Own.SentAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain

/-- The type of a sending's decision. -/
abbrev Dec : Type 1 :=
  ∀ L : Type, Par → Option Nat → DState L → List Fmt.RoundView → Except String (Array Nat × DState L)

/-- **The law's form**: the decision says yes just where asks holds, and then returns the new
messages' numbers and the written record. -/
def WritesLaw (dec : Dec) : Prop :=
  ∀ (L : Type) (P : Par) (owed : Option Nat) (d d' : DState L) (r₁ r₂ : Fmt.RoundView) (ids : Array Nat),
    dec L P owed d [r₁, r₂] = .ok (ids, d') ↔
      asks P owed d r₁ r₂ ∧ ids = (Array.range P.sent.size).map (· + d.st.oracles.size) ∧
        d' = behind P d (seedsOf P r₁) (answersIn r₂)

/-- The kind's own decision meets it. -/
theorem writesLaw : WritesLaw fun _ => decideSend :=
  fun _ P owed d d' r₁ r₂ ids => decideSend_iff P owed d d' r₁ r₂ ids

/-- Whatever meets it says yes where the kind's decision does, with the same value. -/
theorem writesLaw_unique (dec : Dec) (h : WritesLaw dec) (L : Type) (P : Par) (owed : Option Nat)
    (d : DState L) (r₁ r₂ : Fmt.RoundView) (x : Array Nat × DState L) :
    dec L P owed d [r₁, r₂] = .ok x ↔ decideSend P owed d [r₁, r₂] = .ok x :=
  (h L P owed d x.2 r₁ r₂ x.1).trans (decideSend_iff P owed d x.2 r₁ r₂ x.1).symm

/-- Yes to all; no to all. -/
def yesAll : Dec := fun _ _ _ d _ => .ok (#[], d)
def noAll : Dec := fun _ _ _ _ _ => .error "no"

/-- A place with one message: one row of one entry over E, one answer. -/
def toyP : Par :=
  { place := ⟨1, none, 0, .K1⟩, codes := { base := #[{ logN := 1, ell := 1, r := 0 }] }
    gp := { samples := 1, firstTree := 0 }, work := 0
    parts := [("one", #[{ shape := { code := 0, mainRows := 1, mainDeg := 3, answers := 1 } }])] }

def toyD : DState Unit :=
  { st := { codes := toyP.codes }, book := {}, roots := 0, opened := [], loc := () }

def toyR₁ : Fmt.RoundView := ⟨[], ⟨[(1, 0, 0)], [], [], none⟩⟩
def toyR₂ : Fmt.RoundView := ⟨[.answer (5, 0, 0)], ⟨[], [], [], none⟩⟩

theorem toy_sent : toyP.sent =
    #[{ shape := { code := 0, mainRows := 1, mainDeg := 3, answers := 1 } }] := rfl

theorem toy_lay : (layTrees toyP.codes toyP.sent).isSome = true := by
  rw [toy_sent]
  simp [layTrees, toyP, List.range_succ, TreeShape.mainWidth, TreeShape.maskWidth, noId]

theorem toy_plan : planOkOwn toyP = true := by
  have h := toy_lay
  rw [toy_sent] at h
  simp only [planOkOwn, planOk, Par.tuple, toy_sent, ← Own.sentShapeFits_agrees, Own.treesCan_eq]
  simp [toyP, Blk.shapeOk, Msg.of, Msg.padFits, Msg.e]
  exact ⟨h, Nat.one_le_two_pow⟩

theorem toy_trees : toyP.trees.length = 1 := by
  unfold Par.trees
  rw [toy_sent, Own.treesMade_eq]
  simp [layTrees, toyP, List.range_succ, TreeShape.mainWidth, TreeShape.maskWidth, noId]

theorem toy_fit : roundsFit (rounds toyP) [toyR₁, toyR₂] = true := by
  have h := toy_trees
  simp only [rounds, roundsFit, seedEntry, answerEntry, Fmt.DeclaredRound.items, Fmt.Entry.cut, h]
  decide

theorem toy_asks : asks toyP none toyD toyR₁ toyR₂ := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · decide
  · have h := toy_lay
    simp only [Ground.ok, Ground.recvL, Ground.sentL, List.cons_append, List.nil_append,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    refine ⟨?_, h, rfl⟩
    rw [toy_sent]
    simp [toyD, toyP, ← Own.sentShapeFits_agrees, Blk.shapeOk]
  · decide

theorem yesAll_fails : ¬ WritesLaw yesAll := fun h =>
  nomatch ((h Unit toyP (some 0) toyD toyD toyR₁ toyR₂ #[]).1 rfl).1.1

theorem noAll_fails : ¬ WritesLaw noAll := fun h =>
  nomatch (h Unit toyP none toyD _ toyR₁ toyR₂ _).2 ⟨toy_asks, rfl, rfl⟩

end VerifiableInference.Desc.K1
