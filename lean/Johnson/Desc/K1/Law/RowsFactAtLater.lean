-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/RowsFactAtLater.lean: THE THREE TESTS ON THE ROWS ON THE TABLE RIDE OVER AN
ACCEPT OF EITHER SUB-PROTOCOL OF A SEGMENT's LATER PLACES, each by itself.

  LaterSame s s'   what such an accept leaves: the rows on the table; the index masks' number; the
                   statement grows; the ledgers stay in order; the chain does not stand at its end
                   behind it.
  commitAtS_same, k1Quiet_same, later_same   at a segment's later moment; at the quiet step behind
                   the reads' sending; at both sub-protocols (Later,
                   Johnson/Desc/K1/Law/InOrderAtLater.lean), on any rounds.
  later_pileMasks, later_pileWithin, later_oneRow   THE THREE ARMS, at the layer's own tests as code
                   (Johnson/Desc/K13/PubK13.lean). The third is earned outright.
  later_rowsFact   the three as one (RowsFact, Johnson/Desc/K13/Law/OwedFoldFacts.lean).

What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.LedgerAtLater
import Johnson.Desc.K13.Law.WithinReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice Desc.Plain
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground (groundKeeps_grows)
open VerifiableInference.Desc.Keeps (Decides ofInv)
open VerifiableInference.Desc.K13 (pileMasksC pileWithinC oneRowC)
open VerifiableInference.Desc.K13.Law (FitStays RowsFact commitAtS_ledgersFit pileWithinC_quiet
  oneRowC_not_mem)
open OnBytes.Model.Stages (LinkH)
open IM (k1Reads k1Quiet)

/-- What an accept of a later place's sub-protocol leaves. -/
def LaterSame (s s' : S) : Prop :=
  s'.rows = s.rows ∧ s'.out.indexMasks = s.out.indexMasks ∧ Grows s.st s'.st ∧
    FitStays s.st s'.st ∧ ∀ a', s'.here ≠ .mem a'

theorem LaterSame.trans {a b c : S} (h : LaterSame a b) (k : LaterSame b c) : LaterSame a c :=
  ⟨k.1.trans h.1, k.2.1.trans h.2.1, h.2.2.1.trans k.2.2.1, fun x => k.2.2.2.1 (h.2.2.2.1 x),
    k.2.2.2.2⟩

/-- **A segment's later moment.** -/
theorem commitAtS_same (P : Par) (link moment : Nat) (arrays : Option (List Nat)) :
    Decides LaterSame (commitAtS (Cl := Unit) P link moment arrays) := by
  intro s rs gs s' h
  refine ⟨commitAtS_rows P link moment arrays s s' rs gs h,
    by rw [(commitAtS_left P link moment arrays s s' rs gs h).2],
    Rel.commitAtS_keeps groundKeeps_grows P link moment arrays s rs gs s' h,
    commitAtS_ledgersFit P link moment arrays s rs gs s' h, ?_⟩
  intro a' ha'
  obtain ⟨-, -, hh⟩ := commitAtS_here P link moment arrays s s' rs gs h
  rcases hh with ⟨a, b, -, e⟩ | ⟨a, b, -, e⟩ | ⟨a, b, -, e, -, -⟩ <;>
    (rw [e] at ha'; cases ha')

/-- The quiet step leaves what the links left, and does not stand at the chain's end. -/
theorem k1Quiet_out (G : ProofFile.Ground) (l : Nat) (X : LinkH) :
    Decides (fun s s' : S => s'.out = s.out ∧ ∀ a', s'.here ≠ .mem a') (k1Quiet G l X) := by
  refine k1Quiet_decides _ (fun P s rs gs s' h => ?_) (fun P s rs gs s' h => ?_)
    (fun A s s' h => ?_) G l X
  · obtain ⟨a, own, tl', ha, _, _, rfl⟩ := K8.ReadsQuiet.layers_ok h
    exact ⟨rfl, fun a' hh => nomatch hh⟩
  · obtain ⟨a, cov, x, t, tl', ha, _, _, _, _, _, rfl⟩ := K8.ReadsQuiet.head_ok h
    exact ⟨rfl, fun a' hh => nomatch hh⟩
  · obtain ⟨a, t, tl, ha, rfl⟩ := Meaning.K2.readsAtSO_eq h
    exact ⟨rfl, fun a' hh => nomatch hh⟩

/-- **The quiet step behind the reads' sending.** -/
theorem k1Quiet_same (G : ProofFile.Ground) (l : Nat) (X : LinkH) :
    Decides LaterSame (k1Quiet G l X) := by
  intro s rs gs s' h
  have e : s'.st = s.st := k1Quiet_st G l X s rs gs s' h
  obtain ⟨ho, hm⟩ := k1Quiet_out G l X s rs gs s' h
  refine ⟨k1Quiet_rows G l X s rs gs s' h, by rw [ho], ?_, ?_, hm⟩
  · rw [e]
    exact Grows.refl _
  · rw [e]
    exact fun x => x

/-- **At both sub-protocols of a segment's later places**, on any rounds. -/
theorem later_same {B own : Block S Unit} (hB : Later B own) : Decides LaterSame B := by
  intro s rs gs s' h
  cases hB with
  | digits q gp l piece digits => exact commitAtS_same _ l 2 digits s rs gs s' h
  | reads Z G l X pr reads =>
    have h' : ((laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).decide s
        (rs.take (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).rounds.length)
        (gs.take (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).openings)).bind (fun s₁ =>
        (k1Quiet G l X).decide s₁
          (rs.drop (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).rounds.length)
          (gs.drop (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).openings)) = .ok s' := h
    obtain ⟨s₁, h1, h2⟩ := (bind_ok _ _ _).1 h'
    exact (commitAtS_same _ l 1 reads s _ _ s₁ h1).trans (k1Quiet_same G l X _ _ _ _ h2)

/-! ## The three arms -/

variable {B own : Block S Unit} {s s' : S} {rs : List Fmt.RoundView}
  {gs : List (List (Nat × List UInt64))}

/-- **"K13.pileMasks"** rides. -/
theorem later_pileMasks (hB : Later B own) (h : B.decide s rs gs = .ok s')
    (h0 : pileMasksC s = true) : pileMasksC s' = true := by
  obtain ⟨hr, ho, -, -, -⟩ := later_same hB s rs gs s' h
  unfold pileMasksC at h0 ⊢
  rw [hr, ho]
  exact h0

/-- **"K13.pileWithin"** rides. -/
theorem later_pileWithin (hB : Later B own) (h : B.decide s rs gs = .ok s')
    (h0 : pileWithinC s = true) : pileWithinC s' = true := by
  obtain ⟨hr, -, hg, hF, -⟩ := later_same hB s rs gs s' h
  exact pileWithinC_quiet hr hg hF h0

/-- **"K13.oneRow"** is earned outright: the chain does not stand at its end. -/
theorem later_oneRow (hB : Later B own) (h : B.decide s rs gs = .ok s') : oneRowC s' = true :=
  oneRowC_not_mem (later_same hB s rs gs s' h).2.2.2.2

/-- The three as one. -/
theorem later_rowsFact (hB : Later B own) : Decides (ofInv RowsFact) B :=
  fun _ _ _ _ h hf => ⟨later_pileMasks hB h hf.1, later_pileWithin hB h hf.2.1, later_oneRow hB h⟩

end VerifiableInference.Desc.K1
