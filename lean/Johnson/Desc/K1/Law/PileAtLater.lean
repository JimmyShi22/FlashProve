-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/PileAtLater.lean: the table's item "pile" goes BACK over a yes of the block at a
segment's later place.

  PileBackAtLater, pileBackAtLater   the statement and its proof. At the layer of K13
                    (Johnson/Desc/K13/Law/FillK13.lean) the item says: all rows on the table are
                    true (RowsTrue), at a reader rw that is a family in the chain's state.
  later_rows        the rows on the table stay, at both blocks (Later,
                    Johnson/Desc/K1/Law/InOrderAtLater.lean), on any rounds.
  k1Quiet_decides   A TOOL: whatever the three quiet steps keep (K8.ReadsQuiet.layers, head;
                    First.Att.readsAtSO), the quiet block behind the reads' sending keeps.

rw IS A LETTER of the composed meaning (Johnson/Desc/Sound/MgAll.lean: rw13). ONE PREMISE IS LEFT,
"reader", at the very two states and witness: what the rows behind say at the reader behind, they
say at the reader in front. Its payer at the reader through the state's own book:
Johnson/Desc/K13/Law/ReaderAtCommit.lean (the sending) and Johnson/Desc/K1/Law/ReaderAtLater.lean
(both blocks).

What is not claimed. That a description lays these blocks at these places. Nothing on soundness, on
an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.InOrderAtLater
import Johnson.Desc.K1.Law.RowsAtCommit
import Johnson.Desc.K13.Law.Letters

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice Desc.Plain
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Decides)
open VerifiableInference.Desc.K13.Law (RowsTrue)
open OnBytes.Model.Stages (LinkH)
open IM (k1Reads k1Quiet)

variable {Cl : Type}

/-! ## 1 Whatever the three quiet steps keep, the quiet block behind the reads' sending keeps -/

section
variable (R : S → S → Prop)
  (h1 : ∀ P : K8.ReadsQuiet.PG, Decides R (K8.ReadsQuiet.layers P))
  (h2 : ∀ P : K8.ReadsQuiet.PH, Decides R (K8.ReadsQuiet.head P))
  (h3 : ∀ (A : Attention.Plan) (s s' : S), First.Att.readsAtSO A s = .ok s' → R s s')
include h1 h2

theorem blockAt_decides {G : Array Layer.HPlan2} {hS : Head.Shape} {HLy : Head.HL}
    {H : Head.HPlanH2} {kinds : List (Nat × Nat)} {l : Nat} {q : Block S Unit}
    (h : K8.ReadsQuiet.blockAt G hS HLy H kinds l = some q) : Decides R q := by
  unfold K8.ReadsQuiet.blockAt at h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain ⟨hp, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact h1 _
  · split at h
    · obtain rfl := Option.some.inj h
      exact h2 _
    · cases h

include h3

theorem readsQuietAt_decides {G : ProofFile.Ground} (l : Nat) (X : LinkH) (piece : Nat)
    (q : Block S Unit) (h : ProofFile.readsQuietAt G l X piece = some q) : Decides R q := by
  unfold ProofFile.readsQuietAt at h
  by_cases k1 : (X.kind == 1) = true
  · rw [if_pos k1] at h
    by_cases k2 : (piece == 4) = true
    · rw [if_pos k2] at h
      unfold First.Att.readsAtO at h
      obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 h
      exact fun s rs gs s' hd => h3 A s s' hd
    · rw [if_neg k2] at h
      cases h
  · rw [if_neg k1] at h
    by_cases k2 : (piece == (if X.kind == 0 then 4 else 5)) = true
    · rw [if_pos k2] at h
      exact blockAt_decides R h1 h2 h
    · rw [if_neg k2] at h
      cases h

/-- **Whatever the three quiet steps keep, the quiet block keeps.** -/
theorem k1Quiet_decides (G : ProofFile.Ground) (l : Nat) (X : LinkH) : Decides R (k1Quiet G l X) := by
  unfold k1Quiet
  dsimp only
  cases hq : ProofFile.readsQuietAt G l X (if X.kind == 0 || X.kind == 1 then 4 else 5) with
  | none => exact fun s rs gs s' h => nomatch h
  | some q => exact readsQuietAt_decides R h1 h2 h3 l X _ q hq

end

/-! ## 2 The rows on the table stay -/

theorem k1Quiet_rows (G : ProofFile.Ground) (l : Nat) (X : LinkH) :
    Decides (fun s s' : S => s'.rows = s.rows) (k1Quiet G l X) := by
  refine k1Quiet_decides _ (fun P s rs gs s' h => ?_) (fun P s rs gs s' h => ?_)
    (fun A s s' h => ?_) G l X
  · obtain ⟨a, own, tl', ha, _, _, rfl⟩ := K8.ReadsQuiet.layers_ok h
    simp [S.rows, ha]
  · obtain ⟨a, cov, x, t, tl', ha, _, _, _, _, _, rfl⟩ := K8.ReadsQuiet.head_ok h
    simp [S.rows, ha]
  · obtain ⟨a, t, tl, ha, rfl⟩ := Meaning.K2.readsAtSO_eq h
    simp [S.rows, ha]

/-- **At both blocks of a segment's later places.** -/
theorem later_rows {B own : Block S Unit} (hB : Later B own) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : B.decide s rs gs = .ok s') : s'.rows = s.rows := by
  cases hB with
  | digits q gp l piece digits => exact commitAtS_rows _ l 2 digits s s' rs gs h
  | reads Z G l X pr reads =>
    have h' : ((laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).decide s
        (rs.take (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).rounds.length)
        (gs.take (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).openings)).bind (fun s₁ =>
        (k1Quiet G l X).decide s₁
          (rs.drop (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).rounds.length)
          (gs.drop (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).openings)) = .ok s' := h
    obtain ⟨s₁, h1, h2⟩ := (bind_ok _ _ _).1 h'
    exact (k1Quiet_rows G l X _ _ _ _ h2).trans (commitAtS_rows _ l 1 reads s s₁ _ _ h1)

/-! ## 3 The statement, and its proof -/

/-- **G.pile.** The item "pile" at the layer of K13 says: all rows on the table are true, at a
reader rw that is a family in the chain's state. It goes BACK over a yes of a later place's block,
on any rounds, if what the rows behind say at the reader behind, they say at the reader in front. -/
def PileBackAtLater : Prop :=
  ∀ (B own : Block S Unit), Later B own → ∀ {Pp W : Type} {nR k : ℕ}
    (rw : Pp × S → W → K13.Law.Wit GE nR k) (x x' : Pp × S) (w : W) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))), B.decide x.2 rs gs = .ok x'.2 →
    (RowsTrue (rw x') x'.2 w → RowsTrue (rw x) x'.2 w) →
    RowsTrue (rw x') x'.2 w → RowsTrue (rw x) x.2 w

theorem pileBackAtLater : PileBackAtLater := by
  intro B own hB Pp W nR k rw x x' w rs gs h hread hw r hr
  refine hread hw r ?_
  rw [later_rows hB x.2 x'.2 rs gs h]
  exact hr

end VerifiableInference.Desc.K1
