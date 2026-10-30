-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/TieLaw.lean: tieOk p = true gives its clauses as propositions, so that the test
Johnson/Desc/K12/Law/TieOk.lean is no transcription.

Statements and proofs.
Main names:
  `TiedW`: by recursion, as the test walks: at a stage but the last the written round number 1 + kk
    ("SEND seed") sends the shape that the next stage's one opening declares.
  `tied_of_walk`, `tied_of_ok`: tieOk p = true gives: the written rounds are there (w0 :: w); "BAT"
    declares no opening and no stored table; there are as many written rounds as laid declared
    rounds; TiedW holds along the place's own rounds.
Limits: No soundness is claimed, and nothing is said on hiding.
Every theorem of this file is proved outright; what each rests on is printed at the file's end.

-/
import Johnson.Desc.K12.Law.DealLaw
import Johnson.Desc.K12.Law.TieOk

set_option autoImplicit false
namespace H2K.First
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.Sw
open H2K.Pub (WR writtenOf kk)

def TiedW : ℕ → Fmt.M1.Stage → List Fmt.M1.Stage → Laid → List WR → Prop
  | _, _, [], _, _ => True
  | j, cur, nxt :: rest, l, w =>
    (∃ (dS : WR) (o : Fmt.Shape × Fmt.TreeSource), w[1 + kk cur]? = some dS ∧
      (cutN nxt rest (l.drop (cur.k + 3))).flatMap (·.opens) = [o] ∧ dS.tree = some o.1) ∧
    TiedW (j + 1) nxt rest (l.drop (cur.k + 3)) (w.drop (kk cur + 3))

theorem tied_of_walk : ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid)
    (w : List WR), ok (tieWalk j cur rest l w) = true → TiedW j cur rest l w
  | [], _, _, _, _, _ => trivial
  | nxt :: rest, j, cur, l, w, h => by
    unfold tieWalk at h
    unfold ok at h
    rw [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, tied_of_walk rest (j + 1) nxt _ _ h2⟩
    dsimp only at h1
    split at h1
    · rename_i dS o e1 e2
      exact ⟨dS, o, e1, e2, of_decide_eq_true h1⟩
    · cases h1

/-- The test's yes gives its clauses as propositions. -/
theorem tied_of_ok (p : P12) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hs : p.nums.stages = a :: rest) (h : tieOk p = true) :
    ∃ (w0 : WR) (w : List WR), writtenOf p.nums = some (w0 :: w) ∧
      nOpen (((laidOf p).take 1).map (·.1)) = 0 ∧ w.length = (laidS p).length ∧
      TiedW 0 a rest (laidS p) w := by
  unfold tieOk at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h0, h1⟩ := h
  obtain ⟨ww, hw⟩ := Option.isSome_iff_exists.1 h0
  unfold tieOn at h1
  rw [hs] at h1
  dsimp only at h1
  rw [ok_append] at h1
  obtain ⟨h2, h3⟩ := h1
  unfold ok at h2
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at h2
  obtain ⟨b1, b2⟩ := h2
  have hB : writtenB p = ww.drop 1 := by
    unfold writtenB
    rw [hw]
    rfl
  cases ww with
  | nil =>
    -- No written round: then the first tie, or the length, refuses; the length says that nothing
    -- is laid
    rw [hB] at b2 h3
    exfalso
    cases rest with
    | nil =>
      -- A test of one stage has no declared rounds at all
      unfold writtenOf at hw
      unfold H2U.roundsOfNums at hw
      rw [hs] at hw
      cases hw
    | cons nxt rest =>
      have := tied_of_walk (nxt :: rest) 0 a _ _ h3
      obtain ⟨⟨dS, o, e1, _, _⟩, _⟩ := this
      simp at e1
  | cons w0 w =>
    rw [hB] at b2 h3
    refine ⟨w0, w, hw, ?_, b2, tied_of_walk rest 0 a _ _ h3⟩
    rw [← nOpenB_eq]
    exact b1

end H2K.First
