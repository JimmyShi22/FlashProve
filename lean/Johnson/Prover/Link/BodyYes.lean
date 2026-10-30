-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/BodyYes.lean: THE INDUCTION OVER THE STAGES OF A PROXIMITY TEST, AS A FRAME: if
an invariant is such that at every stage each of the description's own parts says yes on bodyAll's
share for it, and the invariant holds again behind the stage, then the stages' block says yes on all
that bodyAll (Johnson/Prover/Link/BodyAll.lean) shows. Statement and proof; the invariant is a
letter.

  StageYes      at a stage that is not the last: the fold, the switch and the batching behind it say
                yes on sRF | sRS with sGS | nothing, and leave bodyAll's own records · the next mask
                has come · four public numbers of the cut of the proximity test's frame
                (Johnson/Desc/K12/Frame.lean) (rounds and openings of the fold's and the switch's
                blocks): PREMISES here, like the rest
  body_yes_of   Inv ⟹ StageYes ∧ Inv behind (at every stage but the last) · Inv ⟹ the base case's
                yes, with Post of the record that it leaves (at the last) · Inv in front ⟹ the
                stages' block says yes, and Post holds of the record that it leaves. Post: a second
                letter: what stands behind the test reads that record

By: the library's stagesFrom_ok (an iff) and stagesFrom_last (Johnson/Desc/K12/FrameLaws.lean).
The rounds are handed as a block's decide is shown them: without the sealed digest (noDigest).

Not shown here. That any invariant meets the two premises. Nothing on soundness; nothing on what
any value that is sent discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.BodyAll
import Johnson.Desc.K12.FrameLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (sgOf)

/-- The verifier's record behind the switch. Where the switch's part refuses: sT1, what stood in
front, in silence (.toOption.getD); StageYes.switch asks that it returns .ok. -/
def sT2 (p : P12) (K : BCoins) (last : Bool) (j : ℕ) (cur next : Fmt.M1.Stage) (l : Laid) (o : ℕ)
    (t : T12) (P : PS) (col : ℕ → List UInt64) (row : GroupRow) (D : ℕ → Fmt.Drawn) : T12 :=
  ((guardedProximityTestParts.switch p j cur next last (((l.drop (1 + cur.k)).take 2).map (·.1))).decide
    (sT1 p K j cur l o t P row D) ((sRS p K j cur next l o t P row D).map noDigest)
    (sGS cur o col D)).toOption.getD (sT1 p K j cur l o t P row D)

/-- **What one stage that is not the last delivers.** -/
structure StageYes (p : P12) (K : BCoins) (rest : List Fmt.M1.Stage) (j : ℕ)
    (cur next : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS) (col : ℕ → List UInt64)
    (D : ℕ → Fmt.Drawn) : Prop where
  fold : ∃ t₁, (guardedProximityTestParts.fold p j cur ((l.take (1 + cur.k)).map (·.1))).decide t
    ((sRF K j cur o P (rowOf t) D).map noDigest) [] = .ok t₁
  switch : ∃ t₂, (guardedProximityTestParts.switch p j cur next rest.isEmpty
    (((l.drop (1 + cur.k)).take 2).map (·.1))).decide (sT1 p K j cur l o t P (rowOf t) D)
    ((sRS p K j cur next l o t P (rowOf t) D).map noDigest) (sGS cur o col D) = .ok t₂
  behind : ∃ t₃, (guardedProximityTestParts.batBehind p (j + 1) next
    (((l.drop (1 + cur.k)).take 2).map (·.1))).decide
    (sT2 p K rest.isEmpty j cur next l o t P col (rowOf t) D) [] [] = .ok t₃
  came : (!p.early || guardedProximityTestParts.maskCame (sT3 p K rest.isEmpty j cur next l o t P col (rowOf t) D)) =
    true
  nF : (foldAt guardedProximityTestParts p j cur l : Block T12 Unit).rounds.length =
    1 + ((sgOf cur).h + (sgOf cur).g)
  oF : (foldAt guardedProximityTestParts p j cur l : Block T12 Unit).openings = 0
  nS : (switchAt guardedProximityTestParts p j cur next rest.isEmpty l : Block T12 Unit).rounds.length = 2
  oS : (switchAt guardedProximityTestParts p j cur next rest.isEmpty l : Block T12 Unit).openings = 1

theorem getD_of_ok {α : Type} {e : Except String α} {x d : α} (h : e = .ok x) :
    e.toOption.getD d = x := by
  rw [h]
  rfl

/-- **The induction.** -/
theorem body_yes_of (p : P12) (K : BCoins) (D : ℕ → Fmt.Drawn)
    (Inv : List Fmt.M1.Stage → ℕ → Fmt.M1.Stage → Laid → ℕ → T12 → PS → (ℕ → List UInt64) → Prop)
    (Post : T12 → Prop)
    (hstep : ∀ next rest j cur l o t P col, Inv (next :: rest) j cur l o t P col →
      StageYes p K rest j cur next l o t P col D ∧
        Inv rest (j + 1) next (l.drop (cur.k + 3)) (o + ((sgOf cur).h + (sgOf cur).g) + 3)
          (sT3 p K rest.isEmpty j cur next l o t P col (rowOf t) D)
          (sNext K rest.isEmpty j cur next o P (rowOf t) D)
          (sCol K rest.isEmpty j cur next o P (rowOf t) D))
    (hbase : ∀ j cur l o t P col, Inv [] j cur l o t P col →
      ∃ t', (guardedProximityTestParts.base p j cur (l.map (·.1))).decide t
        ((lastOut p j cur o t P col (rowOf t) D).rs.map noDigest)
        (lastOut p j cur o t P col (rowOf t) D).gs = .ok t' ∧ Post t') :
    ∀ rest j cur l o t P col, Inv rest j cur l o t P col →
      ∃ t', (stagesFrom guardedProximityTestParts p j cur rest l : Block T12 Unit).decide t
        ((bodyAll p K rest j cur l o t P col D).rs.map noDigest)
        (bodyAll p K rest j cur l o t P col D).gs = .ok t' ∧ Post t'
  | [], j, cur, l, o, t, P, col, h => by
    obtain ⟨t', ht, hP⟩ := hbase j cur l o t P col h
    exact ⟨t', (stagesFrom_last guardedProximityTestParts p j cur l t _ _).trans ht, hP⟩
  | next :: rest, j, cur, l, o, t, P, col, h => by
    obtain ⟨Y, hI⟩ := hstep next rest j cur l o t P col h
    obtain ⟨t', ih, hP⟩ := body_yes_of p K D Inv Post hstep hbase rest _ _ _ _ _ _ _ hI
    obtain ⟨t₁, h1⟩ := Y.fold
    obtain ⟨t₂, h2⟩ := Y.switch
    obtain ⟨t₃, h3⟩ := Y.behind
    have e1 : sT1 p K j cur l o t P (rowOf t) D = t₁ := getD_of_ok h1
    have e2 : sT2 p K rest.isEmpty j cur next l o t P col (rowOf t) D = t₂ := getD_of_ok h2
    have e3 : sT3 p K rest.isEmpty j cur next l o t P col (rowOf t) D = t₃ := getD_of_ok h3
    have lF : ((sRF K j cur o P (rowOf t) D).map noDigest).length =
        1 + ((sgOf cur).h + (sgOf cur).g) := by
      rw [List.length_map]; exact length_foldRV _ _ _ _ _
    have lS : ((sRS p K j cur next l o t P (rowOf t) D).map noDigest).length = 2 := rfl
    have lG : (sGS cur o col D).length = 1 := rfl
    refine ⟨t', (stagesFrom_ok guardedProximityTestParts p j cur next rest l t t' _ _).2
      ⟨t₁, t₂, t₃, ?_, ?_, ?_, ?_, ?_⟩, hP⟩
    · rw [Y.nF, Y.oF]
      show (guardedProximityTestParts.fold p j cur _).decide t (((sRF K j cur o P (rowOf t) D ++
                         sRS p K j cur next l o t P (rowOf t) D ++ _).map noDigest).take _) (List.take 0 _) = _
      rw [List.map_append, List.map_append, List.append_assoc, ← lF, List.take_left',
        List.take_zero]
      · exact h1
      · rfl
    · rw [Y.nF, Y.oF, Y.nS, Y.oS]
      show (guardedProximityTestParts.switch p j cur next rest.isEmpty _).decide t₁
        ((((sRF K j cur o P (rowOf t) D ++ sRS p K j cur next l o t P (rowOf t) D ++ _).map
          noDigest).drop _).take 2) (((sGS cur o col D ++ _).drop 0).take 1) = _
      rw [List.map_append, List.map_append, List.append_assoc, ← lF, List.drop_left' rfl,
        List.take_left' lS, List.drop_zero, List.take_left' lG, ← e1]
      exact h2
    · rw [← e2]; exact h3
    · rw [← e3]; exact Y.came
    · rw [Y.nF, Y.oF, Y.nS, Y.oS, ← e3]
      show (stagesFrom guardedProximityTestParts p (j + 1) next rest _ : Block T12 Unit).decide _
        (((sRF K j cur o P (rowOf t) D ++ sRS p K j cur next l o t P (rowOf t) D ++ _).map
          noDigest).drop _) ((sGS cur o col D ++ _).drop (0 + 1)) = _
      rw [List.map_append, List.map_append,
        List.drop_left' (by rw [List.length_append, lF, lS]), List.drop_left' lG]
      exact ih

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.getD_of_ok
#print axioms Johnson.Prover.Link.body_yes_of
