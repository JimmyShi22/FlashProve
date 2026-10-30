-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/LinkShape.lean: THE SHAPE OF WHAT linkAll SHOWS
(Johnson/Prover/Link/LinkAll.lean): how many rounds, and that the round at place i drew D i.
Statements and proofs; each is an unfolding or an induction after bodyAll's own recursion. No value
is read.

  bodyLen            the number of the stages' rounds: s.h + s.g + 3 a stage, 2 at the last
  showRV_drawn, foldRV_drawn, bodyAll_drawn, linkAll_drawn   the round at place i drew D (o + i)
  bodyAll_length, bodyAll_trees, linkAll_length, linkAll_trees   rounds and trees are as many
  sg0_eq             sg0 P is sgOf of the first stage

Not shown here. Nothing on a decision; nothing on soundness; nothing on what any value that is sent
discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.LinkCausal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (sgOf)
open _root_.Desc.K15 (P15 p12Of)
open H2K.JointK (laidOf)

/-- The number of the stages' rounds. -/
def bodyLen : Fmt.M1.Stage → List Fmt.M1.Stage → ℕ
  | _, [] => 2
  | cur, next :: rest => (sgOf cur).h + (sgOf cur).g + 3 + bodyLen next rest

theorem showRV_drawn : ∀ (k : ℕ) (q : RIdx (sVars GE 2 k) → GE) (D : ℕ → Fmt.Drawn) (i : ℕ)
    (r : Fmt.RoundView), (showRV k q D)[i]? = some r → r.drawn = D i
  | 0, _, _, _, _, h => by cases h
  | _ + 1, _, _, 0, _, h => by cases h; rfl
  | k + 1, q, D, i + 1, r, h => showRV_drawn k _ (fun n => D (n + 1)) i r h

theorem foldRV_drawn (s : Sg) (v μ : s.cIn.J → GE) (W : HIdx (sVars GE 2 (s.h + s.g)) → GE)
    (D : ℕ → Fmt.Drawn) : ∀ (i : ℕ) (r : Fmt.RoundView), (foldRV s v μ W D)[i]? = some r → r.drawn = D i
  | 0, _, h => by cases h; rfl
  | i + 1, r, h => showRV_drawn _ _ (fun n => D (n + 1)) i r h

theorem bodyAll_length (p : P12) (K : BCoins) (D : ℕ → Fmt.Drawn) :
    ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS)
      (col : ℕ → List UInt64), (bodyAll p K rest j cur l o t P col D).rs.length = bodyLen cur rest
  | [], _, _, _, _, _, _, _ => rfl
  | next :: rest, j, cur, l, o, t, P, col => by
    show (sRF K j cur o P (rowOf t) D ++ sRS p K j cur next l o t P (rowOf t) D ++
      (bodyAll p K rest _ _ _ _ _ _ _ D).rs).length = _
    rw [List.length_append, List.length_append, length_sRF, bodyAll_length p K D rest]
    show 1 + _ + 2 + _ = _ + 3 + _
    omega

theorem bodyAll_trees (p : P12) (K : BCoins) (D : ℕ → Fmt.Drawn) :
    ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS)
      (col : ℕ → List UInt64), (bodyAll p K rest j cur l o t P col D).tr.length = bodyLen cur rest
  | [], _, _, _, _, _, _, _ => rfl
  | next :: rest, j, cur, l, o, t, P, col => by
    show ((sRF K j cur o P (rowOf t) D).map (fun (_ : Fmt.RoundView) (_ : ℕ) => ([] : List UInt64)) ++
      [sCol K rest.isEmpty j cur next o P (rowOf t) D, fun _ => []] ++
      (bodyAll p K rest _ _ _ _ _ _ _ D).tr).length = _
    rw [List.length_append, List.length_append, List.length_map, length_sRF,
      bodyAll_trees p K D rest]
    show 1 + _ + 2 + _ = _ + 3 + _
    omega

theorem bodyAll_drawn (p : P12) (K : BCoins) (D : ℕ → Fmt.Drawn) :
    ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS)
      (col : ℕ → List UInt64) (i : ℕ) (r : Fmt.RoundView),
      (bodyAll p K rest j cur l o t P col D).rs[i]? = some r → r.drawn = D (o + i)
  | [], _, _, _, _, _, _, _, 0, _, h => by cases h; rfl
  | [], _, _, _, _, _, _, _, 1, _, h => by cases h; rfl
  | [], _, _, _, _, _, _, _, _ + 2, _, h => by cases h
  | next :: rest, j, cur, l, o, t, P, col, i, r, h => by
    have hlen := length_sRF K j cur o P (rowOf t) D
    have l2 : (sRS p K j cur next l o t P (rowOf t) D).length = 2 := rfl
    have h' : (sRF K j cur o P (rowOf t) D ++ sRS p K j cur next l o t P (rowOf t) D ++
      (bodyAll p K rest (j + 1) next (l.drop (cur.k + 3)) (o + ((sgOf cur).h + (sgOf cur).g) + 3)
        (sT3 p K rest.isEmpty j cur next l o t P col (rowOf t) D)
        (sNext K rest.isEmpty j cur next o P (rowOf t) D)
        (sCol K rest.isEmpty j cur next o P (rowOf t) D) D).rs)[i]? = some r := h
    by_cases c1 : i < 1 + ((sgOf cur).h + (sgOf cur).g)
    · rw [get3_left _ _ _ i (by rw [hlen]; exact c1)] at h'
      exact foldRV_drawn _ _ _ _ (fun n => D (o + n)) i r h'
    · by_cases c2 : i < 3 + ((sgOf cur).h + (sgOf cur).g)
      · rw [get3_mid _ _ _ i (by rw [hlen]; omega) (by rw [hlen, l2]; omega), hlen] at h'
        rcases (by omega : i = 1 + ((sgOf cur).h + (sgOf cur).g) ∨
          i = 2 + ((sgOf cur).h + (sgOf cur).g)) with e | e
        · subst e
          rw [Nat.sub_self] at h'
          cases h'
          show D (o + 1 + _) = D (o + (1 + _))
          rw [Nat.add_assoc]
        · subst e
          have e1 : 2 + ((sgOf cur).h + (sgOf cur).g) - (1 + ((sgOf cur).h + (sgOf cur).g)) =
              1 := by omega
          rw [e1] at h'
          cases h'
          show D (o + 2 + _) = D (o + (2 + _))
          rw [Nat.add_assoc]
      · rw [get3_right _ _ _ i (by rw [hlen, l2]; omega), hlen, l2] at h'
        have ih := bodyAll_drawn p K D rest _ _ _ _ _ _ _ _ r h'
        rw [ih]
        congr 1
        omega

theorem sg0_eq (P : P15) (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hs : (p12Of P).nums.stages = first :: rest) : sg0 P = sgOf first := by
  unfold sg0
  rw [hs]
  rfl

variable (P : P15) (S : Sz) (t : ℕ) (X : LIn S) (C : LCoins) (D : ℕ → Fmt.Drawn)

theorem linkAll_length (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hs : (p12Of P).nums.stages = first :: rest) :
    (linkAll P S t X C D).rs.length = 6 + bodyLen first rest := by
  rw [linkAll_rs P S t X C D first rest hs, List.length_append, List.length_append,
    bodyAll_length]
  rfl

theorem linkAll_trees (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hs : (p12Of P).nums.stages = first :: rest) :
    (linkAll P S t X C D).tr.length = 6 + bodyLen first rest := by
  rw [linkAll_tr P S t X C D first rest hs, List.length_append, List.length_append,
    bodyAll_trees]
  rfl

theorem lFront_drawn : ∀ (i : ℕ) (r : Fmt.RoundView), (lFront S t X C D)[i]? = some r → r.drawn = D i
  | 0, _, h => by cases h; rfl
  | 1, _, h => by cases h; rfl
  | 2, _, h => by cases h; rfl
  | 3, _, h => by cases h; rfl
  | 4, _, h => by cases h; rfl
  | n + 5, _, h => by
    rw [List.getElem?_eq_none (by show 5 ≤ n + 5; omega)] at h
    cases h

theorem linkAll_drawn (i : ℕ) (r : Fmt.RoundView) (h : (linkAll P S t X C D).rs[i]? = some r) :
    r.drawn = D i := by
  cases hs : (p12Of P).nums.stages with
  | nil => rw [linkAll_nil P S t X C D hs] at h; cases h
  | cons first rest =>
    rw [linkAll_rs P S t X C D first rest hs] at h
    have l5 : (lFront S t X C D).length = 5 := rfl
    by_cases c1 : i < 5
    · rw [get3_left _ _ _ i (by rw [l5]; exact c1)] at h
      exact lFront_drawn S t X C D i r h
    · by_cases c2 : i = 5
      · subst c2
        rw [get3_mid _ _ _ 5 (by rw [l5]) (by rw [l5]; show 5 < 5 + 1; omega), l5] at h
        cases h
        rfl
      · rw [get3_right _ _ _ i (by rw [l5]; show 5 + 1 ≤ i; omega), l5] at h
        have e := bodyAll_drawn _ _ D rest _ _ _ _ _ _ _ _ r h
        rw [e]
        congr 1
        show 6 + (i - (5 + 1)) = i
        omega

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.bodyAll_length
#print axioms Johnson.Prover.Link.bodyAll_trees
#print axioms Johnson.Prover.Link.bodyAll_drawn
#print axioms Johnson.Prover.Link.sg0_eq
#print axioms Johnson.Prover.Link.linkAll_length
#print axioms Johnson.Prover.Link.linkAll_trees
#print axioms Johnson.Prover.Link.linkAll_drawn
