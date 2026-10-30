-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/LinkWidths.lean: HOW MANY WORDS EACH WRITTEN COLUMN OF linkAll HAS
(Johnson/Prover/Link/LinkAll.lean): a public list, the same at all positions, draws, letters and
inputs. Statements and proofs. It is what the premise hW of look_wanted (LinkFrameServed.lean) on
widths (every column of next has its tree's width, at every history) compares with a plan's declared
trees.

  length_lastCol, length_sCol, length_lCol
  stageW s         3 * 2 ^ (s.h + s.g) + 3 * (2 * 2 ^ s.h)
  bodyWidths       a stage: 0 at the fold's rounds · the new tree's width at "SEND seed" · 0 at
                   "CS"; the last: 0, 0
  bodyAll_widths, linkAll_widths
  linkNext_width   the column that linkNext writes in round i has the list's i-th number of words

Not shown here. That a plan declares these widths. Nothing on a decision, on soundness or on what
any written value discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.LinkShape
import Johnson.Prover.Link.HyStage

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (sgOf)
open _root_.Desc.K15 (P15 p12Of)
open H2K.JointK (laidOf)

/-- The width of a stage's tree: length_stageColW's number (Johnson/Prover/Link/HyStage.lean). -/
def stageW (s : Sg) : ℕ := 3 * 2 ^ (s.h + s.g) + 3 * (2 * 2 ^ s.h)

theorem length_lastCol (s : Sg) (P : PS) (x : ℕ) : (lastCol s P x).length = 12 := rfl

/-- The width of the tree that a switch into the stage next sends. -/
def nextW (last : Bool) (next : Fmt.M1.Stage) : ℕ := if last then 12 else stageW (sgOf next)

theorem length_sCol (K : BCoins) (last : Bool) (j : ℕ) (cur next : Fmt.M1.Stage) (o : ℕ) (P : PS)
    (row : GroupRow) (D : ℕ → Fmt.Drawn) (x : ℕ) :
    (sCol K last j cur next o P row D x).length = nextW last next := by
  cases last
  · exact length_stageColW _ _ _ _ _ _ _ x
  · rfl

def bodyWidths : Fmt.M1.Stage → List Fmt.M1.Stage → List ℕ
  | _, [] => [0, 0]
  | cur, next :: rest =>
    List.replicate (1 + ((sgOf cur).h + (sgOf cur).g)) 0 ++ [nextW rest.isEmpty next, 0] ++
      bodyWidths next rest

theorem map_const_zero {α : Type} : ∀ l : List α,
    (l.map fun (_ : α) (_ : ℕ) => ([] : List UInt64)).map (fun c => (c 0).length) =
      List.replicate l.length 0
  | [] => rfl
  | _ :: l => congrArg (0 :: ·) (map_const_zero l)

theorem bodyAll_widths (p : P12) (K : BCoins) (D : ℕ → Fmt.Drawn) (x : ℕ) :
    ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS)
      (col : ℕ → List UInt64),
      (bodyAll p K rest j cur l o t P col D).tr.map (fun c => (c x).length) = bodyWidths cur rest
  | [], _, _, _, _, _, _, _ => rfl
  | next :: rest, j, cur, l, o, t, P, col => by
    show ((sRF K j cur o P (rowOf t) D).map (fun (_ : Fmt.RoundView) (_ : ℕ) => ([] : List UInt64)) ++
      [sCol K rest.isEmpty j cur next o P (rowOf t) D, fun _ => []] ++
      (bodyAll p K rest _ _ _ _ _ _ _ D).tr).map (fun c => (c x).length) = _
    rw [List.map_append, List.map_append, bodyAll_widths p K D x rest, List.map_map]
    show (sRF K j cur o P (rowOf t) D).map (fun _ => 0) ++
      [(sCol K rest.isEmpty j cur next o P (rowOf t) D x).length, 0] ++ _ = _
    rw [length_sCol, List.map_const', length_sRF]
    rfl

variable (P : P15) (S : Sz) (t : ℕ) (X : LIn S) (C : LCoins) (D : ℕ → Fmt.Drawn)

theorem length_lCol (x : ℕ) : (lCol P S X C D x).length = 3 * (S.P.R + (S.P.R + 1)) :=
  length_firstColW S _ _ _ _ x

theorem linkAll_widths (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hs : (p12Of P).nums.stages = first :: rest) (x : ℕ) :
    (linkAll P S t X C D).tr.map (fun c => (c x).length) =
      [0, 3 * (S.P.R + (S.P.R + 1)), 0, 0, 0, 0] ++ bodyWidths first rest := by
  rw [linkAll_tr P S t X C D first rest hs, List.map_append, List.map_append, bodyAll_widths]
  show [0, (lCol P S X C D x).length] ++ [0, 0, 0, 0] ++ _ = _
  rw [length_lCol]
  rfl

/-- **The column that linkNext writes in round i.** -/
theorem linkNext_width (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hs : (p12Of P).nums.stages = first :: rest) (i : ℕ) (h : List Fmt.Drawn) (k x : ℕ) :
    ((linkNext P S t X C i h).col k x).length =
      ([0, 3 * (S.P.R + (S.P.R + 1)), 0, 0, 0, 0] ++ bodyWidths first rest).getD i 0 := by
  rw [← linkAll_widths P S t X C (fun j => h.getD j ⟨[], [], [], none⟩) first rest hs x,
    List.getD_eq_getElem?_getD, List.getElem?_map]
  show ((((linkAll P S t X C fun j => h.getD j ⟨[], [], [], none⟩).tr[i]?).getD
    fun _ => []) x).length = _
  cases (linkAll P S t X C fun j => h.getD j ⟨[], [], [], none⟩).tr[i]? <;> rfl

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.length_sCol
#print axioms Johnson.Prover.Link.bodyAll_widths
#print axioms Johnson.Prover.Link.linkAll_widths
#print axioms Johnson.Prover.Link.linkNext_width
