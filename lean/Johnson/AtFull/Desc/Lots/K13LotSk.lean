-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K13LotSk.lean: THE SKELETONS OF K13's THREE LOTS (K13.lot · K13.lot4 ·
K13.lotEnd: Johnson/Desc/ProofFile/Lot/K13.lean · K13At4.lean · K13End.lean), AT EVERY PUBLIC PART Z
AND EVERY GROUND G: NO HYPOTHESIS. After the pattern of K4's row (steps 1 and 3).
Why. ProofFile.Sk.back_of_skel (Johnson/Desc/ProofFile/Law/Skel/) reads of a lot its skeleton alone:
lotSk G L. Each of the three lots is one sub-protocol (or none), reads nothing of G, and supplies no
batching, no test and no run: so its skeleton is plain data off a few fields of Z.
  plainSk name bs   the skeleton of such a lot
  lot    skM3 kCol sent ok · fromM3 · sentM3 · okM3: twins on the table of steps and the entries;
        **lot_sk**: it reads Z.first.lin.kCol · Z.first.pendingRows · Z.cuts · the entries' roots.
        The three works, and lin beyond kCol, enter no skeleton.
        NOTE: fromM3 is 0 where the table has no step "M.0.call", as K13.fromOf is: beforeAt
        (Johnson/Road/K4/K4SentAt.lean) is there the sum of all steps' rounds.
  lot4   parM4 · skM4 codes lin g; **lot4_sk**: it reads Z.first.codes · Z.first.lin · the own
        group's number. THE LOT RETURNS NO SUB-PROTOCOL where linMessageW answers none: skM4 is
        an Option. The samples' number, the first tree's and whereOf Z enter no skeleton.
  lotEnd skM5 ok · okM5; **lotEnd_sk**: it reads the rows that the last declared round but one owes.
  lemmas: toldFrom_empties · sum_roots · from_eq · sent_eq · some_eq · owed_eq · m3_blocks ·
        m4_blocks · m5_blocks
CALLED, NOT TYPED ANEW: rootsOf · rootsFrom_eq · beforeAt (Johnson/Road/K4/K4SentAt.lean).
Limits. The name in a skeleton is the LOT's; the written table's is the spot's. Nothing on what Z
is. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Law.Skel.SkelCut
import Johnson.Desc.ProofFile.Lot.K13
import Johnson.Desc.ProofFile.Lot.K13At4
import Johnson.Desc.ProofFile.Lot.K13End
import Johnson.AtFull.K4Sent.Written
import Johnson.AtFull.Cut.CutWrittenLit
import Johnson.Desc.Ok.PlanWritten.CutTest
import Johnson.Desc.Ok.PlanWritten.MadeTestLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.LotRows
open OnBytes OnBytes.Params
open VerifiableInference.Desc.First (Cut)
open VerifiableInference.PlanWritten (cutFirstFull sameRow proofSizedFull)
open ProofFile (Pub Lot Ground)
open ProofFile.Sk (Skel skel LotSk lotSk toldFrom)
open Johnson.AtFull.K4Sent (esWritten)
open Johnson.AtFull.Cut (cutWritten)
open Johnson.G

/-- A lot's skeleton where the lot has blocks of its own and nothing else. -/
def plainSk (name : String) (bs : List Skel) : LotSk :=
  ⟨name, false, [], bs, fun _ => none, fun _ => false, fun _ => false⟩

/-! ## K13.lot -/

/-- The skeleton of the members' batching, off three values. -/
def skM3 (kCol sent : ℕ) (ok : Bool) : Skel :=
  { name := "K13: the members' batching", place := ⟨1, none, 3, .K13⟩, nRounds := 2 + kCol
    nOracles := 2 + kCol, told := [], before := (List.range sent).map fun n => (1, n)
    planOk := ok, claims := [], after := [] }

/-- The rounds in front of the step "M.0.call"; 0 where the table of steps has none of that name: as
K13.fromOf reads it. -/
def fromM3 (cuts : List Cut) : ℕ :=
  if cuts.any fun c => c.look == "M.0.call" then OnBytes.Road.K4.beforeAt cuts "M.0.call" else 0

/-- How many roots the first chain has sent in front of that step. -/
def sentM3 (cuts : List Cut) (es : List Fmt.Entry) : ℕ :=
  OnBytes.Road.K4.rootsOf (es.take (fromM3 cuts))

/-- The lot's test on the plan. -/
def okM3 (cuts : List Cut) (rows : ℕ) : Bool :=
  decide (1 < rows) && cuts.any fun c => c.look == "M.0.call"

/-! ## K13.lot4 -/

/-- K1's numbers of W's sending, off what a skeleton reads. -/
def parM4 (codes : Codes) (g : ℕ) (msg : Array OracleNotice) : K1.Par :=
  { place := ⟨1, none, 4, .K1⟩, codes := codes, gp := { samples := 0, firstTree := 0 }, work := 0,
    parts := [("W and the messages sent with it", msg)], groups := K1.inGroup g msg }

/-- The skeleton of W's commitment with the own group and (Eval) behind it. -/
def skM4 (codes : Codes) (lin : LinShape) (g : ℕ) : Option Skel :=
  (linMessageW lin).map fun msg =>
    { name := "W's commitment, the own group and (Eval)", place := ⟨1, none, 4, .K1⟩, nRounds := 2
      nOracles := 2, told := toldFrom 0 (K1.oracles (parM4 codes g msg)), before := []
      planOk := K1.planOkOwn (parM4 codes g msg), claims := [], after := [] }

/-! ## K13.lotEnd -/

/-- The skeleton of the first chain's end. -/
def skM5 (ok : Bool) : Skel :=
  { name := "the end of chain 1", place := ⟨1, none, 5, .frame⟩, nRounds := 1, nOracles := 1
    told := [], before := [], planOk := ok, claims := [], after := [] }

/-- The last round but one owes no rows. -/
def okM5 (es : List Fmt.Entry) : Bool := (es.dropLast.getLast?).all (·.rows == 0)

/-! ## The general rows: at every public part and every ground -/

/-- Rounds that tell nothing. -/
theorem toldFrom_empties : ∀ (n k : ℕ), toldFrom k (List.replicate n []) = []
  | 0, _ => rfl
  | n + 1, k => by
    rw [List.replicate_succ]
    simp [toldFrom, toldFrom_empties n (k + 1)]

/-- The plain sum is the forced one (rootsOf, Johnson/Road/K4/K4SentAt.lean). -/
theorem sum_roots (l : List Fmt.DeclaredRound) :
    (l.map (·.entry.roots)).sum = OnBytes.Road.K4.rootsOf (l.map (·.entry)) := by
  unfold OnBytes.Road.K4.rootsOf
  rw [OnBytes.Road.K4.rootsFrom_eq, List.foldl_map, List.sum_eq_foldl, List.foldl_map]

theorem from_eq (Z : Pub) : fromOf Z = fromM3 Z.cuts := by
  unfold fromOf fromOf? ProofFile.Pub.roundsBefore? fromM3
  split <;> rfl

theorem sent_eq (Z : Pub) : (whereOf Z).sent = sentM3 Z.cuts (Z.D.1.map (·.entry)) := by
  show ((Z.D.1.take (fromOf Z)).map (·.entry.roots)).sum = _
  unfold sentM3
  rw [sum_roots, List.map_take, from_eq]

theorem some_eq (Z : Pub) : (fromOf? Z).isSome = Z.cuts.any fun c => c.look == "M.0.call" := by
  unfold fromOf? ProofFile.Pub.roundsBefore?
  by_cases h : (Z.cuts.any fun c => c.look == "M.0.call") = true
  · rw [if_pos h, h]
    rfl
  · rw [if_neg h, eq_false_of_ne_true h]
    rfl

/-- **K13.lot: the lot's blocks' skeletons.** -/
theorem m3_blocks (Z : Pub) (G : Ground) : ((lot Z).blocks G).map skel =
    [skM3 Z.first.lin.kCol (sentM3 Z.cuts (Z.D.1.map (·.entry)))
      (okM3 Z.cuts Z.first.pendingRows)] := by
  show [skel _] = _
  congr 1
  unfold skM3 okM3
  rw [← sent_eq, ← some_eq]
  simp only [skel, Skel.mk.injEq]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · show (([] ++ battRounds (whereOf Z)) ++ []).length = _
    simp [battRounds, whereOf]
    omega
  · show (([] ++ List.replicate (2 + (whereOf Z).lin.kCol) []) ++ []).length = _
    simp [whereOf]
  · show toldFrom 0 (([] ++ List.replicate (2 + (whereOf Z).lin.kCol) []) ++ []) = _
    rw [List.nil_append, List.append_nil]
    exact toldFrom_empties _ _
  · show ([] ++ (List.range (whereOf Z).sent).map fun n => ((whereOf Z).chain, n)) ++ [] = _
    rw [List.nil_append, List.append_nil]
    rfl
  · show ((((((true && decide (1 < (whereOf Z).rows)) && true) && fits (whereOf Z)) &&
      (fromOf? Z).isSome)) && true) = _
    have hf : fits (whereOf Z) = true := rfl
    rw [hf]
    simp [whereOf]

/-- **K13.lot, at every public part and every ground.** -/
theorem lot_sk (Z : Pub) (G : Ground) : lotSk G (lot Z) =
    plainSk "K13: the members' batching"
      [skM3 Z.first.lin.kCol (sentM3 Z.cuts (Z.D.1.map (·.entry)))
        (okM3 Z.cuts Z.first.pendingRows)] := by
  unfold lotSk plainSk
  rw [m3_blocks]
  rfl

/-- **K13.lot4: the lot's blocks' skeletons.** -/
theorem m4_blocks (Z : Pub) (G : Ground) : ((lot4 Z).blocks G).map skel =
    (skM4 Z.first.codes Z.first.lin (K1.ownGroup Z.first)).toList := by
  have e : (lot4 Z).blocks G =
      ((wBlock Z).toList.map (atM4 (whereOf Z))).map (fun b => b.retype) ++ [] := rfl
  rw [e, List.append_nil]
  unfold wBlock K1.wAt skM4
  cases linMessageW Z.first.lin with
  | none => rfl
  | some msg =>
    show [skel _] = [_]
    congr 1
    simp only [skel, Skel.mk.injEq]
    refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, ?_, rfl, rfl⟩
    · show toldFrom 0 (K1.oracles _ ++ []) = _
      rw [List.append_nil]
      rfl
    · show ((K1.planOkOwn _ && true) && true) = _
      rw [Bool.and_true, Bool.and_true]
      rfl

/-- **K13.lot4, at every public part and every ground.** -/
theorem lot4_sk (Z : Pub) (G : Ground) : lotSk G (lot4 Z) =
    plainSk "K1 and K13: W's commitment, the request's own group and the row (Eval)"
      (skM4 Z.first.codes Z.first.lin (K1.ownGroup Z.first)).toList := by
  unfold lotSk plainSk
  rw [m4_blocks]
  rfl

theorem owed_eq (l : List Fmt.DeclaredRound) :
    ChainEnd.nothingOwedOnPlan l.dropLast = okM5 (l.map (·.entry)) := by
  unfold ChainEnd.nothingOwedOnPlan okM5
  rw [← List.map_dropLast, List.getLast?_map]
  cases l.dropLast.getLast? <;> rfl

/-- **K13.lotEnd: the lot's blocks' skeletons.** -/
theorem m5_blocks (Z : Pub) (G : Ground) : ((lotEnd Z).blocks G).map skel =
    [skM5 (okM5 (Z.D.1.map (·.entry)))] := by
  show [skel _] = _
  congr 1
  unfold skM5
  rw [← owed_eq]
  simp only [skel, Skel.mk.injEq]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩
  show (ChainEnd.nothingOwedOnPlan (inFrontOf Z) && true) = _
  rw [Bool.and_true]
  rfl

/-- **K13.lotEnd, at every public part and every ground.** -/
theorem lotEnd_sk (Z : Pub) (G : Ground) : lotSk G (lotEnd Z) =
    plainSk "the end of the first chain" [skM5 (okM5 (Z.D.1.map (·.entry)))] := by
  unfold lotSk plainSk
  rw [m5_blocks]
  rfl

end VerifiableInference.Desc.K13.LotRows

#print axioms VerifiableInference.Desc.K13.LotRows.toldFrom_empties
#print axioms VerifiableInference.Desc.K13.LotRows.sum_roots
#print axioms VerifiableInference.Desc.K13.LotRows.from_eq
#print axioms VerifiableInference.Desc.K13.LotRows.sent_eq
#print axioms VerifiableInference.Desc.K13.LotRows.some_eq
#print axioms VerifiableInference.Desc.K13.LotRows.owed_eq
#print axioms VerifiableInference.Desc.K13.LotRows.m3_blocks
#print axioms VerifiableInference.Desc.K13.LotRows.m4_blocks
#print axioms VerifiableInference.Desc.K13.LotRows.m5_blocks
#print axioms VerifiableInference.Desc.K13.LotRows.lot_sk
#print axioms VerifiableInference.Desc.K13.LotRows.lot4_sk
#print axioms VerifiableInference.Desc.K13.LotRows.lotEnd_sk
