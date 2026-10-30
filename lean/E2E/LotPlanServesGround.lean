-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotPlanServesGround.lean: what E2E/LotPlanServes.lean needs of the key file's description in the
goals' scope, off the five returns of which the offline description is made, WITHOUT the test protocolDataWellFormed. It stands on laws.14
alone and names no prover's value.

Why. LotPlanServes has two premises on the public files: offlineDescription returns, and the files are in scope. The laws
on the key file's rows and places in E2E/ take KeyNamed or KeySourced, whose members are shown only where protocolDataWellFormed accepts.
The library's older laws on the key file's back speak off the returns alone: this file calls them.

Main names.
  Made5 Z X N P: the reader, the maker and the three functions return X, N, P at Z (the field source of KeySourced).
  pins, plan, wanted, rows, decl, sized, lin: in scope, off Made5: the written values; the tests on the plan and on the
    places pass; the three chains' rows are the three written lists; the declared rounds are the written ones.
  mem_unrunD: a declared round of a list of runs is one of the distinct rounds.
  stored_recs, a_written, v_written, rows_written, split_written, w_written: closed lines, put to Lean's kernel. EACH CAN
    SAY NO.
  stored_decl: so every stored table that a written round declares has the item 0, the depth 32 and the width 2048.
  column_some: below 2^32 the stand-in committer's column at the written shape is there, with 2048 entries.
  widths_of: planServes' premise hst, at any description with the written rounds and any prover with such columns.

Nothing on soundness, completeness, hiding or binding. No law over coins.
-/
import Johnson.AtFull.KeyBack.KeyBackAtFixed
import Johnson.AtFull.KeyBack.InScope
import Johnson.HB.LLHARD.KB8.Row
import Johnson.HB.LLHARD.KB8.PinsOfReturns
import Johnson.IMR.KeyBackOfRows
import Johnson.Bind.ForProver.Laws
import Johnson.Desc.ProofFile.Honest.Law.PlanGives
import E2E.KeyPlaces
import E2E.KeyBookHeldK1Jobs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.LotPlanGround
open VerifiableInference VerifiableInference.Desc
open Johnson.KB8 (declKeyFull declRecsFull unrunD rangesNumsFull laterPlacesFull)
open Johnson.RunOne.Sound (rowsOf)
open Lk6.AtPlan (keyFull)
open Bind.ForProver (encAt shapeOfIndex rowsFit encAt_length)
open AtPublicFiles.KeyBook (fullFirst fullShared fullSecond)
open ProofFile.Honest (Prover TableRand)

/-- **The five returns**: the field source of KeySourced (E2E/KeyPublic.lean), alone. -/
def Made5 (Z : VerifierAndGoals.PublicFiles) (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces) : Prop :=
  ∃ X₀ m, PlanWritten.publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) = .ok X₀ ∧
    Key.madeAt X₀ Z.lay Key.fixedDigest = .ok m ∧ Key.sourceOf m = .ok X ∧
    Key.rangesNumbers m = .ok N ∧ Key.laterPlaces m = .ok P

section Scope
variable {Z : VerifierAndGoals.PublicFiles} {X : Key.Source} {N : H2U.PlaceNums} {P : Key.LaterPlaces}

/-- In scope what the rows read is written, and so is the shared chain's shape as read back. -/
theorem pins (scope : VerifierAndGoals.InScope Z = true) (h : Made5 Z X N P) :
    Johnson.KB8.Pins X N P ∧ X.Y.k.shared.lin = keyFull.once.shape := by
  obtain ⟨X₀, m, h0, hm, r1, r2, r3⟩ := h
  have hN : N = rangesNumsFull :=
    Except.ok.inj (r2.symm.trans (Johnson.AtFull.KeyBack.rangesNumbers_in_scope scope h0 hm))
  have hP : P = laterPlacesFull :=
    Except.ok.inj (r3.symm.trans (Johnson.AtFull.KeyBack.laterPlaces_in_scope scope h0 hm))
  have hx := Johnson.KB8.pinsX_at_fixed scope h0 hm r1
  exact ⟨Johnson.KB8.pins_of_parts hx (Johnson.KB8.pinsNP_of_eq hN hP), hx.sharedLin⟩

/-- In scope the description passes its tests on the plan. -/
theorem plan (scope : VerifierAndGoals.InScope Z = true) (h : Made5 Z X N P) :
    (Key.descriptionFromSource X N P).planOk = true := by
  obtain ⟨X₀, m, h0, hm, r1, r2, r3⟩ := h
  exact Johnson.KB4.key_planOk_in_scope scope h0 hm r1 r2 r3

/-- In scope its places and numbers of rounds are the table's. -/
theorem wanted (scope : VerifierAndGoals.InScope Z = true) (h : Made5 Z X N P) :
    (Key.descriptionFromSource X N P).wantedOk = true :=
  IM.key_wantedOk (pins scope h).1 (pins scope h).2

/-- **In scope the three chains' rows are the three written lists**, off the returns. -/
theorem rows (scope : VerifierAndGoals.InScope Z = true) (h : Made5 Z X N P) :
    rowsOf (Key.descriptionFromSource X N P).first.blocksInOrder = fullFirst ∧
      rowsOf (Key.descriptionFromSource X N P).shared.blocksInOrder = fullShared ∧
      rowsOf (Key.descriptionFromSource X N P).second.blocksInOrder = fullSecond := by
  have hp := plan scope h
  have hw := wanted scope h
  obtain ⟨X₀, m, h0, hm, r1, r2, r3⟩ := h
  exact AtPublicFiles.KeyBook.places_of_made scope h0 hm (IM.descOfMade_of_rows r1 r2 r3) hp hw

/-- **In scope the declared rounds are the written ones.** -/
theorem decl (scope : VerifierAndGoals.InScope Z = true) (h : Made5 Z X N P) :
    (Key.descriptionFromSource X N P).roundsDeclaredByBlocks = declKeyFull :=
  Johnson.KB8.decl_full (pins scope h).1

/-- In scope the sized key is the written value. -/
theorem sized (scope : VerifierAndGoals.InScope Z = true) (h : Made5 Z X N P) :
    X.chains.made.sized.key = keyFull := (pins scope h).1.sized

/-- In scope the first chain's shape of the test on the table, as read back, is the written one. -/
theorem lin (scope : VerifierAndGoals.InScope Z = true) (h : Made5 Z X N P) :
    X.Y.k.oneTime.lin = keyFull.once.shape := (pins scope h).1.lin

end Scope

/-! ## The closed lines -/

/-- A declared round of a list of runs is one of the distinct rounds. -/
theorem mem_unrunD {recs : List Fmt.DeclaredRound} {runs : List (Nat × Nat)} {d : Fmt.DeclaredRound}
    (h : d ∈ unrunD recs runs) : d ∈ recs := by
  unfold unrunD at h
  obtain ⟨x, -, hx⟩ := List.mem_flatMap.1 h
  cases e : recs[x.2]? with
  | none =>
    rw [e] at hx
    exact absurd (show d ∈ ([] : List Fmt.DeclaredRound) from hx) List.not_mem_nil
  | some r =>
    rw [e] at hx
    have hx' : d ∈ List.replicate x.1 r := hx
    rw [(List.mem_replicate.1 hx').2]
    exact List.mem_of_getElem? e

/-- **Every stored table that a distinct written round declares: the item 0, the depth 32, the width 2048.** A closed
question to Lean's kernel. -/
theorem stored_recs : (declRecsFull.all fun d => d.stored.all fun t =>
    t.item == 0 && t.sh.a == 32 && t.sh.W == 2048) = true := by decide +kernel

/-- A negative test: at another width the same line says no, so some round does declare a stored table. -/
theorem stored_recs_no : (declRecsFull.all fun d => d.stored.all fun t =>
    t.item == 0 && t.sh.a == 32 && t.sh.W == 2047) = false := by decide +kernel

/-- The committer's depth at the key's written index. -/
theorem a_written : (shapeOfIndex keyFull.once.shape.fold.index).a = 32 := by decide +kernel

/-- The committer's number of rows, as a power of 2, at the key's written index. -/
theorem v_written : (shapeOfIndex keyFull.once.shape.fold.index).v = 11 := by decide +kernel

/-- The matrix fits the rows at the written sizes. -/
theorem rows_written : rowsFit (shapeOfIndex keyFull.once.shape.fold.index) keyFull.once.shape.kLo
    keyFull.once.shape.matrixRows = true := by decide +kernel

/-- The written shape splits. -/
theorem split_written : keyFull.once.shape.sharedSplitNeeded = true := by decide +kernel

/-- The written shape has a message W. -/
theorem w_written : (OnBytes.linMessageW keyFull.once.shape).isSome = true := by
  have h := AtPublicFiles.KeyBook.rides_full.2.2
  cases e : OnBytes.linMessageW keyFull.once.shape with
  | none =>
    rw [e] at h
    cases h
  | some a => rfl

/-- **Every stored table that a written round of the three lists declares.** -/
theorem stored_decl : ∀ d ∈ declKeyFull.1 ++ declKeyFull.2.1 ++ declKeyFull.2.2, ∀ t ∈ d.stored,
    t.item = 0 ∧ t.sh.a = 32 ∧ t.sh.W = 2048 := by
  intro d hd t ht
  have hm : d ∈ declRecsFull := by
    rcases List.mem_append.1 hd with hd | hd
    · rcases List.mem_append.1 hd with hd | hd
      · exact mem_unrunD hd
      · exact mem_unrunD hd
    · exact mem_unrunD hd
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 stored_recs d hm) t ht
  rw [Bool.and_eq_true, Bool.and_eq_true] at h1
  exact ⟨beq_iff_eq.1 h1.1.1, beq_iff_eq.1 h1.1.2, beq_iff_eq.1 h1.2⟩

/-- **Below 2^32 the column at the written shape is there, with 2048 entries.** General in the index shape s with the two
numbers. -/
theorem column_some (s : OnBytes.Params.IndexShape) (ha : (shapeOfIndex s).a = 32)
    (hv : (shapeOfIndex s).v = 11) (entry : ℕ → ℕ → UInt64) (ρ : TableRand) (y : ℕ)
    (hy : y < 2 ^ 32) : ∃ c, encAt (shapeOfIndex s) entry ρ y = some c ∧ c.length = 2048 := by
  have hy' : y < 2 ^ (shapeOfIndex s).a := by
    rw [ha]
    exact hy
  obtain ⟨c, hc⟩ : ∃ c, encAt (shapeOfIndex s) entry ρ y = some c := ⟨_, if_pos hy'⟩
  have hl := encAt_length _ _ _ _ c hc
  rw [hv] at hl
  exact ⟨c, hc, hl.trans (by norm_num)⟩

/-- **planServes' premise on the stored columns**, at a description with the written rounds and a prover that has, at the
item 0 and below 2^32, a column of 2048 entries. -/
theorem widths_of {Xi W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Xi} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    (hd : F.roundsDeclaredByBlocks = declKeyFull) (w₀ : W₀) (rc : Rc)
    (hc : ∀ y, y < 2 ^ 32 → ∃ c, H.stored w₀ rc 0 y = some c ∧ c.length = 2048) :
    ∀ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ t ∈ d.stored, ∀ y, y < 2 ^ t.sh.a →
      ∃ u, H.storedWords w₀ rc t.item y = some u ∧ u.length = t.sh.W := by
  rw [hd]
  intro d hdm t ht y hy
  obtain ⟨e1, e2, e3⟩ := stored_decl d hdm t ht
  rw [e2] at hy
  obtain ⟨c, h1, h2⟩ := hc y hy
  refine ⟨c.map OnBytes.Slice.ofF, ?_, ?_⟩
  · unfold Prover.storedWords
    rw [e1, h1]
    rfl
  · rw [List.length_map, h2, e3]

end AtPublicFiles.LotPlanGround

#print axioms AtPublicFiles.LotPlanGround.pins
#print axioms AtPublicFiles.LotPlanGround.plan
#print axioms AtPublicFiles.LotPlanGround.wanted
#print axioms AtPublicFiles.LotPlanGround.rows
#print axioms AtPublicFiles.LotPlanGround.decl
#print axioms AtPublicFiles.LotPlanGround.sized
#print axioms AtPublicFiles.LotPlanGround.lin
#print axioms AtPublicFiles.LotPlanGround.mem_unrunD
#print axioms AtPublicFiles.LotPlanGround.stored_recs
#print axioms AtPublicFiles.LotPlanGround.stored_recs_no
#print axioms AtPublicFiles.LotPlanGround.a_written
#print axioms AtPublicFiles.LotPlanGround.v_written
#print axioms AtPublicFiles.LotPlanGround.rows_written
#print axioms AtPublicFiles.LotPlanGround.split_written
#print axioms AtPublicFiles.LotPlanGround.w_written
#print axioms AtPublicFiles.LotPlanGround.stored_decl
#print axioms AtPublicFiles.LotPlanGround.column_some
#print axioms AtPublicFiles.LotPlanGround.widths_of
