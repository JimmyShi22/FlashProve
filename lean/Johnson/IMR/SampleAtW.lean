-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/SampleAtW.lean: THE TEST sampleL AT THE TWO MESSAGES OF THE OWN GROUP (the index masks'
message and W), AT THE LETTERS AT WHICH THE LAST CHAIN's TABLE SPENDS IT, WHERE THE TEST madeRow
ACCEPTS: the premise on the top coordinate's words and the five tests on shape and codes are paid;
five premises on the message and its seed are left. Statements and proofs.

WHY. rcLastB's fourth conjunct sampleTwoB (Johnson/ToldDescR/RcLastCode.lean) asks sampleL at cs := (ToldDesc.p14At Z).codes, at the seat ⟨o, sh, 0, 0, default, 0⟩, at sh := the index masks' shape and at sh := W's shape (p14At Z).S.w. IM.sampleL_of_seed_all (Johnson/IMR/SampleOfSeedBoth.lean) gives sampleL's accept from eleven premises. Six of them read shape and codes alone (htop only through its guard). Shape and codes are functions of the sized proof,
which is the written one where madeRow accepts (IM.pins, Johnson/IMR/SendsPinned.lean).
WHAT IS SAID.
  shW · shI               the two shapes at the written sized proof
  wCube_written           W's cube there: the mask's table has 8 bits, the main table 18, the cube 19 coordinates (by the kernel)
  wShape_written · iShape_written   the rows of the two shapes: W has both tables; the index masks' message has the mask's alone
  wTests · iTests         the tests on shape and codes alone, at the two shapes (by the kernel)
  wCube_pinned            so where madeRow accepts: maskBits < mainBits at W: sampleL_of_seed_all's htop is idle there
  **sampleL_at_W** · **sampleL_at_index**   sampleL's accept at the two shapes, from five premises
  example_W_met           the five premises are met together at W's written shape and codes, at a point longer than the cube
  wCube_can_fail          the closed fact can fail: at the index masks' shape the like is false

THE PREMISES LEFT, at both: hs: the message is sampled · hform: row0 is Send.form's at the seed ·
hrows: the message's one sample row is row0 with some target · hlen: the seed's point has the cube's
coordinates · hβ: the seed's factor reads as a unit of the field. hy: madeRow Z = true, as in
Johnson/IMR/SendsPinned.lean.

What is not claimed. hy and the five at any state. That (LLT25.vAt Z N₁).wShape is (p14At Z).S.w and its indexShape the shape named here: read in Johnson/LLT25R/LastAt.lean, which is not imported. No soundness.

-/
import Johnson.IMR.SendsPinned
import Johnson.IMR.SampleOfSeedBoth
import Johnson.ToldDescR.LastBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IM

open OnBytes OnBytes.Params OnBytes.Slice Johnson.Pack H2K.Pin
open H2K.First (Seat1)
open VerifiableInference.PlanWritten (madeRow)
open ToldDesc (p14At)

/-- W's shape at the written sized proof. -/
def shW : OracleShape := zW.batch.shape.w

/-- The index masks' message's shape at the written sized proof. -/
def shI : OracleShape := (zW.request.atStart.head?.map (·.shape)).getD default

theorem wCube_written : (Send.cube zW.codes shW).maskBits = 8 ∧
    (Send.cube zW.codes shW).mainBits = 18 ∧ (Send.cube zW.codes shW).bits = 19 := by
  decide +kernel

theorem wShape_written : shW.mainRows = 1 ∧ shW.maskRows = 1 ∧ shW.answers = 1 := by decide +kernel

theorem iShape_written : shI.mainRows = 0 ∧ shI.maskRows = 1 ∧ shI.answers = 1 := by decide +kernel

/-- The tests on shape and codes alone, at W. -/
theorem wTests : 0 < shW.mainRows ∧ 0 < shW.maskRows ∧
    2 ^ ceilLog2 (mainB zW.codes shW).ell = (mainB zW.codes shW).ell ∧
    2 ^ ceilLog2 (maskB zW.codes shW).ell = (maskB zW.codes shW).ell := by decide +kernel

/-- And at the index masks' message. -/
theorem iTests : 0 < shI.maskRows ∧
    2 ^ ceilLog2 (maskB zW.codes shI).ell = (maskB zW.codes shI).ell := by decide +kernel

/-- The closed fact can fail: at the index masks' shape the mask's table is not the smaller. -/
theorem wCube_can_fail :
    ¬ ((Send.cube zW.codes shI).maskBits < (Send.cube zW.codes shI).mainBits) := by decide +kernel

theorem p14_codes {Z : ProofFile.Pub} (hy : madeRow Z = true) : (p14At Z).codes = zW.codes := by
  show Z.p.chains.made.sized.proof.codes = _
  rw [(pins hy).1]

theorem p14_w {Z : ProofFile.Pub} (hy : madeRow Z = true) : (p14At Z).S.w = shW := by
  show Z.p.chains.made.sized.proof.batch.shape.w = _
  rw [(pins hy).1]
  rfl

theorem index_shape {Z : ProofFile.Pub} (hy : madeRow Z = true) :
    (Z.p.chains.made.sized.proof.request.atStart.head?.map (·.shape)).getD default = shI := by
  rw [(pins hy).1]
  rfl

/-- **Where madeRow accepts, W's mask table has fewer bits than its main table.** -/
theorem wCube_pinned {Z : ProofFile.Pub} (hy : madeRow Z = true) :
    (Send.cube (p14At Z).codes (p14At Z).S.w).maskBits <
      (Send.cube (p14At Z).codes (p14At Z).S.w).mainBits := by
  rw [p14_codes hy, p14_w hy, wCube_written.1, wCube_written.2.1]
  decide

/-- sampleL's accept at W's written shape and codes. -/
theorem sampleL_written_W (o : Nat) (x : OnBytes.Oracle) (seed : SampleSeed) (row0 : Row) (tt : E)
    (β : GEˣ) (hs : x.sampled = true) (hform : Send.form zW.codes shW o seed 0 = some row0)
    (hrows : x.sampleRows.toList = [{ row0 with target := tt }])
    (hlen : bitsZ zW.codes shW ≤ seed.z.length) (hβ : (β : GE) = readE seed.beta) :
    ok (sampleL zW.codes ⟨o, shW, 0, 0, default, 0⟩ x) = true :=
  sampleL_of_seed_all zW.codes ⟨o, shW, 0, 0, default, 0⟩ x seed row0 tt β hs hform hrows hlen hβ
    wShape_written.2.2 (Or.inl wTests.1) (Or.inl (Or.inl wTests.2.1))
    (Or.inr wTests.2.2.1) (Or.inr wTests.2.2.2)
    (fun _ _ h => by
      have h' : (Send.cube zW.codes shW).maskBits = (Send.cube zW.codes shW).mainBits := h
      rw [wCube_written.1, wCube_written.2.1] at h'
      cases h')

/-- sampleL's accept at the index masks' written shape and codes. -/
theorem sampleL_written_index (o : Nat) (x : OnBytes.Oracle) (seed : SampleSeed) (row0 : Row)
    (tt : E) (β : GEˣ) (hs : x.sampled = true)
    (hform : Send.form zW.codes shI o seed 0 = some row0)
    (hrows : x.sampleRows.toList = [{ row0 with target := tt }])
    (hlen : bitsZ zW.codes shI ≤ seed.z.length) (hβ : (β : GE) = readE seed.beta) :
    ok (sampleL zW.codes ⟨o, shI, 0, 0, default, 0⟩ x) = true :=
  sampleL_of_seed_all zW.codes ⟨o, shI, 0, 0, default, 0⟩ x seed row0 tt β hs hform hrows hlen hβ
    iShape_written.2.2 (Or.inr iTests.1) (Or.inl (Or.inl iTests.1))
    (Or.inl iShape_written.1) (Or.inr iTests.2)
    (fun h _ _ => by
      have h' : 0 < shI.mainRows := h
      rw [iShape_written.1] at h'
      cases h')

/-- A seed whose point is LONGER than W's cube (21 coordinates against 19). -/
def exSeedW : SampleSeed := ⟨List.replicate 21 (E.mk3 7 0 0), E.mk3 3 0 0⟩

/-- A message of W's written shape whose one sample row is Send.form's at that seed. -/
def exXW : OnBytes.Oracle :=
  { shape := shW, sampled := true
    sampleRows := ((Send.form zW.codes shW 0 exSeedW 0).map fun r => #[r]).getD #[] }

/-- **The five premises can be met together at W's written shape and codes**, at a point longer than
the cube. -/
theorem example_W_met : ok (sampleL zW.codes ⟨0, shW, 0, 0, default, 0⟩ exXW) = true := by
  have hs : (Send.form zW.codes shW 0 exSeedW 0).isSome = true := by decide +kernel
  obtain ⟨row0, hform⟩ := Option.isSome_iff_exists.1 hs
  have h3 : readE (E.mk3 3 0 0) ≠ 0 := fun q => by
    have := (isZeroE_iff (E.mk3 3 0 0) (by decide +kernel)).2 q
    revert this
    decide +kernel
  refine sampleL_written_W 0 exXW exSeedW row0 row0.target (Units.mk0 _ h3) rfl hform ?_
    (by decide +kernel) rfl
  unfold exXW
  rw [hform]
  rfl

/-- **sampleL ACCEPTS AT W, AT THE LAST TABLE's OWN LETTERS, FROM FIVE PREMISES.** -/
theorem sampleL_at_W {Z : ProofFile.Pub} (hy : madeRow Z = true) (o : Nat) (x : OnBytes.Oracle)
    (seed : SampleSeed) (row0 : Row) (tt : E) (β : GEˣ) (hs : x.sampled = true)
    (hform : Send.form (p14At Z).codes (p14At Z).S.w o seed 0 = some row0)
    (hrows : x.sampleRows.toList = [{ row0 with target := tt }])
    (hlen : bitsZ (p14At Z).codes (p14At Z).S.w ≤ seed.z.length)
    (hβ : (β : GE) = readE seed.beta) :
    ok (sampleL (p14At Z).codes ⟨o, (p14At Z).S.w, 0, 0, default, 0⟩ x) = true := by
  rw [p14_codes hy, p14_w hy] at hform hlen ⊢
  exact sampleL_written_W o x seed row0 tt β hs hform hrows hlen hβ

/-- **AND AT THE INDEX MASKS' MESSAGE.** -/
theorem sampleL_at_index {Z : ProofFile.Pub} (hy : madeRow Z = true) (o : Nat) (x : OnBytes.Oracle)
    (seed : SampleSeed) (row0 : Row) (tt : E) (β : GEˣ) (hs : x.sampled = true)
    (hform : Send.form (p14At Z).codes
      ((Z.p.chains.made.sized.proof.request.atStart.head?.map (·.shape)).getD default) o seed 0 =
        some row0)
    (hrows : x.sampleRows.toList = [{ row0 with target := tt }])
    (hlen : bitsZ (p14At Z).codes
      ((Z.p.chains.made.sized.proof.request.atStart.head?.map (·.shape)).getD default) ≤
        seed.z.length)
    (hβ : (β : GE) = readE seed.beta) :
    ok (sampleL (p14At Z).codes
      ⟨o, (Z.p.chains.made.sized.proof.request.atStart.head?.map (·.shape)).getD default, 0, 0,
        default, 0⟩ x) = true := by
  rw [p14_codes hy, index_shape hy] at hform hlen ⊢
  exact sampleL_written_index o x seed row0 tt β hs hform hrows hlen hβ

end IM

#print axioms IM.wCube_written
#print axioms IM.wShape_written
#print axioms IM.iShape_written
#print axioms IM.wTests
#print axioms IM.iTests
#print axioms IM.wCube_can_fail
#print axioms IM.wCube_pinned
#print axioms IM.sampleL_written_W
#print axioms IM.sampleL_written_index
#print axioms IM.example_W_met
#print axioms IM.sampleL_at_W
#print axioms IM.sampleL_at_index
