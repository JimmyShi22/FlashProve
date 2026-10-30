-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Dec/FitAtWritten.lean: THE FRAME's TEST ON NUMBERS SAYS YES AT THE WRITTEN LISTS OF THE
FULL-SIZE EXAMPLE, AS THEOREMS, by evaluations in Lean's kernel: at the data of `dryKeyFull` and
`dryProofFull` (Johnson/G/DryKeyLit.lean, DryProofLit.lean), the entry's written rounds `dsFull` and stored
openings `frD.xs`, with K := 24086 blocks, request trees of depths 6 and 0, and v := 2^63. And the compiled
verifier's own count of typed queries there, as a number: 715984.

What was there. The numbers of blocks: `blocksT_wholeFull` (140), `blocksT_wholePFull` (24086)
(Johnson/G/DryKeyBlocks.lean, DryProofBlocks.lean). Work and depths: `workFit_keyFull` … `depthFit_proofFull`
(Johnson/G/DryKeyTests.lean, DryProofTestsFull.lean). The entry's: `kMax_frRds_le`, `cntEntry_dsFull`. NEW HERE: the
count: the three lists' lengths, what they open at most, and the greatest depth, at both files.

Main names.
  `foldl_max_le`, `depthAtMost`, `maxDepthT_le`, `nOpenT_eq`, `cntWhole_of`: general: the count of a file's arm from
    three lengths, the number of openings and a test on depths.
  `writtenKFull`, `writtenPFull`: the two files' data at the written lists, in the form of the tests already in the library.
  `cntWhole_keyFull dep` = 58753 + dep · `cntWhole_proofFull dep` = 643684 + dep.
  `cntFrameFull_written`: the count at depths (depthReq, depthReqT) is 715978 + depthReq + depthReqT: 715984 at (6, 0).
  `frameFitFull_written`: the frame's Bool `frameFitFull` says yes. `frameFitFullD_written`: the test WITH CODE of the frame
    with the entry's three letters says yes.
  `controls_written`: with one block less, and with v one below the count, the test says no.

Limits. THE THEOREMS SPEAK OF THE WRITTEN LISTS, which were made at one made-up request. THAT THESE ARE THE PLAN's ROUNDS AT THE
RELEASE's PUBLIC FILES IS NO THEOREM AT THE FULL SIZE (the heads of Johnson/G/DryProofBlocks.lean and
Johnson/G/RoundsOfPlanGuard.lean). An evaluation by Lean's interpreter at the plan's own data at the stored full-size files gave the same
numbers (a run inside this project; no theorem). The depths 6 and 0 and K are numerals here: that a run lays them is seen at the run. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.Dec.FailsClosed
import Johnson.G.DryKeyTests
import Johnson.G.DryProofTestsFull
import Johnson.G.DryKeyBlocks
import Johnson.G.DryProofBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G
open OnBytes OnBytes.Maker OnBytes.Flat OnBytes.Slice _root_.Run _root_.Run.PQ
open OnBytes.K.Arm (cntWhole)
open VerifiableInference.OnPublicFiles

/-! ## General -/

/-- A fold by the greater is at most b, if its start and every member's value are. -/
theorem foldl_max_le {α : Type} (g : α → ℕ) (b : ℕ) : ∀ (l : List α) (n : ℕ), n ≤ b →
    (∀ d ∈ l, g d ≤ b) → l.foldl (fun a d => max a (g d)) n ≤ b
  | [], _, hn, _ => hn
  | x :: l, n, hn, h =>
    foldl_max_le g b l (max n (g x)) (max_le hn (h x List.mem_cons_self))
      fun d hd => h d (List.mem_cons_of_mem _ hd)

/-- No tree that a round of the list sends is deeper than b. -/
def depthAtMost (b : ℕ) (ds : List RDT) : Bool :=
  ds.all fun d => d.trees.all fun s => decide (s.a ≤ b)

theorem maxDepthT_le {b : ℕ} {ds : List RDT} (h : depthAtMost b ds = true) : maxDepthT ds ≤ b := by
  unfold depthAtMost at h
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact foldl_max_le (fun d : RDT => d.trees.foldl (fun n s => max n s.a) 0) b ds 0 (Nat.zero_le _)
    fun d hd => foldl_max_le (fun s : Fmt.Shape => s.a) b d.trees 0 (Nat.zero_le _) (h d hd)

/-- What a list of rounds opens at most, over the eager sum. -/
theorem nOpenT_eq (ds : List RDT) : nOpenT ds =
    sumE 0 (ds.map fun d => (d.stored.map (·.count)).sum + d.entry.poss * d.opens.length) :=
  sum_eq_sumE _

/-- The same in two sums: the stored tables' parts; the draws for the trees that are opened. (At the proof
file's first chain the kernel runs out of stack on the one sum, and gets through each of the two.) -/
theorem nOpenT_split (ds : List RDT) : nOpenT ds =
    sumE 0 (ds.map fun d => (d.stored.map (·.count)).sum) +
      sumE 0 (ds.map fun d => d.entry.poss * d.opens.length) := by
  unfold nOpenT
  rw [List.sum_map_add, sum_eq_sumE, sum_eq_sumE]

/-- What a file opens at most, from six sums. (At a letter D: so that no step of the proof meets a long list.) -/
theorem nOpenW_of (D : WholeD) (s₁ o₁ s₂ o₂ s₃ o₃ : ℕ)
    (hs₁ : sumE 0 (D.ds₁.map fun d => (d.stored.map (·.count)).sum) = s₁)
    (ho₁ : sumE 0 (D.ds₁.map fun d => d.entry.poss * d.opens.length) = o₁)
    (hs₂ : sumE 0 (D.ds₂.map fun d => (d.stored.map (·.count)).sum) = s₂)
    (ho₂ : sumE 0 (D.ds₂.map fun d => d.entry.poss * d.opens.length) = o₂)
    (hs₃ : sumE 0 (D.ds₃.map fun d => (d.stored.map (·.count)).sum) = s₃)
    (ho₃ : sumE 0 (D.ds₃.map fun d => d.entry.poss * d.opens.length) = o₃) :
    nOpenW D = s₁ + o₁ + (s₂ + o₂ + (s₃ + o₃)) := by
  unfold nOpenW
  rw [nOpenT_split, nOpenT_split, nOpenT_split, hs₁, ho₁, hs₂, ho₂, hs₃, ho₃]

/-- **The count of a file's arm**, from the three lists' lengths, the number of openings, and a test: no
tree is deeper than the stored table's depth a. -/
theorem cntWhole_of (D : WholeD) (a dep l₁ l₂ l₃ n : ℕ) (h₁ : lenE 0 D.ds₁ = l₁)
    (h₂ : lenE 0 D.ds₂ = l₂) (h₃ : lenE 0 D.ds₃ = l₃) (hn : nOpenW D = n)
    (d₁ : depthAtMost a D.ds₁ = true) (d₂ : depthAtMost a D.ds₂ = true)
    (d₃ : depthAtMost a D.ds₃ = true) :
    cntWhole (D.at a) dep =
      2 + ((1 + (l₁ + (1 + (l₂ + (1 + l₃)))) + 1) + (n * (a + 1) + (dep + 1))) := by
  have hm : maxDepthW (D.at a) = a :=
    max_eq_left (max_le (maxDepthT_le d₁) (max_le (maxDepthT_le d₂) (maxDepthT_le d₃)))
  have hn' : nOpenW (D.at a) = n := hn
  unfold cntWhole
  rw [hm, hn']
  show 2 + ((1 + (D.ds₁.length + (1 + (D.ds₂.length + (1 + D.ds₃.length)))) + 1) + _) = _
  rw [length_of_lenE h₁, length_of_lenE h₂, length_of_lenE h₃]

/-! ## The key file's written lists -/

/-- The key file's data at the written lists, over the twin that the kernel can evaluate. -/
abbrev dKeyFull : WholeD := WholeD.of 32 (wholeTwin dryKeyFull.1 dryKeyFull.2.1 dryKeyFull.2.2)

set_option maxRecDepth 1000000 in
theorem len_keyFull : lenE 0 dKeyFull.ds₁ = 18850 ∧ lenE 0 dKeyFull.ds₂ = 68 ∧
    lenE 0 dKeyFull.ds₃ = 30 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem nOpen_keyFull : nOpenW dKeyFull = 1206 := by
  unfold nOpenW
  rw [nOpenT_eq, nOpenT_eq, nOpenT_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem depth_keyFull : depthAtMost 32 dKeyFull.ds₁ = true ∧ depthAtMost 32 dKeyFull.ds₂ = true ∧
    depthAtMost 32 dKeyFull.ds₃ = true := by decide +kernel

/-! ## The proof file's written lists -/

/-- The proof file's data at the written lists, over the twin with written openings. -/
abbrev dProofFull : WholeD := WholeD.of 32 wProofFull

set_option maxRecDepth 1000000 in
theorem len_proofFull : lenE 0 dProofFull.ds₁ = 48292 ∧ lenE 0 dProofFull.ds₂ = 68 ∧
    lenE 0 dProofFull.ds₃ = 30 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem stored1_proofFull :
    sumE 0 (dProofFull.ds₁.map fun d => (d.stored.map (·.count)).sum) = 0 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem opens1_proofFull :
    sumE 0 (dProofFull.ds₁.map fun d => d.entry.poss * d.opens.length) = 16899 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem stored2_proofFull :
    sumE 0 (dProofFull.ds₂.map fun d => (d.stored.map (·.count)).sum) = 64 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem opens2_proofFull :
    sumE 0 (dProofFull.ds₂.map fun d => d.entry.poss * d.opens.length) = 711 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem stored3_proofFull :
    sumE 0 (dProofFull.ds₃.map fun d => (d.stored.map (·.count)).sum) = 0 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem opens3_proofFull :
    sumE 0 (dProofFull.ds₃.map fun d => d.entry.poss * d.opens.length) = 365 := by decide +kernel

theorem nOpen_proofFull : nOpenW dProofFull = 18039 :=
  nOpenW_of dProofFull 0 16899 64 711 0 365 stored1_proofFull opens1_proofFull stored2_proofFull
    opens2_proofFull stored3_proofFull opens3_proofFull

set_option maxRecDepth 1000000 in
theorem depth_proofFull : depthAtMost 32 dProofFull.ds₁ = true ∧
    depthAtMost 32 dProofFull.ds₂ = true ∧ depthAtMost 32 dProofFull.ds₃ = true := by
  decide +kernel

/-! ## The counts -/

/-- The two files' data at the written lists, in the form of the tests already in the library. -/
abbrev writtenKFull : WholeD := WholeD.of 32 (wholeAt (some dryKeyFull))
abbrev writtenPFull : WholeD := WholeD.of 32 (wholeAt (some dryProofFull))

theorem writtenKFull_eq : writtenKFull = dKeyFull := by
  show WholeD.of 32 (Three.Whole.of dryKeyFull.1 dryKeyFull.2.1 dryKeyFull.2.2) = _
  rw [whole_eq]

theorem writtenPFull_eq : writtenPFull = dProofFull := by
  show WholeD.of 32 (Three.Whole.of dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2) = _
  rw [whole_proofFull]

/-- The depth of the tables' code at the full size. -/
theorem fr_a : frS.P.T.a = 32 := by decide +kernel

theorem cntWhole_keyFull (dep : ℕ) : cntWhole (writtenKFull.at frS.P.T.a) dep = 58753 + dep := by
  rw [writtenKFull_eq, fr_a, cntWhole_of dKeyFull 32 dep _ _ _ _ len_keyFull.1 len_keyFull.2.1
    len_keyFull.2.2 nOpen_keyFull depth_keyFull.1 depth_keyFull.2.1 depth_keyFull.2.2]
  omega

theorem cntWhole_proofFull (dep : ℕ) :
    cntWhole (writtenPFull.at frS.P.T.a) dep = 643684 + dep := by
  rw [writtenPFull_eq, fr_a, cntWhole_of dProofFull 32 dep _ _ _ _ len_proofFull.1
    len_proofFull.2.1 len_proofFull.2.2 nOpen_proofFull depth_proofFull.1 depth_proofFull.2.1
    depth_proofFull.2.2]
  omega

/-- **The compiled verifier's own count of typed queries at the written lists.** -/
theorem cntFrameFull_written (depthReq depthReqT : ℕ) :
    cntFrameFull writtenKFull writtenPFull depthReq depthReqT =
      715978 + depthReq + depthReqT := by
  unfold cntFrameFull
  rw [cntWhole_keyFull, cntWhole_proofFull]
  omega

/-! ## The tests -/

theorem blocks_keyFull :
    blocksT .two (writtenKFull.ds₁ ++ (writtenKFull.ds₂ ++ writtenKFull.ds₃)) = 140 :=
  blocksT_wholeFull

theorem blocks_proofFull :
    blocksT .two (writtenPFull.ds₁ ++ (writtenPFull.ds₂ ++ writtenPFull.ds₃)) = 24086 :=
  blocksT_wholePFull

/-- **The frame's Bool `frameFitFull` says yes at the written lists.** -/
theorem frameFitFull_written :
    frameFitFull 24086 (2 ^ 63) 6 0 writtenKFull writtenPFull = true :=
  (frameFitFull_iff _ _ _ _ _ _).2
    ⟨max_le (blocks_keyFull.le.trans (by norm_num))
        (max_le (kMax_frRds_le.trans (by norm_num)) blocks_proofFull.le),
      workFit_keyFull, depthFit_keyFull, workFit_proofFull, depthFit_proofFull,
      (cntFrameFull_written 6 0).le.trans (by norm_num), by norm_num⟩

set_option maxRecDepth 1000000 in
/-- The entry's four tests at the written rounds. -/
theorem entryFitB_dsFull : entryFitB 24086 dsFull = true := by decide +kernel

/-- **The test with code, of the frame with the entry's three letters, says yes there.** -/
theorem frameFitFullD_written :
    sizeNumbersFitAtFullSize 24086 (2 ^ 63) 6 0 writtenKFull writtenPFull dsFull frD.xs = true := by
  have hk : kThree .two writtenKFull [] writtenPFull ≤ 24086 :=
    max_le (blocks_keyFull.le.trans (by norm_num)) (max_le (Nat.zero_le _) blocks_proofFull.le)
  have hc : cntFrameFullD writtenKFull writtenPFull dsFull frD.xs 6 0 ≤ 2 ^ 63 := by
    rw [cntFrameFullD_landed, cntFrameFull_written]
    norm_num
  unfold sizeNumbersFitAtFullSize
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨hk, entryFitB_dsFull⟩, workFit_keyFull⟩, depthFit_keyFull⟩, workFit_proofFull⟩,
    depthFit_proofFull⟩, hc⟩, by norm_num⟩

/-- **Two controls**: with one block less, and with v one below the count, the test says no. -/
theorem controls_written :
    sizeNumbersFitAtFullSize 24085 (2 ^ 63) 6 0 writtenKFull writtenPFull dsFull frD.xs = false ∧
      sizeNumbersFitAtFullSize 24086 715983 6 0 writtenKFull writtenPFull dsFull frD.xs = false := by
  constructor
  · cases h : sizeNumbersFitAtFullSize 24085 (2 ^ 63) 6 0 writtenKFull writtenPFull dsFull frD.xs with
    | false => rfl
    | true =>
      have h1 := (frameFitFullD_parts h).hk
      have h2 : blocksT .two (writtenPFull.ds₁ ++ (writtenPFull.ds₂ ++ writtenPFull.ds₃)) ≤ 24085 :=
        ((le_max_right _ _).trans (le_max_right _ _)).trans h1
      rw [blocks_proofFull] at h2
      omega
  · cases h : sizeNumbersFitAtFullSize 24086 715983 6 0 writtenKFull writtenPFull dsFull frD.xs with
    | false => rfl
    | true =>
      have h1 := (frameFitFullD_parts h).hcnt
      rw [cntFrameFullD_landed, cntFrameFull_written] at h1
      omega

end Johnson.G

#print axioms Johnson.G.cntWhole_of
#print axioms Johnson.G.cntWhole_keyFull
#print axioms Johnson.G.cntWhole_proofFull
#print axioms Johnson.G.cntFrameFull_written
#print axioms Johnson.G.frameFitFull_written
#print axioms Johnson.G.frameFitFullD_written
#print axioms Johnson.G.controls_written
