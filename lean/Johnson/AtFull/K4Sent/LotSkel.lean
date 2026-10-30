-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/K4Sent/LotSkel.lean: K4's lot's twelve skeletons are the written ones, at hypotheses
by field. NO OPENING IS TAKEN.

What it says.
  `es_tie`         the written first chain's entries under their two names (`esWritten` here,
                   `P5T.esFull.1`) are one list. By unfolding.
  `k4SkelFull`     the twelve written skeletons, by a rule: at group g: name "G‹g›:3" · chain 1,
                   link 2 g, piece 3, K4 · 170 rounds at g = 0, 168 else, twice · no told round ·
                   `before` as in row 28 g + 4 of `cutFirstFull` · the test on the plan true ·
                   "front", "back" · "free-slot".
  `skel_written`   a closed fact, by Lean's kernel: the twin `k4FromSk` at the written values, each
                   view made a skeleton, gives `k4SkelFull`. `skel_noStep`,
                   `skel_oneRootMore_no`: negative tests: a step struck from the table; one root
                   more at a round that lies in no window (the numbering in `before` shifts).
  `len_of_numbers` K4's table has 170 | 168 rounds wherever six numbers of the public parameters sum
                   to 137. `len_of_nums`: so it has wherever the fifteen numbers that its rounds
                   read (numsOf, Johnson/AtFull/Rounds/K4Nums.lean) are the written ones (numsW):
                   hlen below, from that equation. General laws.
  `k4_lot_skel`    for public files in the goals' scope, where the public part Z and the blank
                   ground G₀ are returned (the FRONT's two steps), if hc the table of steps is the
                   written one, he the first chain's declared rounds have the written entries, hlen
                   K4's table has 170 | 168 rounds at each group:
                   ((ProofFile.k4Lot Z).blocks G₀).map ProofFile.Sk.skel = k4SkelFull.

Limits. A joining and closed facts at written values of one set of public files, with synthetic
weights: it pays none of hc · he · hlen. At the second hash function `OnBytes.secondHashFunction` alone.
Nothing on soundness.
-/
import Johnson.AtFull.K4Sent.Rows
import Johnson.Road.K4.K4LotSkel
import Johnson.Road.K4.K4CutRows
import Johnson.AtFull.Rounds.K4Nums
import Johnson.Goal.Meaning.PlanNames
import Johnson.P5T.PlanSeatsFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.K4Sent

open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par rounds covers)
open OnBytes.Road.K4
open VerifiableInference.PlanWritten (cutFirstFull)
open Johnson.AtFull.Cut (cutWritten)
open ProofFile.Sk (Skel skel)

/-- The written first chain's entries under their two names are one list. -/
theorem es_tie : esWritten = P5T.esFull.1 := rfl

/-- The twelve written skeletons. -/
def k4SkelFull : List Skel :=
  (List.range 12).map fun g =>
    { name := "G" ++ toString g ++ ":3", place := ⟨1, some (2 * g), 3, .K4⟩, nRounds := roundsW g,
      nOracles := roundsW g, told := [],
      before := ((cutFirstFull[28 * g + 4]?).map (·.2.2.2.2.2)).getD [], planOk := true,
      claims := ["front", "back"], after := ["free-slot"] }

/-- A view made a skeleton, at the written number of rounds and a test on the plan that passes. -/
def k4SkelW (v : Bool × String × ℕ × ℕ × List (ℕ × ℕ) × ℕ) : Skel :=
  skOfView (roundsW v.2.2.2.2.2) true v

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **At the written values the twin's views, made skeletons, are the written twelve.** -/
theorem skel_written :
    (k4FromSk cutWritten esWritten 12 skW 0 none).map k4SkelW = k4SkelFull := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A negative test: without the step «G5.0.call» they are not. -/
theorem skel_noStep :
    decide ((k4FromSk (cutWritten.filter fun c => c.look != "G5.0.call") esWritten 12 skW 0
      none).map k4SkelW = k4SkelFull) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A second negative test: one root more at round number 2, which lies in no window: twelve views
still, and made skeletons they are not the written twelve. -/
theorem skel_oneRootMore_no :
    (fun V : List (Bool × String × ℕ × ℕ × List (ℕ × ℕ) × ℕ) =>
      decide (V.length = 12) && !decide (V.map k4SkelW = k4SkelFull))
      (k4FromSk cutWritten (bumpAt 2 esWritten) 12 skW 0 none) = true := by
  decide +kernel

/-- **K4's number of rounds from six numbers of the public parameters.** -/
theorem len_of_numbers (P : Layer.Pub) (hp : Layer.HPlan2) (g : ℕ)
    (h : P.rd.muV + 2 * P.y.h.lt + hp.lamS + P.rd.muH + P.rd.muH2 + P.wsLay.lk = 137) :
    (rounds P hp g).length = roundsW g := by
  rw [rounds_len]
  unfold roundsW
  by_cases hg : (g == 0) = true <;> simp [hg] <;> omega

/-- **K4's number of rounds where the fifteen numbers are the written ones.** -/
theorem len_of_nums {P : Layer.Pub} {hp : Layer.HPlan2} {g : ℕ}
    (h : Johnson.AtFull.Rounds.numsOf P hp = Johnson.AtFull.Rounds.numsW g) :
    (rounds P hp g).length = roundsW g := by
  unfold Johnson.AtFull.Rounds.numsOf Johnson.AtFull.Rounds.numsW at h
  simp only [List.cons.injEq] at h
  obtain ⟨h1, -, -, -, -, -, h7, -, h9, -, -, h12, -, h14, h15, -⟩ := h
  exact len_of_numbers P hp g (by omega)

variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}

/-- **K4's LOT's TWELVE SKELETONS ARE THE WRITTEN ONES**, at hypotheses by field; no opening. -/
theorem k4_lot_skel (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀)
    (hc : Z.cuts = cutWritten) (he : Z.D.1.map (·.entry) = esWritten)
    (hlen : ∀ g < 12, ∀ hp, G₀.W.G[g]? = some hp →
      (rounds G₀.W.layers hp g).length = roundsW g) :
    ((ProofFile.k4Lot Z).blocks G₀).map skel = k4SkelFull := by
  have hpub := IM.ground_publicK hZ hG
  have hn : G₀.W.G.size = 12 :=
    (Meaning.plans_size hpub).trans (Meaning.scope_plans hS hR hpub).2.1
  have hs : k4SentB Z = true := k4SentB_written hc he
  have step : ∀ x ∈ ProofFile.k4From Z G₀ G₀.built.toList 0 none,
      skel (ProofFile.k4Block x) = k4SkelW (k4ViewOf x) := by
    intro x hx
    obtain ⟨eP, -, -, hgp⟩ := IM.k4_seated hZ hG hx
    have hg : x.2.g < 12 := by
      obtain ⟨h, -⟩ := Array.getElem?_eq_some_iff.1 hgp
      omega
    have hl : (rounds x.2.P x.2.hp x.2.g).length = roundsW x.2.g := by
      rw [eP]
      exact hlen x.2.g hg x.2.hp hgp
    have hok : (covers x.2.P && x.1) = true := by
      have h := k4Block_ok hS hR hZ hG hs hx
      rw [Bool.and_eq_true, k4Block_planOk] at h
      exact h.1
    rw [skel_k4Block, hl, hok]
    rfl
  have e : (ProofFile.k4From Z G₀ G₀.built.toList 0 none).map (skel ∘ ProofFile.k4Block) =
      (ProofFile.k4From Z G₀ G₀.built.toList 0 none).map (k4SkelW ∘ k4ViewOf) :=
    List.map_congr_left fun x hx => step x hx
  rw [k4Lot_blocks, List.map_map, e, ← List.map_map, k4From_view, hc, he, hn,
    built_sk hS hR hZ hG]
  exact skel_written

#print axioms Johnson.AtFull.K4Sent.es_tie
#print axioms Johnson.AtFull.K4Sent.skel_written
#print axioms Johnson.AtFull.K4Sent.skel_noStep
#print axioms Johnson.AtFull.K4Sent.skel_oneRootMore_no
#print axioms Johnson.AtFull.K4Sent.len_of_numbers
#print axioms Johnson.AtFull.K4Sent.len_of_nums
#print axioms Johnson.AtFull.K4Sent.k4_lot_skel

end Johnson.AtFull.K4Sent
