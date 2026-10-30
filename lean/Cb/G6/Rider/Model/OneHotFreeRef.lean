-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/G6/Rider/Model/OneHotFreeRef.lean: a witness at the reference size: in the field relation of a
feed-forward segment all clauses but identity j10 at one place hold, and j10 fails there.

Statements and proofs. No protocol occurs here. `hot_free` (Cb/G6/Rider/Model/OneHotFree.lean)
starts from a trace in the relation that meets three premises. Here they are met by the library's
honest trace at the all-zero index (`ScalesSanity.iZero`, Inst/Model/ScalesSanity.lean): for all
valid settings and every prompt the program runs there (`zero_true`), so the honest trace of each
group's feed-forward segment is in the segment's field relation modulo every prime
(`All.ffK_honest`, Inst/Model/All/HonestK.lean) and reads out the program's values (`FFSeg.honestK`,
Inst/Model/FF/Scales.lean).

Main names:
  `zero_layer`: the weights of a layer, read from the matrix of the all-zero index, are zero.
  `zero_lr`, `zero_es`: at zero weights every logit of the router is 0 and the chosen expert is 0.
  `hon0 pp prompt g`: the honest cells of the feed-forward segment of group g at the all-zero index.
  `zero_off`: they meet the three premises of `hot_free`, in every group g < 12, at every instance
    l' < 2 and position i < 1,024, over every commutative ring.
  `hot_witness`: modulo every prime p there is a trace on the valid names of the feed-forward
    segment of group g with cells of absolute value at most 128, every key in its table, every
    identity but j10 at (l', i) equal to 0, and j10 at (l', i) not 0. The relation is the one that
    the conditions of the 24 segments of the layers name (`Cm.TP.segFF`, Cm/TargetPRel.lean). The
    trace is `hon0` with the selector's cells of (l', i) set to 0.
  `hot_witness_gold`: the same modulo 2^64 - 2^32 + 1, with no premise on the prime.
  `hot_witness_ref`: the same at the reference settings: no premise is left but the ranges of g, l',
    i.

Limits: one witness for each valid setting, prompt, group, instance and position, all at the
all-zero index, which is made up. It refutes "the other clauses give j10" as a statement for all
indices; of another index it says nothing. It is the first of the two sentences that a use of the
rule for a second zero test should prove (`hollow_own`, Cb/G6/Rider/Both.lean):
the other clauses hold while the source fails. The second, on an accepted
transcript, is not spoken of: no reduction occurs here.

Terms: lean/GLOSSARY.md.

-/
import Inst.Model.All.HonestK
import Inst.Model.ScalesSanity
import Code.Field
import Cb.G6.Rider.Model.OneHotFree

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Rider
open Finset Inst.Model Inst.Model.FFSeg Inst.Model.All Inst.Model.ScalesSanity
open Inst.Model.Layout (kRef hRef)

/-- The weights of a layer, read from the matrix of the all-zero index, are zero. -/
theorem zero_layer {L : ℕ} (hL : L < 48) :
    Layout.layerOf ppref kRef (Layout.matrixRef iZero) L = zeroLayer :=
  (Layout.MatrixOf.layerOf_matrixOf ppref kRef iZero.property (by decide) (by decide)
    (show L < ppref.layers from hL)).trans layW_zero

/-- At zero weights every logit of the router is 0. -/
theorem zero_lr (P : Params) (hr : 1 ≤ P.kr) (x : ℕ → Vec) (i e : ℕ) :
    FF.lr P zeroLayer x i e = 0 := by
  simp [FF.lr, FF.ly, FF.l3, FF.lw, zeroLayer, dot_zero, rhu_zero hr, clamp]

theorem argTo_zero : ∀ n, argTo (fun _ => 0) n = 0
  | 0 => rfl
  | n + 1 => by
    show (if (0 : ℤ) < 0 then n + 1 else argTo (fun _ => 0) n) = 0
    rw [if_neg (lt_irrefl _), argTo_zero n]

/-- At zero weights the chosen expert is 0. -/
theorem zero_es (P : Params) (hr : 1 ≤ P.kr) (x : ℕ → Vec) (i : ℕ) : FF.es P zeroLayer x i = 0 := by
  unfold FF.es
  rw [show FF.lr P zeroLayer x i = fun _ => 0 from funext fun e => zero_lr P hr x i e]
  exact argTo_zero _

/-- The read-out of a function on all names, cut to the valid names and mapped into a ring, at valid
indices. -/
theorem val_rd {R : Type} [CommRing R] (D : Dim) (u : Cell → ℤ) (X : Arr) {n j q : ℕ}
    (hn : n < X.cnt D) (hj : j < X.width D) (hq : q < D.T) :
    val (rd D (fun c => u c.val) : Cell → R) X n j q = ((val u X n j q : ℤ) : R) := by
  unfold FFSeg.val
  push_cast
  refine congrArg (· + _) (sum_congr rfl fun k hk => ?_)
  unfold rd
  rw [dif_pos (show (⟨X, k, n, j, q⟩ : Cell).Valid D from ⟨mem_range.1 hk, hn, hj, hq⟩)]

section Ref
variable (pp : ScalesAndPolicy) (prompt : Fin ppref.T → Fin ppref.V) (g : ℕ)

/-- The honest cells of the feed-forward segment of group g at the all-zero index. -/
noncomputable def hon0 : Cell → ℤ :=
  FFSeg.hon (scl := SFK pp.kap pp.nf g) DF tbRef (wOf (Layout.matrixRef iZero) g) (4 * g)
    (xsK pp.kap (fun _ => tbRef) (Layout.matrixRef iZero) prompt g)
    (osK pp.kap (fun _ => tbRef) (Layout.matrixRef iZero) prompt g)

variable {pp} (hpp : Lawful pp) {g} {l' i : ℕ} (hg : g < 12) (hl : l' < 2) (hi : i < 1024)

include hpp in
/-- At all valid settings the program runs at the all-zero index, on every prompt. -/
theorem zero_runs :
    RunsK ppref pp.kap pp.nf (tbsOf fun _ => tbRef)
      (Layout.weightsOf ppref kRef (Layout.matrixRef iZero)) prompt := by
  have e : Layout.weightsOf ppref kRef (Layout.matrixRef iZero) = iZero.val :=
    congrArg Subtype.val (Layout.indexOf_matrixRef iZero)
  rw [e]
  exact (zero_true hpp prompt).1

include hpp hg in
/-- The honest cells read out the program's values. -/
theorem hon0_val (X : Arr) (n j q : ℕ) :
    val (hon0 pp prompt g) X n j q =
      hv (scl := SFK pp.kap pp.nf g) DF tbRef (wOf (Layout.matrixRef iZero) g) (4 * g)
        (xsK pp.kap (fun _ => tbRef) (Layout.matrixRef iZero) prompt g)
        (osK pp.kap (fun _ => tbRef) (Layout.matrixRef iZero) prompt g) X n j q :=
  (FFSeg.honestK (ffK (lawfulK_of hpp) hg)
    (settingK (lawfulK_of hpp) (Layout.wfw_matrixRef iZero) (tokOf_lt prompt) hg) _ _
    (runs_groupK (lawfulK_of hpp) (zero_runs prompt hpp) hg)).2.1 X n j q

include hpp hg hl hi in
/-- The honest cells at the all-zero index meet the three premises of `hot_free`, over every
commutative ring. -/
theorem zero_off {R : Type} [CommRing R] :
    OffOK DF l' i (rd DF (fun c => hon0 pp prompt g c.val) : Cell → R) fun l =>
      layerR DF.P kRef (fun r c => ((Layout.matrixRef iZero r c : ℤ) : R)) (4 * g + l) := by
  have hL : 4 * g + (2 * l' + 1) < 48 := by omega
  have hw : wOf (Layout.matrixRef iZero) g (2 * l' + 1) = zeroLayer := zero_layer hL
  have hr : 1 ≤ (Dim.Pl (scl := SFK pp.kap pp.nf g) DF (2 * l' + 1)).kr :=
    (ffK (lawfulK_of hpp) hg (2 * l' + 1)).rr.1
  have hW : layerR DF.P kRef (fun r c => ((Layout.matrixRef iZero r c : ℤ) : R))
      (4 * g + (2 * l' + 1)) = LW.ofInt R zeroLayer := by
    rw [← zero_layer hL]
    exact Cast.layerCast' ppref kRef (Layout.matrixRef iZero) _
  refine ⟨fun e j x => ?_, fun e j x => ?_, fun e j x => ?_, fun e he hn => ?_, ?_⟩
  · rw [hW]
    exact Int.cast_zero
  · rw [hW]
    exact Int.cast_zero
  · rw [hW]
    exact Int.cast_zero
  · rw [val_rd DF _ .sel hl hn hi, hon0_val prompt hpp hg]
    show (((if e = FF.es _ (wOf (Layout.matrixRef iZero) g (2 * l' + 1)) _ i then 1 else 0 : ℤ) :
      ℤ) : R) = 0
    rw [hw, zero_es _ hr, if_neg (Nat.ne_of_gt he), Int.cast_zero]
  · rw [val_rd DF _ .lr hl (show 0 < 128 by norm_num) hi, hon0_val prompt hpp hg]
    show _ * (((FF.lr _ (wOf (Layout.matrixRef iZero) g (2 * l' + 1)) _ i 0 : ℤ) : ℤ) : R) = 0
    rw [hw, zero_lr _ hr, Int.cast_zero, mul_zero]

end Ref

/-- A witness, modulo every prime p. For all valid settings pp, every prompt, every group g < 12,
instance l' < 2 and position i < 1,024: a trace on the valid names of the feed-forward segment of
group g, at the matrix of the all-zero index, with cells of absolute value at most 128, every key in
its table and every identity but j10 at (l', i) equal to 0, at which j10 at (l', i) is not 0. -/
theorem hot_witness {p : ℕ} [Fact p.Prime] {pp : ScalesAndPolicy} (hpp : Lawful pp)
    (prompt : Fin ppref.T → Fin ppref.V) {g l' i : ℕ} (hg : g < 12) (hl : l' < 2) (hi : i < 1024) :
    ∃ t : {c : Cell // c.Valid DF} → ℤ,
      (∀ c, |t c| ≤ 128) ∧
      (∀ k, (trace (scl := SFK pp.kap pp.nf g) DF tbRef kRef (4 * g) (decide (g = 0))
            (ZMod p)).key (tokOf prompt)
          (fun r c => ((Layout.matrixRef iZero r c : ℤ) : ZMod p)) t k ∈
        (trace (scl := SFK pp.kap pp.nf g) DF tbRef kRef (4 * g) (decide (g = 0))
          (ZMod p)).table k) ∧
      (∀ j : (trace (scl := SFK pp.kap pp.nf g) DF tbRef kRef (4 * g) (decide (g = 0))
            (ZMod p)).Idn, j.val ≠ .j10 l' i →
        (trace (scl := SFK pp.kap pp.nf g) DF tbRef kRef (4 * g) (decide (g = 0))
          (ZMod p)).idn (tokOf prompt)
          (fun r c => ((Layout.matrixRef iZero r c : ℤ) : ZMod p)) t j = 0) ∧
      (trace (scl := SFK pp.kap pp.nf g) DF tbRef kRef (4 * g) (decide (g = 0))
          (ZMod p)).idn (tokOf prompt)
        (fun r c => ((Layout.matrixRef iZero r c : ℤ) : ZMod p)) t
        ⟨.j10 l' i, ⟨hl, hi⟩⟩ ≠ 0 := by
  obtain ⟨hRF, hB⟩ := ffK_honest (p := p) (lawfulK_of hpp) (Layout.wfw_matrixRef iZero)
    (zero_runs prompt hpp) hg
  obtain ⟨-, h2, h3, h4⟩ := hot_free (scl := SFK pp.kap pp.nf g) DF l' i tbRef kRef (4 * g)
    (decide (g = 0)) (tokOf prompt) _ _ hRF (zero_off prompt hpp hg hl hi)
  refine ⟨_, fun c => ?_, h2, h3,
    fun h0 => neg_ne_zero.2 (one_ne_zero (α := ZMod p)) (h4.symm.trans h0)⟩
  unfold offT
  split
  · norm_num
  · exact hB c.val c.2

/-- The witness modulo 2^64 - 2^32 + 1: no premise on the prime is left. -/
theorem hot_witness_gold {pp : ScalesAndPolicy} (hpp : Lawful pp) (prompt : Fin ppref.T → Fin ppref.V)
    {g l' i : ℕ} (hg : g < 12) (hl : l' < 2) (hi : i < 1024) :
    ∃ t : {c : Cell // c.Valid DF} → ℤ,
      (∀ c, |t c| ≤ 128) ∧
      (∀ k, (trace (scl := SFK pp.kap pp.nf g) DF tbRef kRef (4 * g) (decide (g = 0))
            (ZMod Code.pGold)).key (tokOf prompt)
          (fun r c => ((Layout.matrixRef iZero r c : ℤ) : ZMod Code.pGold)) t k ∈
        (trace (scl := SFK pp.kap pp.nf g) DF tbRef kRef (4 * g) (decide (g = 0))
          (ZMod Code.pGold)).table k) ∧
      (∀ j : (trace (scl := SFK pp.kap pp.nf g) DF tbRef kRef (4 * g) (decide (g = 0))
            (ZMod Code.pGold)).Idn, j.val ≠ .j10 l' i →
        (trace (scl := SFK pp.kap pp.nf g) DF tbRef kRef (4 * g) (decide (g = 0))
          (ZMod Code.pGold)).idn (tokOf prompt)
          (fun r c => ((Layout.matrixRef iZero r c : ℤ) : ZMod Code.pGold)) t j = 0) ∧
      (trace (scl := SFK pp.kap pp.nf g) DF tbRef kRef (4 * g) (decide (g = 0))
          (ZMod Code.pGold)).idn (tokOf prompt)
        (fun r c => ((Layout.matrixRef iZero r c : ℤ) : ZMod Code.pGold)) t
        ⟨.j10 l' i, ⟨hl, hi⟩⟩ ≠ 0 :=
  haveI : Fact (Nat.Prime Code.pGold) := ⟨Code.pGold_prime⟩
  hot_witness hpp prompt hg hl hi

/-- The witness at the reference settings (`ppRef`, valid by `lawful_ref`, Inst/Model/Scales.lean),
modulo 2^64 - 2^32 + 1: no premise is left but the ranges of g, l' and i. -/
theorem hot_witness_ref (prompt : Fin ppref.T → Fin ppref.V) {g l' i : ℕ} (hg : g < 12)
    (hl : l' < 2) (hi : i < 1024) :
    ∃ t : {c : Cell // c.Valid DF} → ℤ,
      (∀ c, |t c| ≤ 128) ∧
      (∀ k, (trace (scl := SFK ppRef.kap ppRef.nf g) DF tbRef kRef (4 * g) (decide (g = 0))
            (ZMod Code.pGold)).key (tokOf prompt)
          (fun r c => ((Layout.matrixRef iZero r c : ℤ) : ZMod Code.pGold)) t k ∈
        (trace (scl := SFK ppRef.kap ppRef.nf g) DF tbRef kRef (4 * g) (decide (g = 0))
          (ZMod Code.pGold)).table k) ∧
      (∀ j : (trace (scl := SFK ppRef.kap ppRef.nf g) DF tbRef kRef (4 * g) (decide (g = 0))
            (ZMod Code.pGold)).Idn, j.val ≠ .j10 l' i →
        (trace (scl := SFK ppRef.kap ppRef.nf g) DF tbRef kRef (4 * g) (decide (g = 0))
          (ZMod Code.pGold)).idn (tokOf prompt)
          (fun r c => ((Layout.matrixRef iZero r c : ℤ) : ZMod Code.pGold)) t j = 0) ∧
      (trace (scl := SFK ppRef.kap ppRef.nf g) DF tbRef kRef (4 * g) (decide (g = 0))
          (ZMod Code.pGold)).idn (tokOf prompt)
        (fun r c => ((Layout.matrixRef iZero r c : ℤ) : ZMod Code.pGold)) t
        ⟨.j10 l' i, ⟨hl, hi⟩⟩ ≠ 0 :=
  hot_witness_gold lawful_ref prompt hg hl hi

end Cb.Rider

#print axioms Cb.Rider.zero_off
#print axioms Cb.Rider.hot_witness
#print axioms Cb.Rider.hot_witness_gold
#print axioms Cb.Rider.hot_witness_ref
