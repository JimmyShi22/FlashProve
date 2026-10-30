-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/ReadSF.lean: CONDITIONAL: the honest prover's side of an attention
segment's own rounds: the summand "the score at the index" (`sSF`,
Johnson/Desc/K5/Honest/Index.lean), read in a field, is the library's step s16
(Inst/Model/Att/Sums.lean): its weights, its two hidden maps at ANY point, its sum over the cube;
and it has what the masked sumcheck's prover asks of a summand. Names for pieces of the summand's
text, and statements with their proofs.

Main names:
  `under3`, `read_under3`   a threefold sum of a table's entries under the equality weights of
                  three cuts of a point: the multilinear extension of the table, read
  `read_keyAtIndex`   the key that the index's cells select is the library's `sel`
  `sfTab`, `sSF_endAt`   the summand's tables, which are arrays made once; a hidden map in them
  `sfA_reads`, `sfB_reads`   the maps read as the library's `Aext`, `Bext` of step s16
  `sSF_reads`     `StepReads` (Johnson/Desc/K5/Honest/Law/ProductsLaw.lean) of the summand
  `sSF_total`     the sum over the cube reads as `sumPhi` of step s16
  `sSF_tame`      `Summand.Tame` at 4 coefficients a variable and 3 in Y (degree at most 2)

Every statement on the summand but `sSF_terms` is conditional. The premises, and who is meant to
show each:
`Sized`, `Planned`: public, the caller's. `Drawn`: the round that draws many elements has been heard
with all its elements: the caller's. `IndexPts`: the library's challenges p are the prover's, read,
in the fields o, tg and ti, which are all that step s16 reads: it holds at `pubOf`
(Johnson/Desc/K5/Honest/Law/Cells.lean, Weights.lean). No cell is asked to be a bit.
Limits.
Nothing here says that a premise holds at any place.
No property is claimed by a definition.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Law.Weights
import Johnson.Desc.K5.Honest.Law.ProductsLaw
import Cb.Pv.Att.Mean.Reads
import Cb.Pv.Att.Mean.Weights

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading)
open OnBytes.Road (pt)
open VerifiableInference.Desc.First.Att.P (Geo geoOf eqTab wAtIndex wCells)
open Inst.Model.AttSeg
open Finset

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## A threefold sum under three cuts of a point -/

/-- The sum over i, j, k of eq(x's first a coordinates, i) eq(its next b, j) eq(the rest, k) times
the entry (i 2^b + j) 2^c + k of a table. -/
def under3 (a b c : ℕ) (x t : Array E) : E :=
  under (eqTab (x.extract 0 a)) fun i => under (eqTab (x.extract a (a + b))) fun j =>
    under (eqTab (x.extract (a + b) x.size)) fun k => t.getD ((i * 2 ^ b + j) * 2 ^ c + k) zeroE

/-- **It reads as the multilinear extension of the table, read.** -/
theorem read_under3 {a b c : ℕ} {x : Array E} (hx : x.size = a + b + c) (t : Array E) :
    ρ.val (under3 a b c x t) =
      Blocks.ext (a + b + c) (fun X => ρ.val (t.getD X zeroE)) (pt ρ x) := by
  have z1 : (x.extract 0 a).size = a := by
    rw [size_extract_le x (by omega)]
    omega
  have z2 : (x.extract a (a + b)).size = b := by
    rw [size_extract_le x (by omega)]
    omega
  have z3 : (x.extract (a + b) x.size).size = c := by
    rw [size_extract_le x (le_refl _)]
    omega
  rw [Cb.Pv.Att.ext_three]
  unfold under3
  rw [read_under_eq ρ z1 (v := pt ρ x) fun j hj => by
    rw [pt_extract ρ x 0 a j (by omega), Nat.zero_add]]
  refine sum_congr rfl fun i _ => ?_
  rw [read_under_eq ρ z2 (v := sh (pt ρ x) a) fun j hj => pt_extract ρ x a (a + b) j (by omega),
    mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [read_under_eq ρ z3 (v := sh (pt ρ x) (a + b)) fun k hk =>
    pt_extract ρ x (a + b) x.size k (by omega), mul_sum, mul_sum]
  exact sum_congr rfl fun k _ => by ring

/-! ## The key that the index's cells select -/

/-- The product of a list made of the numbers below n. -/
theorem prod_list_range (n : ℕ) (f : ℕ → K) :
    ((List.range n).map f).prod = ∏ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ, ← ih, List.range_succ, List.map_append, List.prod_append]
    simp

/-- **The key that the index's cells select is the library's**, at any cells. -/
theorem read_keyAtIndex {P : Pub5} (H : Sized P) (w : K5In) (b hk i ch : ℕ) :
    ρ.val (keyAtIndex P.g.lt P.g.HA w b hk i ch) = sel P.D (tOf ρ w) b hk i ch := by
  unfold keyAtIndex sel
  rw [read_sumTo, H.lt, ← Dim.T_eq]
  refine sum_congr rfl fun j _ => ?_
  refine (read_foldl_mul ρ (fun k => if (j >>> k) % 2 == 1 then w.ibit k b hk i
    else subE oneE (w.ibit k b hk i)) (List.range P.D.lT) (w.kx (b / P.g.HA) hk j ch)).trans ?_
  rw [read_kx, prod_list_range]
  refine congrArg (keyV (tOf ρ w) (P.D.lamOf b) hk j ch * ·) (prod_congr rfl fun k _ => ?_)
  have hb : ((j >>> k) % 2 == 1) = j.testBit k := by
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, beq_eq_decide]
  rw [hb]
  unfold eq1 bitR
  cases j.testBit k
  · simp only [Bool.false_eq_true, if_false, ρ.sub, ρ.one, read_ibit]
    ring
  · simp only [if_true, read_ibit]
    ring

/-! ## The summand's tables -/

/-- The hidden map number n on the cube: the entry (i G + hk) D + ch. The text of `sSF`. -/
def sfTab (g : Geo) (w : K5In) (n : ℕ) : Array E :=
  (Array.range (2 ^ g.lt * 2 ^ g.lgk * 2 ^ g.ldh)).map fun e =>
    if n % 2 == 0 then
      w.q (n / 2) (e / 2 ^ g.ldh % 2 ^ g.lgk) (e / (2 ^ g.ldh * 2 ^ g.lgk)) (e % 2 ^ g.ldh)
    else
      keyAtIndex g.lt g.HA w (n / 2) (e / 2 ^ g.ldh % 2 ^ g.lgk) (e / (2 ^ g.ldh * 2 ^ g.lgk))
        (e % 2 ^ g.ldh)

/-- A hidden map of the summand, in its table. -/
theorem sSF_endAt (P : Pub5) (w : K5In) (c : Chal) (x : List E) {n : ℕ} (hn : n < 2 * P.g.NP) :
    (sSF P w c).endAt x n = under3 P.g.lt P.g.lgk P.g.ldh x.toArray (sfTab P.g w n) := by
  have e : (sSF P w c).endAt x n = under3 P.g.lt P.g.lgk P.g.ldh x.toArray
      (((Array.range (2 * P.g.NP)).map (sfTab P.g w)).getD n #[]) := rfl
  rw [e, getD_range_map _ _ _ hn]

theorem sSF_terms (P : Pub5) (w : K5In) (c : Chal) (x : List E) :
    (sSF P w c).terms x = pairsOf P.g.NP
      (wAtIndex P.g { (heardAt P c fun _ => none) with atIndex := sumAt x.toArray }) := rfl

/-! ## The maps, read -/

variable {P : Pub5} (H : Sized P) (w : K5In)
include H

/-- **The first map reads as the library's**, at any point of the step's length. -/
theorem sfA_reads (C : Calls) (p : Pub K) {x : Array E} (hx : x.size = Step.s16.g P.D) (b : ℕ) :
    ρ.val (under3 P.g.lt P.g.lgk P.g.ldh x (sfTab P.g w (2 * b))) =
      Aext P.D C p (tOf ρ w) .s16 b (pt ρ x) := by
  rw [H.lt]
  refine (read_under3 ρ (a := P.D.lT) (b := P.D.lg) (c := P.D.ln) hx _).trans ?_
  refine Blocks.ext_congr (fun X hX => ?_) _
  have hX' : X < 2 ^ P.g.lt * 2 ^ P.g.lgk * 2 ^ P.g.ldh := by
    rw [H.lt, ← pow_add, ← pow_add]
    exact hX
  unfold sfTab
  rw [getD_range_map _ _ _ hX', Nat.mul_mod_right, Nat.mul_div_cancel_left b (by norm_num)]
  show ρ.val (w.q b _ _ _) = qryV (tOf ρ w) b (X / P.D.ch % P.D.nG) (X / P.D.ch / P.D.nG)
    (X % P.D.ch)
  rw [read_q, Nat.div_div_eq_div_mul]
  rfl

/-- **The second map reads as the library's.** -/
theorem sfB_reads (C : Calls) (p : Pub K) {x : Array E} (hx : x.size = Step.s16.g P.D) (b : ℕ) :
    ρ.val (under3 P.g.lt P.g.lgk P.g.ldh x (sfTab P.g w (2 * b + 1))) =
      Bext P.D C p (tOf ρ w) .s16 b (pt ρ x) := by
  have hX0 : ∀ X, X < 2 ^ (P.D.lT + P.D.lg + P.D.ln) →
      X < 2 ^ P.g.lt * 2 ^ P.g.lgk * 2 ^ P.g.ldh := fun X hX => by
    rw [H.lt, ← pow_add, ← pow_add]
    exact hX
  have e : ∀ X, X < 2 ^ (P.D.lT + P.D.lg + P.D.ln) →
      ρ.val ((sfTab P.g w (2 * b + 1)).getD X zeroE) = Bcube P.D C p (tOf ρ w) .s16 b X :=
    fun X hX => by
      unfold sfTab
      rw [getD_range_map _ _ _ (hX0 X hX), show (2 * b + 1) % 2 = 1 by omega,
        show (2 * b + 1) / 2 = b by omega]
      show ρ.val (keyAtIndex P.g.lt P.g.HA w b _ _ _) =
        sel P.D (tOf ρ w) b (X / P.D.ch % P.D.nG) (X / P.D.ch / P.D.nG) (X % P.D.ch)
      rw [read_keyAtIndex ρ H, Nat.div_div_eq_div_mul]
      rfl
  rw [H.lt]
  refine (read_under3 ρ (a := P.D.lT) (b := P.D.lg) (c := P.D.ln) hx _).trans ?_
  exact Blocks.ext_congr e _

/-! ## The summand -/

variable (Pl : Planned P) {c : Chal} (Dr : Drawn P c) (C : Calls) {p : Pub K}
  (I : IndexPts ρ P c p)
include Pl Dr I

/-- **The summand's weights and maps read as the library's of step s16.** -/
theorem sSF_reads : StepReads ρ (sSF P w c) P.D C p (tOf ρ w) .s16 := by
  have hv : (sSF P w c).vars = Step.s16.g P.D := by
    show P.g.lt + P.g.lgk + P.g.ldh = P.D.lT + P.D.lg + P.D.ln
    rw [H.lt]
    rfl
  have hs : ∀ x : List E, x.length = (sSF P w c).vars → x.toArray.size = Step.s16.g P.D :=
    fun x hx => by
      rw [List.size_toArray]
      exact hx.trans hv
  refine ⟨hv, ⟨_, sSF_terms P w c, fun x hx b hb => ?_⟩, fun x hx b hb => ?_,
    fun x hx b hb => ?_⟩
  · have e : x.toArray.size = P.D.lT + P.D.lg + P.D.ln := hs x hx
    exact atIndex_reads ρ H Pl Dr C I x.toArray (by omega) hb
  · rw [sSF_endAt P w c x (by show 2 * b < 2 * P.D.nb; omega)]
    exact sfA_reads ρ H w C _ (hs x hx) b
  · rw [sSF_endAt P w c x (by show 2 * b + 1 < 2 * P.D.nb; omega)]
    exact sfB_reads ρ H w C _ (hs x hx) b

/-- **The sum over the cube reads as the library's sum of step s16.** -/
theorem sSF_total : ρ.val (sSF P w c).total = sumPhi P.D C p (tOf ρ w) .s16 :=
  (sSF_reads ρ H w Pl Dr C I).total

omit I in
/-- **The summand has what the masked sumcheck's prover asks of it.** The statement names no
challenges of the library's, so those made of the prover's are laid, at made-up numbers and a
made-up point of the lookup's. It stands where the round that draws many elements has been heard;
of the summand at earlier challenges nothing is said. -/
theorem sSF_tame : (sSF P w c).Tame ρ (List.replicate (sSF P w c).vars 4) 2 :=
  (sSF_reads ρ H w Pl Dr ⟨fun _ => 0, 0, 0⟩ (indexPts_pubOf ρ P c fun _ => 0)).tame
    fun b ξ => Cb.Pv.Att.wbExt16 P.D _ _ b ξ

end H2K5.Honest

#print axioms H2K5.Honest.read_under3
#print axioms H2K5.Honest.prod_list_range
#print axioms H2K5.Honest.read_keyAtIndex
#print axioms H2K5.Honest.sSF_endAt
#print axioms H2K5.Honest.sSF_terms
#print axioms H2K5.Honest.sfA_reads
#print axioms H2K5.Honest.sfB_reads
#print axioms H2K5.Honest.sSF_reads
#print axioms H2K5.Honest.sSF_total
#print axioms H2K5.Honest.sSF_tame
