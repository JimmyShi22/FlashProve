-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/G6/Rider/Model/Denom.lean: identity at3 of an attention segment ("the denominator of a row is the
sum of the row's weights") as one array on a cube, and its multilinear extension at a pick of
coordinates of a call's key point.

Statements and proofs. No protocol occurs here. The rule for a second zero test on a block's
challenges (Cb/G6/Rider/Carrier.lean) has a source `OnCubes` and a target `AtCoords`, both over free
arrays. This file fills the array with `denVec` (Cb/Pv/Att/Mean/DenStep.lean) and restates source
and target in the names of Inst/Model/Att/Trace.lean and Inst/Model/Att/Points.lean. The cube is (b
| g | i): nu + D.lg + D.lT variables, b the number of a piece. nu is a free letter with D.nb ≤ 2^nu;
in `den_out` it is C.a 2 - D.lW.
Main names:
  `denVec_pieces`: `denVec` is `onPieces` (Cb/G6/Rider/Picks.lean) of the identities at3.
  `denFam D cells`: the family of one member. `cells` is a free letter: how the cells are read off a
    state and a tuple of messages.
  `den_source`: `OnCubes` of the family says that `idnVal` is 0 at every valid `Idn.at3 b g i`.
  `den_target`: `AtCoords` of the family says that the extension of `denVec` is 0 at the chosen
    coordinates.
  `den_ext`: the extension of `denVec` at any point p is the sum over the pieces b < D.nb of the
    equality weight of p's first nu coordinates at b times the read `rd2` of the identities at the
    next D.lg and the next D.lT coordinates.
  `zC_keyIx`: the key point of call c (`Calls.zC`) is the whole point read through `keyIx`.
  `den_out`: at the pick `callIx` (C.a 2 - D.lW) of the key point of call 2 (its first C.a 2 - D.lW
    coordinates, one skipped, the next D.lg + D.lT) the extension of `denVec` is `denOut D C z t`.
  `den_not_back`: the target does not give the source. If D.nb ≤ 2^(C.a 2 - D.lW) and D.nb and D.lT
    are at least 1, there are cells at which `denOut` is 0 at the point 0 and the source fails.
Limits: nothing on which block draws the point, on its counts, or on who tests the target. No
premise ties C to D but those written. `den_not_back` gives one point for one choice of cells; it
counts nothing.
-/
import Cb.Pv.Att.Mean.DenStep
import Blocks.LookupCalls
import Blocks.LookupRel
import Cb.G6.Rider.Picks
import Cb.G6.Rider.Carrier

set_option autoImplicit false

namespace Cb.Rider
open Blocks Finset Inst.Model Inst.Model.AttSeg Cb.Pv.Att

section Denom
variable {K : Type} [Field K] (D : Dim)

theorem denVec_pieces (t : Raw → K) :
    denVec D t = onPieces D.lg D.lT D.nb fun b g i => idnVal D t (.at3 b g i) := by
  funext X
  unfold denVec onPieces blkOf gOf iOf
  rw [← D.T_eq]
  rfl

variable {St M : Type} (cells : St → M → Raw → K)

/-- The family of one member; the cells are read off the state and the tuple of messages by
`cells`. -/
def denFam : Unit → St → M → ℕ → K := fun _ st m => denVec D (cells st m)

/-- The source, in the names of the field relation. -/
theorem den_source {nu : ℕ} (hN : D.nb ≤ 2 ^ nu) (st : St) (m : M) :
    OnCubes (fun _ : Unit => nu + D.lg + D.lT) (denFam D cells) st m ↔
      ∀ b g i, Idn.Valid D (.at3 b g i) → idnVal D (cells st m) (.at3 b g i) = 0 := by
  have e := onPieces_zero (lgk := D.lg) (lt := D.lT) hN
    fun b g i => idnVal D (cells st m) (.at3 b g i)
  rw [← denVec_pieces] at e
  constructor
  · intro h b g i hv
    exact e.1 (h ()) b hv.1 g hv.2.1 i (by rw [← D.T_eq]; exact hv.2.2)
  · intro h _
    exact e.2 fun b hb g hg i hi => h b g i ⟨hb, hg, by rw [D.T_eq]; exact hi⟩

/-- The target. -/
theorem den_target (nu : ℕ) (sel : ℕ → ℕ) (st : St) (pt : ℕ → K) (m : M) :
    AtCoords (fun _ : Unit => nu + D.lg + D.lT) (fun _ => sel) (denFam D cells) st pt m ↔
      ext (nu + D.lg + D.lT) (denVec D (cells st m)) (fun t => pt (sel t)) = 0 :=
  ⟨fun h => h (), fun h _ => h⟩

/-- The equality factor from an offset on is the equality factor of the shifted point. -/
private theorem eqN_sh (g off : ℕ) (p : ℕ → K) (X : ℕ) : eqN g 0 (sh p off) X = eqN g off p X := by
  unfold eqN sh
  simp only [Nat.zero_add]

/-- The equality factor reads the first g coordinates of its point. -/
private theorem eqN_congr_pt {g : ℕ} {p p' : ℕ → K} (h : ∀ t < g, p t = p' t) (X : ℕ) :
    eqN g 0 p X = eqN g 0 p' X := by
  unfold eqN
  refine prod_congr rfl fun t ht => ?_
  rw [Nat.zero_add, h t (mem_range.1 ht)]

/-- The extension of `denVec` at any point, piece by piece. -/
theorem den_ext {nu : ℕ} (hN : D.nb ≤ 2 ^ nu) (t : Raw → K) (p : ℕ → K) :
    ext (nu + D.lg + D.lT) (denVec D t) p =
      ∑ b ∈ range D.nb, eqN nu 0 p b *
        rd2 D (sh p nu) (eqT D (sh p (nu + D.lg))) fun g i => idnVal D t (.at3 b g i) := by
  rw [ext_two (nu + D.lg) D.lT, pow_add, Alg.sum_range_mul_add]
  have hb : ∀ b ∈ range (2 ^ nu),
      (∑ g ∈ range (2 ^ D.lg), ∑ i ∈ range (2 ^ D.lT),
        eqN (nu + D.lg) 0 p (b * 2 ^ D.lg + g) * eqN D.lT (nu + D.lg) p i *
          denVec D t ((b * 2 ^ D.lg + g) * 2 ^ D.lT + i)) =
      (if b < D.nb then eqN nu 0 p b *
        rd2 D (sh p nu) (eqT D (sh p (nu + D.lg))) fun g i => idnVal D t (.at3 b g i) else 0) *
          1 := by
    intro b _
    rw [mul_one]
    split
    · next hlt =>
      unfold rd2 eqT
      rw [mul_sum, show D.nG = 2 ^ D.lg from rfl, D.T_eq]
      refine sum_congr rfl fun g hg => ?_
      rw [mul_sum]
      refine sum_congr rfl fun i hi => ?_
      obtain ⟨e1, e2, e3⟩ := cut_of (P := b) (mem_range.1 hg) (mem_range.1 hi)
      rw [eqN_append' nu D.lg 0 p b (mem_range.1 hg), Nat.zero_add, eqN_sh, eqN_sh, denVec_pieces]
      unfold onPieces
      rw [e1, e2, e3, if_pos hlt]
      ring
    · next hge =>
      refine sum_eq_zero fun g hg => sum_eq_zero fun i hi => ?_
      obtain ⟨e1, _, _⟩ := cut_of (P := b) (mem_range.1 hg) (mem_range.1 hi)
      rw [denVec_pieces]
      unfold onPieces
      rw [e1, if_neg hge, mul_zero]
  rw [sum_congr rfl hb, sum_range_ite_lt hN]
  exact sum_congr rfl fun b _ => mul_one _

omit [Field K] in
/-- The key point of a call is the whole point read through `keyIx`. -/
theorem zC_keyIx (C : Calls) (c : Fin 4) (h : C.e c ≤ C.sg) (z : ℕ → K) (t : ℕ) :
    C.zC c z t = z (keyIx C.Dk C.sg (C.e c) t) := by
  unfold Calls.zC keyIx
  split
  · congr 1
    omega
  · rfl

/-- At the pick of the key point of call 2, the extension of `denVec` is `denOut`. -/
theorem den_out (C : Calls) (hN : D.nb ≤ 2 ^ (C.a 2 - D.lW)) (z : ℕ → K) (t : Raw → K) :
    ext (C.a 2 - D.lW + D.lg + D.lT) (denVec D t)
      (fun s => C.zC 2 z (callIx (C.a 2 - D.lW) s)) = denOut D C z t := by
  rw [den_ext D hN]
  unfold denOut
  refine sum_congr rfl fun b _ => ?_
  have e1 : eqN (C.a 2 - D.lW) 0 (fun s => C.zC 2 z (callIx (C.a 2 - D.lW) s)) b =
      wp D C z .w3 b := by
    unfold wp
    rw [show Fam.nu0 D .w3 + b = b from Nat.zero_add b]
    exact eqN_congr_pt (fun s hs => by
      show C.zC 2 z (callIx (C.a 2 - D.lW) s) = C.zC 2 z s
      unfold callIx
      rw [if_pos hs]) b
  have e2 : sh (fun s => C.zC 2 z (callIx (C.a 2 - D.lW) s)) (C.a 2 - D.lW) = yg D C z := by
    funext s
    show C.zC 2 z (callIx (C.a 2 - D.lW) (C.a 2 - D.lW + s)) = C.zC 2 z (C.a 2 - D.lW + (1 + s))
    unfold callIx
    rw [if_neg (by omega)]
    congr 1
    omega
  have e3 : sh (fun s => C.zC 2 z (callIx (C.a 2 - D.lW) s)) (C.a 2 - D.lW + D.lg) =
      yi D C z := by
    funext s
    show C.zC 2 z (callIx (C.a 2 - D.lW) (C.a 2 - D.lW + D.lg + s)) =
      C.zC 2 z (C.a 2 - D.lW + (1 + D.lg + s))
    unfold callIx
    rw [if_neg (by omega)]
    congr 1
    omega
  rw [e1, e2, e3]

/-- The target does not give the source: cells whose identity at3 is 1 at (0, 0, 1) and 0 elsewhere,
and the point 0. -/
theorem den_not_back (C : Calls) (hN : D.nb ≤ 2 ^ (C.a 2 - D.lW)) (hb : 1 ≤ D.nb)
    (hT : 1 ≤ D.lT) :
    ∃ t : Raw → K, denOut D C (fun _ => 0) t = 0 ∧
      ¬ ∀ b g i, Idn.Valid D (.at3 b g i) → idnVal D t (.at3 b g i) = 0 := by
  let t : Raw → K := fun c =>
    match c with
    | .den k b g i => if k = 0 ∧ b = 0 ∧ g = 0 ∧ i = 1 then 1 else 0
    | .c _ jj _ _ => if jj = 3 then -128 else 0
    | _ => 0
  have hE : ∀ b g i, EF D t b g i = 0 := by
    intro b g i
    simp [EF, rowSum, wtV, w0, w1, t]
  have hd : ∀ b g i, denV t b g i = if b = 0 ∧ g = 0 ∧ i = 1 then 1 else 0 := by
    intro b g i
    simp [denV, sum_range_succ, t]
  have hv : ∀ b g i, idnVal D t (.at3 b g i) = if b = 0 ∧ g = 0 ∧ i = 1 then 1 else 0 := by
    intro b g i
    show denV t b g i - EF D t b g i = _
    rw [hE, hd, sub_zero]
  refine ⟨t, ?_, fun h => ?_⟩
  · rw [← den_out D C hN]
    have hp : ∀ s < C.a 2 - D.lW + D.lg + D.lT,
        C.zC 2 (fun _ => (0 : K)) (callIx (C.a 2 - D.lW) s) =
          cubePt (C.a 2 - D.lW + D.lg + D.lT) 0 s := by
      intro s hs
      have e : C.zC 2 (fun _ => (0 : K)) (callIx (C.a 2 - D.lW) s) = 0 := by
        unfold Calls.zC
        split <;> rfl
      rw [e]
      simp [cubePt, nat, hs, Alg.corner, Alg.bits]
    rw [ext_congr_point hp, ext_cubePt _ _ (Nat.two_pow_pos _)]
    simp [denVec, hv]
  · have h1 : 1 < D.T := by
      rw [D.T_eq]
      exact Nat.one_lt_two_pow (by omega)
    have h0 := h 0 0 1 ⟨by omega, Nat.two_pow_pos _, h1⟩
    rw [hv] at h0
    simp at h0

end Denom

end Cb.Rider

#print axioms Cb.Rider.den_source
#print axioms Cb.Rider.den_target
#print axioms Cb.Rider.den_ext
#print axioms Cb.Rider.zC_keyIx
#print axioms Cb.Rider.den_out
#print axioms Cb.Rider.den_not_back
