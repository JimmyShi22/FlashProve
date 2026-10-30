-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/G6/Rider/Model/AttFree.lean: the other clauses of the relation of an attention segment do not
give identity at3 ("the denominator of a row is the sum of the row's weights"): a witness.

Definitions, statements and proofs. No protocol occurs here, no challenge and no transcript: the
file speaks of the relation on cells `RFraw` (Inst/Model/Att/Trace.lean) alone.

What it is for. An attention sub-proof tests the identities at3 at the point that its lookup has
drawn. The rule for such a second test (Cb/G6/Rider/Both.lean) says nothing
wherever the rest of the relation before the block already gives the tested clause. On the library's
relation of a segment that is not so for at3: there are cells at which every other clause of `RFraw`
holds and at3 fails.

Who else reads the cells of at3. at3 is `denV` less `EF`. The cells of den are read, beside at3, by
the looked-up values `key3W` alone; with `key4` these say that out is AC / den, rounded, for
whatever den ≥ 1: they do not compare den with the weights. The cells of the weights are read by
`key2` and, through AC, by `key3W`. [Read off the definitions; the theorems below do not state it.]

Main names:
  `outQ`: the quotient of step (PA7) at values 0.
  `offDen D tb Q Kx V O`: the honest trace `honG` (Inst/Model/Att/HonestGen.lean) at queries Q, keys
    Kx, values V, outputs O, with every denominator raised by 1 and the two high digits of the
    division set to match. The lemmas on it ask `Adm` of HonestGen.lean and that the values of the
    segment's layers are 0.
  `adm_off`: `Adm` holds at the values 0 and their quotient `outQ`.
  `offDen_small`, `offDen_keys`, `offDen_at1`, `offDen_at2`: every valid cell is at most 128 in
    absolute value; every looked-up value in a piece is an entry of its table; at1 and at2 are 0.
  `offDen_at3`: at3 is 1 at every valid index.
  `att_free`: over every commutative ring in which 1 ≠ 0, for all sizes that HonestGen.lean allows
    and with at least one pair: there is a trace of integers with clause (1) (cells at most 128 in
    absolute value), clause (2) and the identities at1, at2 of `RFraw`, at which at3 is not 0 at any
    valid index, and there is a valid index.
  `att_free_sized`: the same under the library's records `SizeOK`, `ExpTab`
    (Inst/Model/Att/Scales.lean); at the sizes, scales and table of a segment g < nGr of the whole
    reduction they are `sizeOKK`, `expTabK` (Inst/Model/All/NoWrapK.lean), under `LawfulK`.
    `att_free_not`: so `RFraw` fails at that trace while clauses (1), (2) and every identity that
    is no at3 hold.
  `att_free_ref`: the same at the reference sizes, valid scales and tables with their ranges.

Limits: the witness is against the relation of one attention segment. Its borrowed cells val and out
are 0; the relation of the whole reduction, in which other segments read these cells, is not spoken
of. Of the two sentences that a use of the rule should prove (`hollow_own`, Cb/G6/Rider/Both.lean)
this is the core of the first alone, and on the library's relation, not at a
joint of a protocol; of the second (an accepted output with the whole relation behind the block)
nothing is said. Nothing on a verifier, on counts or on an honest prover of a protocol.

Terms: lean/GLOSSARY.md.

-/
import Inst.Model.Att.Scales

set_option autoImplicit false

namespace Cb.Rider
open Finset Inst.Model Inst.Model.AttSeg Inst.Model.AttSeg.Hon

section Off
variable [scl : Scl] (D : Dim) (tb : Tables) (Q Kx V O : ℕ → ℕ → ℕ → ℕ → ℤ)

/-- The values: 0 everywhere. -/
def val0 : ℕ → ℕ → ℕ → ℕ → ℤ := fun _ _ _ _ => 0

/-- The quotient of step (PA7) at the values 0. -/
def outQ (b g i n : ℕ) : ℤ :=
  (2 * acP D tb Q Kx val0 b g i n + denP D tb Q Kx b g i) / (2 * denP D tb Q Kx b g i)

/-- The honest trace with every denominator raised by 1; the high digits qh, qh' of the division are
those of den + 1 and of den. Meant for values V that are 0. -/
def offDen : Raw → ℤ
  | .den k b g i => cellW 4 (denP D tb Q Kx b g i + 1) k
  | .qh b g i _ => (denP D tb Q Kx b g i + 1) / 2 ^ 16 - 128
  | .qh' b g i _ => denP D tb Q Kx b g i / 2 ^ 16 - 128
  | c => honG D tb Q Kx V O c

variable {D tb Q Kx V O}

/-- The conditions of Inst/Model/Att/HonestGen.lean at the values 0 and their quotient. -/
theorem adm_off (hq : ∀ b g i n, |Q b g i n| ≤ 2047) (hk : ∀ lam g j n, |Kx lam g j n| ≤ 2047)
    (hch : (D.ch : ℤ) * 2047 ^ 2 ≤ Smax) (hT : D.T ≤ 1024) (hO : ExpOK D.sh D.u0)
    (hE : ∀ u : ℕ, u < D.u0 → 1 ≤ tb.Exp u ∧ tb.Exp u ≤ 2 ^ 12) (hE0 : tb.Exp 0 = 2 ^ 12) :
    Adm D tb Q Kx val0 (outQ D tb Q Kx) where
  q := hq
  k := hk
  v := fun _ _ _ _ => by simp [val0]
  o := fun _ _ _ _ _ => rfl
  ch := hch
  T := hT
  ex := hO
  exp := hE
  exp0 := hE0

variable (h : Adm D tb Q Kx V O) (hV : ∀ b < D.nb, ∀ g j n, V (D.lamOf b) g j n = 0)

local notation "W" => offDen D tb Q Kx V O
local notation "H" => honG D tb Q Kx V O

include hV in
/-- At values 0 the weighted sums are 0. -/
theorem acP_off {b : ℕ} (hb : b < D.nb) (g i n : ℕ) : acP D tb Q Kx V b g i n = 0 := by
  unfold acP
  exact sum_eq_zero fun j _ => by rw [hV b hb, mul_zero]

include h hV in
/-- At values 0 the outputs are 0. -/
theorem out_off {b : ℕ} (hb : b < D.nb) (g : ℕ) {i n : ℕ} (hi : i < D.T) (hn : n < D.ch) :
    O b g i n = 0 := by
  have hd := (denP_range h b g hi).1
  rw [h.o b g i n hn, acP_off hV hb]
  exact Int.ediv_eq_zero_of_lt (by linarith) (by linarith)

theorem denV_off (b g i : ℕ) : denV W b g i = denP D tb Q Kx b g i + 1 :=
  sum_cellW (by norm_num) _

theorem qhV_off (b g i n : ℕ) : qhV W b g i n = (denP D tb Q Kx b g i + 1) / 2 ^ 16 := by
  simp [qhV, offDen]

theorem qhV'_off (b g i n : ℕ) : qhV' W b g i n = denP D tb Q Kx b g i / 2 ^ 16 := by
  simp [qhV', offDen]

include h hV in
theorem RE_off {b : ℕ} (hb : b < D.nb) (g : ℕ) {i n : ℕ} (hi : i < D.T) (hn : n < D.ch) :
    RE D W b g i n = denP D tb Q Kx b g i + 1 := by
  have e1 : AC D W b g i n = AC D H b g i n := rfl
  have e2 : outV W b g i n = outV H b g i n := rfl
  rw [RE, e1, e2, AC_hon h b g hi, outV_hon, acP_off hV hb, out_off h hV hb g hi hn, denV_off]
  ring

include h hV in
theorem key3W_off (χ : ℕ) {b : ℕ} (hb : b < D.nb) (g : ℕ) {i n : ℕ} (hi : i < D.T)
    (hn : n < D.ch) : InLut tau3 (key3W D W χ b g i n) := by
  unfold key3W
  split_ifs
  · rw [RE_off h hV hb g hi hn, qhV_off]
    exact inLut_tau3 _
  · rw [RE_off h hV hb g hi hn, qhV'_off, denV_off]
    have e : 2 * (denP D tb Q Kx b g i + 1) - 1 - (denP D tb Q Kx b g i + 1) -
        2 ^ 16 * (denP D tb Q Kx b g i / 2 ^ 16) =
        denP D tb Q Kx b g i - 2 ^ 16 * (denP D tb Q Kx b g i / 2 ^ 16) := by ring
    rw [e]
    exact inLut_tau3 _

include h in
theorem key4_off (b g : ℕ) {i : ℕ} (hi : i < D.T) (n : ℕ) : InLut tau4 (key4 W b g i n) := by
  obtain ⟨d0, d1⟩ := denP_range h b g hi
  rw [key4, qhV_off, qhV'_off]
  exact inLut_tau4 (by omega) (by omega) (by omega) (by omega)

omit scl in
/-- A property of all keys of two families, at the pieces b < nb, holds at every index in a piece.
-/
theorem twoFam_lt {P : ℤ → Prop} {nb l l' : ℕ} {f f' : ℕ → ℕ → ℤ} {pad : ℤ}
    (hf : ∀ b < nb, ∀ y, P (f b y)) (hf' : ∀ b y, P (f' b y))
    {X : ℕ} (hX : X < nb * 2 ^ l + nb * 2 ^ l') : P (twoFam nb l l' f f' pad X) := by
  unfold twoFam
  split_ifs with h1 h2
  · exact hf _ (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h1)) _
  · exact hf' _ _
  · omega

include h hV in
/-- Every looked-up value in a piece is an entry of its table. -/
theorem offDen_keys : ∀ (c : Fin 4) (X : ℕ), X < D.used c →
    InLut (lut D tb c) (keyVec D tb W c X)
  | 0, X, hX => keyVec_hon h 0 X hX
  | 1, X, hX => keyVec_hon h 1 X hX
  | 2, _, hX =>
    twoFam_lt (fun b hb y => key3W_off h hV _ hb _ (Nat.mod_lt _ T_pos') (Nat.mod_lt _ ch_pos'))
      (fun b y => key3X_hon h b _ (Nat.mod_lt _ T_pos')) hX
  | 3, X, hX => by
      have hX' : X < D.nb * 2 ^ D.l4 := hX
      have e : keyVec D tb W 3 X =
          key4 W (X / 2 ^ D.l4) (X % 2 ^ D.l4 / D.ch / D.T)
            (X % 2 ^ D.l4 / D.ch % D.T) (X % 2 ^ D.l4 % D.ch) := by
        simp only [keyVec, twoFam, if_pos hX']
      rw [e]
      exact key4_off h _ _ (Nat.mod_lt _ T_pos') _

include h in
theorem offDen_at1 (k b g i : ℕ) (hv : Idn.Valid D (.at1 k b g i)) :
    idnVal D W (.at1 k b g i) = 0 := idn_hon h (.at1 k b g i) hv

include h in
theorem offDen_at2 (b g i : ℕ) (hv : Idn.Valid D (.at2 b g i)) :
    idnVal D W (.at2 b g i) = 0 := idn_hon h (.at2 b g i) hv

include h in
/-- At every valid index the denominator is the sum of the row's weights and 1 more. -/
theorem offDen_at3 (b g i : ℕ) (hv : Idn.Valid D (.at3 b g i)) :
    idnVal D W (.at3 b g i) = 1 := by
  have e : EF D W b g i = EF D H b g i := rfl
  show denV W b g i - EF D W b g i = 1
  rw [denV_off, e, EF_hon h b g hv.2.2]
  ring

include h in
/-- Every valid cell has absolute value at most 128. -/
theorem offDen_small : ∀ c : Raw, c.Valid D → |W c| ≤ 128
  | .den k b g i, hv => by
      obtain ⟨d0, d1⟩ := denP_range h b g hv.2.2.2
      have hle : |denP D tb Q Kx b g i + 1| ≤ 128 * 256 ^ (4 - 1) := by
        rw [abs_of_nonneg (by linarith)]
        have e : (128 : ℤ) * 256 ^ (4 - 1) = 2147483648 := by norm_num
        rw [e]
        linarith
      exact writable_of_abs_le (n := 4) _ hle k hv.1
  | .qh b g i n, hv => by
      obtain ⟨d0, d1⟩ := denP_range h b g hv.2.2.1
      show |(denP D tb Q Kx b g i + 1) / 2 ^ 16 - 128| ≤ 128
      rw [abs_le]
      constructor <;> omega
  | .qh' b g i n, hv => by
      obtain ⟨d0, d1⟩ := denP_range h b g hv.2.2.1
      show |denP D tb Q Kx b g i / 2 ^ 16 - 128| ≤ 128
      rw [abs_le]
      constructor <;> omega
  | .c ρ jj b x, hv => abs_hon_le h (.c ρ jj b x) hv
  | .mx k b g i, hv => abs_hon_le h (.mx k b g i) hv
  | .ib k b g i, hv => abs_hon_le h (.ib k b g i) hv
  | .qry k b g i n, hv => abs_hon_le h (.qry k b g i n) hv
  | .out k b g i n, hv => abs_hon_le h (.out k b g i n) hv
  | .key k lam g j n, hv => abs_hon_le h (.key k lam g j n) hv
  | .val k lam g j n, hv => abs_hon_le h (.val k lam g j n) hv

end Off

/-! ## The witness -/

/-- The other clauses of the relation of an attention segment do not give at3. Over every
commutative ring F in which 1 ≠ 0, at all sizes and tables that Inst/Model/Att/HonestGen.lean allows
and with at least one pair (b, g, i): there is a trace t of integers with clause (1) of RFraw (every
valid cell is small: here at most 128 in absolute value, where RFraw asks less than 2^18), clause
(2) (every looked-up value in a piece is an entry of its table, formed in F) and the identities at1
and at2 at every valid index, at which at3 is not 0 at any valid index; and a valid index of at3
exists. So RFraw fails at t by at3 alone. -/
theorem att_free [scl : Scl] (D : Dim) (tb : Tables) (F : Type) [CommRing F] [Nontrivial F]
    (hch : (D.ch : ℤ) * 2047 ^ 2 ≤ Smax) (hT : D.T ≤ 1024) (hO : ExpOK D.sh D.u0)
    (hE : ∀ u : ℕ, u < D.u0 → 1 ≤ tb.Exp u ∧ tb.Exp u ≤ 2 ^ 12) (hE0 : tb.Exp 0 = 2 ^ 12)
    (hb : 0 < D.nb) :
    ∃ t : Raw → ℤ,
      (∀ c : Raw, c.Valid D → |t c| ≤ 128) ∧
      (∀ (c : Fin 4) (X : ℕ), X < D.used c →
        keyVec D tb (castT t : Raw → F) c X ∈ lutSet (lut D tb c)) ∧
      (∀ k b g i, Idn.Valid D (.at1 k b g i) → idnVal D (castT t : Raw → F) (.at1 k b g i) = 0) ∧
      (∀ b g i, Idn.Valid D (.at2 b g i) → idnVal D (castT t : Raw → F) (.at2 b g i) = 0) ∧
      (∀ b g i, Idn.Valid D (.at3 b g i) → idnVal D (castT t : Raw → F) (.at3 b g i) ≠ 0) ∧
      Idn.Valid D (.at3 0 0 0) := by
  have h := adm_off (D := D) (tb := tb) (Q := val0) (Kx := val0) (fun _ _ _ _ => by simp [val0])
    (fun _ _ _ _ => by simp [val0]) hch hT hO hE hE0
  have hV : ∀ b < D.nb, ∀ g j n, val0 (D.lamOf b) g j n = 0 := fun _ _ _ _ _ => rfl
  refine ⟨offDen D tb val0 val0 val0 (outQ D tb val0 val0), offDen_small h,
    fun c X hX => ?_, fun k b g i hv => ?_, fun b g i hv => ?_, fun b g i hv => ?_,
    hb, Nat.two_pow_pos _, T_pos'⟩
  · obtain ⟨ι, h1, h2⟩ := offDen_keys h hV c X hX
    exact ⟨ι, h1, by rw [key_cast, h2]⟩
  · rw [idn_cast, offDen_at1 h k b g i hv, Int.cast_zero]
  · rw [idn_cast, offDen_at2 h b g i hv, Int.cast_zero]
  · rw [idn_cast, offDen_at3 h b g i hv, Int.cast_one]
    exact one_ne_zero

/-- The same under the two records in which the library states these conditions for a segment at
its own scales (Inst/Model/Att/Scales.lean). -/
theorem att_free_sized [scl : Scl] {D : Dim} (hD : SizeOK D) {tb : Tables} (hT : ExpTab D tb)
    (hb : 0 < D.nb) (F : Type) [CommRing F] [Nontrivial F] :
    ∃ t : Raw → ℤ,
      (∀ c : Raw, c.Valid D → |t c| ≤ 128) ∧
      (∀ (c : Fin 4) (X : ℕ), X < D.used c →
        keyVec D tb (castT t : Raw → F) c X ∈ lutSet (lut D tb c)) ∧
      (∀ k b g i, Idn.Valid D (.at1 k b g i) → idnVal D (castT t : Raw → F) (.at1 k b g i) = 0) ∧
      (∀ b g i, Idn.Valid D (.at2 b g i) → idnVal D (castT t : Raw → F) (.at2 b g i) = 0) ∧
      (∀ b g i, Idn.Valid D (.at3 b g i) → idnVal D (castT t : Raw → F) (.at3 b g i) ≠ 0) ∧
      Idn.Valid D (.at3 0 0 0) :=
  att_free D tb F (by
      have : (D.ch : ℤ) ≤ 128 := by exact_mod_cast hD.ch
      unfold Smax
      nlinarith) hD.T hD.ex hT.rng hT.zero hb

/-- So the relation fails at that trace, and by at3 alone. -/
theorem att_free_not [scl : Scl] {D : Dim} (hD : SizeOK D) {tb : Tables} (hT : ExpTab D tb)
    (hb : 0 < D.nb) (F : Type) [CommRing F] [Nontrivial F] :
    ∃ t : Raw → ℤ, ¬ RFraw D tb F t ∧
      (∀ c : Raw, c.Valid D → |t c| < 2 ^ 18) ∧
      (∀ (c : Fin 4) (X : ℕ), X < D.used c →
        keyVec D tb (castT t : Raw → F) c X ∈ lutSet (lut D tb c)) ∧
      ∀ j : Idn, j.Valid D → (∀ b g i, j ≠ .at3 b g i) → idnVal D (castT t : Raw → F) j = 0 := by
  obtain ⟨t, h1, h2, h3, h4, h5, h6⟩ := att_free_sized hD hT hb F
  refine ⟨t, fun hR => h5 0 0 0 h6 (hR.2.2 _ h6),
    fun c hc => lt_of_le_of_lt (h1 c hc) (by norm_num), h2, fun j hj hn => ?_⟩
  cases j with
  | at1 k b g i => exact h3 k b g i hj
  | at2 b g i => exact h4 b g i hj
  | at3 b g i => exact absurd rfl (hn b g i)

/-- The same at the reference sizes, for valid scales and tables with their ranges. -/
theorem att_free_ref [scl : Scl] [law : Lawful] (tb : Tables) (htb : tb.OK ppref) (F : Type)
    [CommRing F] [Nontrivial F] :
    ∃ t : Raw → ℤ,
      (∀ c : Raw, c.Valid Dim.ref → |t c| ≤ 128) ∧
      (∀ (c : Fin 4) (X : ℕ), X < Dim.ref.used c →
        keyVec Dim.ref tb (castT t : Raw → F) c X ∈ lutSet (lut Dim.ref tb c)) ∧
      (∀ k b g i, Idn.Valid Dim.ref (.at1 k b g i) →
        idnVal Dim.ref (castT t : Raw → F) (.at1 k b g i) = 0) ∧
      (∀ b g i, Idn.Valid Dim.ref (.at2 b g i) →
        idnVal Dim.ref (castT t : Raw → F) (.at2 b g i) = 0) ∧
      (∀ b g i, Idn.Valid Dim.ref (.at3 b g i) →
        idnVal Dim.ref (castT t : Raw → F) (.at3 b g i) ≠ 0) ∧
      Idn.Valid Dim.ref (.at3 0 0 0) :=
  att_free Dim.ref tb F (by rw [ref_sizes.2.2.2.2.2.1]; unfold Smax; norm_num)
    (by rw [ref_sizes.2.2.2.2.1]) law.ex (fun u hu => htb.2.2.2.1 u hu) htb.2.2.2.2
    (by rw [ref_sizes.2.2.2.2.2.2.1]; norm_num)

end Cb.Rider

#print axioms Cb.Rider.offDen_keys
#print axioms Cb.Rider.offDen_at3
#print axioms Cb.Rider.offDen_small
#print axioms Cb.Rider.att_free
#print axioms Cb.Rider.att_free_sized
#print axioms Cb.Rider.att_free_not
#print axioms Cb.Rider.att_free_ref
