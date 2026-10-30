-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegFFCellIdn.lean: identities of the feed-forward segment as families (`Fam`) of
Cb/Req/ReqSpec.lean: the 17 identities of the ledger of a normalisation, (J1) to (J9), and (J10)
"the selection bits of a layer with experts add up to 1".

Definitions and proofs.
A family has one value at each vertex b < 2^v of a cube; a vertex beyond the index set is called
dead. A sum atom (`Atom.sum`) is the sum over further variables of a sum of terms; an index atom
(`Atom0.idx`) is linear in the index matrix.
A ledger (Inst/Model/Common/Ledger.lean) is the function D from the number of a byte to its value.
Of its 17 identities (`Ledger.idn`) number k < 9 is (J1) for s = k; 9 to 16 are (J2) to (J9). The
feed-forward segment has one ledger for each norm instance ν < `FFSeg.Dim.nNu`
(Inst/Model/FF/Index.lean) and position i.

Main names:
  `iA`, `iF`, `iG`: affine forms in the bytes of the ledger (`idn_eq`: see its doc comment);
    W_k = ∑_j ∑_(l + l' = k) b_l[j] b_l'[j] (`Ledger.Wsum`; b_0 to b_4: the five cells of the value
    x[j]) is 0 for k ≥ 9.
  `jnFam g k`, `jn_val`: the family of identity k. Vertices b = ν · 2^10 + i: 3 bits for the norm
    instance, 10 for the position; no vertex is dead. W_k is a sum atom over the ⌈log2 d⌉ bits of
    the channel j, with 25 terms b_l · b_l' under the coefficient tables [l + l' = k and j < d].
  `j10Fam g`, `j10_val`: affine; vertices b = ℓ' · 2^10 + i.

In Cm/TargetSegFFCellIdnOK.lean:
  `j11Fam g tok`: in the first segment, (J11) "the stream starts with the embedding of the token".
    Vertices b = j · 2^10 + i, 13 bits for the channel. Emb[tok_i][j] is a sum atom over the 18 bits
    of a token t: the index atom `aEmb` (Cm/TargetSegIdxModel.lean) under the public coefficient
    table [t = tok_x(i), t < 202,048, j < d], a function of the instance. So the atom's dead
    vertices (tokens from 202,048 on, where it reads free entries of the index matrix) have the
    coefficient 0; at a dead channel the family is 0.
  `idnFams g tok`: the list of these families ((J11) only for g = 0).
Terms: lean/GLOSSARY.md.
-/
import Cm.SegFFCellKit
import Cm.SegFFCellLed
import Cm.SegFF
import Cm.SegIdxModelProofs
import Cm.SegIdxRun

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg
open Cb Code Inst.Model Inst.Model.All Finset
open Inst.Model.Layout (kRef)

variable [scl : Scl]

/-! ## 1. The identities of the ledger, on forms -/

section Led
variable {E : Type} [Field E] (np : NormPar) (D : ℕ → CForm E)

def iA (k : ℕ) : CForm E :=
  if k < 9 then LF.cs D k - D k - (256 : E) • LF.cs D (k + 1)
  else if k = 9 then cK 0 - LF.Blo D - ((2 : E) ^ 23) • LF.Bhi D
  else if k = 10 then
    LF.Vlo D + cK ((np.eps : ℤ) : E) - ((2 : E) ^ 25) • LF.Blo D -
      LF.l1 D + ((2 : E) ^ 48) • LF.kc D
  else if k = 11 then LF.Vhi D - LF.Bhi D - LF.kc D
  else if k = 12 then LF.l1 D + LF.h1 D - (2 : E) • LF.sig D
  else if k = 13 then cK 0 - LF.q1 D
  else if k = 15 then
    cK (2 ^ (np.M + 1)) + LF.sig D - LF.s0 D - ((2 : E) ^ 25) • LF.q1 D - (2 : E) • LF.rr D
  else if k = 16 then LF.rr D + LF.rq D - LF.sig D + cK 1
  else cK 0

def iF (k n : ℕ) : CForm E :=
  if n = 0 then
    (if k = 9 then LF.sa D
      else if k = 10 then (-1 : E) • LF.sa D
      else if k = 11 then (-1 : E) • LF.sb D
      else if k = 13 then LF.Rlo D
      else if k = 14 then LF.Rhi D
      else if k = 15 then (-2 : E) • LF.Rlo D
      else cK 0)
  else if k = 13 then LF.Rhi D else cK 0

def iG (k n : ℕ) : CForm E :=
  if n = 0 then
    (if k = 9 then LF.sb D
      else if k = 10 then LF.sa D
      else if k = 11 then LF.sb D
      else if k = 13 then LF.sb D
      else if k = 14 then LF.sb D
      else if k = 15 then LF.sa D
      else cK 0)
  else if k = 13 then LF.sa D else cK 0

theorem wsum_zero {K : Type} [CommRing K] (d : ℕ) (b : ℕ → ℕ → K) {k : ℕ} (hk : 9 ≤ k) :
    Ledger.Wsum d b k = 0 := by
  unfold Ledger.Wsum
  refine sum_eq_zero fun j _ => sum_eq_zero fun l hl => sum_eq_zero fun l' hl' => if_neg ?_
  have := mem_range.mp hl
  have := mem_range.mp hl'
  omega

/-- For k < 17, identity k of the ledger is W_k + iA + iF_0 iG_0 + iF_1 iG_1. -/
theorem idn_eq (A : ℕ → ℕ → ℕ → E) (d : ℕ) (b : ℕ → ℕ → E) {k : ℕ} (hk : k < 17) :
    Ledger.Wsum d b k + (iA np D k).val A + ∑ n ∈ range 2, (iF D k n).val A * (iG D k n).val A =
      Ledger.idn np (Ledger.Wsum d b) (fun m => (D m).val A) k := by
  by_cases h9 : k < 9
  · have e : ∀ n, (iF D k n : CForm E) = cK 0 := fun n => by
      unfold iF
      split_ifs <;> first | rfl | omega
    simp [iA, Ledger.idn, h9, e]
    ring
  · rw [wsum_zero d b (by omega)]
    interval_cases k <;> (simp [iA, iF, iG, Ledger.idn, sum_range_succ]; try ring)

variable {D} {P : Cb.Place → Prop} (h : ∀ n < 99, AllPl P (D n))
include h

theorem allPl_iA (k : ℕ) : AllPl P (iA np D k) := by
  unfold iA
  refine AllPl.ite
    (fun hk =>
      ((LF.allPl_cs h (by omega)).sub (h k (by omega))).sub ((LF.allPl_cs h (by omega)).smul _))
    fun _ => ?_
  refine AllPl.ite
    (fun _ => ((AllPl.cK _).sub (LF.allPl_Blo h)).sub ((LF.allPl_Bhi h).smul _)) fun _ => ?_
  refine AllPl.ite
    (fun _ =>
      ((((LF.allPl_Vlo h).add (AllPl.cK _)).sub ((LF.allPl_Blo h).smul _)).sub (LF.allPl_l1 h)).add
        ((LF.allPl_kc h).smul _)) fun _ => ?_
  refine AllPl.ite
    (fun _ => ((LF.allPl_Vhi h).sub (LF.allPl_Bhi h)).sub (LF.allPl_kc h)) fun _ => ?_
  refine AllPl.ite
    (fun _ => ((LF.allPl_l1 h).add (LF.allPl_h1 h)).sub ((LF.allPl_sig h).smul _)) fun _ => ?_
  refine AllPl.ite (fun _ => (AllPl.cK _).sub (LF.allPl_q1 h)) fun _ => ?_
  refine AllPl.ite
    (fun _ =>
      ((((AllPl.cK _).add (LF.allPl_sig h)).sub (LF.allPl_s0 h)).sub ((LF.allPl_q1 h).smul _)).sub
        ((LF.allPl_rr h).smul _)) fun _ => ?_
  exact AllPl.ite
    (fun _ => (((LF.allPl_rr h).add (LF.allPl_rq h)).sub (LF.allPl_sig h)).add (AllPl.cK _))
    fun _ => AllPl.cK _

theorem allPl_iF (k n : ℕ) : AllPl P (iF D k n) := by
  unfold iF
  refine AllPl.ite (fun _ => ?_) fun _ => AllPl.ite (fun _ => LF.allPl_Rhi h) fun _ => AllPl.cK _
  refine AllPl.ite (fun _ => LF.allPl_sa h) fun _ =>
    AllPl.ite (fun _ => (LF.allPl_sa h).smul _) fun _ =>
      AllPl.ite (fun _ => (LF.allPl_sb h).smul _) fun _ => ?_
  exact AllPl.ite (fun _ => LF.allPl_Rlo h) fun _ =>
    AllPl.ite (fun _ => LF.allPl_Rhi h) fun _ =>
      AllPl.ite (fun _ => (LF.allPl_Rlo h).smul _) fun _ => AllPl.cK _

theorem allPl_iG (k n : ℕ) : AllPl P (iG D k n) := by
  unfold iG
  refine AllPl.ite (fun _ => ?_) fun _ => AllPl.ite (fun _ => LF.allPl_sa h) fun _ => AllPl.cK _
  refine AllPl.ite (fun _ => LF.allPl_sb h) fun _ =>
    AllPl.ite (fun _ => LF.allPl_sa h) fun _ => AllPl.ite (fun _ => LF.allPl_sb h) fun _ => ?_
  exact AllPl.ite (fun _ => LF.allPl_sb h) fun _ =>
    AllPl.ite (fun _ => LF.allPl_sb h) fun _ =>
      AllPl.ite (fun _ => LF.allPl_sa h) fun _ => AllPl.cK _

end Led

/-! ## 2. The families of the ledger's identities, and (J10) -/

section Fams
variable {X F E : Type} [Field F] [Field E] [Algebra F E] (g : ℕ)

/-- the number of bits of a channel -/
def wD : ℕ := Nat.clog 2 DF.d

theorem d_le : DF.d ≤ 2 ^ wD := Nat.le_pow_clog (by norm_num) _

/-- The parts of the family of identity k. -/
def jnSpec (k : ℕ) : QSpec X E where
  v := 3 + 10
  w := wD
  nS := 25
  nQ := 2
  κ := fun n _ b' => if n / 5 + n % 5 = k ∧ b' % 2 ^ wD < DF.d then 1 else 0
  p := fun n b' =>
    if b' % 2 ^ wD < DF.d then
      cBS g (b' / 2 ^ wD / 2 ^ 10) (n / 5) (b' % 2 ^ wD) (b' / 2 ^ wD % 2 ^ 10)
    else cK 0
  q := fun n b' =>
    if b' % 2 ^ wD < DF.d then
      cBS g (b' / 2 ^ wD / 2 ^ 10) (n % 5) (b' % 2 ^ wD) (b' / 2 ^ wD % 2 ^ 10)
    else cK 0
  a := fun b => iA (FFSeg.npOf DF (b / 2 ^ 10)) (cLed g (b / 2 ^ 10) (b % 2 ^ 10)) k
  f := fun n b => iF (cLed g (b / 2 ^ 10) (b % 2 ^ 10)) k n
  g := fun n b => iG (cLed g (b / 2 ^ 10) (b % 2 ^ 10)) k n

def jnFam (k : ℕ) : Cb.Fam X E := (jnSpec (X := X) (E := E) g k).fam

/-- (J10) -/
def j10Fam : Cb.Fam X E :=
  affFam (1 + 10) fun b => cSum DF.nx (fun e => cVal g .sel (b / 2 ^ 10) e (b % 2 ^ 10)) - cK 1

variable (Φ : IdxFmt F) (x₀ : X) (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E)

theorem sum25 {M : Type} [AddCommMonoid M] (G : ℕ → ℕ → M) :
    ∑ n ∈ range 25, G (n / 5) (n % 5) = ∑ l ∈ range 5, ∑ l' ∈ range 5, G l l' := by
  rw [show (25 : ℕ) = 5 * 5 from rfl, Alg.sum_range_mul_add]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b hb => ?_
  have := mem_range.mp hb
  rw [show (a * 5 + b) / 5 = a by omega, show (a * 5 + b) % 5 = b by omega]

/-- (V) (the label: the head of Cm/TargetSegFFAffPass.lean) For k < 17, the family's value at the
vertex ν · 2^10 + i is identity k of Inst/Model/FF/Trace.lean at (ν, i); at every vertex. -/
theorem jn_val (emb : ℕ → ℕ → E) (tok : ℕ → ℕ) {k : ℕ} (hk : k < 17) (b : ℕ) :
    (jnFam (X := X) g k).val Φ x₀ W A b =
      FFSeg.idnVal DF (tA g A) emb tok (.jn k (b / 2 ^ 10) (b % 2 ^ 10)) := by
  unfold jnFam
  rw [QSpec.fam_val]
  have hsum : (∑ j ∈ range (2 ^ (jnSpec (X := X) (E := E) g k).w),
        ∑ n ∈ range (jnSpec (X := X) (E := E) g k).nS,
          (jnSpec (X := X) (E := E) g k).κ n x₀ (b * 2 ^ (jnSpec (X := X) (E := E) g k).w + j) *
            (((jnSpec (X := X) (E := E) g k).p
                n (b * 2 ^ (jnSpec (X := X) (E := E) g k).w + j)).val A *
              ((jnSpec (X := X) (E := E) g k).q
                n (b * 2 ^ (jnSpec (X := X) (E := E) g k).w + j)).val A)) =
      Ledger.Wsum DF.d (fun l j => FFSeg.bS DF (tA g A) (b / 2 ^ 10) l j (b % 2 ^ 10)) k := by
    unfold Ledger.Wsum
    rw [← sum_range_ind d_le]
    refine sum_congr rfl fun j hj => ?_
    have hj' : j < 2 ^ wD := mem_range.mp hj
    have e1 : (b * 2 ^ wD + j) / 2 ^ wD = b := by
      rw [Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt hj', Nat.add_zero]
    have e2 : (b * 2 ^ wD + j) % 2 ^ wD = j := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hj']
    simp only [jnSpec, e1, e2]
    by_cases hd : j < DF.d
    · rw [if_pos hd,
        ← sum25 fun l l' =>
          if l + l' = k then
            FFSeg.bS DF (tA g A) (b / 2 ^ 10) l j (b % 2 ^ 10) *
              FFSeg.bS DF (tA g A) (b / 2 ^ 10) l' j (b % 2 ^ 10)
          else 0]
      refine sum_congr rfl fun n _ => ?_
      by_cases hn : n / 5 + n % 5 = k <;> simp [hn, hd]
    · rw [if_neg hd]
      exact sum_eq_zero fun n _ => by simp [hd]
  rw [hsum]
  have h := idn_eq (FFSeg.npOf DF (b / 2 ^ 10)) (cLed g (b / 2 ^ 10) (b % 2 ^ 10)) A DF.d
    (fun l j => FFSeg.bS DF (tA g A) (b / 2 ^ 10) l j (b % 2 ^ 10)) hk
  rw [val_cLed] at h
  exact h

theorem jn_wf (k : ℕ) : (jnFam (X := X) g k : Cb.Fam X E).WF Φ := QSpec.fam_wf _ Φ

theorem dec2_lt {a b : ℕ} (hb : b < 2 ^ (a + 10)) : b / 2 ^ 10 < 2 ^ a ∧ b % 2 ^ 10 < 2 ^ 10 :=
  ⟨by rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add]; exact hb,
    Nat.mod_lt _ (Nat.two_pow_pos _)⟩

theorem jn_places (k : ℕ) : ∀ p ∈ (jnFam (X := X) g k : Cb.Fam X E).places, IsFF g p := by
  refine QSpec.fam_places _ (fun n hn b' hb' => ?_) (fun b hb => ?_) (fun n _ b hb => ?_)
  · have hn : n < 25 := hn
    have hb : b' / 2 ^ wD < 2 ^ (3 + 10) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add]
      exact hb'
    have hν : b' / 2 ^ wD / 2 ^ 10 < 8 := (dec2_lt hb).1
    exact ⟨AllPl.ite (fun hd => inFF_cBS g (show _ ≤ 2 * 4 by omega) (by omega) hd (dec2_lt hb).2)
        fun _ => AllPl.cK _,
      AllPl.ite (fun hd =>
          inFF_cBS g (show _ ≤ 2 * 4 by omega) (Nat.mod_lt _ (by norm_num)) hd (dec2_lt hb).2)
        fun _ => AllPl.cK _⟩
  · exact allPl_iA _ (inFF_cLed g (dec2_lt hb).1 (dec2_lt hb).2) k
  · exact ⟨allPl_iF (inFF_cLed g (dec2_lt hb).1 (dec2_lt hb).2) k n,
      allPl_iG (inFF_cLed g (dec2_lt hb).1 (dec2_lt hb).2) k n⟩

theorem j10_val (emb : ℕ → ℕ → E) (tok : ℕ → ℕ) (b : ℕ) :
    (j10Fam (X := X) g).val Φ x₀ W A b =
      FFSeg.idnVal DF (tA g A) emb tok (.j10 (b / 2 ^ 10) (b % 2 ^ 10)) := by
  unfold j10Fam
  rw [affFam_val]
  simp [FFSeg.idnVal]

theorem j10_wf : (j10Fam (X := X) g : Cb.Fam X E).WF Φ := affFam_wf _ _ Φ

theorem j10_places : ∀ p ∈ (j10Fam (X := X) g : Cb.Fam X E).places, IsFF g p :=
  affFam_places fun b hb => by
    have h1 : b / 2 ^ 10 < 2 := by simpa using (dec2_lt hb).1
    have hne : DF.ne = 2 := rfl
    have h2 : b / 2 ^ 10 < DF.ne := by rw [hne]; exact h1
    show InFF g (cSum DF.nx (fun e => cVal g .sel (b / 2 ^ 10) e (b % 2 ^ 10)) - cK 1 : CForm E)
    refine AllPl.sub (AllPl.cSum fun e he => ?_) (AllPl.cK _)
    exact inFF_cVal g h2 he (dec2_lt hb).2

end Fams
end Cm.Seg
