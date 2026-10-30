-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadDown.lean

The plain head's conditions, from the challenge field down to the integers modulo the prime.

A protocol over the field E = Cb.Gl.E can at best show that keys and identities, formed in E from
cells that are integers, lie in their tables and are 0 IN E. The relation of the integer model
(Cm/TargetPRel.lean: "Cond") has them in the integers modulo p = Cb.Gl.p. This file states the way
down in the library's own statements and adds nothing to them: "down" is "Cm.Seg.TS.head_holds"
after "Cm.Seg.TS.head_holds_int". New here are
"plainRF_ring" and "ledgerRF_ring", the two theorems on the third digit, and the witness.

Main definitions and theorems:
* "gl_big", "big_gl": 2^61 - 1 ≤ p, the size condition "Cm.TI.Big" at the protocol's prime.
* "MatHolds np x Wz M": for integer matrices M of cells and an integer index matrix Wz: every key
  of the plain head, formed in E at the cells that the matrices hold at the library's places
  ("Cm.Seg.TS.tH"), is an entry of its table, and each of the 17 identities is 0.
* "matHolds_iff_seg": that is "Holds" of the head's segment ("Cm.Seg.TS.head_holds").
* "down": for cells t that M holds ("Cm.Spec.ReadsAt"), it is equivalent to the clauses headKey and
  headIdn of "Cm.TP.Cond", letter by letter ("Cm.Seg.TS.head_holds_int").
* "rf_of_mat", "rf_of_trace", "cond_of_mat": with the bound on cells it gives the field relation
  "Cm.Plain.TP.RF" modulo p; with the layers' conditions it gives "Cm.TP.Cond".
* "plainRF_ring", "ledgerRF_ring": the same way down where cells come as "Head.Cells", not as
  matrices: over any commutative ring K with an injective ring homomorphism from the integers
  modulo p, the field relation over K is the field relation modulo p. "plainRF_gl": at K = E.
* "hd0_plain", "hd0_ledger": the third digit of a margin, as a program may test it: c times the key
  lies in [0, 2^16), where c is the inverse of 2^23 ("Policy.LedgerHead.inLut_R23_iff").
  "exists_inv23": such a c exists in every such K, for an odd prime p.
* "matHolds_met": the hypotheses are met together: at every lawful table, for every true request,
  by the matrices of the honest trace. (A lawful table and a true request exist: "Top.lawful_exists"
  and "Top.next_true_exists" in HeadTop.lean.)

Not claimed: that any protocol or program shows "MatHolds" or a relation over E; that the cells of
a proof are integers below the bound; anything on the request or the index matrix. All theorems are
deductions inside the library.
-/
import Cm.TargetSegHeadAsm
import Cm.TargetPRelProofs
import Policy.Rel.LedgerHeadInt
import Policy.Rel.LedgerThirdDigit

set_option autoImplicit false

namespace OnBytes.Road.Hd.Down

open Inst.Model Inst.Model.Head

/-! ## 1. The prime -/

/-- The library's prime is at least 2^61 - 1. -/
theorem gl_big : 2 ^ 61 - 1 ≤ Cb.Gl.p := by decide +kernel

/-- The size condition of the theorems on wrap-around holds at the protocol's prime. -/
theorem big_gl : Cm.TI.Big Cb.Gl.p := ⟨gl_big⟩

/-! ## 2. Integer matrices of cells -/

/-- Keys and identities of the plain head, formed in the challenge field from integer matrices M of
cells (read at the library's places) and an integer index matrix Wz. -/
structure MatHolds (np : NormPar) (x : Instance ppref) (Wz : Mat) (M : ℕ → ℕ → ℕ → ℤ) : Prop where
  keys : ∀ f a i, a < Cm.Plain.len f → i < nT →
    InLut (Cm.Plain.TP.tableOf f)
      (Cm.Plain.TP.key np (Cm.Seg.TS.tH (Cb.Partition.castM (E := Cb.Gl.E) M))
        (Cm.Seg.TS.HW fun r c => ((Wz r c : ℤ) : Cb.Gl.F)) (Cm.reqOf x) f a i)
  idns : ∀ i < nT, ∀ k < 17,
    Cm.Plain.idn np (Cm.Seg.TS.tH (Cb.Partition.castM (E := Cb.Gl.E) M)) i k = 0

/-- An entry of a table in E is the image of the entry in F. -/
theorem inLut_gl (T : Lut) (a : Cb.Gl.E) :
    InLut T a ↔ ∃ u < T.rows, a = algebraMap Cb.Gl.F Cb.Gl.E ((T.row u : ℤ) : Cb.Gl.F) :=
  ⟨fun ⟨u, hu, e⟩ => ⟨u, hu, e.trans (map_intCast (algebraMap Cb.Gl.F Cb.Gl.E) _).symm⟩,
    fun ⟨u, hu, e⟩ => ⟨u, hu, e.trans (map_intCast (algebraMap Cb.Gl.F Cb.Gl.E) _)⟩⟩

/-- "MatHolds" is what the head's segment asks of these matrices. -/
theorem matHolds_iff_seg (np : NormPar) (x : Instance ppref) (Wz : Mat) (M : ℕ → ℕ → ℕ → ℤ) :
    MatHolds np x Wz M ↔
      (Cm.Seg.TS.segHead np).Holds Cm.Seg.TS.fmtRef x (fun r c => ((Wz r c : ℤ) : Cb.Gl.F))
        (Cb.Partition.castM (E := Cb.Gl.E) M) :=
  ⟨fun h => (Cm.Seg.TS.head_holds np x _ _).2
      ⟨fun f a i ha hi => (inLut_gl _ _).1 (h.keys f a i ha hi), h.idns⟩,
    fun h =>
      ⟨fun f a i ha hi => (inLut_gl _ _).2 (((Cm.Seg.TS.head_holds np x _ _).1 h).1 f a i ha hi),
        ((Cm.Seg.TS.head_holds np x _ _).1 h).2⟩⟩

/-- **The way down**: for integer cells t that the matrices hold at the places of the names that
the plain head reads, the conditions in E are the conditions modulo p. -/
theorem down (np : NormPar) (x : Instance ppref) (Wz : Mat) (M : ℕ → ℕ → ℕ → ℤ) (t : Cells ℤ)
    (hR : Cm.Spec.ReadsAt t M) :
    MatHolds np x Wz M ↔
      (∀ f a i, a < Cm.Plain.len f → i < nT →
        InLut (Cm.Plain.TP.tableOf f)
          (Cm.Plain.TP.key np (t.cast Cb.Gl.F) (Cm.TP.castH Cb.Gl.p Wz) (Cm.reqOf x) f a i)) ∧
      ∀ i < nT, ∀ k < 17, Cm.Plain.idn np (t.cast Cb.Gl.F) i k = 0 :=
  (matHolds_iff_seg np x Wz M).trans (Cm.Seg.TS.head_holds_int np x Wz M t hR)

/-- **With the bound on cells: the field relation of the plain head modulo p.** -/
theorem rf_of_mat {np : NormPar} {x : Instance ppref} {Wz : Mat} {M : ℕ → ℕ → ℕ → ℤ}
    {t : Cells ℤ} (hR : Cm.Spec.ReadsAt t M) (small : Cm.Plain.Small (2 ^ 18) t)
    (h : MatHolds np x Wz M) :
    Cm.Plain.TP.RF (F := ZMod Cb.Gl.p) np (Cm.TP.castH Cb.Gl.p Wz) (Cm.reqOf x) t :=
  ⟨small, ((down np x Wz M t hR).1 h).1, ((down np x Wz M t hR).1 h).2⟩

/-- The bound of the model's relation bounds the cells that the plain head reads. -/
theorem small_of_below2 {B : ℤ} {T : All.Trace} (b : Cm.Below2 B T) : Cm.Plain.Small B T.vHead :=
  fun j hj => ⟨b.hf j hj, b.hd j hj, b.hr j hj, fun _ hφ => b.toBelowL.headX hφ hj⟩

/-- The same at the head's cells of a trace of the whole model. -/
theorem rf_of_trace {np : NormPar} {x : Instance ppref} {Wz : Mat} {M : ℕ → ℕ → ℕ → ℤ}
    {T : All.Trace} (b : Cm.Below2 (2 ^ 18) T) (hR : Cm.Spec.ReadsAt T.vHead M)
    (h : MatHolds np x Wz M) :
    Cm.Plain.TP.RF (F := ZMod Cb.Gl.p) np (Cm.TP.castH Cb.Gl.p Wz) (Cm.reqOf x) T.vHead :=
  rf_of_mat hR (small_of_below2 b) h

/-- **With the layers' conditions and the condition on y: all conditions of the model's relation.**
The two clauses on the head are "down", unchanged. -/
theorem cond_of_mat {s : Cm.Scales} {W : Mat} {x : Instance ppref} {T : All.Trace}
    {M : ℕ → ℕ → ℕ → ℤ}
    (cL : Cm.TP.CondL Cb.Gl.p s.kap s.nf W (All.tokOf x.prompt) T)
    (hy : x.e < ppref.T → ((x.y.val : ℕ) : ZMod Cb.Gl.p) = 0)
    (hR : Cm.Spec.ReadsAt T.vHead M) (h : MatHolds s.nf x W M) : Cm.TP.Cond Cb.Gl.p s W x T :=
  ⟨cL, ((down s.nf x W M T.vHead hR).1 h).1, ((down s.nf x W M T.vHead hR).1 h).2, hy⟩

/-! ## 3. Cells as they are: any ring into which the integers modulo p embed -/

section Ring
variable {p : ℕ} {K : Type} [CommRing K] (ι : ZMod p →+* K)

/-- Integer cells carried into K are the cells modulo p carried on by ι. -/
theorem cast_map (tz : Cells ℤ) : tz.cast K = (tz.cast (ZMod p)).map ι := by
  simp only [Cells.cast, Cells.map, map_intCast]

/-- The map takes a key of the plain head on integer cells read modulo p to the key read in K. -/
theorem plainKey_map (np : NormPar) (Hz : Mat) (y : Req) (tz : Cells ℤ) (f : Cm.Plain.Fam)
    (a i : ℕ) :
    ι (Cm.Plain.TP.key np (tz.cast (ZMod p)) (fun j v => ((Hz j v : ℤ) : ZMod p)) y f a i) =
      Cm.Plain.TP.key np (tz.cast K) (fun j v => ((Hz j v : ℤ) : K)) y f a i := by
  rw [Cm.Plain.TP.map_key ι, ← cast_map ι tz]
  simp only [map_intCast]

/-- The same for a key of the head with the ledger. -/
theorem ledgerKey_map (np : NormPar) (Hz : Mat) (y : Req) (tz : Cells ℤ) (f : Fam) (a i : ℕ) :
    ι (Policy.LedgerHead.key np (tz.cast (ZMod p)) (fun j v => ((Hz j v : ℤ) : ZMod p)) y f a i) =
      Policy.LedgerHead.key np (tz.cast K) (fun j v => ((Hz j v : ℤ) : K)) y f a i := by
  rw [Policy.LedgerHead.map_key ι, ← cast_map ι tz]
  simp only [map_intCast]

/-- The same for an identity. -/
theorem idn_map (np : NormPar) (tz : Cells ℤ) (i k : ℕ) :
    ι (Cm.Plain.idn np (tz.cast (ZMod p)) i k) = Cm.Plain.idn np (tz.cast K) i k := by
  rw [Cm.Plain.map_idn' ι, ← cast_map ι tz]

/-- a value modulo p is 0 if and only if its image is -/
theorem zero_iff (hι : Function.Injective ι) {a : ZMod p} {b : K} (e : ι a = b) :
    b = 0 ↔ a = 0 := by
  rw [← e]
  exact map_eq_zero_iff ι hι

/-- a value modulo p is an entry of a table if and only if its image is -/
theorem inLut_iff (hι : Function.Injective ι) (T : Lut) {a : ZMod p} {b : K} (e : ι a = b) :
    InLut T b ↔ InLut T a :=
  ⟨fun ⟨u, hu, h⟩ => ⟨u, hu, hι (by rw [e, h, map_intCast])⟩,
    fun ⟨u, hu, h⟩ => ⟨u, hu, by rw [← e, h, map_intCast]⟩⟩

/-- **The plain head's field relation over K is the relation modulo p.** -/
theorem plainRF_ring (hι : Function.Injective ι) {np : NormPar} {Hz : Mat} {y : Req}
    {tz : Cells ℤ} :
    Cm.Plain.TP.RF (F := K) np (fun j v => ((Hz j v : ℤ) : K)) y tz ↔
      Cm.Plain.TP.RF (F := ZMod p) np (fun j v => ((Hz j v : ℤ) : ZMod p)) y tz :=
  ⟨fun h =>
      ⟨h.small,
        fun f a i ha hi =>
          (inLut_iff ι hι _ (plainKey_map ι np Hz y tz f a i)).1 (h.keys f a i ha hi),
        fun i hi k hk => (zero_iff ι hι (idn_map ι np tz i k)).1 (h.idns i hi k hk)⟩,
    fun h =>
      ⟨h.small,
        fun f a i ha hi =>
          (inLut_iff ι hι _ (plainKey_map ι np Hz y tz f a i)).2 (h.keys f a i ha hi),
        fun i hi k hk => (zero_iff ι hι (idn_map ι np tz i k)).2 (h.idns i hi k hk)⟩⟩

/-- The same for the first clause of the cost ledger. -/
theorem dB4_map (y : Req) (tz : Cells ℤ) (i : ℕ) :
    ι (dB4 (tz.cast (ZMod p)) y i) = dB4 (tz.cast K) y i := by
  rw [map_dB4 ι, ← cast_map ι tz]

/-- The same for its second clause. -/
theorem dZ_map (y : Req) (tz : Cells ℤ) (i : ℕ) :
    ι (dZ (tz.cast (ZMod p)) y i) = dZ (tz.cast K) y i := by
  rw [map_dZ ι, ← cast_map ι tz]

/-- The same for its third clause. -/
theorem sB2_map (y : Req) (tz : Cells ℤ) : ι (sB2 (tz.cast (ZMod p)) y) = sB2 (tz.cast K) y := by
  rw [map_sB2 ι, ← cast_map ι tz]

/-- The same for its fourth clause. -/
theorem sB3_map (y : Req) (tz : Cells ℤ) : ι (sB3 (tz.cast (ZMod p)) y) = sB3 (tz.cast K) y := by
  rw [map_sB3 ι, ← cast_map ι tz]

/-- **The field relation of the head with the ledger over K is the relation modulo p.** -/
theorem ledgerRF_ring (hι : Function.Injective ι) {np : NormPar} {Hz : Mat} {y : Req}
    {tz : Cells ℤ} :
    Policy.LedgerHead.RF (F := K) np (fun j v => ((Hz j v : ℤ) : K)) y tz ↔
      Policy.LedgerHead.RF (F := ZMod p) np (fun j v => ((Hz j v : ℤ) : ZMod p)) y tz :=
  ⟨fun h =>
      ⟨h.small,
        fun f a i ha hi =>
          (inLut_iff ι hι _ (ledgerKey_map ι np Hz y tz f a i)).1 (h.keys f a i ha hi),
        fun i hi k hk => (zero_iff ι hι (idn_map ι np tz i k)).1 (h.idns i hi k hk),
        fun i hi => ⟨(zero_iff ι hι (dB4_map ι y tz i)).1 (h.jc i hi).1,
          (zero_iff ι hι (dZ_map ι y tz i)).1 (h.jc i hi).2⟩,
        ⟨(zero_iff ι hι (sB2_map ι y tz)).1 h.sums.1,
          (zero_iff ι hι (sB3_map ι y tz)).1 h.sums.2⟩⟩,
    fun h =>
      ⟨h.small,
        fun f a i ha hi =>
          (inLut_iff ι hι _ (ledgerKey_map ι np Hz y tz f a i)).2 (h.keys f a i ha hi),
        fun i hi k hk => (zero_iff ι hι (idn_map ι np tz i k)).2 (h.idns i hi k hk),
        fun i hi => ⟨(zero_iff ι hι (dB4_map ι y tz i)).2 (h.jc i hi).1,
          (zero_iff ι hι (dZ_map ι y tz i)).2 (h.jc i hi).2⟩,
        ⟨(zero_iff ι hι (sB2_map ι y tz)).2 h.sums.1,
          (zero_iff ι hι (sB3_map ι y tz)).2 h.sums.2⟩⟩⟩

include ι in
/-- For an odd prime p the inverse of 2^23 exists in K. -/
theorem exists_inv23 [Fact p.Prime] (hp : 2 < p) : ∃ c : K, c * 2 ^ 23 = 1 := by
  have h2 : (2 : ZMod p) ≠ 0 := fun h0 => by
    have h1 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    have hd := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 p).1 h1)
    omega
  refine ⟨ι ((2 ^ 23 : ZMod p)⁻¹), ?_⟩
  have e : ι ((2 ^ 23 : ZMod p)⁻¹) * 2 ^ 23 = ι ((2 ^ 23 : ZMod p)⁻¹ * 2 ^ 23) := by
    rw [map_mul, map_pow, map_ofNat]
  rw [e, inv_mul_cancel₀ (pow_ne_zero 23 h2), map_one]

end Ring

/-- **At the challenge field.** -/
theorem plainRF_gl {np : NormPar} {Hz : Mat} {y : Req} {tz : Cells ℤ} :
    Cm.Plain.TP.RF (F := Cb.Gl.E) np (fun j v => ((Hz j v : ℤ) : Cb.Gl.E)) y tz ↔
      Cm.Plain.TP.RF (F := ZMod Cb.Gl.p) np (fun j v => ((Hz j v : ℤ) : ZMod Cb.Gl.p)) y tz :=
  plainRF_ring (algebraMap Cb.Gl.F Cb.Gl.E) (algebraMap Cb.Gl.F Cb.Gl.E).injective

/-- ledgerRF_ring at the library's field and its extension. -/
theorem ledgerRF_gl {np : NormPar} {Hz : Mat} {y : Req} {tz : Cells ℤ} :
    Policy.LedgerHead.RF (F := Cb.Gl.E) np (fun j v => ((Hz j v : ℤ) : Cb.Gl.E)) y tz ↔
      Policy.LedgerHead.RF (F := ZMod Cb.Gl.p) np (fun j v => ((Hz j v : ℤ) : ZMod Cb.Gl.p)) y
        tz :=
  ledgerRF_ring (algebraMap Cb.Gl.F Cb.Gl.E) (algebraMap Cb.Gl.F Cb.Gl.E).injective

/-! ## 4. The third digit of a margin, divided -/

section HD0
variable {K : Type} [CommRing K] {c : K} (hc : c * 2 ^ 23 = 1) (np : NormPar) (t : Cells K)
  (H : ℕ → ℕ → K) (y : Req) (v i : ℕ)
include hc

/-- The key of the family HD0 lies in 2^23 · [0, 2^16) if and only if c times the key lies in
[0, 2^16), c the inverse of 2^23. -/
theorem hd0_plain :
    InLut (Cm.Plain.TP.tableOf .HD0) (Cm.Plain.TP.key np t H y .HD0 v i) ↔
      InLut R16 (c * Cm.Plain.TP.key np t H y .HD0 v i) :=
  Policy.LedgerHead.inLut_R23_iff hc _

/-- hd0_plain for the head with the ledger. -/
theorem hd0_ledger :
    InLut (Policy.LedgerHead.tableOf .HD0) (Policy.LedgerHead.key np t H y .HD0 v i) ↔
      InLut R16 (c * Policy.LedgerHead.key np t H y .HD0 v i) :=
  Policy.LedgerHead.inLut_R23_iff hc _

end HD0

/-! ## 5. The hypotheses can be met -/

/-- **At every lawful table, for every true request: the matrices of the honest trace meet
"MatHolds", hold the trace's cells, and these are below the bound.** -/
theorem matHolds_met {s : Cm.Scales} (hs : s.Lawful) (i : Cm.Idx) (x : Instance ppref)
    (ht : Cm.TrueAt s.kap s.nf i x) :
    Cm.Spec.ReadsAt (Cm.trace2 s i x).vHead (Cm.Seg.toMat Cm.Seg.Hd.plain (Cm.trace2 s i x)) ∧
      Cm.Plain.Small (2 ^ 18) (Cm.trace2 s i x).vHead ∧
      MatHolds s.nf x i.mat (Cm.Seg.toMat Cm.Seg.Hd.plain (Cm.trace2 s i x)) := by
  haveI := big_gl
  have hR := Cm.TP.sub_at s i x _ (Cm.TP.trace_of_true (p := Cb.Gl.p) hs i x ht)
  exact ⟨Cm.Seg.readsAt_toMat _, small_of_below2 hR.2.1,
    (down s.nf x i.mat _ _ (Cm.Seg.readsAt_toMat _)).2 ⟨hR.2.2.headKey, hR.2.2.headIdn⟩⟩

end OnBytes.Road.Hd.Down

#print axioms OnBytes.Road.Hd.Down.big_gl
#print axioms OnBytes.Road.Hd.Down.down
#print axioms OnBytes.Road.Hd.Down.rf_of_trace
#print axioms OnBytes.Road.Hd.Down.cond_of_mat
#print axioms OnBytes.Road.Hd.Down.plainRF_gl
#print axioms OnBytes.Road.Hd.Down.ledgerRF_gl
#print axioms OnBytes.Road.Hd.Down.hd0_plain
#print axioms OnBytes.Road.Hd.Down.hd0_ledger
#print axioms OnBytes.Road.Hd.Down.exists_inv23
#print axioms OnBytes.Road.Hd.Down.matHolds_met
