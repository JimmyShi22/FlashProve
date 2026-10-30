-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/Starts.lean: CONDITIONAL: the honest prover's side of an attention
segment's own rounds: where the cells have the identities of the library's relation, three equations
between what the prover sends hold, read in a field: the sum of "the index's cells are bits" is 0;
the sum of "the score at the index" is the batch of the row maxima that were sent; the two sums of
the value product, less the accumulator, less the batching element times the denominator, are 0.
These are the starts of two masked sumchecks and one claim of the verifier's on scalars alone. Of
the other sumchecks' starts, those of the softmax-table units, of the division and of the two halves
of the value product are scalars that the prover lays as the sums themselves, so that there is
nothing to show but that a value is the same at two rounds' challenges; the start of "the key at the
index" is not the matter of this file. Definitions, and statements with their proofs.

Main names:
  `read_overPieces`, `read_under2`   a sum over a unit's pieces; a sum over heads and tokens under
                    two tables of equality weights is the library's read `rd2`
  `pieces_eq`, `pieces_wp`   a unit's pieces carry the unit's weights
  `LonePts`, `lonePts_of`    the premise on the points at which the division's scalars are taken
  `hb_zero`         the sum of `sHB` reads 0
  `MaxPts`, `m6_reads`   the row maxima that are sent read as the library's `rvM6`
  `sf_start`        the sum of `sSF` reads as the batch of these
  `zc_reads`, `acc_reads`    the denominator's and the accumulator's scalar read as the library's
                    rule values `rv .. .zc`, `rv .. .acc` (Inst/Model/Att/KeyForms.lean)
  `acc_row`         the library's accumulator at one pair and head, tile by tile
  `claim6_of_reads`, `claim6_zero`, `claim6_fronts`   the equation of the value product

Every statement on a value of the prover's is conditional. The premises, and who is meant to show
each: `AtIdn` (Johnson/Desc/K5/Honest/Law/Idn.lean): whoever holds that the cells are a trace of
the library's relation; `claim6_of_reads` asks only for the weaker `Rider` of that file. `Sized`,
`Planned`, `PairsAre`, that a token has at most 16 bits: public, the caller's. `IndexPts`, `MaxPts`,
`DivPts`, `LonePts`: the library's challenges p are the prover's, read: they follow from `KeyPtsAre`
and `UnitIs`, or hold at `pubOf` (Johnson/Desc/K5/Honest/Law/Weights.lean); `DivPts` asks both, or,
at another p, in `pubOf`'s place that the batching element heard, read, is p's `th`. `Drawn`, and
that the verifier's function of the points returns: tests on lengths alone, the caller's.
Limits. Each value is read at the challenges at which it is evaluated; that a value sent at one
round is the same at a later round's challenges is not the matter of this file: the statements are
general in p so that one p can serve at both. Nothing here says that a premise holds at any place.
No property is claimed by a definition.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Alone
import Johnson.Desc.K5.Honest.Law.Idn
import Johnson.Desc.K5.Honest.Law.ReadSF
import Johnson.Desc.K5.Honest.Law.ReadHB
import Johnson.Desc.K5.Honest.Law.ReadVD
import Johnson.Desc.K5.Honest.Law.ReadVM

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading)
open OnBytes.Road (pt)
open VerifiableInference.Desc.First.Att.P (Geo W1 DivP Pts UnitG Pc eqTab eqAt cover piecesOf
  weights inner pcsSorted weights_eq KeyPtsAre UnitIs)
open Inst.Model.AttSeg hiding ibV
open Finset

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## Tools -/

/-- **A sum over a unit's pieces.** -/
theorem read_overPieces (pw : Array W1) (f : W1 → E) :
    ρ.val (overPieces pw f) = ∑ b ∈ range pw.size,
      ρ.val (pw.getD b ⟨0, 0, zeroE⟩).wp * ρ.val (f (pw.getD b ⟨0, 0, zeroE⟩)) := by
  unfold overPieces
  rw [← Array.foldl_toList, read_foldl_add ρ (fun q : W1 => mulE q.wp (f q)), ρ.zero, zero_add,
    Lists.sum_map_range ⟨0, 0, zeroE⟩, Array.length_toList]
  refine sum_congr rfl fun b _ => ?_
  have e : pw.toList.getD b ⟨0, 0, zeroE⟩ = pw.getD b ⟨0, 0, zeroE⟩ := by
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  rw [e, ρ.mul]

/-- **A sum over heads and tokens under two tables of equality weights is the library's read.** -/
theorem read_under2 (D : Dim) {zg zi : Array E} {vg vi : ℕ → K} (ng : zg.size = D.lg)
    (hg : ∀ k < D.lg, pt ρ zg k = vg k) (ni : zi.size = D.lT) (hi : ∀ k < D.lT, pt ρ zi k = vi k)
    {f : ℕ → ℕ → E} {a : ℕ → ℕ → K} (hf : ∀ g i, ρ.val (f g i) = a g i) :
    ρ.val (under (eqTab zg) fun hk => under (eqTab zi) fun i => f hk i) =
      rd2 D vg (eqT D vi) a := by
  rw [read_under_eq ρ ng hg]
  unfold rd2 eqT
  rw [Dim.T_eq]
  refine sum_congr rfl fun g _ => ?_
  rw [read_under_eq ρ ni hi, mul_sum]
  exact sum_congr rfl fun i _ => by rw [hf]; ring

/-- A unit's pieces are made of its sorted list of pieces, one by one. -/
theorem pieces_eq (u : UnitG) (zk : Array E) :
    piecesOf u zk = ((pcsSorted u).map fun pc : Pc =>
      ({ lam := pc.lam, a := pc.a, wp := eqAt (zk.extract 0 (u.n - pc.b)) (pc.off >>> pc.b) } :
        W1)).toArray := by
  unfold piecesOf pcsSorted
  rw [← List.map_mergeSort (f := fun pc : Pc =>
      ({ lam := pc.lam, a := pc.a, wp := eqAt (zk.extract 0 (u.n - pc.b)) (pc.off >>> pc.b) } : W1))
    (r := fun x y => Decidable.decide (x.lam < y.lam) ||
      (x.lam == y.lam && Decidable.decide (x.a ≤ y.a))) (fun _ _ _ _ => rfl)]

/-- **A unit's pieces carry the unit's weights.** -/
theorem pieces_wp (u : UnitG) (zk : Array E) (b : ℕ) :
    ((piecesOf u zk).getD b ⟨0, 0, zeroE⟩).wp = (weights u zk).getD b zeroE := by
  rw [pieces_eq, weights_eq]
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map]
  cases (pcsSorted u)[b]? <;> rfl

/-! ## The points of the division's scalars -/

/-- **What the division's scalars read of the lookup's points**: the pieces' weights and the three
cuts of the inner point of the list of the remainders' low bits, read, are the library's; piece
number b is pair number b. -/
structure LonePts (ρ : Reading K) (P : Pub5) (C : Calls) (p : Pub K) (d : DivP) : Prop where
  nW : d.pwW.size = P.D.nb
  hw : ∀ b < P.D.nb, ρ.val (d.pwW.getD b ⟨0, 0, zeroE⟩).wp = wp P.D C p.z .w3 b
  pairs : PairsAre P.g d.pwW
  nG : d.zgW.size = P.D.lg
  hg : ∀ k < P.D.lg, pt ρ d.zgW k = yg P.D C p.z k
  nI : d.ziW.size = P.D.lT
  hi : ∀ k < P.D.lT, pt ρ d.ziW k = yi P.D C p.z k
  nC : d.zcW.size = P.D.ln
  hn : ∀ k < P.D.ln, pt ρ d.zcW k = yn P.D C p.z k

/-- These hold where the key points, read, are the library's, and the list's unit is the library's
family with a piece for each pair. -/
theorem lonePts_of {P : Pub5} (H : Sized P) {c : Chal} {pts : Pts} (hp : ptsOf P c = some pts)
    {C : Calls} {p : Pub K} (Kp : KeyPtsAre ρ C p.z c.zk)
    (UW : ∀ wl, P.g.single .wl = some wl → ∃ q, UnitIs P.D C .w3 q wl)
    (pr : PairsAre P.g pts.d.pwW) : LonePts ρ P C p pts.d := by
  obtain ⟨u, Cu⟩ := pts_cut hp
  obtain ⟨q, U⟩ := UW u Cu.single
  have hlt := H.lt
  have nZ := Cu.nZ
  have lp := VerifiableInference.Desc.First.Att.P.lookPts_of Kp U
  have rd : ∀ j < P.D.lW, pt ρ (inner u (c.zk.getD u.call #[])) j = uW P.D C p.z j :=
    fun j hj => VerifiableInference.Desc.First.Att.P.inner_read Kp U j hj
  have hW : P.D.lW = 1 + P.D.lg + P.D.lT + P.D.ln := rfl
  have g2 : P.g.lgk = P.D.lg := rfl
  have g4 : P.g.ldh = P.D.ln := rfl
  refine ⟨Cu.nW, fun b hb => ?_, pr, ?_, fun k hk => ?_, ?_, fun k hk => ?_, ?_, fun k hk => ?_⟩
  · rw [Cu.pwW, pieces_wp]
    exact lp.hw b hb
  · rw [Cu.zgW, size_extract_le _ (by omega)]
    omega
  · rw [Cu.zgW, pt_extract ρ _ _ _ k (by omega)]
    exact lp.hg k hk
  · rw [Cu.ziW, size_extract_le _ (by omega)]
    omega
  · rw [Cu.ziW, pt_extract ρ _ _ _ k (by omega)]
    exact lp.hi k hk
  · rw [Cu.zcW, size_extract_le _ (by omega)]
    omega
  · rw [Cu.zcW, pt_extract ρ _ _ _ k (by omega), rd _ (by omega), g2, hlt]
    rfl

/-! ## The index's cells are bits -/

/-- **The sum of "the index's cells are bits" reads 0.** The statement names no challenges of the
library's: those made of the prover's are laid, at a made-up point of the lookup's. CONDITIONAL: see
the head. -/
theorem hb_zero {P : Pub5} (H : Sized P) (w : K5In) (Pl : Planned P) {c : Chal} (Dr : Drawn P c)
    (hK : P.D.lT ≤ 2 ^ 4) (A : AtIdn P.D (tOf ρ w)) : ρ.val (sHB P w c).total = 0 := by
  rw [sHB_total ρ H w Pl Dr hK (bitPts_pubOf ρ P c fun _ => 0)]
  exact bitSum_zero 4 A _

/-! ## The score at the index -/

/-- The named points on the maximum, where the verifier's function returns. -/
theorem maxOf_some {P : Pub5} {c : Chal} {pts : Pts} (hp : ptsOf P c = some pts) :
    maxOf P c = pts.x := by
  unfold maxOf
  rw [hp]
  rfl

/-- **What the row maxima read of the challenges**: two cuts of the round that draws many elements,
read, are the library's tg and ti. The batching element of the score at the index, which is drawn
behind the round that sends the maxima, is not among them. -/
structure MaxPts (ρ : Reading K) (P : Pub5) (c : Chal) (p : Pub K) : Prop where
  tg : ∀ k < P.D.lg, pt ρ (heardAt P c fun _ => none).point k = p.tg k
  ti : ∀ k < P.D.lT, pt ρ (heardAt P c fun _ => none).point (P.D.lg + k) = p.ti k

theorem IndexPts.max {P : Pub5} {c : Chal} {p : Pub K} (I : IndexPts ρ P c p) : MaxPts ρ P c p :=
  ⟨I.tg, I.ti⟩

/-- **The row maxima that are sent read as the library's.** -/
theorem m6_reads {P : Pub5} (H : Sized P) (w : K5In) {c : Chal} (Dr : Drawn P c) {pts : Pts}
    (hp : ptsOf P c = some pts) {p : Pub K} (I : MaxPts ρ P c p) {b : ℕ} (hb : b < P.D.nb) :
    ρ.val ((m6 P w c).getD b zeroE) = rvM6 P.D p (tOf ρ w) b := by
  obtain ⟨u, Cu⟩ := pts_cut hp
  have hpt := Dr.point
  have hs : 2 * P.D.lg + 2 * P.D.lT + 4 ≤ (heardAt P c fun _ => none).point.size := hpt
  have e : (m6 P w c).getD b zeroE = under (eqTab (maxOf P c).tg) fun hk =>
      under (eqTab (maxOf P c).ti) fun i => w.mx b hk i := by
    show ((List.range P.g.NP).map fun b => under (eqTab (maxOf P c).tg) fun hk =>
      under (eqTab (maxOf P c).ti) fun i => w.mx b hk i).getD b zeroE = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show b < P.g.NP from hb)]
    rfl
  rw [e, maxOf_some hp, Cu.tg, Cu.ti, H.lt]
  refine read_under2 ρ P.D (size_extract_le _ (by show P.D.lg ≤ _; omega)) (fun k hk => ?_) ?_
    (fun k hk => ?_) (fun g i => read_mx ρ w b g i)
  · rw [pt_extract ρ _ 0 _ k (by show 0 + k < P.D.lg; omega), Nat.zero_add]
    exact I.tg k hk
  · rw [size_extract_le _ (by show P.D.lg + P.D.lT ≤ _; omega)]
    show P.D.lg + P.D.lT - P.D.lg = P.D.lT
    omega
  · rw [pt_extract ρ _ _ _ k (by show P.D.lg + k < P.D.lg + P.D.lT; omega)]
    exact I.ti k hk

/-- **The sum of "the score at the index" reads as the batch of the row maxima that were sent.** c:
the challenges at which the sum is taken. c0: those at which the maxima were sent, in front of the
round that draws the batching element; both read as one p. The library's numbers of the lookup do
not enter step s16: made-up ones are laid. CONDITIONAL: see the head. -/
theorem sf_start {P : Pub5} (H : Sized P) (w : K5In) (Pl : Planned P) {c c0 : Chal}
    (Dr : Drawn P c) (Dr0 : Drawn P c0) {pts : Pts} (hp : ptsOf P c0 = some pts) {p : Pub K}
    (I : IndexPts ρ P c p) (I0 : MaxPts ρ P c0 p) (A : AtIdn P.D (tOf ρ w)) :
    ρ.val (sSF P w c).total = ∑ b ∈ range P.D.nb, p.o b * ρ.val ((m6 P w c0).getD b zeroE) := by
  rw [sSF_total ρ H w Pl Dr ⟨fun _ => 0, 0, 0⟩ I, score_start A]
  exact sum_congr rfl fun b hb => by rw [m6_reads ρ H w Dr0 hp I0 (mem_range.mp hb)]

/-! ## The denominator's scalar -/

/-- **The denominator's scalar reads as its rule value.** -/
theorem zc_reads {P : Pub5} (w : K5In) {C : Calls} {p : Pub K} {d : DivP}
    (L : LonePts ρ P C p d) : ρ.val (zcAt P.g w d) = rv P.D C p (tOf ρ w) .zc := by
  unfold zcAt atRow
  rw [read_overPieces, L.nW]
  refine sum_congr rfl fun b hb => ?_
  have hb' := mem_range.mp hb
  rw [L.hw b hb', show pairNo P.g (d.pwW.getD b ⟨0, 0, zeroE⟩) = b from L.pairs.pair hb']
  exact congrArg _ (read_under2 ρ P.D L.nG L.hg L.nI L.hi fun g i => read_zd ρ w b g i)

/-! ## The accumulator's scalar -/

/-- The values of layer lam at head g and token j, at the lookup's point on the channels. -/
def vAt (D : Dim) (C : Calls) (z : ℕ → K) (t : Raw → K) (lam g j : ℕ) : K :=
  conN D (yn D C z) fun n => valV t lam g j n

/-- **The library's accumulator at one pair and head, at the lookup's point, tile by tile**: the
tiles below the diagonal by their slots, then the tiles on it. Algebra on the library's definitions,
at all cells. -/
theorem acc_row (D : Dim) (C : Calls) (p : Pub K) (t : Raw → K) (b g : ℕ) :
    ∑ i ∈ range (2 ^ D.lT), Blocks.eqN D.lT 0 (yi D C p.z) i * conN D (yn D C p.z) (AC D t b g i) =
      (∑ P ∈ range D.hP, ∑ s ∈ range (D.nBlk - 1), ∑ i' ∈ range D.B,
        Blocks.eqN (D.lP + 1) 0 (yI D C p.z) (D.rowBlk P s) * Blocks.eqN D.lB 0 (yi' D C p.z) i' *
          ∑ j' ∈ range D.B, wtV t .M b (D.codeM g P s i' j') *
            vAt D C p.z t (D.lamOf b) g (D.B * D.colBlk P s + j')) +
      ∑ I ∈ range D.nBlk, ∑ i' ∈ range D.B,
        Blocks.eqN (D.lP + 1) 0 (yI D C p.z) I * Blocks.eqN D.lB 0 (yi' D C p.z) i' *
          ∑ j' ∈ range D.B, wtV t .D b (D.codeD g I i' j') *
            vAt D C p.z t (D.lamOf b) g (D.B * I + j') := by
  have e : ∀ i, conN D (yn D C p.z) (AC D t b g i) =
      Cb.Pv.Att.rowBelow D t (vAt D C p.z t (D.lamOf b) g) b g i +
        Cb.Pv.Att.rowOn D t (vAt D C p.z t (D.lamOf b) g) b g i := by
    intro i
    have l := Cb.Pv.Att.rowSum_lin D t b g i 0 (yn D C p.z) fun j n => valV t (D.lamOf b) g j n
    simp only [zero_mul, zero_add] at l
    exact l.symm
  simp only [e, mul_add, sum_add_distrib]
  congr 1
  · refine (Cb.Pv.Att.right11 D C p t (vAt D C p.z t (D.lamOf b) g) b g).trans ?_
    refine sum_congr rfl fun P _ => sum_congr rfl fun s _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun i' _ => by
      show _ * (_ * ∑ j' ∈ range D.B, wtV t .M b (D.codeM g P s i' j') *
        vAt D C p.z t (D.lamOf b) g (D.B * D.colBlk P s + j')) = _
      ring
  · rw [← Dim.T_eq, Cb.Pv.Att.sum_pos]
    refine sum_congr rfl fun I _ => sum_congr rfl fun i' hi' => ?_
    have h' := mem_range.mp hi'
    show eqT D (yi D C p.z) (D.B * I + i') * Cb.Pv.Att.rowOn D t _ b g (D.B * I + i') = _
    unfold Cb.Pv.Att.rowOn
    rw [Cb.Pv.Att.yi_split D C p I h', (Cb.Pv.Att.pos_parts D h').1,
      (Cb.Pv.Att.pos_parts D h').2]

/-- A sum over a tile's places, the key's outside, turned into the query's outside. -/
theorem swap_tile (n : ℕ) (A c : ℕ → K) (W : ℕ → ℕ → K) :
    ∑ jl ∈ range n, A jl * ∑ il ∈ range n, c il * W il jl =
      ∑ il ∈ range n, c il * ∑ jl ∈ range n, W il jl * A jl := by
  simp only [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

/-- **One tile's share**, read. -/
theorem read_tileSum {P : Pub5} (H : Sized P) (w : K5In) {C : Calls} {p : Pub K} {d : DivP}
    (L : LonePts ρ P C p d) (onDiag : Bool) (pc : W1) (hk : ℕ) {I : ℕ} (hI : I < P.D.nBlk)
    (J : ℕ) (idx : ℕ → ℕ → ℕ) :
    ρ.val (tileSum P.g w (eqTab d.ziW) (eqTab d.zcW) onDiag pc hk I J idx) =
      ∑ il ∈ range P.D.B,
        Blocks.eqN (P.D.lP + 1) 0 (yI P.D C p.z) I * Blocks.eqN P.D.lB 0 (yi' P.D C p.z) il *
          ∑ jl ∈ range P.D.B, wtV (tOf ρ w) (regOf onDiag) (pairNo P.g pc) (idx il jl) *
            vAt P.D C p.z (tOf ρ w) pc.lam hk (P.D.B * J + jl) := by
  have hB : P.g.B = P.D.B := H.Z.B
  rw [← swap_tile]
  unfold tileSum
  rw [hB, read_sumTo]
  refine sum_congr rfl fun jl _ => ?_
  rw [ρ.mul, read_under_eq ρ L.nC L.hn, read_sumTo]
  refine congrArg₂ (· * ·) ?_ (sum_congr rfl fun il hil => ?_)
  · rw [Nat.mul_comm J]
    exact sum_congr rfl fun n _ => by rw [read_v]
  · have hil' : il < 2 ^ P.D.lB := mem_range.mp hil
    have hlt : I * P.D.B + il < 2 ^ P.D.lT := by
      rw [← Dim.T_eq]
      show I * P.D.B + il < P.D.nBlk * P.D.B
      calc I * P.D.B + il < I * P.D.B + P.D.B := Nat.add_lt_add_left hil' _
        _ = (I + 1) * P.D.B := by ring
        _ ≤ P.D.nBlk * P.D.B := Nat.mul_le_mul_right _ hI
    rw [ρ.mul, read_ew, read_eqTab ρ L.nI L.hi hlt]
    exact congrArg (· * _) (Cb.Pv.Att.yi_cut P.D C p I hil')

/-- **The accumulator's scalar reads as its rule value.** The prover's sum runs over the tiles by
their slots, the slot that stands for no tile left out, as the library's sum over a row does. -/
theorem acc_reads {P : Pub5} (H : Sized P) (w : K5In) {C : Calls} {p : Pub K} {d : DivP}
    (L : LonePts ρ P C p d) : ρ.val (accAt P.g w d) = rv P.D C p (tOf ρ w) .acc := by
  have hB : P.g.B = P.D.B := H.Z.B
  have hhP : P.g.hP = P.D.hP := OnBytes.Road.Rows.dim_hP H.Z
  have hnT : P.g.nT = P.D.nBlk := OnBytes.Road.Rows.dim_nBlk H.Z
  unfold accAt
  rw [read_overPieces, L.nW]
  show _ = ∑ b ∈ range P.D.nb, wp P.D C p.z .w3 b * atY P.D C p (AC P.D (tOf ρ w) b)
  refine sum_congr rfl fun b hb => ?_
  have hb' := mem_range.mp hb
  have hlam : (d.pwW.getD b ⟨0, 0, zeroE⟩).lam = P.D.lamOf b := lam_of L.pairs hb'
  have hpair : pairNo P.g (d.pwW.getD b ⟨0, 0, zeroE⟩) = b := L.pairs.pair hb'
  rw [L.hw b hb', Cb.Pv.Att.atY_rd2]
  refine congrArg _ ?_
  rw [read_under_eq ρ L.nG L.hg]
  unfold rd2 eqT
  rw [Dim.T_eq]
  refine sum_congr rfl fun g _ => ?_
  have s : ∑ i ∈ range (2 ^ P.D.lT), Blocks.eqN P.D.lg 0 (yg P.D C p.z) g *
        Blocks.eqN P.D.lT 0 (yi P.D C p.z) i * conN P.D (yn P.D C p.z) (AC P.D (tOf ρ w) b g i) =
      Blocks.eqN P.D.lg 0 (yg P.D C p.z) g * ∑ i ∈ range (2 ^ P.D.lT),
        Blocks.eqN P.D.lT 0 (yi P.D C p.z) i *
          conN P.D (yn P.D C p.z) (AC P.D (tOf ρ w) b g i) := by
    rw [mul_sum]
    exact sum_congr rfl fun i _ => by ring
  rw [s, acc_row, ρ.add]
  refine congrArg _ (congrArg₂ (· + ·) ?_ ?_)
  · rw [read_sumTo, hhP]
    refine sum_congr rfl fun Pq hPq => ?_
    rw [read_sumTo, hnT]
    refine sum_congr rfl fun s hs => ?_
    have hblk := P.D.blk_of_slot (mem_range.mp hPq) (mem_range.mp hs)
    have hc : cover P.D.nBlk Pq s = (P.D.rowBlk Pq s, P.D.colBlk Pq s) := by
      unfold cover Dim.rowBlk Dim.colBlk
      split_ifs <;> rfl
    show ρ.val (tileSum P.g w _ _ false _ g (cover P.D.nBlk Pq s).1 (cover P.D.nBlk Pq s).2
      (idxM P.g g Pq s)) = _
    rw [hc, read_tileSum ρ H w L false _ g hblk.2.1, hlam, hpair]
    refine sum_congr rfl fun il _ => congrArg _ (sum_congr rfl fun jl _ => ?_)
    unfold idxM
    rw [hhP, hnT, hB]
    rfl
  · rw [read_sumTo, hnT]
    refine sum_congr rfl fun I hI => ?_
    rw [read_tileSum ρ H w L true _ g (mem_range.mp hI), hlam, hpair]
    refine sum_congr rfl fun il _ => congrArg _ (sum_congr rfl fun jl _ => ?_)
    unfold idxD
    rw [hnT, hB]
    rfl

/-! ## The equation of the value product -/

/-- **The equation of the value product, from the four readings.** SM, SD: any two summands that
read as the library's steps s11 and s12; acc, zc: any two elements that read as the accumulator's
and the denominator's rule values; all at one p. -/
theorem claim6_of_reads {SM SD : Summand} {D : Dim} {C : Calls} {p : Pub K} {t : Raw → K}
    (RM : StepReads ρ SM D C p t .s11) (RD : StepReads ρ SD D C p t .s12) {acc zc : E}
    (ha : ρ.val acc = rv D C p t .acc) (hz : ρ.val zc = rv D C p t .zc)
    (hR : Rider D C p.z t) :
    ρ.val SM.total + ρ.val SD.total - ρ.val acc - p.th * ρ.val zc = 0 := by
  rw [RM.total, RD.total, ha, hz]
  exact valueProduct_zero hR

/-- A value at the division's points, where the verifier's function returns. -/
theorem ofDiv_some {P : Pub5} {c : Chal} {pts : Pts} (hp : ptsOf P c = some pts) (f : DivP → E) :
    ofDiv P c f = f pts.d := by
  unfold ofDiv
  rw [hp]
  rfl

/-- **The equation of the value product**, of the four values at one list of challenges: the two
sums, less the accumulator's scalar, less the batching element times the denominator's scalar, read
0. CONDITIONAL: see the head. -/
theorem claim6_zero {P : Pub5} (H : Sized P) (w : K5In) (Pl : Planned P) {c : Chal} {Dv : DivIn}
    (h : divIn P c = some Dv) {C : Calls} {p : Pub K} (R : DivPts ρ P C p Dv)
    (L : LonePts ρ P C p Dv.d) (A : AtIdn P.D (tOf ρ w)) :
    ρ.val (sVM P w c).total + ρ.val (sVD P w c).total - ρ.val (accV P w c) -
      p.th * ρ.val (zcV P w c) = 0 := by
  obtain ⟨pts, _, hp, _, ed, _⟩ := divIn_spec h
  refine claim6_of_reads ρ (sVM_reads ρ w H Pl h R L.pairs) (sVD_reads ρ H w Pl h R L.pairs) ?_ ?_
    (A.rider C p.z)
  · unfold accV
    rw [ofDiv_some hp, ← ed]
    exact acc_reads ρ H w L
  · unfold zcV
    rw [ofDiv_some hp, ← ed]
    exact zc_reads ρ w L

/-- **The equation of the value product, of the values as they are sent**: c: the challenges at
which the two sums are taken; c0: those at which the accumulator's and the denominator's scalars
were sent, in front of the round that draws the batching element; both read as one p. CONDITIONAL:
see the head. -/
theorem claim6_fronts {P : Pub5} (H : Sized P) (w : K5In) (Pl : Planned P) {c c0 : Chal}
    {Dv : DivIn} (h : divIn P c = some Dv) {pts0 : Pts} (hp0 : ptsOf P c0 = some pts0) {C : Calls}
    {p : Pub K} (R : DivPts ρ P C p Dv) (pr : PairsAre P.g Dv.d.pwW)
    (L0 : LonePts ρ P C p pts0.d) (A : AtIdn P.D (tOf ρ w)) :
    ρ.val (sVM P w c).total + ρ.val (sVD P w c).total - ρ.val (accV P w c0) -
      p.th * ρ.val (zcV P w c0) = 0 := by
  refine claim6_of_reads ρ (sVM_reads ρ w H Pl h R pr) (sVD_reads ρ H w Pl h R pr) ?_ ?_
    (A.rider C p.z)
  · unfold accV
    rw [ofDiv_some hp0]
    exact acc_reads ρ H w L0
  · unfold zcV
    rw [ofDiv_some hp0]
    exact zc_reads ρ w L0

end H2K5.Honest

#print axioms H2K5.Honest.read_overPieces
#print axioms H2K5.Honest.read_under2
#print axioms H2K5.Honest.pieces_eq
#print axioms H2K5.Honest.pieces_wp
#print axioms H2K5.Honest.lonePts_of
#print axioms H2K5.Honest.hb_zero
#print axioms H2K5.Honest.maxOf_some
#print axioms H2K5.Honest.IndexPts.max
#print axioms H2K5.Honest.m6_reads
#print axioms H2K5.Honest.sf_start
#print axioms H2K5.Honest.zc_reads
#print axioms H2K5.Honest.acc_row
#print axioms H2K5.Honest.swap_tile
#print axioms H2K5.Honest.read_tileSum
#print axioms H2K5.Honest.acc_reads
#print axioms H2K5.Honest.claim6_of_reads
#print axioms H2K5.Honest.ofDiv_some
#print axioms H2K5.Honest.claim6_zero
#print axioms H2K5.Honest.claim6_fronts
