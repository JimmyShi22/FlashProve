-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/TilesKit.lean: the honest prover's side of an attention segment's own
rounds: the sums over heads, tokens and channels, the weights on tiles and tokens, and the softmax
weight at a point of its region, READ IN A FIELD, are the library's. Statements with their proofs,
two definitions of premises, and names for two pieces of a summand's text.

rho is any reading (OnBytes/Model/HideLaws.lean): a map from the program's elements to a field that
takes 0, 1, sums, differences and products to the field's. The library is Inst/Model/Att. The points
are any points: no coordinate is asked to be 0 or 1.

Main names:
  `last_size`, `pt_last`    the last coordinates of a point
  `pt_append`               two points laid in a row
  `read_rd3`                a sum over heads, tokens and channels is the library's read `rd3`
  `tiles_fst`, `tiles_snd`  the weights of the tile rows and of the tile columns, made of two cuts
                            of a point, are the library's `blkRow`, `blkCol`
  `tok_reads`               the tokens' weights, made of weights on tiles and a point in the tile
  `read_planeAt`, `read_weightAt`
                            a plane, and the softmax weight, at a point of the region: the
                            multilinear extension of the cells over the region's entries
  `lam_of`                  where piece number b is pair number b, its layer is the library's
  `UnitReads`               the premises on a softmax-table unit's named points
  `UnitPlace`               the premises on the place at a softmax-table unit
  `unitA`, `unitB`, `sK_eq` names for the two hidden maps of a softmax-table unit's summand

Limits. Every statement with a premise is conditional on it. `Sized` (Law/Cells.lean) speaks of the
planner's shape alone. `UnitReads` ties two cuts of a lookup call's key point to the library's
points: who calls a lemma here has to show it (for the points that the verifier's text makes,
Johnson/Desc/First/Att/Claims/PointsTieU.lean has such ties under its own premises). `UnitPlace`
says that the place has the unit, that the verifier's function of the points returns, and that the
plan's numbers are the library's. By Law/UnitPts.lean's Limits, `UnitPlace`'s clause `np` (a piece
for each pair) fails at a plan whose group has layers of more than one shift. No property is claimed
by a definition.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Law.Cells
import Cb.Pv.Att.Mean.ReadsTiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading)
open OnBytes.Road (pt)
open VerifiableInference.Desc.First.Att.P (Geo W1 ScoreP DivP UnitG geoOf eqTab ofNat tok tileSums
  lastCoords scoreTiles scoreW inner)
open Inst.Model.AttSeg
open Finset

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## The last coordinates of a point -/

theorem last_size (z : Array E) {n : ℕ} (hn : n ≤ z.size) : (lastCoords z n).size = n := by
  unfold lastCoords
  rw [size_extract_le z (Nat.le_refl _)]
  omega

/-- A coordinate of the last n. -/
theorem pt_last (z : Array E) {n j : ℕ} (hn : n ≤ z.size) (hj : j < n) :
    pt ρ (lastCoords z n) j = pt ρ z (z.size - n + j) := by
  unfold lastCoords
  exact pt_extract ρ z _ _ j (by omega)

/-- A coordinate of two points laid in a row. -/
theorem pt_append (a b : Array E) (j : ℕ) :
    pt ρ (a ++ b) j = if j < a.size then pt ρ a j else pt ρ b (j - a.size) := by
  unfold pt
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_append]
  split <;> rfl

/-! ## A sum over heads, tokens and channels -/

/-- **A sum over heads, tokens and channels is the library's read.** vg: a point that agrees with
the first coordinates of r. Psi: the tokens' weights, read. vn: a point that agrees with the channel
point zc. a: the summed values, read. -/
theorem read_rd3 {P : Pub5} (H : Sized P) {r tk zc : Array E} {vg Ψ vn : ℕ → K}
    {a : ℕ → ℕ → ℕ → K} {f : ℕ → ℕ → ℕ → E} (hr : P.D.lg ≤ r.size)
    (hg : ∀ k < P.D.lg, pt ρ r k = vg k) (ht : tk.size = P.D.T)
    (hΨ : ∀ i < P.D.T, ρ.val (tk.getD i zeroE) = Ψ i) (hc : zc.size = P.D.ln)
    (hn : ∀ k < P.D.ln, pt ρ zc k = vn k)
    (hf : ∀ g < P.D.nG, ∀ i < P.D.T, ∀ n < P.D.ch, ρ.val (f g i n) = a g i n) :
    ρ.val (overHeads P.g r fun hk => atTokens tk (eqTab zc) fun i n => f hk i n) =
      rd3 P.D vg Ψ vn a := by
  rw [read_overHeads, H.G]
  unfold rd3
  refine sum_congr rfl fun g hg' => ?_
  rw [read_atTokens, ht, size_eqTab, hc, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun n hn' => ?_
  rw [read_eqTab ρ (n := P.D.lg) (size_extract_le r hr) (v := vg)
      (fun j hj => by
        rw [pt_extract ρ r 0 _ j (by show 0 + j < P.D.lg; omega), Nat.zero_add]
        exact hg j hj)
      (mem_range.mp hg'), hΨ i (mem_range.mp hi), read_eqTab ρ hc hn (mem_range.mp hn'),
    hf g (mem_range.mp hg') i (mem_range.mp hi) n (mem_range.mp hn')]
  ring

/-! ## Weights on tiles and tokens -/

/-- **The weights of the tile rows**, made of the cuts [a, b) and [b, c) of a point r, which are its
coordinates of the slot row and of the tile slot: the library's weights of the row blocks. -/
theorem tiles_fst {P : Pub5} (H : Sized P) {r : Array E} {a b c : ℕ} (ha : a = P.D.lg)
    (hb : b = P.D.lg + P.D.lP) (hc : c = P.D.lg + P.D.lP + (P.D.lP + 1)) (hr : c ≤ r.size) {I : ℕ}
    (hI : I < P.D.nBlk) :
    ρ.val ((tileSums P.g (eqTab (r.extract a b)) (eqTab (r.extract b c))).1.getD I zeroE) =
      blkRow P.D (sh (pt ρ r) P.D.lg) (sh (pt ρ r) (P.D.lg + P.D.lP)) I := by
  subst ha hb hc
  have hl : P.S.lnT = P.D.lP + 1 := H.lnT
  refine OnBytes.Road.Rows.tiles_row ρ H.Z (zP := r.extract P.D.lg (P.D.lg + P.D.lP))
    (zs := r.extract (P.D.lg + P.D.lP) (P.D.lg + P.D.lP + (P.D.lP + 1))) ?_ ?_ ?_ ?_ ?_
  · rw [size_extract_le r (by omega)]
    show P.D.lg + P.D.lP - P.D.lg = P.D.lP
    omega
  · rw [size_extract_le r hr, hl]
    omega
  · exact fun j hj => pt_extract ρ r _ _ j (Nat.add_lt_add_left hj _)
  · exact fun j hj => pt_extract ρ r _ _ j (by omega)
  · rw [OnBytes.Road.Rows.dim_nBlk H.Z]
    exact hI

/-- **The weights of the tile columns**: the library's weights of the column blocks. -/
theorem tiles_snd {P : Pub5} (H : Sized P) {r : Array E} {a b c : ℕ} (ha : a = P.D.lg)
    (hb : b = P.D.lg + P.D.lP) (hc : c = P.D.lg + P.D.lP + (P.D.lP + 1)) (hr : c ≤ r.size) {J : ℕ}
    (hJ : J < P.D.nBlk) :
    ρ.val ((tileSums P.g (eqTab (r.extract a b)) (eqTab (r.extract b c))).2.getD J zeroE) =
      blkCol P.D (sh (pt ρ r) P.D.lg) (sh (pt ρ r) (P.D.lg + P.D.lP)) J := by
  subst ha hb hc
  have hl : P.S.lnT = P.D.lP + 1 := H.lnT
  refine OnBytes.Road.Rows.tiles_col ρ H.Z (zP := r.extract P.D.lg (P.D.lg + P.D.lP))
    (zs := r.extract (P.D.lg + P.D.lP) (P.D.lg + P.D.lP + (P.D.lP + 1))) ?_ ?_ ?_ ?_ ?_
  · rw [size_extract_le r (by omega)]
    show P.D.lg + P.D.lP - P.D.lg = P.D.lP
    omega
  · rw [size_extract_le r hr, hl]
    omega
  · exact fun j hj => pt_extract ρ r _ _ j (Nat.add_lt_add_left hj _)
  · exact fun j hj => pt_extract ρ r _ _ j (by omega)
  · rw [OnBytes.Road.Rows.dim_nBlk H.Z]
    exact hJ

/-- **The weights of the tokens**, made of weights hi on the tiles, which read as wt, and a point lo
in the tile, which agrees with v. -/
theorem tok_reads {P : Pub5} (H : Sized P) {hi lo : Array E} {wt v : ℕ → K}
    (hhi : ∀ I < P.D.nBlk, ρ.val (hi.getD I zeroE) = wt I) (hlo : lo.size = P.D.lB)
    (hv : ∀ j < P.D.lB, pt ρ lo j = v j) :
    (tok P.g hi lo).size = P.D.T ∧ ∀ i < P.D.T, ρ.val ((tok P.g hi lo).getD i zeroE) =
      Blocks.eqN P.D.lB 0 v (i % P.D.B) * wt (i / P.D.B) :=
  ⟨(OnBytes.Road.Rows.tok_size P.S hi lo).trans H.T, fun _ hi' =>
    OnBytes.Road.Rows.tok_psi ρ H.Z H.T.symm
      (fun I hI => hhi I (by rw [← OnBytes.Road.Rows.dim_nBlk H.Z]; exact hI)) hlo hv hi'⟩

/-! ## Planes and the softmax weight at a point of the region -/

/-- **A plane at a point of its region**: the multilinear extension of the plane's cells over the
region's entries. -/
theorem read_planeAt (w : K5In) (onDiag : Bool) (z : Array E) (x b : ℕ) :
    ρ.val (planeAt w onDiag (eqTab z) x b) =
      Blocks.ext z.size (fun n => tOf ρ w (.c (regOf onDiag) x b n)) (pt ρ z) := by
  unfold planeAt Blocks.ext
  rw [read_underN_eq ρ rfl fun _ _ => rfl]
  exact sum_congr rfl fun n _ => by rw [read_c]

/-- **The softmax weight at a point of its region**: the multilinear extension of the library's
array of softmax weights over the region's entries. The 128 that the prover adds once is the
extension of the 128 that the library adds at every entry. -/
theorem read_weightAt (w : K5In) (onDiag : Bool) (z : Array E) (b : ℕ) :
    ρ.val (weightAt w onDiag z b) =
      Blocks.ext z.size (wtV (tOf ρ w) (regOf onDiag) b) (pt ρ z) := by
  have e : wtV (tOf ρ w) (regOf onDiag) b = fun n =>
      (tOf ρ w (.c (regOf onDiag) 3 b n) + 128) + 256 * tOf ρ w (.c (regOf onDiag) 4 b n) := rfl
  rw [e, Blocks.ext_add, Blocks.ext_add, Blocks.ext_const, Blocks.ext_smul]
  unfold weightAt
  dsimp only
  rw [ρ.add, ρ.add, ρ.mul, read_planeAt, read_planeAt, read_ofNat, read_ofNat]
  push_cast
  ring

/-! ## Pieces and pairs -/

/-- The piece's layer is the library's layer of the pair. -/
theorem lam_of {P : Pub5} {pw : Array W1} (h : PairsAre P.g pw) {b : ℕ} (hb : b < P.D.nb) :
    (pw.getD b ⟨0, 0, zeroE⟩).lam = P.D.lamOf b := (h b hb).1

/-- **The premises on a softmax-table unit's named points**: the query's and the key's place in a
tile are the library's two points of that name, and piece number b is pair number b. -/
structure UnitReads (P : Pub5) (C : Calls) (z : ℕ → K) (k : ScoreP) : Prop where
  si : k.zi.size = P.D.lB
  i : ∀ j < P.D.lB, pt ρ k.zi j = zi' P.D C z j
  sj : k.zj.size = P.D.lB
  j : ∀ j < P.D.lB, pt ρ k.zj j = zj' P.D C z j
  pairs : PairsAre P.g k.pw

/-! ## The two hidden maps of a softmax-table unit, under names -/

/-- The first hidden map of a softmax-table unit, piece b, at the point r: the queries. The text of
`sK` (Johnson/Desc/K5/Honest/Products.lean). -/
def unitA (g : Geo) (w : K5In) (k : ScoreP) (r : Array E) (b : ℕ) : E :=
  overHeads g r fun hk =>
    atTokens (tok g (scoreTiles g { k with sc := { k.sc with r := r } }).1 k.zi)
      (eqTab (lastCoords r g.ldh)) fun pos ch =>
        w.q (pairOf g (k.pw.getD b ⟨0, 0, zeroE⟩)) hk pos ch

/-- The second: the keys. -/
def unitB (g : Geo) (w : K5In) (k : ScoreP) (r : Array E) (b : ℕ) : E :=
  overHeads g r fun hk =>
    atTokens (tok g (scoreTiles g { k with sc := { k.sc with r := r } }).2 k.zj)
      (eqTab (lastCoords r g.ldh)) fun pos ch => w.kx (k.pw.getD b ⟨0, 0, zeroE⟩).lam hk pos ch

/-- Where the place has the unit and the verifier's function returns its points, the summand is the
sum of products of these two maps. -/
theorem sK_eq (P : Pub5) (w : K5In) (c : Chal) {i : ℕ} {u : UnitG} {k : ScoreP}
    (hu : P.g.scores[i]? = some u) (hk : (ptsOf P c).bind (·.scores[i]?) = some k) :
    sK P w c i = ofProducts ((cut P.x).getD i 3 - 3) u.pcs.length
      (fun r => (scoreW P.g u (c.zk.getD u.call #[]) r).getD #[]) (unitA P.g w k)
      (unitB P.g w k) := by
  unfold sK
  simp only [hu, hk, Option.map_some, Option.getD_some]
  rfl

/-- **The premises on the place at the softmax-table unit number i**; s: the library's step. The
place has the unit u; the verifier's function of the points returns, with the points k for this
unit, which bear the unit's flag; the unit's inner point has the length n; the sumcheck has the
step's number of variables; the unit has a piece for each pair. The first, the fifth and the sixth
are public. Law/UnitPts.lean draws the third from the first two, and the fourth and the sixth from
its own premises; the first, the second and the fifth are left to the caller. -/
structure UnitPlace (P : Pub5) (c : Chal) (i : ℕ) (u : UnitG) (k : ScoreP) (s : Step) (n : ℕ) :
    Prop where
  unit : P.g.scores[i]? = some u
  pts : (ptsOf P c).bind (·.scores[i]?) = some k
  flag : k.below = u.below
  size : (inner u (c.zk.getD u.call #[])).size = n
  vars : (cut P.x).getD i 3 - 3 = s.g P.D
  np : u.pcs.length = P.D.nb

end H2K5.Honest

#print axioms H2K5.Honest.last_size
#print axioms H2K5.Honest.pt_last
#print axioms H2K5.Honest.read_rd3
#print axioms H2K5.Honest.tiles_fst
#print axioms H2K5.Honest.tiles_snd
#print axioms H2K5.Honest.tok_reads
#print axioms H2K5.Honest.read_planeAt
#print axioms H2K5.Honest.read_weightAt
#print axioms H2K5.Honest.pt_append
#print axioms H2K5.Honest.sK_eq
#print axioms H2K5.Honest.lam_of
