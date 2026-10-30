-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/Cells.lean: the honest prover's side of an attention segment's own
rounds: its readers of cells, its tables of equality weights, its cube and its challenges, READ IN A
FIELD, are the library's. Definitions, and statements with their proofs.

rho is any reading (OnBytes/Model/HideLaws.lean): a map from the program's elements to a field that
takes 0, 1, sums, differences and products to the field's. The library is Inst/Model/Att: the trace
of an attention segment (Trace.lean) and its sumchecks' summands (Sums.lean).

Main names:
  `tOf`           the cells, read: a trace in the library's sense
  `read_q`, `read_o`, `read_kx`, `read_v`, `read_zd`, `read_mx`, `read_ibit`, `read_rh`,
  `read_rhp`, `read_c`, `read_ew`, and all eleven in one: `cells_are`
                  each reader of Johnson/Desc/K5/Honest/Faces.lean is the library's array at `tOf`
                  (`rh`, `rhp`: that array less 128; `c`: a cell of `tOf` itself)
  `Sized`         the premise on the shape's numbers; what follows of it: `Sized.lt` .. `Sized.T`;
                  `sized_of_hid`: it holds of what the planner of shapes returns
  `PairsAre`, `PairsAre.pair`   the premise "piece number b is pair number b"
  `read_eqTab`, `size_eqTab`, `read_under_eq`, `read_underN_eq`
                  a table of equality weights, and a sum under one
  `pt_extract`, `size_extract_le`, `read_eqTab_cut`   a cut of a point, and its table
  `read_rd2`      a sum over heads and tokens is the library's read `rd2`
  `vertex`, `cube_eq`, `vertex_length`, `vertex_reads`, `pt_vertex`, `pt_vertex_eq`,
  `sum_list_range`, `sum_cube`
                  the cube of Johnson/Desc/K5/Honest/Terms.lean lists the library's vertices
  `chal_sumAt`    a sumcheck of which only the challenges are laid gives these challenges back
  `pubOf`         the library's challenges (`Pub`), made of the prover's challenges so far, read
  `getD_range_map`  an entry of an array that is made once

Limits. Every statement with a premise is conditional on it. `Sized` and `PairsAre` are public:
they speak of the planner's shape and of a unit's pieces; who calls a lemma here has to show them
of the place. `pubOf` takes the
lookup's end point z as a letter: nothing here ties z to the key points. A challenge that has not
been heard reads as 0, so `pubOf` has a meaning only for the fields whose rounds lie in front.
No property is claimed by a definition.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Law.Read
import Johnson.Desc.K5.Honest.Index
import Johnson.Road.Rows.AttEnds14Tiles
import Cb.Pv.Att.Mean.BitsScore

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading)
open OnBytes.Road (pt)
open VerifiableInference.Desc.First.Att.P (Geo geoOf eqTab ofNat chal W1)
open Inst.Model.AttSeg
open Finset

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## The cells -/

/-- **The cells, read**: a trace in the library's sense. -/
def tOf (w : K5In) : Raw → K := fun q => ρ.val (w.cell q)

/-- The region of a flag. -/
def regOf (onDiag : Bool) : Reg := if onDiag then .D else .M

variable (w : K5In)

theorem read_q (b g i n : ℕ) : ρ.val (w.q b g i n) = qryV (tOf ρ w) b g i n :=
  read_limbs ρ 2 _

theorem read_o (b g i n : ℕ) : ρ.val (w.o b g i n) = outV (tOf ρ w) b g i n :=
  read_limbs ρ 2 _

theorem read_kx (lam g j n : ℕ) : ρ.val (w.kx lam g j n) = keyV (tOf ρ w) lam g j n :=
  read_limbs ρ 2 _

theorem read_v (lam g j n : ℕ) : ρ.val (w.v lam g j n) = valV (tOf ρ w) lam g j n :=
  read_limbs ρ 2 _

theorem read_zd (b g i : ℕ) : ρ.val (w.zd b g i) = denV (tOf ρ w) b g i :=
  read_limbs ρ 4 _

theorem read_mx (b g i : ℕ) : ρ.val (w.mx b g i) = mxV (tOf ρ w) b g i :=
  read_limbs ρ 4 _

theorem read_ibit (k b g i : ℕ) : ρ.val (w.ibit k b g i) = ibV (tOf ρ w) k b g i := rfl

/-- The library's array has the 128 added that the cell lacks. -/
theorem read_rh (b g i n : ℕ) : ρ.val (w.rh b g i n) = qhV (tOf ρ w) b g i n - 128 := by
  unfold qhV
  rw [add_sub_cancel_right]
  rfl

theorem read_rhp (b g i n : ℕ) : ρ.val (w.rhp b g i n) = qhV' (tOf ρ w) b g i n - 128 := by
  unfold qhV'
  rw [add_sub_cancel_right]
  rfl

theorem read_c (onDiag : Bool) (x b n : ℕ) :
    ρ.val (w.c onDiag x b n) = tOf ρ w (.c (regOf onDiag) x b n) := rfl

/-- A number, read. -/
theorem read_ofNat (n : ℕ) : ρ.val (ofNat n) = (n : K) := Fo.ofNat_val ρ n

theorem read_ew (onDiag : Bool) (b n : ℕ) :
    ρ.val (w.ew onDiag b n) = wtV (tOf ρ w) (regOf onDiag) b n := by
  unfold K5In.ew wtV w0 w1
  rw [ρ.add, ρ.add, ρ.mul, read_ofNat, read_ofNat, read_c, read_c]
  norm_num

/-- **The eleven readers of cells, read, are the library's arrays at the cells, read**; two of them
less 128, and one is a cell itself. -/
theorem cells_are :
    (∀ b g i n, ρ.val (w.q b g i n) = qryV (tOf ρ w) b g i n) ∧
    (∀ b g i n, ρ.val (w.o b g i n) = outV (tOf ρ w) b g i n) ∧
    (∀ lam g j n, ρ.val (w.kx lam g j n) = keyV (tOf ρ w) lam g j n) ∧
    (∀ lam g j n, ρ.val (w.v lam g j n) = valV (tOf ρ w) lam g j n) ∧
    (∀ b g i, ρ.val (w.zd b g i) = denV (tOf ρ w) b g i) ∧
    (∀ b g i, ρ.val (w.mx b g i) = mxV (tOf ρ w) b g i) ∧
    (∀ k b g i, ρ.val (w.ibit k b g i) = ibV (tOf ρ w) k b g i) ∧
    (∀ b g i n, ρ.val (w.rh b g i n) = qhV (tOf ρ w) b g i n - 128) ∧
    (∀ b g i n, ρ.val (w.rhp b g i n) = qhV' (tOf ρ w) b g i n - 128) ∧
    (∀ onDiag x b n, ρ.val (w.c onDiag x b n) = tOf ρ w (.c (regOf onDiag) x b n)) ∧
    (∀ onDiag b n, ρ.val (w.ew onDiag b n) = wtV (tOf ρ w) (regOf onDiag) b n) :=
  ⟨read_q ρ w, read_o ρ w, read_kx ρ w, read_v ρ w, read_zd ρ w, read_mx ρ w, read_ibit ρ w,
    read_rh ρ w, read_rhp ρ w, read_c ρ w, read_ew ρ w⟩

/-! ## The shape's numbers -/

/-- The library's sizes at the place. -/
abbrev Pub5.D (P : Pub5) : Dim := OnBytes.Road.L5.dimOf P.S

/-- **The premise on the shape's numbers**: the library's equations on a shape, and that a token has
the bits of a tile and of a place in a tile. Public. -/
structure Sized (P : Pub5) : Prop where
  Z : OnBytes.Road.Rows.Sizes P.S
  tok : P.S.cf.lt = P.S.lnT + P.S.cf.lB

namespace Sized
variable {P : Pub5} (H : Sized P)
include H

theorem lnT : P.g.lnT = P.D.lP + 1 := by
  have := H.Z.lnT
  show P.S.lnT = P.S.lnT - 1 + 1
  omega

theorem lt : P.g.lt = P.D.lT := by
  have := H.Z.lnT
  have := H.tok
  show P.S.cf.lt = P.S.lnT - 1 + 1 + P.S.cf.lB
  omega

omit H in
theorem lgk : P.g.lgk = P.D.lg := rfl
omit H in
theorem ldh : P.g.ldh = P.D.ln := rfl
omit H in
theorem lB : P.g.lB = P.D.lB := rfl
omit H in
theorem HA : P.g.HA = P.D.na := rfl
omit H in
theorem Lam : P.g.Lam = P.D.nl := rfl
omit H in
theorem NP : P.g.NP = P.D.nb := rfl

theorem G : P.g.G = P.D.nG := H.Z.G

theorem T : P.g.T = P.D.T := by
  rw [Dim.T_eq, ← H.lt]
  exact H.Z.T

end Sized

/-- The premise holds of every shape that the verifier's planner of shapes returns. -/
theorem sized_of_hid {P : Pub5} {lid : ℕ} {cf : OnBytes.Attention.Cfg}
    {fs : OnBytes.Model.Forest.Shape}
    (h : OnBytes.Attention.shapeHid lid cf = Except.ok (P.S, fs)) : Sized P := by
  have Z := OnBytes.Road.Rows.sizes_of_hid h
  have e := (OnBytes.Road.Rows.norm_of_hid h).lt
  have l := Z.lnT
  exact ⟨Z, by omega⟩

/-- **Piece number b is pair number b**: its layer is b / HA and its head b % HA. Public: it holds
of a unit whose call holds all pairs. It follows from this library's `PiecesAll`
(Johnson/Road/Rows/AttRead.lean), which speaks of the same pieces in another type. -/
def PairsAre (g : Geo) (pw : Array W1) : Prop :=
  ∀ b < g.NP, (pw.getD b ⟨0, 0, zeroE⟩).lam = b / g.HA ∧ (pw.getD b ⟨0, 0, zeroE⟩).a = b % g.HA

/-- Under it a piece's pair has the piece's number. -/
theorem PairsAre.pair {g : Geo} {pw : Array W1} (h : PairsAre g pw) {b : ℕ} (hb : b < g.NP) :
    pairOf g (pw.getD b ⟨0, 0, zeroE⟩) = b := by
  unfold pairOf
  rw [(h b hb).1, (h b hb).2]
  exact Nat.div_add_mod' b g.HA

/-! ## Tables of equality weights -/

theorem size_eqTab (z : Array E) : (eqTab z).size = 2 ^ z.size := OnBytes.Road.eqTab_size z

/-- An entry of a table of equality weights, at a point that agrees with v. -/
theorem read_eqTab {z : Array E} {n : ℕ} (hz : z.size = n) {v : ℕ → K}
    (hv : ∀ j < n, pt ρ z j = v j) {c : ℕ} (hc : c < 2 ^ n) :
    ρ.val ((eqTab z).getD c zeroE) = Blocks.eqN n 0 v c :=
  OnBytes.Road.Rows.eqTab_at ρ hz hv hc

/-- A sum under a table of equality weights. -/
theorem read_under_eq {z : Array E} {n : ℕ} (hz : z.size = n) {v : ℕ → K}
    (hv : ∀ j < n, pt ρ z j = v j) (f : ℕ → E) :
    ρ.val (under (eqTab z) f) = ∑ c ∈ range (2 ^ n), Blocks.eqN n 0 v c * ρ.val (f c) := by
  rw [read_under, size_eqTab, hz]
  exact sum_congr rfl fun c hc => by rw [read_eqTab ρ hz hv (mem_range.mp hc)]

/-- The same for the sum with the short cut at a weight 0. -/
theorem read_underN_eq {z : Array E} {n : ℕ} (hz : z.size = n) {v : ℕ → K}
    (hv : ∀ j < n, pt ρ z j = v j) (f : ℕ → E) :
    ρ.val (underN (eqTab z) f) = ∑ c ∈ range (2 ^ n), Blocks.eqN n 0 v c * ρ.val (f c) := by
  rw [read_underN_under, read_under_eq ρ hz hv]

/-! ## Cuts of a point -/

/-- A cut that lies inside the point has its length. -/
theorem size_extract_le (r : Array E) {a b : ℕ} (hb : b ≤ r.size) :
    (r.extract a b).size = b - a := by
  rw [Array.size_extract]
  omega

/-- A coordinate of a cut. -/
theorem pt_extract (r : Array E) (a b j : ℕ) (h : a + j < b) :
    pt ρ (r.extract a b) j = pt ρ r (a + j) := by
  unfold pt
  rw [VerifiableInference.Desc.First.Att.P.extract_getD r a b j h]

/-- The table of equality weights of the cut [a, a + n) of a point. -/
theorem read_eqTab_cut (r : Array E) {a n : ℕ} (h : a + n ≤ r.size) :
    (eqTab (r.extract a (a + n))).size = 2 ^ n ∧ ∀ c < 2 ^ n,
      ρ.val ((eqTab (r.extract a (a + n))).getD c zeroE) = Blocks.eqN n 0 (sh (pt ρ r) a) c := by
  have hz : (r.extract a (a + n)).size = n := by
    rw [size_extract_le r h]
    omega
  refine ⟨by rw [size_eqTab, hz], fun c hc => read_eqTab ρ hz (fun j hj => ?_) hc⟩
  exact pt_extract ρ r a (a + n) j (by omega)

/-- A list as an array has the list's coordinates. -/
theorem pt_toArray (x : List E) (j : ℕ) : pt ρ x.toArray j = ρ.val (x.getD j zeroE) := by
  unfold pt
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-! ## A sum over heads and tokens -/

/-- **A sum over heads and tokens is the library's read.** vg: a point that agrees with the first
coordinates of r. Psi: the tokens' weights, read. a: the summed values, read. -/
theorem read_rd2 {P : Pub5} (H : Sized P) {r tk : Array E} {vg Ψ : ℕ → K} {a : ℕ → ℕ → K}
    {f : ℕ → ℕ → E} (hr : P.D.lg ≤ r.size) (hg : ∀ k < P.D.lg, pt ρ r k = vg k)
    (ht : tk.size = P.D.T) (hΨ : ∀ i < P.D.T, ρ.val (tk.getD i zeroE) = Ψ i)
    (hf : ∀ g < P.D.nG, ∀ i < P.D.T, ρ.val (f g i) = a g i) :
    ρ.val (overHeads P.g r fun hk => underN tk fun i => f hk i) = rd2 P.D vg Ψ a := by
  rw [read_overHeads, H.G]
  unfold rd2
  refine sum_congr rfl fun g hg' => ?_
  rw [read_underN, ht, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [read_eqTab ρ (n := P.D.lg) (size_extract_le r hr) (v := vg)
      (fun j hj => by
        rw [pt_extract ρ r 0 _ j (by show 0 + j < P.D.lg; omega), Nat.zero_add]
        exact hg j hj)
      (mem_range.mp hg'), hΨ i (mem_range.mp hi), hf g (mem_range.mp hg') i (mem_range.mp hi)]
  ring

/-! ## The cube -/

/-- The vertex number X of the cube of n variables: X's bits, the highest first. -/
def vertex (n X : ℕ) : List E :=
  (List.range n).map fun k => if X.testBit (n - 1 - k) then oneE else zeroE

theorem vertex_length (n X : ℕ) : (vertex n X).length = n := by
  unfold vertex
  simp

theorem vertex_succ (n X : ℕ) :
    vertex (n + 1) X = (if X.testBit n then oneE else zeroE) :: vertex n X := by
  unfold vertex
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  show (if X.testBit (n + 1 - 1 - (k + 1)) then oneE else zeroE) = _
  rw [show n + 1 - 1 - (k + 1) = n - 1 - k by omega]

/-- A vertex hangs on the bits below n alone. -/
theorem vertex_add (n X : ℕ) (hX : X < 2 ^ n) : vertex n (2 ^ n + X) = vertex n X := by
  unfold vertex
  refine List.map_congr_left fun k hk => ?_
  have hk' : k < n := List.mem_range.mp hk
  rw [Nat.testBit_two_pow_add_gt (by omega)]

/-- **The cube is the list of the vertices**, in the order of their numbers. -/
theorem cube_eq : ∀ n : ℕ, cube n = (List.range (2 ^ n)).map (vertex n)
  | 0 => rfl
  | n + 1 => by
    show (cube n).map (zeroE :: ·) ++ (cube n).map (oneE :: ·) = _
    rw [cube_eq n, pow_succ, Nat.mul_two, List.range_add, List.map_append, List.map_map,
      List.map_map, List.map_map]
    congr 1
    · refine List.map_congr_left fun X hX => ?_
      have hX' : X < 2 ^ n := List.mem_range.mp hX
      show zeroE :: vertex n X = vertex (n + 1) X
      rw [vertex_succ, Nat.testBit_lt_two_pow hX']
      rfl
    · refine List.map_congr_left fun X hX => ?_
      have hX' : X < 2 ^ n := List.mem_range.mp hX
      show oneE :: vertex n X = vertex (n + 1) (2 ^ n + X)
      rw [vertex_succ, vertex_add n X hX', Nat.testBit_two_pow_add_eq,
        Nat.testBit_lt_two_pow hX']
      rfl

/-- A vertex's coordinate, read, is the library's. -/
theorem vertex_reads (n X k : ℕ) (hk : k < n) :
    ρ.val ((vertex n X).getD k zeroE) = (Blocks.cubePt n X : ℕ → K) k := by
  rw [Cb.Pv.Att.cubePt_at n X k hk]
  unfold vertex
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  show ρ.val (if X.testBit (n - 1 - k) then oneE else zeroE) = _
  split
  · exact ρ.one
  · exact ρ.zero

theorem pt_vertex (n X k : ℕ) (hk : k < n) :
    pt ρ (vertex n X).toArray k = (Blocks.cubePt n X : ℕ → K) k := by
  rw [pt_toArray, vertex_reads ρ n X k hk]

/-- A vertex, read, is the library's vertex: past the last coordinate both are 0. -/
theorem pt_vertex_eq (n X : ℕ) : pt ρ (vertex n X).toArray = (Blocks.cubePt n X : ℕ → K) := by
  funext k
  by_cases hk : k < n
  · exact pt_vertex ρ n X k hk
  · rw [pt_toArray, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by rw [vertex_length]; omega)]
    show ρ.val zeroE = Blocks.nat _ k
    unfold Blocks.nat
    rw [dif_neg hk, ρ.zero]

/-- The sum of a list made of the numbers below n. -/
theorem sum_list_range (n : ℕ) (f : ℕ → K) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ← ih, List.range_succ, List.map_append, List.sum_append]
    simp

/-- A sum over the cube's list is a sum over the vertices' numbers. -/
theorem sum_cube (n : ℕ) (f : List E → K) :
    ((cube n).map f).sum = ∑ X ∈ range (2 ^ n), f (vertex n X) := by
  rw [cube_eq, List.map_map]
  exact sum_list_range (2 ^ n) _

/-! ## The challenges -/

/-- **A sumcheck of which only the challenges are laid gives them back.** -/
theorem chal_sumAt (r : Array E) : chal (sumAt r) = r := by
  show (r.toList ++ [zeroE]).dropLast.toArray = r
  rw [List.dropLast_concat]

/-- **The library's challenges, made of the prover's challenges so far, read.**
z: the lookup's end point. The other fields are read off what was heard, in the verifier's own
type: the batching element of the value product; the five cuts of the round that draws many
elements; the three lists of powers; the three cuts of the challenges of the score at the index. -/
def pubOf (P : Pub5) (c : Chal) (z : ℕ → K) : Pub K :=
  let h := heardAt P c fun _ => none
  let D := P.D
  { z := z
    th := ρ.val (h.gam.getD 1 zeroE)
    tg := fun k => pt ρ h.point k
    ti := fun k => pt ρ h.point (D.lg + k)
    tk := fun k => pt ρ h.point (D.lg + D.lT + k)
    tbg := fun k => pt ρ h.point (D.lg + D.lT + 4 + k)
    tbi := fun k => pt ρ h.point (2 * D.lg + D.lT + 4 + k)
    o := fun b => pt ρ h.om b
    o' := fun b => pt ρ h.om' b
    o'' := fun b => pt ρ h.om'' b
    fi := fun k => pt ρ (chal h.atIndex) k
    fg := fun k => pt ρ (chal h.atIndex) (D.lT + k)
    fn := fun k => pt ρ (chal h.atIndex) (D.lT + D.lg + k) }

/-! ## Arrays that are made once -/

/-- An entry of an array that is made of the numbers below n. -/
theorem getD_range_map {α : Type} (n : ℕ) (f : ℕ → α) (d : α) {i : ℕ} (hi : i < n) :
    ((Array.range n).map f).getD i d = f i := by
  simp [Array.getD_eq_getD_getElem?, hi]

end H2K5.Honest

#print axioms H2K5.Honest.read_q
#print axioms H2K5.Honest.read_o
#print axioms H2K5.Honest.read_kx
#print axioms H2K5.Honest.read_v
#print axioms H2K5.Honest.read_zd
#print axioms H2K5.Honest.read_mx
#print axioms H2K5.Honest.read_ibit
#print axioms H2K5.Honest.read_rh
#print axioms H2K5.Honest.read_rhp
#print axioms H2K5.Honest.read_c
#print axioms H2K5.Honest.read_ofNat
#print axioms H2K5.Honest.read_ew
#print axioms H2K5.Honest.cells_are
#print axioms H2K5.Honest.Sized.lnT
#print axioms H2K5.Honest.Sized.lt
#print axioms H2K5.Honest.Sized.lgk
#print axioms H2K5.Honest.Sized.ldh
#print axioms H2K5.Honest.Sized.lB
#print axioms H2K5.Honest.Sized.HA
#print axioms H2K5.Honest.Sized.Lam
#print axioms H2K5.Honest.Sized.NP
#print axioms H2K5.Honest.Sized.G
#print axioms H2K5.Honest.Sized.T
#print axioms H2K5.Honest.sized_of_hid
#print axioms H2K5.Honest.PairsAre.pair
#print axioms H2K5.Honest.size_eqTab
#print axioms H2K5.Honest.read_eqTab
#print axioms H2K5.Honest.read_under_eq
#print axioms H2K5.Honest.read_underN_eq
#print axioms H2K5.Honest.size_extract_le
#print axioms H2K5.Honest.pt_extract
#print axioms H2K5.Honest.read_eqTab_cut
#print axioms H2K5.Honest.pt_toArray
#print axioms H2K5.Honest.read_rd2
#print axioms H2K5.Honest.vertex_length
#print axioms H2K5.Honest.vertex_succ
#print axioms H2K5.Honest.vertex_add
#print axioms H2K5.Honest.cube_eq
#print axioms H2K5.Honest.vertex_reads
#print axioms H2K5.Honest.pt_vertex
#print axioms H2K5.Honest.pt_vertex_eq
#print axioms H2K5.Honest.sum_list_range
#print axioms H2K5.Honest.sum_cube
#print axioms H2K5.Honest.chal_sumAt
#print axioms H2K5.Honest.getD_range_map
