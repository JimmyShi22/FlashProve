-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HidBase.lean: what holds of a witness's lists by the make, and what only the
packing gives.

ownAt s seat msg k (Johnson/Goal/Meaning/HidSeat.lean) is mzTot (mzAt y) at the symbols y := symAt
(s k) (seat k) msg: column by column, SOME small integers whose packing the column's symbols are,
and 0 where there are none (cellsOf, Cb/Pv/Tail/Unique.lean). So three things hold of these lists
for EVERY msg, and say nothing of it:
  - every entry is below twice the shift in absolute value (small_mzAt);
  - the cast of an entry is cellValS y at that cell: cellValS is by definition the cast of cellsOf
    (cell_ownAt); (these two are the library's weak_base, Cb/Pv/Tail/Base.lean, at these lists: "the
    clause on the packing is what Base says";)
  - the library's laws on a single sub-proof, layer_start_base and att_ord_base, whose premise
    BaseAt they spend only in its first clause (small) and its third (cellValS is the cast), hold at
    these lists from their other premises and the three inequalities Size.Uniq (at attention also
    PlaceOK and Inside): no premise on the packing is left in them (layerOrd_ownAt, attOrd_ownAt).
    THE DEBT HAS MOVED, NOT SHRUNK: by cell_ownAt these other premises, identities and keys at
    cellValS, are statements on the lists themselves: the two records are cheaper to STATE so, not
    cheaper to PAY from a run.
WHAT BITES IS BaseAt's SECOND CLAUSE: the committed symbols ARE the packing of these integers. It is
needed one step lower: where a law on the messages (the symbols; the tables of reads) is carried to
cellValS (the library's agree_cellVal, Cb/Pv/Tail/CellMap.lean, and agree_in,
Cb/Pv/Tail/InLink.lean, under the smallness test's relation relIn). Where a column packs nothing
small the list is 0 there, not what is committed (ownAt_zero), and an identity that holds of the
messages says nothing of the list.

Main names:
  BaseSeg s seat msg k   the symbols of sub-proof k, at its seats, are the packing of small
    integers: the library's Base at symAt (s k) (seat k) msg.
  small_mzAt, cell_ownAt   by the make.
  repack y, baseAt_repack, cellValS_repack   the packing of the integers behind y: it meets BaseAt
    and has the cells of y. (A tool: through it the library's two laws are called without a premise
    on y.)
  baseSeg_iff   BaseSeg says just that the symbols are their own repacking.
  sym_ownAt   UNDER BaseSeg the symbols are the packing of ownAt's integers.
  ownAt_unique   under BaseAt at any integers Mz, ownAt is mzTot Mz.
  layerOrd_ownAt, attOrd_ownAt, attOrd_ownAt_core   the records at a witness's lists, one statement
    a sort.
  ownAt_zero   A TOOTH: where a column's symbols are the packing of nothing small, ownAt is 0 in
    that column.
  noPack_big, notBase_big   a member: at the shift 2^17 and the radix 2^20 a column one of whose
    symbols is 2^62 is the packing of nothing small: BaseSeg fails there and ownAt is 0 in that
    column.

  baseB un y, base_of_baseB, unGl   A TEST WITH CODE for whoever holds a run's symbols: the cells
    that an unpacker reads in them are small and pack back. If it says yes, Base holds, whatever the
    unpacker. unGl: an unpacker with code (three balanced digits). THE CONVERSE IS NOT SHOWN: that
    baseB (unGl s.rad) says yes at every packing of small integers at the radix s.rad. (At another
    radix than the sizes' it says no at honest symbols.)

What is not claimed. BaseSeg of any witness. The smallness test's block would give it (the library's
base_of_relIn, Cb/Pv/Tail/Base.lean: Base at the symbols of the test's own letters) once symAt (s k)
(seat k) msg is tied to these symbols; that tie is not shown. The premises of layerOrd_ownAt and
attOrd_ownAt (identities and keys at cellValS) of any run. Nothing on probabilities or on hiding.
The program does not import this file.
-/
import Johnson.Goal.Meaning.HidPlanSizes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open Inst.Model (Mat)
open Inst.Model.All (DF)
open Inst.Model.FFSeg (dJ d10)
open Inst.Model.AttSeg (Raw Idn idnVal keyVec lut lutSet)
open OnBytes OnBytes.Road OnBytes.Road.Rows.Norms
open OnBytes.Model.Verify (publicOf layerShape)
open OnBytes.Model.Layer (Lay Scales)
open Cb.Pv.Tail (Size Syms JCell BaseAt Base cellValS)

/-- **The symbols of sub-proof k, at its seats, are the packing of small integers.** -/
def BaseSeg (s : ℕ → Size) (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) (msg : Msgs) (k : ℕ) :
    Prop := Base (symAt (s k) (seat k) msg)

section One
variable {s : Size} (y : Syms Cb.Gl.E s)

/-- **By the make**: the integers behind any symbols are small. -/
theorem small_mzAt (hβ : (0 : ℤ) < (s.beta : ℤ)) (μ : Fin s.NM) (c : Fin (s.k μ))
    (i : Fin (s.m μ)) : |Rows.mzAt y μ c i| < 2 * (s.beta : ℤ) := by
  by_cases h : ∃ a, Cb.Pv.Tail.Packs (Cb.Pv.Tail.symL Cb.Gl.E s) y μ c a
  · exact (Cb.Pv.Tail.packs_cellsOf (Cb.Pv.Tail.symL Cb.Gl.E s) h).1 i
  · have e : Rows.mzAt y μ c = fun _ => 0 := by
      unfold Rows.mzAt Cb.Pv.Tail.cellsOf
      rw [dif_neg h]
    rw [e]
    simp only [abs_zero]
    omega

/-- **A tooth**: where a column's symbols are the packing of nothing small, the integers behind it
are 0. -/
theorem mzAt_zero {μ : Fin s.NM} {c : Fin (s.k μ)}
    (h : ¬ ∃ a, Cb.Pv.Tail.Packs (Cb.Pv.Tail.symL Cb.Gl.E s) y μ c a) :
    Rows.mzAt y μ c = fun _ => 0 := by
  unfold Rows.mzAt Cb.Pv.Tail.cellsOf
  rw [dif_neg h]

/-- The packing of the integers behind y. -/
noncomputable def repack : Syms Cb.Gl.E s := fun μ i' c =>
  ((Alg.pack (s.rad : ℤ) (Rows.mzAt y μ c) i'.val : ℤ) : Cb.Gl.E)

theorem baseAt_repack (p : ℕ) [CharP Cb.Gl.E p] (U : s.Uniq p) :
    BaseAt (repack y) (Rows.mzAt y) :=
  Cb.Pv.Tail.baseAt_of_packs p U (small_mzAt y U.1) fun _ _ _ => rfl

/-- The repacking has the cells of y. -/
theorem cellValS_repack (p : ℕ) [CharP Cb.Gl.E p] (U : s.Uniq p) :
    cellValS (repack y) = cellValS y := funext fun j => (baseAt_repack y p U).2.2 j

/-- **Base says just that the symbols are their own repacking.** -/
theorem base_iff_repack (p : ℕ) [CharP Cb.Gl.E p] (U : s.Uniq p) : Base y ↔ repack y = y :=
  ⟨fun B => by
    funext μ i' c
    exact (((Rows.baseAt_mzAt y).mpr B).2.1 μ c i').symm,
    fun e => ⟨_, e ▸ baseAt_repack y p U⟩⟩

end One

section Lists
variable {s : ℕ → Size} {seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ} {msg : Msgs} {k : ℕ}

/-- ownAt within the sizes. -/
theorem ownAt_in {a r c : ℕ} (h : a < (s k).NM) (hc : c < (s k).k a) (hr : r < (s k).m a) :
    ownAt s seat msg k a r c =
      Rows.mzAt (symAt (s k) (seat k) msg) ⟨a, h⟩ ⟨c, hc⟩ ⟨r, hr⟩ := by
  unfold ownAt ownOf mzTot
  rw [dif_pos h, dif_pos hc, dif_pos hr]

/-- **By the make**: the cast of an entry of a witness's list is cellValS of its symbols at that
cell. -/
theorem cell_ownAt {a r c : ℕ} (h : a < (s k).NM) (hc : c < (s k).k a) (hr : r < (s k).m a) :
    ((ownAt s seat msg k a r c : ℤ) : Cb.Gl.E) =
      cellValS (symAt (s k) (seat k) msg) ⟨⟨a, h⟩, ⟨c, hc⟩, ⟨r, hr⟩⟩ := by
  rw [ownAt_in h hc hr]
  rfl

theorem baseSeg_iff (p : ℕ) [CharP Cb.Gl.E p] (U : (s k).Uniq p) :
    BaseSeg s seat msg k ↔ repack (symAt (s k) (seat k) msg) = symAt (s k) (seat k) msg :=
  base_iff_repack _ p U

/-- **Under BaseSeg the symbols are the packing of ownAt's integers.** -/
theorem sym_ownAt (B : BaseSeg s seat msg k) (μ : Fin (s k).NM)
    (i' : Fin (Alg.symRows ((s k).m μ))) (c : Fin ((s k).k μ)) :
    symAt (s k) (seat k) msg μ i' c =
      ((Alg.pack ((s k).rad : ℤ) (fun r : Fin ((s k).m μ) => ownAt s seat msg k μ.val r.val c.val)
        i'.val : ℤ) : Cb.Gl.E) := by
  have e : (fun r : Fin ((s k).m μ) => ownAt s seat msg k μ.val r.val c.val) =
      Rows.mzAt (symAt (s k) (seat k) msg) μ c :=
    funext fun r => ownAt_in μ.isLt c.isLt r.isLt
  rw [e]
  exact ((Rows.baseAt_mzAt _).mpr B).2.1 μ c i'

/-- Whatever integers stand behind the symbols by BaseAt are ownAt. -/
theorem ownAt_unique (p : ℕ) [CharP Cb.Gl.E p] (U : (s k).Uniq p)
    {Mz : ∀ μ : Fin (s k).NM, Fin ((s k).k μ) → Fin ((s k).m μ) → ℤ}
    (B : BaseAt (symAt (s k) (seat k) msg) Mz) : ownAt s seat msg k = mzTot Mz :=
  ownOf_unique p U B

/-- **A tooth**: where a column's symbols are the packing of nothing small, ownAt is 0 in that
column. -/
theorem ownAt_zero {a c : ℕ} (h : a < (s k).NM) (hc : c < (s k).k a)
    (hn : ¬ ∃ v, Cb.Pv.Tail.Packs (Cb.Pv.Tail.symL Cb.Gl.E (s k)) (symAt (s k) (seat k) msg)
      ⟨a, h⟩ ⟨c, hc⟩ v) (r : ℕ) : ownAt s seat msg k a r c = 0 := by
  by_cases hr : r < (s k).m a
  · rw [ownAt_in h hc hr, mzAt_zero _ hn]
  · unfold ownAt ownOf mzTot
    rw [dif_pos h, dif_pos hc, dif_neg hr]

/-- **The record on a group of layers at a witness's list**: the library's layer_start_base, with no
premise on the packing: identities at cellValS of the symbols, and the two clauses on the embedding
and the keys at the list. Paying these identities from the messages still takes the packing (see the
file's head). -/
theorem layerOrd_ownAt {Jr : Type} (p : ℕ) [CharP Cb.Gl.E p] (U : (s k).Uniq p)
    (hβ : 2 * ((s k).beta : ℤ) ≤ 2 ^ 18) (h : Model.Layer.Shape) (sc : Scales) (yl : Lay) (g : ℕ)
    (Wi : Mat) (x : Cm.Seg.XI) (raw : Jr → Cb.Gl.E)
    (hOwn : ∀ j ν, j < 17 → ν < DF.nNu → ∀ i, i < 2 ^ DF.lT →
      dJ (scl := OnBytes.Road.sclOf h sc g 4) DF
        (rdAt yl (Sum.elim raw (cellValS (symAt (s k) (seat k) msg)))) j ν i = 0)
    (hHot : ∀ l, l < DF.ne → ∀ i, i < 2 ^ DF.lT →
      d10 DF (rdAt yl (Sum.elim raw (cellValS (symAt (s k) (seat k) msg)))) l i = 0)
    (hE : EmbField h sc yl g (ownAt s seat msg k) Wi x)
    (hK : KeyField h sc yl g (ownAt s seat msg k) Wi) :
    LayerOrd h sc yl g (ownAt s seat msg k) Wi x := by
  have e := cellValS_repack (symAt (s k) (seat k) msg) p U
  exact layer_start_base h sc yl g Wi x (baseAt_repack (symAt (s k) (seat k) msg) p U) hβ raw
    (by rw [e]; exact hOwn) (by rw [e]; exact hHot) hE hK

/-- **The record on an attention sub-proof at a witness's list**: the library's att_ord_base, with
no premise on the packing. pl: a map of places that is right within the sizes; every valid name's
place lies within the sizes. Paying these identities and keys from the messages still takes the
packing (see the file's head). -/
theorem attOrd_ownAt (p : ℕ) [CharP Cb.Gl.E p] (U : (s k).Uniq p)
    (h2 : 2 * ((s k).beta : ℤ) ≤ 2 ^ 18) {S : Attention.Shape} (φ : Cb.Gl.F →+* Cb.Gl.E)
    {pl : ℕ → ℕ → ℕ → JCell (s k)} (hp : Rows.PlaceOK pl) (hin : Inside (s k) S)
    {t : Raw → Cb.Gl.E}
    (ht : ∀ c, t c = cellValS (symAt (s k) (seat k) msg)
      (pl (L5.addrA S c).1 (L5.addrA S c).2.1 (L5.addrA S c).2.2))
    (own1 : ∀ j b g i, (Idn.at1 j b g i).Valid (L5.dimOf S) →
      idnVal (L5.dimOf S) t (.at1 j b g i) = 0)
    (own2 : ∀ b g i, (Idn.at2 b g i).Valid (L5.dimOf S) → idnVal (L5.dimOf S) t (.at2 b g i) = 0)
    (keys : ∀ (c : Fin 4) (X : ℕ), X < (L5.dimOf S).used c →
      keyVec (scl := L5.sclOf S) (L5.dimOf S) (L5.tbOf S) t c X ∈
        lutSet (lut (scl := L5.sclOf S) (L5.dimOf S) (L5.tbOf S) c))
    (ridden : ∀ b g i, (Idn.at3 b g i).Valid (L5.dimOf S) →
      idnVal (L5.dimOf S) t (.at3 b g i) = 0) :
    L5.AttOrd S (ownAt s seat msg k) := by
  have e := cellValS_repack (symAt (s k) (seat k) msg) p U
  exact attOrd_mzTot hp hin (Rows.att_ord_base φ (baseAt_repack (symAt (s k) (seat k) msg) p U) pl
    h2 (fun c => by rw [e]; exact ht c) own1 own2 keys ridden)

/-- In scope, at sizes that follow the plans: every valid name's place lies within the sizes. -/
theorem attOrd_ownAt_core {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}
    (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) (F : Follows X s) {g : ℕ}
    (hg : g < 12) (p : ℕ) [CharP Cb.Gl.E p] (U : (s (2 * g + 1)).Uniq p)
    (h2 : 2 * ((s (2 * g + 1)).beta : ℤ) ≤ 2 ^ 18) (φ : Cb.Gl.F →+* Cb.Gl.E)
    {pl : ℕ → ℕ → ℕ → JCell (s (2 * g + 1))} (hp : Rows.PlaceOK pl) {t : Raw → Cb.Gl.E}
    (ht : ∀ c, t c = cellValS (symAt (s (2 * g + 1)) (seat (2 * g + 1)) msg)
      (pl (L5.addrA (Hd.shapeA X g) c).1 (L5.addrA (Hd.shapeA X g) c).2.1
        (L5.addrA (Hd.shapeA X g) c).2.2))
    (own1 : ∀ j b g' i, (Idn.at1 j b g' i).Valid (L5.dimOf (Hd.shapeA X g)) →
      idnVal (L5.dimOf (Hd.shapeA X g)) t (.at1 j b g' i) = 0)
    (own2 : ∀ b g' i, (Idn.at2 b g' i).Valid (L5.dimOf (Hd.shapeA X g)) →
      idnVal (L5.dimOf (Hd.shapeA X g)) t (.at2 b g' i) = 0)
    (keys : ∀ (c : Fin 4) (n : ℕ), n < (L5.dimOf (Hd.shapeA X g)).used c →
      keyVec (scl := L5.sclOf (Hd.shapeA X g)) (L5.dimOf (Hd.shapeA X g))
          (L5.tbOf (Hd.shapeA X g)) t c n ∈
        lutSet (lut (scl := L5.sclOf (Hd.shapeA X g)) (L5.dimOf (Hd.shapeA X g))
          (L5.tbOf (Hd.shapeA X g)) c))
    (ridden : ∀ b g' i, (Idn.at3 b g' i).Valid (L5.dimOf (Hd.shapeA X g)) →
      idnVal (L5.dimOf (Hd.shapeA X g)) t (.at3 b g' i) = 0) :
    L5.AttOrd (Hd.shapeA X g) (ownAt s seat msg (2 * g + 1)) :=
  attOrd_ownAt p U h2 φ hp (inside_of_follows h C F hg) ht own1 own2 keys ridden

end Lists

/-! ## A member: symbols that are the packing of nothing small -/

theorem lane_small {m : ℕ} {a : Fin m → ℤ} {t : ℤ} (ht : 0 < t) (hs : Alg.Small t a) (i l : ℕ) :
    |Alg.lane a i l| < 2 * t := by
  unfold Alg.lane
  split
  · exact hs _
  · simp only [abs_zero]
    omega

/-- **At the shift 2^17 and the radix 2^20 a column one of whose symbols is 2^62 is the packing of
nothing small.** -/
theorem noPack_big {s : Size} (hb : s.beta = 2 ^ 17) (hr : s.rad = 2 ^ 20) (y : Syms Cb.Gl.E s)
    {μ : Fin s.NM} {c : Fin (s.k μ)} (i0 : Fin (Alg.symRows (s.m μ)))
    (hy : y μ i0 c = (((2 : ℤ) ^ 62 : ℤ) : Cb.Gl.E)) :
    ¬ ∃ a, Cb.Pv.Tail.Packs (Cb.Pv.Tail.symL Cb.Gl.E s) y μ c a := by
  rintro ⟨a, hs, hp⟩
  have h1 : (((2 : ℤ) ^ 62 : ℤ) : Cb.Gl.E) = ((Alg.pack (s.rad : ℤ) a i0.val : ℤ) : Cb.Gl.E) :=
    hy.symm.trans (hp i0)
  have h2 : ((Alg.pack (s.rad : ℤ) a i0.val - (2 : ℤ) ^ 62 : ℤ) : Cb.Gl.E) = 0 := by
    rw [Int.cast_sub, ← h1, sub_self]
  have h3 := (CharP.intCast_eq_zero_iff Cb.Gl.E Cb.Gl.p _).1 h2
  have hβ : (s.beta : ℤ) = 2 ^ 17 := by rw [hb]; norm_num
  have hρ : (s.rad : ℤ) = 2 ^ 20 := by rw [hr]; norm_num
  rw [hβ] at hs
  have l0 := abs_lt.1 (lane_small (by norm_num) hs i0.val 0)
  have l1 := abs_lt.1 (lane_small (by norm_num) hs i0.val 1)
  have l2 := abs_lt.1 (lane_small (by norm_num) hs i0.val 2)
  have e : Alg.pack (s.rad : ℤ) a i0.val = Alg.lane a i0.val 0 + 2 ^ 20 * Alg.lane a i0.val 1 +
      (2 ^ 20) ^ 2 * Alg.lane a i0.val 2 := by
    unfold Alg.pack
    rw [hρ]
    simp
  have hp' : ((Cb.Gl.p : ℕ) : ℤ) = 2 ^ 64 - 2 ^ 32 + 1 := by
    show (((2 ^ 64 - 2 ^ 32 + 1 : ℕ) : ℕ) : ℤ) = 2 ^ 64 - 2 ^ 32 + 1
    norm_num
  rw [e, hp'] at h3
  generalize Alg.lane a i0.val 0 = x0 at l0 h3
  generalize Alg.lane a i0.val 1 = x1 at l1 h3
  generalize Alg.lane a i0.val 2 = x2 at l2 h3
  have z := Int.eq_zero_of_abs_lt_dvd h3 (by
    rw [abs_lt]
    constructor <;> omega)
  omega

/-- **The member at a witness's letters**: if one symbol of a column, read at its seat, is 2^62,
then BaseSeg fails at that sub-proof, and ownAt is 0 in that column: not what is committed. -/
theorem notBase_big {s : ℕ → Size} {seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ} {msg : Msgs}
    {k : ℕ} (hb : (s k).beta = 2 ^ 17) (hr : (s k).rad = 2 ^ 20) {μ : Fin (s k).NM}
    {c : Fin ((s k).k μ)} (i0 : Fin (Alg.symRows ((s k).m μ)))
    (hy : symAt (s k) (seat k) msg μ i0 c = (((2 : ℤ) ^ 62 : ℤ) : Cb.Gl.E)) :
    ¬ BaseSeg s seat msg k ∧ ∀ r, ownAt s seat msg k μ.val r c.val = 0 := by
  have n := noPack_big hb hr (symAt (s k) (seat k) msg) i0 hy
  exact ⟨fun ⟨Mz, B⟩ => n ⟨Mz μ c, B.1 μ c, B.2.1 μ c⟩, fun r => ownAt_zero μ.isLt c.isLt n r⟩

/-! ## A test with code for an honest run's symbols -/

/-- One of three. -/
def pick3 (t : ℤ × ℤ × ℤ) : ℕ → ℤ
  | 0 => t.1
  | 1 => t.2.1
  | _ => t.2.2

/-- The cells that an unpacker un reads in the symbols: cell r of a column is lane r % 3 of symbol r
/ 3. -/
def cellsBy (un : Cb.Gl.E → ℤ × ℤ × ℤ) {s : Size} (y : Syms Cb.Gl.E s) :
    ∀ μ : Fin s.NM, Fin (s.k μ) → Fin (s.m μ) → ℤ := fun μ c r =>
  pick3 (un (y μ ⟨r.val / 3, by
    have := r.isLt
    unfold Alg.symRows
    omega⟩ c)) (r.val % 3)

/-- **The test**: the cells that un reads in the symbols are below twice the shift, and they pack
back to the symbols. -/
def baseB (un : Cb.Gl.E → ℤ × ℤ × ℤ) {s : Size} (y : Syms Cb.Gl.E s) : Bool :=
  decide (∀ μ : Fin s.NM, ∀ c : Fin (s.k μ),
    (∀ i, |cellsBy un y μ c i| < 2 * (s.beta : ℤ)) ∧
      ∀ i' : Fin (Alg.symRows (s.m μ)),
        y μ i' c = ((Alg.pack (s.rad : ℤ) (cellsBy un y μ c) i'.val : ℤ) : Cb.Gl.E))

/-- **If the test says yes, the symbols are a packing of small integers**, whatever the unpacker. -/
theorem base_of_baseB (p : ℕ) [CharP Cb.Gl.E p] {s : Size} (U : s.Uniq p)
    {un : Cb.Gl.E → ℤ × ℤ × ℤ} {y : Syms Cb.Gl.E s} (h : baseB un y = true) : Base y :=
  ⟨cellsBy un y, Cb.Pv.Tail.baseAt_of_packs p U
    (fun μ c i => ((of_decide_eq_true h) μ c).1 i) fun μ c i' => ((of_decide_eq_true h) μ c).2 i'⟩

/-- An element's first coordinate as an integer between -p / 2 and p / 2. -/
def signedOf (x : Cb.Gl.E) : ℤ :=
  if 2 * x.c0.val < Cb.Gl.p then (x.c0.val : ℤ) else (x.c0.val : ℤ) - (Cb.Gl.p : ℤ)

/-- An unpacker with code: three balanced digits at the radix rad of the first coordinate. -/
def unGl (rad : ℕ) (x : Cb.Gl.E) : ℤ × ℤ × ℤ :=
  let z := signedOf x
  let l0 := Int.bmod z rad
  let z1 := (z - l0) / (rad : ℤ)
  let l1 := Int.bmod z1 rad
  (l0, l1, (z1 - l1) / (rad : ℤ))

/-- At a witness's letters. -/
theorem baseSeg_of_baseB (p : ℕ) [CharP Cb.Gl.E p] {s : ℕ → Size}
    {seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ} {msg : Msgs} {k : ℕ} (U : (s k).Uniq p)
    {un : Cb.Gl.E → ℤ × ℤ × ℤ} (h : baseB un (symAt (s k) (seat k) msg) = true) :
    BaseSeg s seat msg k := base_of_baseB p U h

/-- BaseSeg is the library's Base at symAt, by unfolding. -/
theorem baseSeg_def (s : ℕ → Size) (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) (msg : Msgs)
    (k : ℕ) : BaseSeg s seat msg k = Base (symAt (s k) (seat k) msg) := rfl

end Meaning

#print axioms Meaning.small_mzAt
#print axioms Meaning.mzAt_zero
#print axioms Meaning.baseAt_repack
#print axioms Meaning.cellValS_repack
#print axioms Meaning.base_iff_repack
#print axioms Meaning.ownAt_in
#print axioms Meaning.cell_ownAt
#print axioms Meaning.baseSeg_iff
#print axioms Meaning.sym_ownAt
#print axioms Meaning.ownAt_unique
#print axioms Meaning.ownAt_zero
#print axioms Meaning.layerOrd_ownAt
#print axioms Meaning.attOrd_ownAt
#print axioms Meaning.attOrd_ownAt_core
#print axioms Meaning.lane_small
#print axioms Meaning.noPack_big
#print axioms Meaning.notBase_big
#print axioms Meaning.base_of_baseB
#print axioms Meaning.baseSeg_of_baseB
#print axioms Meaning.baseSeg_def
