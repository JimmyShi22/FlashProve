-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/RowHolds.lean: "the pending row holds" in the merge's law is the pile's own
notion. Definitions, and theorems with their proofs.

`RowSays` (Johnson/Top/H0/MergeLaw/WoRow.lean) was a stand-in: a row on the committed matrix holds
of
the cells and of the index masks' entries, said plainly of the row's four fields. The law of the
batching of the pending rows has its own notion: `Holds` (Johnson/Desc/K13/Law/Means.lean): the
multilinear extension of g^T M at the row's point, and the row's mask form, give the target. Here
the two are shown to be one.

Main names:
  `eqN_lowBits`: the equality weight of the column number C at the row's point reversed
    (`Blocks.eqN`, which counts a number's bits from the top) is the cube's kernel at the row's
    point
    and C's bits, the lowest first (`Alg.eqk`, `lowBits`): THE TWO ORDERS OF BITS FIT.
  `rowSays_iff_holds`: `RowSays lk kRow cells idx r ↔ Holds gl w r`, for a row whose point has lk
    coordinates and a witness w of nR rows and lk column bits with: nR ≤ 2 ^ kRow; the cells are 0
    from row nR on; w's matrix at the bits of C is the cells' column C; w's mask entries, at the
    names in the row, are idx at the names' indices.
  `pending_sizes`: what a return of `wsPending` says of the sizes: the point has the layout's column
    bits, and the layout's rows lie in the cube.
  `ItemsHolds`, `items_holds`: `ItemsRow` with `RowSays` replaced by `Holds`: see its docstring.
  `merge_table_holds`: `merge_table_row` towards `ItemsHolds`.

What stays a premise: as WoRow.lean's head lists it. The witness of Means.lean's type is a letter
inside `ItemsHolds`, under two conditions: its matrix is the cells; its mask entries of the message
number `sr.out.indexMasks` are idx. No such witness is made of a witness of the whole file here.

Limits. It is no soundness of the protocol. An identity between two notions and a restatement: no
random step is added. Nothing on hiding.

-/
import Johnson.Top.H0.MergeLaw.WoRow
import Johnson.Desc.K13.Law.Eval

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open Iop IOR Cb Cb.Pv.Lay TWhole
open OnBytes (E zeroE TensorRow)
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Model (Reading Fork WsLay WsForkOut WsPending wsPending wsSpan wsGammaAdd)
open OnBytes.PscRun (Later)
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.Sound (Frame Piece below)
open VerifiableInference.Desc.First.Pend (takeEntry)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeClaim mergeEntries)
open Johnson.Desc.First.Walk.Law (leftOf rowBy ledgerAt)
open K11Caller (MergeIn GS noRd WeightsSays MergedSays cellsIn)
open _root_.Run (ckP)
open scoped ENNReal
open OnBytes.Road.Rows (pendWeight)
open VerifiableInference.Desc.K13.Law (Wit Holds lhs colOf weights formVal lowBits sum_lowBits)

/-- The equality weight of the column C at the reversed point is the cube's kernel at C's bits. -/
theorem eqN_lowBits (k : ℕ) (psi : List E) (hk : psi.length = k) (C : ℕ) :
    Blocks.eqN k 0 (OnBytes.Road.pt Reading.gl psi.reverse.toArray) C =
      Alg.eqk (Johnson.L5.Layers.rd Reading.gl k psi) (lowBits k C) := by
  unfold Blocks.eqN Alg.eqk
  rw [← Finset.prod_range_reflect, ← Fin.prod_univ_eq_prod_range
    (fun t => if C.testBit (k - 1 - (k - 1 - t)) then
      OnBytes.Road.pt Reading.gl psi.reverse.toArray (0 + (k - 1 - t))
      else 1 - OnBytes.Road.pt Reading.gl psi.reverse.toArray (0 + (k - 1 - t))) k]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hv : (v : ℕ) < k := v.isLt
  have e1 : k - 1 - (k - 1 - (v : ℕ)) = v := by omega
  have e2 : OnBytes.Road.pt Reading.gl psi.reverse.toArray (0 + (k - 1 - (v : ℕ))) =
      Johnson.L5.Layers.rd Reading.gl k psi v := by
    unfold OnBytes.Road.pt Johnson.L5.Layers.rd
    congr 1
    have h3 : k - 1 - (v : ℕ) < psi.reverse.length := by
      rw [List.length_reverse]
      omega
    simp only [Nat.zero_add, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      List.getD_eq_getElem?_getD]
    rw [List.getElem?_reverse (by omega)]
    congr 2
    omega
  rw [e1, e2]
  rfl

/-- **`RowSays` is the pile's `Holds`**, at a witness whose matrix is the cells and whose mask
entries, at the names in the row, are the index masks' entries. -/
theorem rowSays_iff_holds {nR lk kRow : ℕ} (cells : OnBytes.Road.Wm GE) (idx : ℕ → GE)
    (r : TensorRow) (w : Wit GE nR lk) (hpsi : r.psi.length = lk) (hn : nR ≤ 2 ^ kRow)
    (hzero : ∀ j, nR ≤ j → ∀ C, cells j C = 0)
    (hmat : ∀ (i : Fin nR) (C : ℕ), C < 2 ^ lk → w.mat i (lowBits lk C) = cells i C)
    (hmask : ∀ t ∈ r.masks, w.mask t.1 = idx t.1.index) :
    RowSays lk kRow cells idx r ↔ Holds Reading.gl w r := by
  have hA : ∑ j ∈ Finset.range (2 ^ kRow),
      pendWeight Reading.gl r.g j * OnBytes.Road.rowAt Reading.gl lk r.psi.reverse.toArray cells j =
      Alg.mle (colOf w (weights Reading.gl nR r.g)) (Johnson.L5.Layers.rd Reading.gl lk r.psi) := by
    have h1 : ∑ j ∈ Finset.range (2 ^ kRow),
        pendWeight Reading.gl r.g j *
          OnBytes.Road.rowAt Reading.gl lk r.psi.reverse.toArray cells j =
        ∑ j ∈ Finset.range nR,
          pendWeight Reading.gl r.g j *
            OnBytes.Road.rowAt Reading.gl lk r.psi.reverse.toArray cells j := by
      refine (Finset.sum_subset (Finset.range_subset_range.2 hn) fun j _ hj => ?_).symm
      have hj' : nR ≤ j := by simpa using hj
      unfold OnBytes.Road.rowAt
      simp [hzero j hj']
    rw [h1]
    unfold Alg.mle
    rw [← sum_lowBits lk fun b =>
      Alg.eqk (Johnson.L5.Layers.rd Reading.gl lk r.psi) b * colOf w (weights Reading.gl nR r.g) b]
    unfold OnBytes.Road.rowAt VerifiableInference.Desc.K13.Law.colOf
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun C hC => ?_
    rw [← Fin.sum_univ_eq_sum_range
      (fun j => pendWeight Reading.gl r.g j *
        (Blocks.eqN lk 0 (OnBytes.Road.pt Reading.gl r.psi.reverse.toArray) C * cells j C)) nR]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [eqN_lowBits lk r.psi hpsi C, hmat i C (Finset.mem_range.1 hC)]
    show pendWeight Reading.gl r.g i * _ = _ * (pendWeight Reading.gl r.g i * _)
    ring
  have hB : (r.masks.map fun x => idx x.1.index * Reading.gl.val x.2).sum =
      formVal Reading.gl w.mask r.masks := by
    unfold formVal
    congr 1
    refine List.map_congr_left fun t ht => ?_
    rw [hmask t ht]
    ring
  unfold RowSays Holds lhs
  rw [hA, hB]

/-- What a return of the routine wsPending says of the sizes. -/
theorem pending_sizes {lay : WsLay} {o : WsForkOut} {n : ℕ} {S : OnBytes.Params.LinShape}
    {w : WsPending} (hw : wsPending lay o n S = .ok w) :
    o.rm.size = lay.lk ∧ lay.m0 ≤ 2 ^ S.kRow := by
  by_cases c4 : (lay.m0 != S.matrixRows) = true
  case pos => simp [wsPending, bind, Except.bind, c4] at hw
  by_cases c5 : (o.recs.isEmpty || o.recs.length != n || o.rm.size != lay.lk) = true
  case pos => simp [wsPending, bind, Except.bind, pure, Except.pure, c4, c5] at hw
  cases hs : wsSpan lay o.recs with
  | error e => simp [wsPending, bind, Except.bind, pure, Except.pure, c4, c5, hs] at hw
  | ok fl =>
  by_cases c9 : (decide (fl.2 ≤ fl.1) || decide (lay.m0 < fl.2) || decide (62 < S.kRow) ||
      decide (2 ^ S.kRow < lay.m0)) = true
  case pos => simp [wsPending, bind, Except.bind, pure, Except.pure, c4, c5, hs, c9] at hw
  simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, bne, Bool.not_eq_false',
    decide_eq_true_eq, beq_iff_eq] at c5 c9
  exact ⟨c5.2, by omega⟩

variable {Pl : K11Caller.Place} (N : K11Caller.Nums Pl)

/-- **What the merge's yes says, with the pending row's truth in the pile's own words**: `ItemsRow`
(Johnson/Top/H0/MergeLaw/WoRow.lean) with `RowSays` replaced by `Holds`
(Johnson/Desc/K13/Law/Means.lean), at every witness of that file's type, of the layout's numbers of
rows and column bits, whose matrix is the cells and whose mask entries of the index masks' message
are the entries idx. -/
def ItemsHolds (cell : ℕ → ℕ → GE) (mask idx : ℕ → GE) (st : MergeIn Pl.n) (s' : S) : Prop :=
  ∃ (a' : HeadOwn) (wo : WsForkOut), s'.here = .head a' ∧ a'.wo = some wo ∧ leftOf s' = some wo ∧
    ∀ (n : ℕ) (s₂ s₃ : S) (a₂ a₃ : HeadOwn) (cls : List Claim) (Fl : Fork) (entry : ℕ → ℕ → ℕ → GE),
      s₂.here = .head a₂ → a₂.wo = a'.wo → Later a'.F a₂.F → headMergeClaim n s₂ = .ok (cls, s₃) →
      s₃.here = .head a₃ → Later a₃.F Fl →
      cls = [{ form := wo.p.rowForm wo.fvp {} }] ∧
      ∀ (sr : S) (claims : ℕ) (lin : OnBytes.Params.LinShape) (r : TensorRow)
        (wK : Wit GE Pl.lay.m0 Pl.lay.lk),
        leftOf sr = some wo → Johnson.Desc.First.Walk.Law.rowAt Pl.lay claims lin sr = some r →
        (∀ l c l', ledgerAt sr = some l → takeEntry l = some (c, l') → N.c = c) →
        (∀ (i : Fin Pl.lay.m0) (C : ℕ), C < 2 ^ Pl.lay.lk →
          wK.mat i (lowBits Pl.lay.lk C) = cell i C) →
        (∀ c, wK.mask ⟨sr.out.indexMasks, c⟩ = idx c) →
        MergedSays Reading.gl wo Fl mask entry → Holds Reading.gl wK r →
        WeightsSays Reading.gl N st cell mask

theorem items_holds {cell : ℕ → ℕ → GE} {mask idx : ℕ → GE} {st : MergeIn Pl.n} {s' : S}
    (h : ItemsRow N cell mask idx st s') : ItemsHolds N cell mask idx st s' := by
  obtain ⟨a', wo, e1, e2, e3, hall⟩ := h
  refine ⟨a', wo, e1, e2, e3, ?_⟩
  intro n s₂ s₃ a₂ a₃ cls Fl entry p1 p2 p3 p4 p5 p6
  obtain ⟨hcls, hin⟩ := hall n s₂ s₃ a₂ a₃ cls Fl entry p1 p2 p3 p4 p5 p6
  refine ⟨hcls, ?_⟩
  intro sr claims lin r wK hleft hr hc hmat hmask hm hH
  obtain ⟨w0, w, l, c, l', b1, b2, _, _, b5, b6, _, _⟩ := row_tie (left := leftOf) hr
  obtain ⟨z1, z2⟩ := pending_sizes b2
  refine hin sr claims lin r hleft hr hc hm
    ((rowSays_iff_holds (cellsIn Pl cell) idx r wK ?_ z2 ?_ ?_ ?_).2 hH)
  · rw [b5]
    show w.psi.length = Pl.lay.lk
    rw [b6, List.length_reverse, Array.length_toList, z1]
  · intro j hj C
    unfold cellsIn K11Caller.Wof
    rw [dif_neg (by omega)]
  · intro i C hC
    rw [hmat i C hC]
    unfold cellsIn K11Caller.Wof
    rw [dif_pos ⟨i.isLt, hC⟩]
  · intro t ht
    rw [b5] at ht
    have e : t = (⟨sr.out.indexMasks, c⟩, w.beta) := by simpa using ht
    rw [e]
    exact hmask c

variable {F : Frame} {W : Type}

/-- **THE MERGE's LAW AT A PIECE, THE PENDING ROW's TRUTH IN THE PILE's OWN WORDS.** -/
theorem merge_table_holds (P : HeadMergeP) (hlay : Pl.lay = P.lay) (h1 : Pl.n = 1)
    (hk0 : 0 < Pl.lay.lk) (hnum : N.first + 1 + 2 * P.lay.lk + 2 = P.nMsg)
    (hunit : ∀ a u, Pl.lay.U[Pl.ui a]? = some u → OnBytes.Road.UnitOK Pl.lay.lk u) (L : List RDT)
    (he : L.map (·.entry) = mergeEntries P.lay.lk 1 P.work)
    (hkd : ∀ d ∈ L, Fmt.kindOf d.entry.name = some d.kind) :
    ∃ (dZ d0 : RDT) (ds : List RDT) (dY dV : RDT) (hk : ds.length = (GS Reading.gl N (noRd N)).k),
      L = dZ :: d0 :: (ds ++ [dY, dV]) ∧
      ∀ (base : ℕ) (ext : S × F.E.Str → Tr (uLT (ckP .two) (dZ :: d0 :: (ds ++ [dY, dV]))) → W → W)
        (cellOf : S × F.E.Str → ℕ → ℕ → GE) (maskOf idxOf : S × F.E.Str → ℕ → GE),
        (mergePiece F W P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base ext).ior.red.Leads
          (fun a => frontB N a.1 = true)
          (fun a a' => ItemsHolds N (cellOf a) (maskOf a) (idxOf a) (frontIn Pl.n a.1) a'.1)
          (mergePiece F W P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base ext).err ∧
        Err.Below (mergePiece F W P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base ext).err
          ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨dZ, d0, ds, dY, dV, hk, hL, hall⟩ :=
    merge_table_row (F := F) (W := W) N P hlay h1 hk0 hnum hunit L he hkd
  refine ⟨dZ, d0, ds, dY, dV, hk, hL, fun base ext cellOf maskOf idxOf => ?_⟩
  obtain ⟨hleads, hbelow⟩ := hall base ext cellOf maskOf idxOf
  exact ⟨hleads.conseq (fun _ h => h) fun _ _ _ _ _ hq => items_holds N hq, hbelow⟩

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.merge_table_holds
#print axioms VerifiableInference.Desc.First.MergeLaw.items_holds
#print axioms VerifiableInference.Desc.First.MergeLaw.rowSays_iff_holds
