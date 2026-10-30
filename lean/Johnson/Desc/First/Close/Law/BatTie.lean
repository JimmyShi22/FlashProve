-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/BatTie.lean: THE TYPED TIE OF THE BATCHED ROW AT A LINK's CLOSING (kind
K10), for any number of members, kept or not: the row that the batching returns, read as a vector
on the fold's input code, is the batched form of the typed rows at the state behind "BAT": the
arranged form plus weights on the rows that hold no member's row. Definitions, statements and
proofs.

Border.lean, beside this file, has the border behind the fold under one premise: a form F which, at
the batching's state, is the reading `inVec` of the batched row. Here that premise is brought down
to the rows, one by one.
  `rowVec T L N r`: ONE row of the program, laid alone, as a vector on the fold's input code: on the
    slot none: what 1 times the row adds at the index of the group's main table (`Row.mainSum`); on
    a kept slot, at the corner 0 .. 0: the row's coefficient on that entry of the kept message's own
    main table, times `keptWeight` (1 if the layout keeps that message, else 0); on the mask rows:
    what it adds at the index of the group's mask table.
  `hornerSum_zeros`: a sum of zeros under powers.
  `inVec_combine`: the batched row's vector is the sum of x^i times row number i's vector
    (BatVector.lean's three laws, entry by entry).
  `bat_tie`: for any shape: if the typed rows, laid in a list of all their names, have the powers
    of y as their coefficients, and a vector v is the sum of y^i times (the arranged form of typed
    row i plus that row's further weights), then the batched form, arranged, plus the batched
    further weights, at the state (st, z), is v.
  `OrderedV`: `Ordered` (Johnson/Top/H/BatTied.lean) with two clauses more: in the same list, typed
    row number i, arranged, plus its further weights, is `rowVec` of the program's row number i; and
    the further weights are 0 off the free rows. So on every row that a member sent the typed row,
    arranged, IS the program's row.
  `law_tied`: THE LAW OF K10 ON VECTORS, FROM THE ROWS: under `OrderedV`: the proved block's
    verifier puts out a' with the target handed on, and the form behind the fold, at the form
    "arranged plus the batched further weights" and the state of a', is `outVec` of the claim that
    the closing hands on.

Limits. `OrderedV` IS A PREMISE, a clause a row: whoever lays a row owes that the typed row reads as
it. The proof of `law_tied` does not spend the clause on the free rows: it is what the proved
block's knowledge soundness at that form asks (`arrRide_know_add`, Johnson/Top/H/ArrAdd.lean; not
called here). The conditions on the rows (RowFits, MaskFits) and that the mask code's message fits
the layout's place bits are premises; those on the layout's blocks are facts (LayBlocks.lean), since
the layout is the verifier's own. The limits of Border.lean hold. Nothing on soundness, on an honest
prover or on hiding.

-/
import Johnson.Desc.First.Close.Law.Border
import Johnson.Desc.First.Close.Law.BatVector
import Johnson.Top.H.Stations.FormLinear
import Johnson.Top.H.ArrAdd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Tie.Pv.Fold Iop IOR KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open OnBytes.PscRun (drawnOf)
open KObj.Stations.TestHead (fm_sum sum_powers)

/-- A sum of zeros under powers. -/
theorem hornerSum_zeros {α : Type} (y : GE) : ∀ l : List α, hornerSum y (l.map fun _ => 0) = 0
  | [] => rfl
  | _ :: l => by
    rw [List.map_cons, hornerSum, hornerSum_zeros y l, mul_zero, add_zero]

section Rows
variable {S : Sig GE} {R : RowsK S} (N : SlotNames R)

/-- One row of the program, laid alone, as a vector on the fold's input code. -/
noncomputable def rowVec (T : Statement) (L : GroupLayout) (r : OnBytes.Row) : R.Sh.Cin.J → GE :=
  fun j =>
  match j with
  | .inl (b, (none, x)) => r.mainSum rdE T L oneE (Sz.rowNo b + 2 ^ (R.s.h + R.s.g) * x.val)
  | .inl (b, (some q, x)) =>
      if b = fun _ => false then
        keptWeight (K := GE) L (N.orc q) * readE (r.coefficient (N.orc q) .main (N.idx q x))
      else 0
  | .inr (b, x) => r.maskSum rdE T L oneE (Sz.rowNo b + 2 ^ R.s.h * x.val)

/-- **The batched row's vector is the sum of x^i times row number i's vector.** -/
theorem inVec_combine (T : Statement) (g : ℕ) (input : RunInput) (x : E) (row : GroupRow)
    (h : Bat.combine T g input x = some row) (hM : MainBlocksOk T input.layout)
    (hZ : MaskBlocksOk T input.layout)
    (hr : ∀ r ∈ input.rows.toList, RowFits T r ∧ MaskFits T input.layout r)
    (hJ : ∀ y : (Fin R.s.h → Bool) × R.s.cZ.J,
      Sz.rowNo y.1 + 2 ^ R.s.h * y.2.val < 2 ^ (input.layout.h + input.layout.logEllZk))
    (j : R.Sh.Cin.J) :
    inVec N row j =
      hornerSum (readE x) (input.rows.toList.map fun r => rowVec N T input.layout r j) := by
  rcases j with ⟨b, o, y⟩ | ⟨b, y⟩
  · cases o with
    | none => exact combine_main_sum rdE T g input x row h hM (fun r k => (hr r k).1) _
    | some q =>
      by_cases hb : b = fun _ => false
      · show (if b = fun _ => false then _ else 0) = hornerSum (readE x) (input.rows.toList.map
          fun r => if b = fun _ => false then _ else 0)
        simp only [if_pos hb]
        exact combine_kept_all rdE T g input x row h (fun r k => (hr r k).1) _ _
      · show (if b = fun _ => false then _ else 0) = hornerSum (readE x) (input.rows.toList.map
          fun r => if b = fun _ => false then _ else 0)
        simp only [if_neg hb]
        exact (hornerSum_zeros _ _).symm
  · exact combine_mask_sum rdE T g input x row h hZ hr _ (hJ (b, y))

end Rows

/-- **The batched form, arranged, plus the batched further weights**, from the rows one by one. -/
theorem bat_tie {S : Sig GE} {G : Grp S} (Sh : GShape G) (hSh : Sh.rho.Laws) {B : Type} [Fintype B]
    (Sb : B → Type) (sl : ∀ b, Slf GE (Sb b) G.C.J) (Z : Evader GE (G.Row B))
    (fr : ∀ ν, Slf GE (G.RowSt Sb ν) Sh.Cin.J) (st : ∀ ν, G.RowSt Sb ν) (z : Z.D) (y : GE)
    (vs : List (Sh.Cin.J → GE)) (v : Sh.Cin.J → GE) (ord : List (G.Row B)) (hn : ord.Nodup)
    (hall : ∀ ν, ν ∈ ord) (hpow : ∀ i (h : i < ord.length), Z.ze z ord[i] = y ^ i)
    (hread : ord.map (fun ν => Sh.rho.fm (G.rows sl ν (st ν)) + fr ν (st ν)) = vs)
    (hv : ∀ j, v j = hornerSum y (vs.map fun u => u j)) :
    (Sh.form Sb sl Z + Slf.bat Z.ze fr) (st, z) = v := by
  funext j
  rw [hv j, ← hread, List.map_map]
  show _ = hornerSum y (ord.map fun ν => (Sh.rho.fm (G.rows sl ν (st ν)) + fr ν (st ν)) j)
  rw [← sum_powers (Z.ze z) (fun ν => (Sh.rho.fm (G.rows sl ν (st ν)) + fr ν (st ν)) j) y ord hn
    hall hpow]
  show Sh.rho.fm (fun i => ∑ ν, G.rows sl ν (st ν) i * Z.ze z ν) j + ∑ ν, fr ν (st ν) j * Z.ze z ν =
    ∑ ν, Z.ze z ν * (Sh.rho.fm (G.rows sl ν (st ν)) j + fr ν (st ν) j)
  rw [fm_sum _ hSh]
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun ν _ => mul_comm _ _

section Caller
variable {S : Sig GE} (R : RowsK S) (keep : S.O → Prop) [DecidablePred keep] {B : Type} [Fintype B]
  (Sb : B → Type) (sl : ∀ b, Slf GE (Sb b) R.G.C.J) (Z : Evader GE (R.G.Row B))
  (fx : Fin ((R.Sh.fold Sb sl Z).n + 1) × GE) {Kc St₀ Wp : Type} {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub (R.sizeB keep Sb sl Z).kp).Msg × Wp)) (bC bZ : ℕ)
  (w₀ : S.Wit × Wp) (w₁ : LdBrW R.G (R.sizeB keep Sb sl Z).kp Wp)

/-- The typed rows, laid in a list: all names, each once; their targets; the powers; AND THEIR
VECTORS: typed row number i, arranged, plus its further weights, is the program's row number i, laid
alone; AND THE FURTHER WEIGHTS STAND ON FREE ROWS ALONE (rows of the cube that hold no member's row:
`FreeAt`, Johnson/Top/H/ArrAdd.lean). Without the last clause the one before it could be paid by
further weights made up as the difference. x: targets and states of the claim's rows. σ: the
samples. -/
def OrderedV (N : SlotNames R) (fr : ∀ ν, Slf GE (R.G.RowSt Sb ν) R.Sh.Cin.J)
    (x : (B → GE) × (∀ b, Sb b)) (σ : S.Smp) (z : Z.D) (e : E) (T : Statement) (L : GroupLayout)
    (rows : List OnBytes.Row) : Prop :=
  ∃ ord : List (R.G.Row B), ord.Nodup ∧ (∀ ν, ν ∈ ord) ∧
    ord.map (R.G.claims x σ).1 = rows.map (fun w => readE w.target) ∧
    (∀ i (h : i < ord.length), Z.ze z ord[i] = readE e ^ i) ∧
    ord.map (fun ν => R.Sh.rho.fm (R.G.rows sl ν ((R.G.claims x σ).2 ν)) +
      fr ν ((R.G.claims x σ).2 ν)) = rows.map (rowVec N T L) ∧
    ∀ ν s j, ¬ Johnson.Top.H.ArrAdd.FreeAt R.Sh j → fr ν s j = 0

/-- **THE LAW OF K10 ON VECTORS, FROM THE ROWS.** -/
theorem law_tied (L : List (BatFoldCaller GE)) (rB rE rR : Round)
    (ρ : Rd (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁) rB rE rR) (hS : ρ.Scal)
    (hst : StepOK (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).val
      (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).n fx
      (rd2 (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)))
    (hfx : fx.2 * (HVar.plain GE (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).n).mon fx.1 = 1)
    (hL : R.Sh.rho.Laws) (N : SlotNames R) (fr : ∀ ν, Slf GE (R.G.RowSt Sb ν) R.Sh.Cin.J)
    (P : Plan) (T T' : Statement) (g : Nat) (mask : Option Nat) (out : SingleRows)
    (a : ((kBatFoldRide L).src (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).X ×
      ((kBatFoldRide L).src (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).E.Str)
    (τ : Tr (rB :: rE ::
      List.replicate (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).k rR))
    (ht : ρ.DefAt (ρ.V τ)) (h : closing P T g mask (ρ.V τ) = .ok (out, T'))
    (hO : ∀ G e z lay, T.groups[g]? = some G →
      (ρ.viewB τ.1 τ.2.1).drawn.elems = [e.triple] →
      ρ.rdZ (drawnOf (ρ.viewB τ.1 τ.2.1)) = some z → (begun T g G).layout g = some lay →
      OrderedV R Sb sl Z N fr a.1.1.1 a.1.2 z e (begun T g G) lay (runRows T G).toList)
    (hM : ∀ G lay, T.groups[g]? = some G → (begun T g G).layout g = some lay →
      R.s.Z.l ≤ 2 ^ lay.logEllZk ∧
      ∀ w ∈ (runRows T G).toList, MaskFits (begun T g G) lay w)
    (hR : ∀ G, T.groups[g]? = some G → ∀ w ∈ (runRows T G).toList, RowFits (begun T g G) w)
    (hk : P.k = R.s.h + R.s.g) (hh : P.h = R.s.h)
    (hZ : (T.codes.mask.getD P.maskCode default).ell = R.s.Z.l) :
    ∃ (z : Z.D)
      (τ' : Tr ((kBatFoldRide L).block (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).R.red.shape)
      (a' : ((kBatFoldRide L).dst (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).X ×
        ((kBatFoldRide L).dst (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).E.Str),
      ρ.rdZ (drawnOf (ρ.viewB τ.1 τ.2.1)) = some z ∧ ρ.carS.tr τ = some τ' ∧
      ((kBatFoldRide L).block (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).R.red.out a τ' =
        some a' ∧
      a'.1.1.1 = readE out.target ∧
      a'.1.2 = (batX (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁) a.1 z).2 ∧
      (R.Sh.par.reform (R.Sh.form Sb sl Z + Slf.bat Z.ze fr)).slOut a'.1.1.2 = outVec N out := by
  obtain ⟨G, x, row, lay, z, τ', a', hG, h2, h3, h4, hl, hlh, h5, h6, h7, h8, h9⟩ :=
    law_border R keep Sb sl Z fx A₀ bC bZ w₀ w₁ L rB rE rR ρ hS hst hfx P T T' g mask out a τ ht h
      (fun G e z hG hd hz => by
        obtain ⟨G', _, _, lay', _, _, _, _, _, _, _, _, -, -, hG', -, -, hl', -⟩ := closing_inv2 h
        obtain rfl := Option.some.inj (hG.symm.trans hG')
        obtain ⟨ord, o1, o2, o3, o4, -, -⟩ := hO G e z lay' hG hd hz hl'
        exact ⟨ord, o1, o2, o3, o4⟩) hR hk hh hZ
  refine ⟨z, τ', a', h3, h5, h6, h7, h8, h9 N _ ?_⟩
  obtain ⟨ord, o1, o2, -, o4, o5, -⟩ := hO G x z lay hG h2 h3 hl
  obtain ⟨b1, b2⟩ := OnBytes.LayLaw.layout_blocksOk (begun T g G) g lay hl
  obtain ⟨m1, m2⟩ := hM G lay hG hl
  have hJ : ∀ y : (Fin R.s.h → Bool) × R.s.cZ.J,
      Sz.rowNo y.1 + 2 ^ R.s.h * y.2.val < 2 ^ (lay.h + lay.logEllZk) := by
    intro y
    have k1 := OnBytes.Slice.rowNo_lt y.1
    have k2 : y.2.val + 1 ≤ 2 ^ lay.logEllZk := Nat.lt_of_lt_of_le y.2.isLt m1
    rw [hlh, pow_add]
    calc Sz.rowNo y.1 + 2 ^ R.s.h * y.2.val < 2 ^ R.s.h * (y.2.val + 1) := by
          rw [Nat.mul_add, Nat.mul_one]; omega
      _ ≤ _ := Nat.mul_le_mul_left _ k2
  exact bat_tie R.Sh hL Sb sl Z fr _ z (readE x) _ (inVec N row) ord o1 o2 o4 o5 fun j => by
    rw [List.map_map]
    exact inVec_combine N (begun T g G) g ⟨lay, runRows T G⟩ x row h4 b1 b2
      (fun w hw => ⟨hR G hG w hw, m2 w hw⟩) hJ j

end Caller

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.law_tied
#print axioms VerifiableInference.Desc.First.Close.inVec_combine
#print axioms VerifiableInference.Desc.First.Close.bat_tie
