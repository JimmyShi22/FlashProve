-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Pend/Shape/PendShape.lean: THE PENDING ROW (pendingRowO,
Johnson/Desc/First/Pend/Row.lean) ON SHAPES: one function from the shape of what the merge left
(MergeSh, Johnson/Desc/First/Shape/Own.lean) and the shape of statement, book and roots
(Ground.Sh.CoreSh) to the new row's shape (K13.Honest.RowSh) and the shape behind; and the two laws.
General laws; nothing is evaluated. NO TEST OF THIS TEXT READS A VALUE (the library says so in
Johnson/Desc/First/Pend/RowMeans.lean, whose equivalence pendingRowO_means is called here).

  `recBlank`: a claim's rest with the same unit and sizes, and zeros for its elements.
    `rec_sizes`: it has the sizes of the claim that it is made of.
  `unitOf_blank`, `spanOf_blank`, `fits_blank`: the unit, the span of rows and the four tests on a
    claim are the same at the blank (by the library's size_wsGamma, OnBytes/Flat/PendingSizes.lean).
  `gamma_size`: the vector of weights keeps its number of rows.
  `blocksSh k first n`: the blocks of a stretch of n rows from row first on: of each its number of
    dense variables and its number of variables: made at zeros. `blocks_sh`: they are the same at
    any n values (the library's stretchBlocks_skel).
  `pendB`: THE TEST, on shapes: the marks [4] to [19] of the text's own list. `Marks`: what these
    marks say, at the merge itself. **`pendB_iff`**: pendB at the merge's shape accepts just if
    Marks holds. `means_cut`: the library's RowMeans, cut into Marks and the rest.
  **`pendS`**: THE FUNCTION ON SHAPES: pendB; the message of index masks has an open ledger with an
    entry left: then the row's shape, and the shape behind with that entry taken.
  **`pend_carries`**: pendingRowO returns (row, os') at os: then pendS returns (the row's shape, the
    shape behind) at the shapes.
  **`pend_returns`**: pendS returns at the shapes: then pendingRowO returns.

Limits. OF THE ROW's WEIGHT VECTORS THE ROW's SHAPE HOLDS TWO MARKS ALONE (K13.Honest.RowSh,
Johnson/Desc/K13/Honest/ShapeDefs.lean: there is none; each has v variables, or two differ): so
pend_carries says of them no more than these two marks: not how many they are, nor, where two
differ, which numbers of variables they have. Nothing on what the row means. Nothing on soundness,
completeness or hiding.

-/
import Johnson.Desc.First.Pend.RowMeans
import Johnson.Desc.First.Shape.Own
import Johnson.Desc.Ground.Shape.Ground
import Johnson.Desc.K13.Honest.Shape
import OnBytes.Flat.PendingSizes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Pend.Shape
open OnBytes OnBytes.Params OnBytes.Model
open OnBytes.Flat (All2 FacSizes size_wsGamma stretchBlocks_skel skel)
open VerifiableInference.Desc.First.Shape (RecSh recSh MergeSh mergeSh)

/-! ## 1 The blank of a claim's rest -/

def recBlank (c : RecSh) : WsRecClaim :=
  { ui := c.ui, ka := zeroE
    f := c.f.map fun x =>
      { HV := Array.replicate x.1 zeroE, pl := Array.replicate x.2.1 zeroE,
        AV := Array.replicate x.2.2 zeroE } }

theorem fac_sizes : ∀ l : List WsRowFac,
    All2 FacSizes l ((l.map fun x => (x.HV.size, x.pl.size, x.AV.size)).map fun x =>
      ({ HV := Array.replicate x.1 zeroE, pl := Array.replicate x.2.1 zeroE,
         AV := Array.replicate x.2.2 zeroE } : WsRowFac))
  | [] => .nil
  | x :: l => .cons ⟨by simp, by simp, by simp⟩ (fac_sizes l)

theorem rec_sizes (c : WsRecClaim) : All2 FacSizes c.f (recBlank (recSh c)).f := fac_sizes c.f

theorem unitOf_blank (lay : WsLay) (c : WsRecClaim) :
    unitOf lay (recBlank (recSh c)) = unitOf lay c := rfl

theorem spanOf_blank (lay : WsLay) : ∀ (recs : List WsRecClaim) (r : Nat × Nat),
    spanOf lay ((recs.map recSh).map recBlank) r = spanOf lay recs r
  | [], _ => rfl
  | c :: l, r => by
    show spanOf lay ((l.map recSh).map recBlank) _ = spanOf lay l _
    exact spanOf_blank lay l _

theorem fits_blank (lay : WsLay) (n : Nat) (c : WsRecClaim) :
    ClaimFits lay n (recBlank (recSh c)) ↔ ClaimFits lay n c := by
  unfold ClaimFits
  rw [unitOf_blank, size_wsGamma (unitOf lay c) (rec_sizes c) oneE oneE]
  have el : (recBlank (recSh c)).f.length = c.f.length := (rec_sizes c).length.symm
  rw [el]
  exact Iff.rfl

theorem gamma_size (lay : WsLay) : ∀ (recs : List WsRecClaim) (G : Array E),
    (gammaOf lay recs G).size = G.size
  | [], _ => rfl
  | c :: l, G => by
    show (gammaOf lay l (added G _ _)).size = _
    rw [gamma_size lay l, added_size]

/-! ## 2 The blocks of a stretch -/

/-- Of each block: the number of its dense variables; the number of its variables. -/
def blocksSh (k first n : Nat) : List (Nat × Nat) :=
  (stretchBlocks k first (Array.replicate n zeroE) (2 * k + 2) first).map fun t =>
    (t.denseVars.length, t.vars)

theorem blocks_sh (k first : Nat) (v : Array E) :
    ((stretchBlocks k first v (2 * k + 2) first).map fun t => (t.denseVars.length, t.vars)) =
      blocksSh k first v.size := by
  have h := stretchBlocks_skel k first (v := v) (v' := Array.replicate v.size zeroE) (by simp)
    (2 * k + 2) first
  have := congrArg (List.map fun s : List (E × E) × List Nat => (s.2.length, s.1.length)) h
  simpa [List.map_map, Function.comp_def, skel, blocksSh, Tensor.vars] using this

/-! ## 3 The test on shapes -/

/-- The four tests on one claim, with code. -/
def claimFitsB (lay : WsLay) (n : Nat) (c : WsRecClaim) : Bool :=
  (lay.U[c.ui]?).isSome && (wsGamma (unitOf lay c) c oneE).size == (unitOf lay c).rows &&
    c.f.length == (unitOf lay c).g.length && decide ((unitOf lay c).off + (unitOf lay c).rows ≤ n)

theorem claimFitsB_iff (lay : WsLay) (n : Nat) (c : WsRecClaim) :
    claimFitsB lay n c = true ↔ ClaimFits lay n c := by
  unfold claimFitsB ClaimFits
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Option.isSome_iff_exists, and_assoc]

/-- The claims' rests at zeros. -/
def blanks (w : MergeSh) : List WsRecClaim := w.recs.map recBlank

/-- The first row of the span, and the row behind its last. -/
def spanSh (lay : WsLay) (w : MergeSh) : Nat × Nat := spanOf lay (blanks w) (2 ^ 64 - 1, 0)

/-- **THE TEST ON SHAPES**: the marks [4] to [19]. -/
def pendB (lay : WsLay) (S : LinShape) (w : MergeSh) (claims : Nat) : Bool :=
  let first := (spanSh lay w).1
  let last := (spanSh lay w).2
  lay.m0 == S.matrixRows && !w.recs.isEmpty && w.recs.length == claims && w.rm == lay.lk &&
    (blanks w).all (fun c => (lay.U[c.ui]?).isSome) && decide (first < last) &&
    decide (last ≤ lay.m0) && decide (S.kRow ≤ 62) && decide (lay.m0 ≤ 2 ^ S.kRow) &&
    (blanks w).all (claimFitsB lay last) &&
    decide (first + (last - first) ≤ S.matrixRows) && decide (S.kRow < 63) &&
    decide (first + (last - first) ≤ 2 ^ S.kRow) &&
    ((blocksSh S.kRow first (last - first)).map fun x => 2 ^ x.1).sum == last - first

/-- What the marks [4] to [19] say, at the merge itself. -/
def Marks (lay : WsLay) (S : LinShape) (o : WsForkOut) (claims : Nat) : Prop :=
  let first := (spanOf lay o.recs (2 ^ 64 - 1, 0)).1
  let last := (spanOf lay o.recs (2 ^ 64 - 1, 0)).2
  let values := (gammaOf lay o.recs (Array.replicate last zeroE)).extract first last
  let blocks := stretchBlocks S.kRow first values (2 * S.kRow + 2) first
  lay.m0 = S.matrixRows ∧ o.recs ≠ [] ∧ o.recs.length = claims ∧ o.rm.size = lay.lk ∧
  (∀ c ∈ o.recs, ∃ u, lay.U[c.ui]? = some u) ∧ first < last ∧ last ≤ lay.m0 ∧
  S.kRow ≤ 62 ∧ lay.m0 ≤ 2 ^ S.kRow ∧ (∀ c ∈ o.recs, ClaimFits lay last c) ∧
  (first + values.size ≤ S.matrixRows ∧ S.kRow < 63 ∧ first + values.size ≤ 2 ^ S.kRow ∧
    (blocks.map fun t => 2 ^ t.denseVars.length).sum = values.size)

theorem span_sh (lay : WsLay) (o : WsForkOut) :
    spanSh lay (mergeSh o) = spanOf lay o.recs (2 ^ 64 - 1, 0) := spanOf_blank lay o.recs _

theorem values_size (lay : WsLay) (recs : List WsRecClaim) (first last : Nat) :
    ((gammaOf lay recs (Array.replicate last zeroE)).extract first last).size = last - first := by
  rw [Array.size_extract, gamma_size, Array.size_replicate, Nat.min_self]

theorem sum_sh (k first : Nat) (v : Array E) :
    ((stretchBlocks k first v (2 * k + 2) first).map fun t => 2 ^ t.denseVars.length).sum =
      ((blocksSh k first v.size).map fun x => 2 ^ x.1).sum := by
  rw [← blocks_sh, List.map_map]
  rfl

theorem pendB_iff (lay : WsLay) (S : LinShape) (o : WsForkOut) (claims : Nat) :
    pendB lay S (mergeSh o) claims = true ↔ Marks lay S o claims := by
  unfold pendB Marks
  simp only [span_sh, values_size, sum_sh]
  have e1 : (mergeSh o).recs.isEmpty = o.recs.isEmpty := by
    show (o.recs.map recSh).isEmpty = _
    cases o.recs <;> rfl
  have e2 : (mergeSh o).recs.length = o.recs.length := List.length_map _
  have e3 : (blanks (mergeSh o)).all (fun c => (lay.U[c.ui]?).isSome) = true ↔
      ∀ c ∈ o.recs, ∃ u, lay.U[c.ui]? = some u := by
    show (((o.recs.map recSh).map recBlank).all fun c => (lay.U[c.ui]?).isSome) = true ↔ _
    rw [List.map_map, List.all_map, List.all_eq_true]
    exact forall_congr' fun c => imp_congr Iff.rfl Option.isSome_iff_exists
  have e4 : ∀ n, (blanks (mergeSh o)).all (claimFitsB lay n) = true ↔
      ∀ c ∈ o.recs, ClaimFits lay n c := by
    intro n
    show (((o.recs.map recSh).map recBlank).all (claimFitsB lay n)) = true ↔ _
    rw [List.map_map, List.all_map, List.all_eq_true]
    exact forall_congr' fun c => imp_congr Iff.rfl
      ((claimFitsB_iff lay n _).trans (fits_blank lay n c))
  have e5 : (!o.recs.isEmpty) = true ↔ o.recs ≠ [] := by
    cases o.recs <;> simp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, e1, e2, e3, e4, e5, and_assoc]
  exact Iff.rfl

/-! ## 4 The function on shapes -/

open VerifiableInference.Desc.Ground.Sh (CoreSh coreSh stSh orcSh modAt map_modify ledger_get)

/-- A ledger with its next real entry taken. -/
def taken (l : Ledger) : Ledger :=
  { l with next := nextEntry l.rows l.logRows (2 ^ l.logRows) l.next + 1, left := l.left - 1 }

/-- **THE PENDING ROW ON SHAPES.** -/
def pendS (lay : WsLay) (S : LinShape) (im : Nat) (w : MergeSh) (claims : Nat) (a : CoreSh) :
    Option (K13.Honest.RowSh × CoreSh) :=
  if pendB lay S w claims then
    match (a.st.oracles[im]?).bind (·.ledger) with
    | some l =>
      if !l.closed && decide (0 < l.left) then
        some (⟨(blocksSh S.kRow (spanSh lay w).1 ((spanSh lay w).2 - (spanSh lay w).1)).isEmpty,
            K13.Honest.varsMark
              ((blocksSh S.kRow (spanSh lay w).1 ((spanSh lay w).2 - (spanSh lay w).1)).map (·.2)),
            w.rm, [⟨im, nextEntry l.rows l.logRows (2 ^ l.logRows) l.next⟩]⟩,
          { a with st := { a.st with
              oracles := modAt a.st.oracles im fun x => { x with ledger := some (taken l) } } })
      else none
    | none => none
  else none

/-- RowMeans, cut into the marks [4] to [19] and the rest. -/
theorem means_cut (lay : WsLay) (im : Nat) (o : WsForkOut) (claims : Nat) (S : LinShape)
    (os os' : Array OnBytes.Oracle) (row : TensorRow) :
    RowMeans lay im o claims S os os' row ↔
      Marks lay S o claims ∧ ∃ x l, os[im]? = some x ∧ x.ledger = some l ∧ l.closed = false ∧
        0 < l.left ∧
        row = { g := stretchBlocks S.kRow (spanOf lay o.recs (2 ^ 64 - 1, 0)).1
                  ((gammaOf lay o.recs (Array.replicate (spanOf lay o.recs (2 ^ 64 - 1, 0)).2
                    zeroE)).extract (spanOf lay o.recs (2 ^ 64 - 1, 0)).1
                    (spanOf lay o.recs (2 ^ 64 - 1, 0)).2) (2 * S.kRow + 2)
                  (spanOf lay o.recs (2 ^ 64 - 1, 0)).1
                psi := o.rm.toList.reverse
                masks := [(⟨im, nextEntry l.rows l.logRows (2 ^ l.logRows) l.next⟩, o.beta)]
                target := o.fvp } ∧
        os' = os.modify im fun x => { x with ledger := some (taken l) } := by
  unfold RowMeans Marks
  simp only [and_assoc]
  exact Iff.rfl

theorem core_taken (St : Statement) (bk : TreeBook) (rt im : Nat) (l : Ledger) :
    coreSh ⟨{ St with oracles := St.oracles.modify im fun x => { x with ledger := some l } }, bk,
      rt⟩ = { coreSh ⟨St, bk, rt⟩ with st := { (coreSh ⟨St, bk, rt⟩).st with
        oracles := modAt (coreSh ⟨St, bk, rt⟩).st.oracles im fun x =>
          { x with ledger := some l } } } := by
  show CoreSh.mk ⟨St.codes, (St.oracles.modify im _).toList.map orcSh, _⟩ _ _ = _
  rw [map_modify St.oracles im _ orcSh (fun x => { x with ledger := some l }) fun _ => rfl]
  rfl

theorem pend_carries (lay : WsLay) (S : LinShape) (im : Nat) (o : WsForkOut) (claims : Nat)
    (St : Statement) (bk : TreeBook) (rt : Nat) (os' : Array OnBytes.Oracle) (row : TensorRow)
    (h : pendingRowO lay im o claims S St.oracles = .ok (row, os')) :
    pendS lay S im (mergeSh o) claims (coreSh ⟨St, bk, rt⟩) =
      some (K13.Honest.rowSh row, coreSh ⟨{ St with oracles := os' }, bk, rt⟩) := by
  obtain ⟨hM, x, l, hx, hl, h1, h2, rfl, rfl⟩ :=
    (means_cut _ _ _ _ _ _ _ _).1 ((pendingRowO_means _ _ _ _ _ _ _ _).1 h)
  unfold pendS
  rw [if_pos ((pendB_iff lay S o claims).2 hM)]
  have el : ((coreSh ⟨St, bk, rt⟩).st.oracles[im]?).bind (·.ledger) = some l := by
    show ((stSh St).oracles[im]?).bind (·.ledger) = _
    rw [ledger_get, hx]
    exact hl
  rw [el]
  simp only
  rw [if_pos (by rw [h1]; simpa using h2), core_taken, span_sh]
  congr 2
  have e := blocks_sh S.kRow (spanOf lay o.recs (2 ^ 64 - 1, 0)).1
    ((gammaOf lay o.recs (Array.replicate (spanOf lay o.recs (2 ^ 64 - 1, 0)).2 zeroE)).extract
      (spanOf lay o.recs (2 ^ 64 - 1, 0)).1 (spanOf lay o.recs (2 ^ 64 - 1, 0)).2)
  rw [values_size] at e
  rw [← e, List.map_map, List.isEmpty_map]
  show _ = K13.Honest.RowSh.mk _ _ _ _
  congr 1
  show o.rm.size = o.rm.toList.reverse.length
  simp

theorem pend_returns (lay : WsLay) (S : LinShape) (im : Nat) (o : WsForkOut) (claims : Nat)
    (St : Statement) (bk : TreeBook) (rt : Nat) (z : K13.Honest.RowSh × CoreSh)
    (h : pendS lay S im (mergeSh o) claims (coreSh ⟨St, bk, rt⟩) = some z) :
    ∃ y, pendingRowO lay im o claims S St.oracles = .ok y := by
  unfold pendS at h
  by_cases hb : pendB lay S (mergeSh o) claims = true
  · rw [if_pos hb] at h
    have e : ((coreSh ⟨St, bk, rt⟩).st.oracles[im]?).bind (·.ledger) =
        (St.oracles[im]?).bind (·.ledger) := ledger_get St im
    rw [e] at h
    cases hx : St.oracles[im]? with
    | none => rw [hx] at h; exact nomatch h
    | some x =>
      rw [hx] at h
      cases hl : x.ledger with
      | none =>
        have : (some x : Option OnBytes.Oracle).bind (·.ledger) = none := hl
        rw [this] at h
        exact nomatch h
      | some l =>
        have : (some x : Option OnBytes.Oracle).bind (·.ledger) = some l := hl
        rw [this] at h
        simp only at h
        by_cases hc : (!l.closed && decide (0 < l.left)) = true
        · simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
          exact ⟨_, (pendingRowO_means _ _ _ _ _ _ _ _).2 ((means_cut _ _ _ _ _ _ _ _).2
            ⟨(pendB_iff lay S o claims).1 hb, x, l, hx, hl, hc.1, hc.2, rfl, rfl⟩)⟩
        · rw [if_neg hc] at h
          exact nomatch h
  · rw [if_neg hb] at h
    exact nomatch h

end VerifiableInference.Desc.First.Pend.Shape

#print axioms VerifiableInference.Desc.First.Pend.Shape.pend_carries
#print axioms VerifiableInference.Desc.First.Pend.Shape.pend_returns
#print axioms VerifiableInference.Desc.First.Pend.Shape.pendB_iff
#print axioms VerifiableInference.Desc.First.Pend.Shape.fits_blank
#print axioms VerifiableInference.Desc.First.Pend.Shape.spanOf_blank
#print axioms VerifiableInference.Desc.First.Pend.Shape.blocks_sh
