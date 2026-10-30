--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeBack.lean: THE BACK PART OF THE KEY FILE's FIRST CHAIN's SHAPE, AND TWO OF ITS STEPS CUT
IN TWO: STRUCTURE | VALUES (the cut: Johnson/Desc/ProofFile/Honest/Thread/Shape.lean): "the rows on
the table" and the seal. Definitions, statements and proofs. Steps of the verifier's: NOTHING IS
SHOWN OF ANY PROVER.

THE SHAPE's BACK PART. `BackSh`: what is left, without a field element, of the five named values
that the chain's last sub-protocols write: each row on the table by the shape that the batching's
guards read (`RowSh`, Johnson/Desc/K13/Honest/ShapeDefs.lean: two marks on its weights, its point's
length, the slots that its mask form names) · ONE MARK on these rows' weights · what W's sending
announces · the numbers sent with W · the claim and the numbers laid with it (`LaidSh`, the same
file) · ONE MARK on the claim's row weights. The laws are stated at explicit arguments (the
statement's shape, two numbers, a mark, the claims' slots, the back part), so that they can be laid
into whatever product the whole chain's shape is.

  `mostOf`, **`lowB`**: "the weight lies below len", with code: the very test of the first short cut
    of the library's `tensorBelow`. `lowB_of_low`: E2E/KeyWeightsMark.lean's `Low` gives it.
    `lowB_spec`, `lowB_cut`,
    **`weightsB_of_lowB`**: it gives the mark on the row weights. `pileB`, `pileB_of_low`: THE MARK
    on all rows on the table.
  `BackSh`, `backOf`, `backSh`: the type and the reader, which reads four of the chain's named
    values alone. `BackSh.door`, `door_of_back`: what the third chain's start reads of it (`LinSh`,
    E2E/KeyShapeDoor.lean).
  `passes_of_marks`: the mark on the lookups' claims on the keys and the test on their values
    (`keysFormB`, `keysSumB`: E2E/KeyShapeKeys.lean) are together E2E/KeyPasses.lean's `Passes` at
    every claim.
  `varsMark_all`, `runs_pos`, `pendingRow_ne`, **`rowSh_pending`**: THE SHAPE OF A PART's ROW ON THE
    TABLE, at all values: it has a weight; every weight has the matrix's row bits as its variables;
    its point has the matrix's column bits as its length; its slots are the claim's.
  `ledgerS`, `ledgerS_spec`: the clause on the index-mask message's ledger, on the shape.
  `pileOf`, `gPileA`, **`gPile`**, `gPile_spec`: "the rows on the table" on the shape.
    **`pile_returns`**: (B2), with the one named test `keysSumB`. `mapM_map`, `mapM_mem_of`,
      `tableRowsOf_sh`,
    **`pile_carries`**: (B1): a row's shape for each claim; the mark is laid.
  `sealS`, `sealS_eq`, **`gSeal`**, **`seal_law`**: the seal's three clauses are a function of the
    shape, and the seal accepts just where they hold: no test on values.

Limits.
- `gPile` asks more than the step does: "the parameters are admitted", a test on public values that
  the chain asks earlier: the mark is laid by it.
- The batching: E2E/KeyShapeBatch.lean. The step behind W's commitment: E2E/KeyShapeRows.lean. The
  ranges' proximity test: E2E/KeyShapeRanges.lean. W's sending is not treated.
- `RowSh` and `LaidSh` are the hash build's working file's, for the next seal: unread there.
- That `keysSumB` passes: at the claims that a lookup itself makes: E2E/KeyPasses.lean,
  `passes_keysOf`.


-/
import E2E.KeyMarkJoined
import E2E.KeyQuietParts
import Johnson.Desc.K13.Honest.ShapeDefs
import E2E.KeyShapeKeys

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.AtFiles
open OnBytes OnBytes.Params
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.Key (ChainState layPile tableRowsOf firstChainEnd Pieces)
open VerifiableInference.Desc.K13.Honest (RowSh rowSh LaidSh laidSh varsMark)

variable {β : Type}

/-! ## The mark on the rows' weights, with code -/

/-- The largest index at which the weight can be other than 0, as the library's cut counts it. -/
def mostOf (v : Tensor) (count : Nat) : Nat :=
  (List.range count).foldl (fun s t => if (v.denseVars.contains (0 + t) ||
    !isZeroE (v.pairs.getD (0 + t) (zeroE, zeroE)).2) = true then s + 2 ^ t else s) 0

/-- **The weight lies below len**, with code. -/
def lowB (kRow len : Nat) (v : Tensor) : Bool :=
  v.ok && v.vars == kRow && decide (len ≤ 2 ^ kRow) && decide (mostOf v kRow < len)

theorem lowB_of_low {kRow len : Nat} {v : Tensor} (h : Low kRow len v) :
    lowB kRow len v = true := by
  obtain ⟨a, b, c, X, hX, hb⟩ := h
  have hm := foldl_bits_le (fun t => v.denseVars.contains (0 + t) ||
    !isZeroE (v.pairs.getD (0 + t) (zeroE, zeroE)).2) X kRow hb
  have hm' : mostOf v kRow < len := Nat.lt_of_le_of_lt (Nat.le_trans hm (Nat.mod_le _ _)) hX
  unfold lowB
  rw [a, beq_iff_eq.2 b, decide_eq_true c, decide_eq_true hm']
  rfl

theorem lowB_spec {kRow len : Nat} {v : Tensor} (h : lowB kRow len v = true) :
    v.ok = true ∧ v.vars = kRow ∧ len ≤ 2 ^ kRow ∧ mostOf v kRow < len := by
  unfold lowB at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem lowB_cut {kRow len : Nat} {v : Tensor} (h : lowB kRow len v = true) :
    tensorBelow v 0 kRow len = some [v] := by
  obtain ⟨-, hv, hl, hm⟩ := lowB_spec h
  unfold mostOf at hm
  unfold tensorBelow
  dsimp only
  rw [if_neg (by
    rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    omega)]
  rw [if_pos hm]
  split <;> rfl

/-- **Such weights have the mark on the row weights.** -/
theorem weightsB_of_lowB (S : LinShape) (lay : VectorLay) (g : List Tensor)
    (h : g.all (lowB S.kRow S.matrixRows) = true) (h2 : S.kRow ≤ lay.bits) (h3 : lay.bits ≤ 63) :
    weightsB S lay g = true := by
  refine List.all_eq_true.2 fun v hv => ?_
  have hb := List.all_eq_true.1 h v hv
  have c := lowB_cut hb
  obtain ⟨a, b, -⟩ := lowB_spec hb
  obtain ⟨o1, o2⟩ := onTable_ok lay v a (by rw [b]; exact h2) h3
  rw [VerifiableInference.Desc.Own.tensorInOrder_agrees] at o1
  rw [a, c, beq_iff_eq.2 b]
  simp only [Bool.and_self, List.all_cons, List.all_nil, o1, o2, beq_self_eq_true]

/-- **The mark on all rows on the table.** -/
def pileB (S : LinShape) (pile : List TensorRow) : Bool :=
  pile.all fun r => r.g.all (lowB S.kRow S.matrixRows)

theorem pileB_of_low (S : LinShape) (pile : List TensorRow)
    (h : ∀ r ∈ pile, ∀ t ∈ r.g, Low S.kRow S.matrixRows t) : pileB S pile = true :=
  List.all_eq_true.2 fun r hr => List.all_eq_true.2 fun t ht => lowB_of_low (h r hr t ht)

/-! ## The back part -/

/-- **The back part of the first chain's shape.** pile: each row on the table by the shape that the
batching's guards read (`RowSh`); pileOk: the mark on these rows' weights; lin: the claim and the
numbers laid with it (`LaidSh`); weights: the mark on the claim's row weights, true where no claim
is laid. -/
structure BackSh where
  pile : List RowSh
  pileOk : Bool
  msgW : List OracleNotice
  ids : List Nat
  lin : Option LaidSh
  weights : Bool

/-- **The reader**, of the four named values alone. S, cs: the shape of the test on the table and
the codes: public: the mark on the claim's weights is said at them. -/
def backOf (S : LinShape) (cs : Codes)
    (x : List TensorRow × Array OracleNotice × Array Nat × Option LinFirst) : BackSh :=
  ⟨x.1.map rowSh, pileB S x.1, x.2.1.toList, x.2.2.1.toList, x.2.2.2.map laidSh,
    x.2.2.2.all fun l => weightsB S (linLayOmega cs S) l.claim.g⟩

/-- At a state of the chain. -/
def backSh (S : LinShape) (cs : Codes) (s : ChainState β) : BackSh :=
  backOf S cs (s.pile, s.msgW, s.ids, s.lin)

/-- What the third chain's start reads of the back part. -/
def BackSh.door (b : BackSh) : Option LinSh := b.lin.map fun l => ⟨l.w, l.own, l.mask, b.weights⟩

theorem door_of_back (S : LinShape) (cs : Codes) (s : ChainState β) :
    (backSh S cs s).door = s.lin.map (linSh S cs) := by
  unfold BackSh.door backSh backOf
  cases s.lin <;> rfl

/-! ## The marks on the claims on the keys -/

theorem passes_of_marks {m : Wf.Matrix} {lookups : List WfLookup} {keys : List (List Lkp.Keys)}
    (h1 : keysFormB m lookups keys = true) (h2 : keysSumB m lookups keys = true) :
    lookups.length = keys.length ∧ (∀ y ∈ zipT lookups keys, y.1.parts.length = y.2.length) ∧
      ∀ y ∈ zipT lookups keys, ∀ z ∈ y.1.parts.zip y.2, Passes m z.1 z.2 = true := by
  unfold keysFormB keysB at h1
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h1
  unfold keysSumB at h2
  rw [List.all_eq_true] at h2
  refine ⟨h1.1, fun y hy => ?_, fun y hy z hz => ?_⟩
  · have := h1.2 y hy
    rw [Bool.and_eq_true, beq_iff_eq] at this
    exact this.1
  · have a := h1.2 y hy
    rw [Bool.and_eq_true, List.all_eq_true] at a
    have b := h2 y hy
    rw [List.all_eq_true] at b
    rw [← zipT_eq] at hz
    unfold Passes
    rw [a.2 z hz, b z hz]
    rfl

/-! ## The shape of a row on the table -/

theorem varsMark_all : ∀ (l : List Nat) (v : Nat), l ≠ [] → (∀ x ∈ l, x = v) →
    varsMark l = some v
  | [], _, h, _ => absurd rfl h
  | a :: t, v, _, h => by
    obtain rfl := h a (List.mem_cons_self ..)
    show (if t.all (· == a) then some a else none) = some a
    rw [if_pos (List.all_eq_true.2 fun x hx =>
      beq_iff_eq.2 (h x (List.mem_cons_of_mem _ hx)))]

theorem runs_pos (lp : Nat) : ∀ (rs : List WfRun) (u : Nat), Wf.runsOk lp u rs = true →
    ∀ r ∈ rs, 1 ≤ r.places
  | [], _, _, r, hr => by cases hr
  | a :: rs, u, h, r, hr => by
    obtain ⟨h1, -, -, h4⟩ := Slice.Leaves.runsOk_cons h
    rcases List.mem_cons.1 hr with rfl | hr
    · exact h1
    · exact runs_pos lp rs _ h4 r hr

/-- A part's row on the table has a weight. -/
theorem pendingRow_ne (m : Wf.Matrix) (l : WfLookup) (p : WfPart) (c : Lkp.Keys) (e : Array E)
    (h1 : p.runs ≠ []) (h2 : l.digitWeight ≠ []) (h3 : ∀ r ∈ p.runs, 1 ≤ r.places) :
    (Wf.pendingRow m l p c e).g ≠ [] := by
  obtain ⟨r, rs, hr⟩ := List.exists_cons_of_ne_nil h1
  obtain ⟨w, ws, hw⟩ := List.exists_cons_of_ne_nil h2
  have hp : 1 ≤ r.places := h3 r (by rw [hr]; exact List.mem_cons_self ..)
  obtain ⟨n, hn⟩ : ∃ n, r.places = n + 1 := ⟨r.places - 1, by omega⟩
  intro hg
  have hmem : ∀ t, t ∉ (Wf.pendingRow m l p c e).g := fun t ht => by
    rw [hg] at ht
    cases ht
  have hne : ∃ t, t ∈ Wf.weightsOnRows m.kRow (r.firstRow + 0 * r.stride) e r.firstPlace r.places
      (ofF w) := by
    unfold Wf.weightsOnRows
    rw [hn]
    unfold Wf.weightsFrom
    rw [if_pos (by omega)]
    exact ⟨_, List.mem_cons_self ..⟩
  obtain ⟨t, ht⟩ := hne
  refine hmem t ?_
  unfold Wf.pendingRow
  refine List.mem_flatMap.2 ⟨r, by rw [hr]; exact List.mem_cons_self .., ?_⟩
  refine List.mem_flatMap.2 ⟨(w, 0), ?_, ht⟩
  rw [hw]
  exact List.mem_cons_self ..

/-- **The shape of a part's row on the table.** -/
theorem rowSh_pending (m : Wf.Matrix) (l : WfLookup) (p : WfPart) (c : Lkp.Keys) (e : Array E)
    (hne : (Wf.pendingRow m l p c e).g ≠ [])
    (hlow : ∀ t ∈ (Wf.pendingRow m l p c e).g, Low m.kRow m.rows t)
    (hc : c.point.length = m.kCol + p.logPlaces) :
    rowSh (Wf.pendingRow m l p c e) = ⟨false, some m.kRow, m.kCol, c.masks.map (·.1)⟩ := by
  unfold rowSh
  have e1 : (Wf.pendingRow m l p c e).g.isEmpty = false := by
    cases hg : (Wf.pendingRow m l p c e).g with
    | nil => exact absurd hg hne
    | cons a t => rfl
  have e2 : varsMark ((Wf.pendingRow m l p c e).g.map Tensor.vars) = some m.kRow :=
    varsMark_all _ _ (fun h => hne (List.map_eq_nil_iff.1 h)) fun x hx => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
      exact (hlow t ht).2.1
  have e3 : (Wf.pendingRow m l p c e).psi.length = m.kCol := by
    show (c.point.take m.kCol).length = _
    rw [List.length_take, hc]
    omega
  rw [e1, e2, e3]
  rfl

/-! ## "The rows on the table" -/

/-- The clause on the index-mask message's ledger, on the shape. -/
def ledgerS (one : OneTime) (a : StSh) (idx : Nat) : Bool :=
  match a.oracles[idx]? with
  | some o =>
    match o.ledger with
    | some l =>
      l.left + Wf.indexMasks one.ranges (Wf.matrixOf one.lin) ==
        Send.freeMaskEntries o.shape.maskRows (a.codes.mask.getD o.shape.maskCode default).ell
          o.shape.answers
    | none => false
  | none => false

theorem ledgerS_spec (one : OneTime) (S : Statement) (idx : Nat)
    (h : ledgerS one (stSh S) idx = true) : ∃ o l, S.oracles[idx]? = some o ∧ o.ledger = some l ∧
      (l.left + Wf.indexMasks one.ranges (Wf.matrixOf one.lin) ==
        Send.freeMaskEntries o.shape.maskRows (S.codes.mask.getD o.shape.maskCode default).ell
          o.shape.answers) = true := by
  unfold ledgerS at h
  rw [orc_get] at h
  cases ho : S.oracles[idx]? with
  | none =>
    rw [ho] at h
    cases h
  | some o =>
    rw [ho] at h
    have h' : (match o.ledger with
      | some l =>
        l.left + Wf.indexMasks one.ranges (Wf.matrixOf one.lin) ==
          Send.freeMaskEntries o.shape.maskRows (S.codes.mask.getD o.shape.maskCode default).ell
            o.shape.answers
      | none => false) = true := h
    cases hl : o.ledger with
    | none =>
      rw [hl] at h'
      cases h'
    | some l =>
      rw [hl] at h'
      exact ⟨o, l, rfl, hl, h'⟩

/-- The shapes of the rows that the step lays: one for each claim. -/
def pileOf (S : LinShape) (slots : List (List (List Slot))) : List RowSh :=
  slots.flatten.map fun sl => ⟨false, some S.kRow, S.kCol, sl⟩

/-- **"The rows on the table" on the shape.** a: the statement's shape; idx: the index-mask
message's number; keysOk: the mark on the claims on the keys; slots: each claim's slots; b: the back
part; adm: one clause on public values, as an argument: so that it can be paid by a theorem where it
cannot be evaluated. -/
def gPileA (adm : Bool) (one : OneTime) (a : StSh) (idx : Nat) (keysOk : Bool)
    (slots : List (List (List Slot))) (b : BackSh) : Except String BackSh :=
  if b.pile.isEmpty && keysOk && one.ranges.lookups.length == slots.length && ledgerS one a idx &&
      adm then
    .ok { b with pile := pileOf one.lin slots, pileOk := true }
  else .error "the rows on the table: a guard on the shape"

/-- The same, with its clause on public values laid in: "the parameters are admitted". -/
def gPile (one : OneTime) (a : StSh) (idx : Nat) (keysOk : Bool)
    (slots : List (List (List Slot))) (b : BackSh) : Except String BackSh :=
  gPileA (Wf.admitted a.codes one.ranges (Wf.matrixOf one.lin)) one a idx keysOk slots b

theorem gPile_spec {one : OneTime} {a : StSh} {idx : Nat} {keysOk : Bool}
    {slots : List (List (List Slot))} {b t : BackSh} (h : gPile one a idx keysOk slots b = .ok t) :
    b.pile = [] ∧ keysOk = true ∧ one.ranges.lookups.length = slots.length ∧
      ledgerS one a idx = true ∧
      Wf.admitted a.codes one.ranges (Wf.matrixOf one.lin) = true ∧
      t = { b with pile := pileOf one.lin slots, pileOk := true } := by
  unfold gPile gPileA at h
  split at h
  · rename_i c
    simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at c
    exact ⟨c.1.1.1.1, c.1.1.1.2, c.1.1.2, c.1.2, c.2, (Except.ok.inj h).symm⟩
  · cases h

/-- **(B2)**: the guards return and the one test on values passes: the step returns. -/
theorem pile_returns (keysOf : β → List (List Lkp.Keys)) (one : OneTime) (cs : Codes)
    (s : ChainState β) (t : BackSh)
    (h : gPile one (stSh s.d.st) s.idx
      (keysB (Wf.matrixOf one.lin) one.ranges.lookups (keysOf s.base))
      (keysSlots (keysOf s.base)) (backSh one.lin cs s) = .ok t)
    (hv : keysSumB (Wf.matrixOf one.lin) one.ranges.lookups (keysOf s.base) = true) :
    ∃ s', layPile keysOf one s = .ok s' := by
  obtain ⟨h1, h2, hn, h3, -, -⟩ := gPile_spec h
  obtain ⟨o, l, ho, hl, hc⟩ := ledgerS_spec one s.d.st s.idx h3
  have hf : keysFormB (Wf.matrixOf one.lin) one.ranges.lookups (keysOf s.base) = true := by
    unfold keysFormB
    rw [h2, Bool.and_true, beq_iff_eq, hn]
    unfold keysSlots
    rw [List.length_map]
  obtain ⟨p1, p2, p3⟩ := passes_of_marks hf hv
  obtain ⟨rows, e⟩ := layPile_passes keysOf one s o l
    ⟨List.isEmpty_iff.2 (List.map_eq_nil_iff.1 h1), p1, p2, p3, ho, hl, hc⟩
  exact ⟨_, e⟩

theorem mapM_map {α γ δ : Type} (f : α → Option γ) (F : γ → δ) (G : α → δ) :
    ∀ (l : List α) (r : List γ), (∀ x ∈ l, ∀ y, f x = some y → F y = G x) → l.mapM f = some r →
      r.map F = l.map G
  | [], r, _, h => by
    rw [List.mapM_nil] at h
    obtain rfl := Option.some.inj h
    rfl
  | a :: l, r, hn, h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => rw [ha] at h; exact absurd h (by simp)
    | some b =>
      cases hl : l.mapM f with
      | none => rw [ha, hl] at h; exact absurd h (by simp)
      | some bs =>
        rw [ha, hl] at h
        obtain rfl : b :: bs = r := Option.some.inj h
        rw [List.map_cons, List.map_cons, hn a (List.mem_cons_self ..) b ha,
          mapM_map f F G l bs (fun x hx => hn x (List.mem_cons_of_mem _ hx)) hl]

theorem mapM_mem_of {α γ : Type} (f : α → Option γ) :
    ∀ (l : List α) (r : List γ), l.mapM f = some r → ∀ x ∈ l, ∀ y, f x = some y → y ∈ r
  | [], _, _, x, hx, _, _ => by cases hx
  | a :: l, r, h, x, hx, y, hy => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => rw [ha] at h; exact absurd h (by simp)
    | some b =>
      cases hl : l.mapM f with
      | none => rw [ha, hl] at h; exact absurd h (by simp)
      | some bs =>
        rw [ha, hl] at h
        obtain rfl : b :: bs = r := Option.some.inj h
        rcases List.mem_cons.1 hx with rfl | hx
        · rw [ha] at hy
          rw [Option.some.inj hy]
          exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (mapM_mem_of f l bs hl x hx y hy)

/-- **The shapes of one lookup's rows on the table**: one for each claim. -/
theorem tableRowsOf_sh (m : Wf.Matrix) (l : WfLookup) (keys : List Lkp.Keys)
    (rows : List TensorRow) (h : tableRowsOf m l keys = some rows) (hm : m.ok = true)
    (hf : Wf.fitsMatrix m l = true) (hl : Wf.lookupOk Wf.fBits l = true) :
    rows.map rowSh = keys.map fun k => ⟨false, some m.kRow, m.kCol, k.masks.map (·.1)⟩ := by
  have hlow := tableRowsOf_low m l keys rows h hm hf hl
  have hdw : l.digitWeight ≠ [] := by
    have h' := hl
    simp only [Wf.lookupOk, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h'
    exact h'.1.1.1.1.1.1.2
  unfold tableRowsOf at h
  split at h
  · rename_i c
    have e := mapM_map _ rowSh
      (fun x : WfPart × Lkp.Keys => (⟨false, some m.kRow, m.kCol, x.2.masks.map (·.1)⟩ : RowSh))
      _ rows (fun x hx y hy => by
        have hmem : y ∈ rows := mapM_mem_of _ _ rows h x hx y hy
        rw [zipT_eq] at hx
        have hp : x.1 ∈ l.parts := (List.of_mem_zip hx).1
        dsimp only at hy
        split at hy
        · rename_i cc
          simp only [Bool.and_eq_true, beq_iff_eq] at cc
          obtain rfl := Option.some.inj hy
          have hro := Slice.Leaves.runsOk_of hl hp
          have hrn : x.1.runs ≠ [] := by
            have h' := hl
            simp only [Wf.lookupOk, Bool.and_eq_true, List.all_eq_true] at h'
            have h2 := (h'.2 x.1 hp).1
            simp only [Wf.partOk, Bool.and_eq_true, Bool.not_eq_true',
              List.isEmpty_eq_false_iff] at h2
            exact h2.2
          exact rowSh_pending m l x.1 x.2 _
            (pendingRow_ne m l x.1 x.2 _ hrn hdw (runs_pos _ _ 0 hro)) (hlow _ hmem) cc.1.1
        · cases hy) h
    rw [e, zipT_eq]
    have e2 : (l.parts.zip keys).map
        (fun x : WfPart × Lkp.Keys =>
          (⟨false, some m.kRow, m.kCol, x.2.masks.map (·.1)⟩ : RowSh)) =
        ((l.parts.zip keys).map Prod.snd).map fun k =>
          ⟨false, some m.kRow, m.kCol, k.masks.map (·.1)⟩ := by
      rw [List.map_map]
      rfl
    rw [e2, List.map_snd_zip (Nat.le_of_eq (beq_iff_eq.1 c).symm)]
  · cases h

/-- **(B1)**: where the step returns and the guards return, they return the back part behind. The
other named values, the statement, the book and the roots stay. -/
theorem pile_carries (keysOf : β → List (List Lkp.Keys)) (one : OneTime) (cs : Codes)
    (s s' : ChainState β) (hs : layPile keysOf one s = .ok s') (k : Bool) (t : BackSh)
    (h : gPile one (stSh s.d.st) s.idx k (keysSlots (keysOf s.base)) (backSh one.lin cs s) =
      .ok t) : t = backSh one.lin cs s' ∧ ∃ rows, s' = { s with pile := rows } := by
  obtain ⟨-, -, -, -, ha, rfl⟩ := gPile_spec h
  have hlow := layPile_low_admitted keysOf one s s' hs _ ha
  obtain ⟨hm, hall⟩ := admitted_three _ _ _ ha
  unfold layPile at hs
  obtain ⟨_, _, hs⟩ := VerifiableInference.Desc.Third.Law.ok_of_bind hs
  obtain ⟨_, hlen, hs⟩ := VerifiableInference.Desc.Third.Law.ok_of_bind hs
  obtain ⟨rows, hr, hs⟩ := VerifiableInference.Desc.Third.Law.ok_of_bind hs
  obtain ⟨_, _, hs⟩ := VerifiableInference.Desc.Third.Law.ok_of_bind hs
  obtain ⟨_, _, hs⟩ := VerifiableInference.Desc.Third.Law.ok_of_bind hs
  obtain ⟨_, _, hs⟩ := VerifiableInference.Desc.Third.Law.ok_of_bind hs
  obtain rfl := Except.ok.inj hs
  refine ⟨?_, rows.flatten, rfl⟩
  have e0 := mapM_map _ (fun L : List TensorRow => L.map rowSh)
    (fun x : WfLookup × List Lkp.Keys => x.2.map fun k =>
      (⟨false, some one.lin.kRow, one.lin.kCol, k.masks.map (·.1)⟩ : RowSh)) _ rows
    (fun x hx y hy => by
      rw [zipT_eq] at hx
      obtain ⟨a, b⟩ := hall x.1 (List.of_mem_zip hx).1
      exact tableRowsOf_sh (Wf.matrixOf one.lin) x.1 x.2 y hy hm a b)
    (VerifiableInference.Desc.Third.Law.some_of_named hr)
  have e1 : rows.flatten.map rowSh = pileOf one.lin (keysSlots (keysOf s.base)) := by
    rw [List.map_flatten, e0, zipT_eq]
    have e2 : (one.ranges.lookups.zip (keysOf s.base)).map
        (fun x : WfLookup × List Lkp.Keys => x.2.map fun k =>
          (⟨false, some one.lin.kRow, one.lin.kCol, k.masks.map (·.1)⟩ : RowSh)) =
        ((one.ranges.lookups.zip (keysOf s.base)).map Prod.snd).map fun ks => ks.map fun k =>
          ⟨false, some one.lin.kRow, one.lin.kCol, k.masks.map (·.1)⟩ := by
      rw [List.map_map]
      rfl
    rw [e2, List.map_snd_zip (Nat.le_of_eq
      (beq_iff_eq.1 (VerifiableInference.Desc.Third.Law.true_of_need hlen)).symm)]
    unfold pileOf keysSlots
    rw [List.map_flatten, List.map_map]
    congr 1
    refine List.map_congr_left fun ks _ => ?_
    show _ = (ks.map fun k => k.masks.map (·.1)).map _
    rw [List.map_map]
    rfl
  show BackSh.mk _ true _ _ _ _ =
    BackSh.mk (rows.flatten.map rowSh) (pileB one.lin rows.flatten) _ _ _ _
  rw [e1, pileB_of_low one.lin rows.flatten hlow]
  rfl

/-! ## The seal -/

/-- The seal's three clauses, on the shape. owed: the count of rows that waits; own: the own group's
number, if the claim is laid. -/
def sealS (a : StSh) (owed own : Option Nat) : Bool :=
  owed.all (· == 0) && (a.groups.zipIdx.all fun g => g.1.inRun || own == some g.2) &&
    a.oracles.zipIdx.all fun x =>
      !x.1.sampled || (own.bind fun g => a.groups[g]?).any (·.members.contains x.2) ||
        x.1.groups.any fun g => (a.groups[g]?).any (·.inRun)

/-- **They are the library's.** -/
theorem sealS_eq (s : ChainState β) :
    sealS (stSh s.d.st) s.owed (s.lin.map (·.own)) =
      ([("end: no count of rows is owed", s.noneWaits)] ++
        VerifiableInference.Desc.Key.untestedButOwn s).all (·.2) := by
  unfold sealS VerifiableInference.Desc.Key.untestedButOwn
  simp only [List.cons_append, List.nil_append, List.all_cons, List.all_nil, Bool.and_true]
  rw [Bool.and_assoc]
  congr 1
  congr 1
  · show ((s.d.st.groups.toList.map grpSh).zipIdx.all _) = _
    rw [List.zipIdx_map, List.all_map]
    rfl
  · show ((s.d.st.oracles.toList.map orcSh).zipIdx.all _) = _
    rw [List.zipIdx_map, List.all_map]
    congr 1
    funext x
    show (!x.1.sampled ||
      ((s.lin.map (·.own)).bind fun g => (stSh s.d.st).groups[g]?).any (·.members.contains x.2) ||
      x.1.groups.any fun g => ((stSh s.d.st).groups[g]?).any (·.inRun)) = _
    congr 1
    · congr 1
      cases s.lin.map (·.own) with
      | none => rfl
      | some g =>
        show ((stSh s.d.st).groups[g]?).any _ = (s.d.st.groups[g]?).any _
        rw [grp_get]
        cases s.d.st.groups[g]? with
        | none => rfl
        | some G =>
          show G.members.toList.contains x.2 = G.members.contains x.2
          rw [Array.contains_toList]
    · congr 1
      funext g
      rw [grp_get]
      cases s.d.st.groups[g]? <;> rfl

/-- **The seal on the shape**: a test; nothing turns. -/
def gSeal (a : StSh) (owed : Option Nat) (b : BackSh) : Bool := sealS a owed (b.lin.map (·.own))

/-- **The seal accepts just where its three clauses on the shape hold, and returns the state as it
is**: no test on values. -/
theorem seal_law {Cl : Type} (S : LinShape) (cs : Codes) (N : Pieces)
    (inFront : List Fmt.DeclaredRound) (s : ChainState β) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (firstChainEnd (β := β) (Cl := Cl) N inFront).decide s rs gs = .ok s ↔
      gSeal (stSh s.d.st) s.owed (backSh S cs s) = true := by
  have e : gSeal (stSh s.d.st) s.owed (backSh S cs s) =
      sealS (stSh s.d.st) s.owed (s.lin.map (·.own)) := by
    unfold gSeal backSh backOf
    dsimp only
    rw [Option.map_map]
    rfl
  rw [e, sealS_eq, ← refuse_iff]
  show (VerifiableInference.Desc.ChainEnd.refuse
      ([("end: no count of rows is owed", s.noneWaits)] ++
        VerifiableInference.Desc.Key.untestedButOwn s)).map (fun _ => s) = .ok s ↔ _
  cases VerifiableInference.Desc.ChainEnd.refuse
      ([("end: no count of rows is owed", s.noneWaits)] ++
        VerifiableInference.Desc.Key.untestedButOwn s) with
  | error w => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
  | ok u => exact ⟨fun _ => rfl, fun _ => rfl⟩

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.lowB_of_low
#print axioms AtPublicFiles.AtFiles.lowB_spec
#print axioms AtPublicFiles.AtFiles.lowB_cut
#print axioms AtPublicFiles.AtFiles.weightsB_of_lowB
#print axioms AtPublicFiles.AtFiles.pileB_of_low
#print axioms AtPublicFiles.AtFiles.door_of_back
#print axioms AtPublicFiles.AtFiles.passes_of_marks
#print axioms AtPublicFiles.AtFiles.varsMark_all
#print axioms AtPublicFiles.AtFiles.runs_pos
#print axioms AtPublicFiles.AtFiles.pendingRow_ne
#print axioms AtPublicFiles.AtFiles.rowSh_pending
#print axioms AtPublicFiles.AtFiles.ledgerS_spec
#print axioms AtPublicFiles.AtFiles.gPile_spec
#print axioms AtPublicFiles.AtFiles.pile_returns
#print axioms AtPublicFiles.AtFiles.mapM_map
#print axioms AtPublicFiles.AtFiles.mapM_mem_of
#print axioms AtPublicFiles.AtFiles.tableRowsOf_sh
#print axioms AtPublicFiles.AtFiles.pile_carries
#print axioms AtPublicFiles.AtFiles.sealS_eq
#print axioms AtPublicFiles.AtFiles.seal_law
