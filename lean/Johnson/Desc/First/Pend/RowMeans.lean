-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Pend/RowMeans.lean: THEOREMS: WHAT A YES OF THE PENDING ROW'S TEXT GIVES
(Johnson/Desc/First/Pend/Row.lean: `pendingRowO`, with `takeEntry`, `span`, `addClaim`): just when
it returns, and what. No block imports this file, and no byte of the text turns.

What is said (each an "if and only if").
  `pendingRowO_means`: **`pendingRowO … = .ok (row, oracles')` just if `RowMeans …`**: a proposition
    in plain terms with one conjunct for each mark [4] to [22] of the text's own list of tests, and
    with the row and the oracle messages behind written out: the row's weights are the blocks of the
    stretch first .. last of Gamma; its point is the merge's, reversed; its one mask entry is the
    ledger's next real entry, under beta; its target is fv'; and of the oracle messages the one
    ledger alone turns: one entry is taken.
  `pendingRowO_iff`: the same step by step, in the text's own order, still in terms of `span`,
    `addClaim`, `Own.weightsOnRows` and `takeEntry`.
  `takeEntry_iff` [22] · `addClaim_iff` [13] to [16] · `gamma_iff`: the claims' weights added one
    after the other: every claim meets `ClaimFits` at Gamma's number of rows, which no adding turns
    (`added_size`), and Gamma is `gammaOf` · `span_iff` [8]: every claim's unit is in the layout,
    and the span is `spanOf` · `weightsOnRows_iff` [17] to [19].

WHAT THE TESTS READ. The plan's numbers (the layout of W, the number of claims, the table's shape);
sizes of what the merge left (how many claims, how many coordinates the point has, how many factors
a claim has, how many weights `wsGamma` makes of them); the statement's ledger of the message of
index masks. NO TEST READS A VALUE: not a weight, not beta, not fv', not a coordinate of the point.
fv' is a value that the prover has shown; it goes into the row's target untested: that is what the
row is for (the head of Row.lean).

THEY ADD NO SECOND, INDEPENDENT EYE: the right sides are the text read aloud; `spanOf`, `gammaOf`
and `added` are the text's own folds without their refusals.

Helpers that are called, not typed again: `bind_ok`, `throw_bind`, `unless_ok`
(Johnson/Desc/First/Pend/RowOk.lean); `weightsOnRows_isSome_iff`, `weightsOnRows_some`
(Johnson/Desc/Own/StretchAgree.lean).

Limits. By the text's own list [12], [13], [16] and [17] to [19] cannot refuse behind the tests in
front of them; no theorem here says so. Nothing on what Gamma's entries mean. Nothing on soundness,
on an honest prover or on hiding. A yes on made-up data, and a no for each mark that can be reached:
RowToys.lean [not in this library], beside this file.

-/
import Johnson.Desc.First.Pend.RowOk
import Johnson.Desc.Own.StretchAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Pend
open OnBytes OnBytes.Params OnBytes.Model

/-! ## 0 Steps of a text that can refuse -/

theorem bind_iff {α β : Type} (x : Except String α) (f : α → Except String β) (y : β) :
    (x >>= f) = .ok y ↔ ∃ a, x = .ok a ∧ f a = .ok y :=
  ⟨bind_ok, by rintro ⟨a, rfl, h⟩; exact h⟩

theorem unless_iff {β : Type} {c : Prop} [Decidable c] {e : String}
    {f : PUnit → Except String β} {y : β} :
    (if c then (pure PUnit.unit >>= f) else ((throw e : Except String PUnit) >>= f)) = .ok y ↔
      c ∧ f PUnit.unit = .ok y :=
  ⟨unless_ok, by rintro ⟨hc, h⟩; rw [if_pos hc]; exact h⟩

/-! ## 1 The mask entry [22] -/

theorem takeEntry_iff (l : Ledger) (c : ℕ) (l' : Ledger) :
    takeEntry l = some (c, l') ↔
      l.closed = false ∧ 0 < l.left ∧
        c = nextEntry l.rows l.logRows (2 ^ l.logRows) l.next ∧
        l' = { l with next := c + 1, left := l.left - 1 } := by
  unfold takeEntry
  by_cases h : (!l.closed && decide (0 < l.left)) = true
  · rw [if_pos h]
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
    simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨h.1, h.2, rfl, rfl⟩
    · rintro ⟨_, _, rfl, rfl⟩
      exact ⟨rfl, rfl⟩
  · rw [if_neg h]
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
    exact ⟨fun e => (by cases e), fun e => absurd ⟨e.1, e.2.1⟩ h⟩

/-! ## 2 One claim's weights added [13] [14] [15] [16] -/

/-- Gamma with the weights v added from row off on. -/
def added (Gamma v : Array E) (off : ℕ) : Array E :=
  (v.foldl (fun s x => (s.1.modify s.2 fun y => addE y x, s.2 + 1)) (Gamma, off)).1

theorem addClaim_iff (lay : WsLay) (Gamma : Array E) (c : WsRecClaim) (G : Array E) :
    addClaim lay Gamma c = .ok G ↔
      ∃ u, lay.U[c.ui]? = some u ∧ (wsGamma u c oneE).size = u.rows ∧
        c.f.length = u.g.length ∧ u.off + u.rows ≤ Gamma.size ∧
        G = added Gamma (wsGamma u c oneE) u.off := by
  unfold addClaim
  cases hu : lay.U[c.ui]? with
  | none =>
    exact ⟨fun e => absurd e (by simp [throw, throwThe, MonadExceptOf.throw]),
      by rintro ⟨u, h, _⟩; cases h⟩
  | some u =>
    simp only [unless_iff, beq_iff_eq, Option.some.injEq, exists_eq_left']
    constructor
    · rintro ⟨h1, h2, h3, e⟩
      exact ⟨h1, h2, h3, (Except.ok.inj e).symm⟩
    · rintro ⟨h1, h2, h3, rfl⟩
      exact ⟨h1, h2, h3, rfl⟩

theorem added_size (Gamma v : Array E) (off : ℕ) : (added Gamma v off).size = Gamma.size := by
  have key : ∀ (l : List E) (s : Array E × ℕ),
      (l.foldl (fun s x => (s.1.modify s.2 fun y => addE y x, s.2 + 1)) s).1.size = s.1.size := by
    intro l
    induction l with
    | nil => intro s; rfl
    | cons x t ih =>
      intro s
      rw [List.foldl_cons, ih]
      simp
  unfold added
  rw [← Array.foldl_toList]
  exact key _ _

/-- A claim's unit; a unit without a row where the layout has none of that number. -/
def unitOf (lay : WsLay) (c : WsRecClaim) : WsUnit := (lay.U[c.ui]?).getD default

/-- Gamma with all the claims' weights added, in their order. -/
def gammaOf (lay : WsLay) (recs : List WsRecClaim) (G0 : Array E) : Array E :=
  recs.foldl (fun G c => added G (wsGamma (unitOf lay c) c oneE) (unitOf lay c).off) G0

/-- What [13] to [16] ask of one claim, at a Gamma of n rows. -/
def ClaimFits (lay : WsLay) (n : ℕ) (c : WsRecClaim) : Prop :=
  (∃ u, lay.U[c.ui]? = some u) ∧ (wsGamma (unitOf lay c) c oneE).size = (unitOf lay c).rows ∧
    c.f.length = (unitOf lay c).g.length ∧ (unitOf lay c).off + (unitOf lay c).rows ≤ n

theorem gamma_iff (lay : WsLay) : ∀ (recs : List WsRecClaim) (G0 G : Array E),
    recs.foldlM (addClaim lay) G0 = .ok G ↔
      (∀ c ∈ recs, ClaimFits lay G0.size c) ∧ G = gammaOf lay recs G0
  | [], G0, G => by
    simp only [List.foldlM_nil, gammaOf, List.foldl_nil, List.not_mem_nil, false_imp_iff,
      implies_true, true_and]
    exact ⟨fun e => (Except.ok.inj e).symm, fun e => by rw [e]; rfl⟩
  | c :: t, G0, G => by
    rw [List.foldlM_cons, bind_iff]
    constructor
    · rintro ⟨G1, h1, h2⟩
      obtain ⟨u, hu, a1, a2, a3, rfl⟩ := (addClaim_iff lay G0 c G1).1 h1
      have eu : unitOf lay c = u := by unfold unitOf; rw [hu]; rfl
      obtain ⟨b1, b2⟩ := (gamma_iff lay t _ G).1 h2
      rw [added_size] at b1
      refine ⟨fun d hd => ?_, ?_⟩
      · rcases List.mem_cons.1 hd with rfl | hd
        · exact ⟨⟨u, hu⟩, by rw [eu]; exact a1, by rw [eu]; exact a2, by rw [eu]; exact a3⟩
        · exact b1 d hd
      · rw [b2, gammaOf, gammaOf, List.foldl_cons, eu]
    · rintro ⟨h, rfl⟩
      obtain ⟨⟨u, hu⟩, a1, a2, a3⟩ := h c (List.mem_cons_self ..)
      have eu : unitOf lay c = u := by unfold unitOf; rw [hu]; rfl
      rw [eu] at a1 a2 a3
      refine ⟨_, (addClaim_iff lay G0 c _).2 ⟨u, hu, a1, a2, a3, rfl⟩, ?_⟩
      refine (gamma_iff lay t _ _).2 ⟨fun d hd => ?_, ?_⟩
      · rw [added_size]
        exact h d (List.mem_cons_of_mem _ hd)
      · rw [gammaOf, gammaOf, List.foldl_cons, eu]

/-! ## 3 The span [8] -/

/-- The rows that the claims' units span, from r on. -/
def spanOf (lay : WsLay) (recs : List WsRecClaim) (r : ℕ × ℕ) : ℕ × ℕ :=
  recs.foldl (fun r c =>
    (min r.1 (unitOf lay c).off, max r.2 ((unitOf lay c).off + (unitOf lay c).rows))) r

/-- One step of `span`. -/
def spanStep (lay : WsLay) (r : ℕ × ℕ) (c : WsRecClaim) : Except String (ℕ × ℕ) :=
  match lay.U[c.ui]? with
  | some u => pure (min r.1 u.off, max r.2 (u.off + u.rows))
  | none => throw badRows

theorem span_eq (lay : WsLay) (recs : List WsRecClaim) :
    span lay recs = recs.foldlM (spanStep lay) (2 ^ 64 - 1, 0) := by
  unfold span
  congr 1
  funext r c
  unfold spanStep
  cases lay.U[c.ui]? <;> rfl

theorem spanFrom_iff (lay : WsLay) : ∀ (recs : List WsRecClaim) (r0 r : ℕ × ℕ),
    recs.foldlM (spanStep lay) r0 = .ok r ↔
      (∀ c ∈ recs, ∃ u, lay.U[c.ui]? = some u) ∧ r = spanOf lay recs r0
  | [], r0, r => by
    simp only [List.foldlM_nil, spanOf, List.foldl_nil, List.not_mem_nil, false_imp_iff,
      implies_true, true_and]
    exact ⟨fun e => (Except.ok.inj e).symm, fun e => by rw [e]; rfl⟩
  | c :: t, r0, r => by
    rw [List.foldlM_cons, bind_iff]
    cases hu : lay.U[c.ui]? with
    | none =>
      constructor
      · rintro ⟨r1, h1, _⟩
        unfold spanStep at h1
        rw [hu] at h1
        cases h1
      · rintro ⟨h, _⟩
        obtain ⟨u, hu'⟩ := h c (List.mem_cons_self ..)
        rw [hu] at hu'
        cases hu'
    | some u =>
      have eu : unitOf lay c = u := by unfold unitOf; rw [hu]; rfl
      have es : spanStep lay r0 c = .ok (min r0.1 u.off, max r0.2 (u.off + u.rows)) := by
        unfold spanStep; rw [hu]; rfl
      constructor
      · rintro ⟨r1, h1, h2⟩
        rw [es] at h1
        obtain rfl := Except.ok.inj h1
        obtain ⟨b1, b2⟩ := (spanFrom_iff lay t _ r).1 h2
        refine ⟨fun d hd => ?_, ?_⟩
        · rcases List.mem_cons.1 hd with rfl | hd
          · exact ⟨u, hu⟩
          · exact b1 d hd
        · rw [b2, spanOf, spanOf, List.foldl_cons, eu]
      · rintro ⟨h, rfl⟩
        refine ⟨_, es, (spanFrom_iff lay t _ _).2
          ⟨fun d hd => h d (List.mem_cons_of_mem _ hd), ?_⟩⟩
        rw [spanOf, spanOf, List.foldl_cons, eu]

theorem span_iff (lay : WsLay) (recs : List WsRecClaim) (r : ℕ × ℕ) :
    span lay recs = .ok r ↔
      (∀ c ∈ recs, ∃ u, lay.U[c.ui]? = some u) ∧ r = spanOf lay recs (2 ^ 64 - 1, 0) := by
  rw [span_eq, spanFrom_iff]

/-! ## 4 The row -/

/-- **JUST WHEN `pendingRowO` RETURNS, AND WHAT**, step by step, in the text's own order. -/
theorem pendingRowO_iff (lay : WsLay) (indexMasks : ℕ) (o : WsForkOut) (claims : ℕ) (S : LinShape)
    (oracles oracles' : Array Oracle) (row : TensorRow) :
    pendingRowO lay indexMasks o claims S oracles = .ok (row, oracles') ↔
      lay.m0 = S.matrixRows ∧ o.recs ≠ [] ∧ o.recs.length = claims ∧ o.rm.size = lay.lk ∧
      ∃ first last, span lay o.recs = .ok (first, last) ∧
        first < last ∧ last ≤ lay.m0 ∧ S.kRow ≤ 62 ∧ lay.m0 ≤ 2 ^ S.kRow ∧
      ∃ Gamma, o.recs.foldlM (addClaim lay) (Array.replicate last zeroE) = .ok Gamma ∧
      ∃ g, Own.weightsOnRows S first (Gamma.extract first last) = some g ∧
      ∃ l, (oracles[indexMasks]?).bind (·.ledger) = some l ∧
      ∃ c l', takeEntry l = some (c, l') ∧
        row = { g := g, psi := o.rm.toList.reverse, masks := [(⟨indexMasks, c⟩, o.beta)],
                target := o.fvp } ∧
        oracles' = oracles.modify indexMasks fun x => { x with ledger := some l' } := by
  constructor
  · intro h
    unfold pendingRowO at h
    obtain ⟨h4, h⟩ := unless_ok h
    obtain ⟨h5, h⟩ := unless_ok h
    obtain ⟨h6, h⟩ := unless_ok h
    obtain ⟨h7, h⟩ := unless_ok h
    obtain ⟨⟨first, last⟩, hs, h⟩ := bind_ok h
    obtain ⟨h9, h⟩ := unless_ok h
    obtain ⟨h10, h⟩ := unless_ok h
    obtain ⟨h11, h⟩ := unless_ok h
    obtain ⟨h12, h⟩ := unless_ok h
    obtain ⟨Gamma, hG, h⟩ := bind_ok h
    refine ⟨by simpa using h4, by simpa using h5, by simpa using h6, by simpa using h7, first, last,
      hs, h9, h10, h11, h12, Gamma, hG, ?_⟩
    split at h
    · rename_i g hg
      split at h
      · rename_i l hl
        split at h
        · rename_i c l' ht
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          exact ⟨g, hg, l, hl, c, l', ht, h.1.symm, h.2.symm⟩
        · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
      · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
    · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  · rintro ⟨h4, h5, h6, h7, first, last, hs, h9, h10, h11, h12, Gamma, hG, g, hg, l, hl, c, l', ht,
      rfl, rfl⟩
    unfold pendingRowO
    refine unless_iff.2 ⟨by simpa using h4, ?_⟩
    refine unless_iff.2 ⟨by simpa using h5, ?_⟩
    refine unless_iff.2 ⟨by simpa using h6, ?_⟩
    refine unless_iff.2 ⟨by simpa using h7, ?_⟩
    refine (bind_iff _ _ _).2 ⟨(first, last), hs, ?_⟩
    refine unless_iff.2 ⟨h9, ?_⟩
    refine unless_iff.2 ⟨h10, ?_⟩
    refine unless_iff.2 ⟨h11, ?_⟩
    refine unless_iff.2 ⟨h12, ?_⟩
    refine (bind_iff _ _ _).2 ⟨Gamma, hG, ?_⟩
    simp only [hg, hl, ht]
    rfl

theorem weightsOnRows_iff (S : LinShape) (first : ℕ) (values : Array E) (g : List Tensor) :
    Own.weightsOnRows S first values = some g ↔
      (first + values.size ≤ S.matrixRows ∧ S.kRow < 63 ∧ first + values.size ≤ 2 ^ S.kRow ∧
        ((stretchBlocks S.kRow first values (2 * S.kRow + 2) first).map
          fun t => 2 ^ t.denseVars.length).sum = values.size) ∧
      g = stretchBlocks S.kRow first values (2 * S.kRow + 2) first := by
  constructor
  · intro h
    exact ⟨(Own.weightsOnRows_isSome_iff S first values).1 (by rw [h]; rfl),
      Own.weightsOnRows_some h⟩
  · rintro ⟨h, rfl⟩
    obtain ⟨g', hg'⟩ :=
      Option.isSome_iff_exists.1 ((Own.weightsOnRows_isSome_iff S first values).2 h)
    rw [hg', Own.weightsOnRows_some hg']

/-- **WHAT A YES OF `pendingRowO` GIVES, IN PLAIN TERMS**: one conjunct for each mark of the text's
list of tests, and what the row and the oracle messages behind are. -/
def RowMeans (lay : WsLay) (indexMasks : ℕ) (o : WsForkOut) (claims : ℕ) (S : LinShape)
    (oracles oracles' : Array Oracle) (row : TensorRow) : Prop :=
  let first := (spanOf lay o.recs (2 ^ 64 - 1, 0)).1
  let last := (spanOf lay o.recs (2 ^ 64 - 1, 0)).2
  let values := (gammaOf lay o.recs (Array.replicate last zeroE)).extract first last
  let blocks := stretchBlocks S.kRow first values (2 * S.kRow + 2) first
  -- [4] the layout has as many rows as the table
  lay.m0 = S.matrixRows ∧
  -- [5] there is a claim; [6] as many claims as the plan says
  o.recs ≠ [] ∧ o.recs.length = claims ∧
  -- [7] the point has the layout's column bits
  o.rm.size = lay.lk ∧
  -- [8] every claim's unit is in the layout
  (∀ c ∈ o.recs, ∃ u, lay.U[c.ui]? = some u) ∧
  -- [9] the span is not empty; [10] it ends inside the layout
  first < last ∧ last ≤ lay.m0 ∧
  -- [11] at most 62 row bits; [12] the cube holds the layout
  S.kRow ≤ 62 ∧ lay.m0 ≤ 2 ^ S.kRow ∧
  -- [13] to [16], of every claim
  (∀ c ∈ o.recs, ClaimFits lay last c) ∧
  -- [17] the stretch ends inside the table; [18] fewer than 63 row bits, and it lies in the cube;
  -- [19] the blocks cover it
  (first + values.size ≤ S.matrixRows ∧ S.kRow < 63 ∧ first + values.size ≤ 2 ^ S.kRow ∧
    (blocks.map fun t => 2 ^ t.denseVars.length).sum = values.size) ∧
  -- [20] the message number indexMasks is there; [21] it has a ledger
  ∃ x l, oracles[indexMasks]? = some x ∧ x.ledger = some l ∧
    -- [22] the ledger is open and an entry is left
    l.closed = false ∧ 0 < l.left ∧
    row = { g := blocks, psi := o.rm.toList.reverse,
            masks := [(⟨indexMasks, nextEntry l.rows l.logRows (2 ^ l.logRows) l.next⟩, o.beta)],
            target := o.fvp } ∧
    oracles' = oracles.modify indexMasks fun x =>
      { x with ledger := some { l with
          next := nextEntry l.rows l.logRows (2 ^ l.logRows) l.next + 1, left := l.left - 1 } }

theorem pendingRowO_means (lay : WsLay) (indexMasks : ℕ) (o : WsForkOut) (claims : ℕ)
    (S : LinShape) (oracles oracles' : Array Oracle) (row : TensorRow) :
    pendingRowO lay indexMasks o claims S oracles = .ok (row, oracles') ↔
      RowMeans lay indexMasks o claims S oracles oracles' row := by
  rw [pendingRowO_iff]
  unfold RowMeans
  constructor
  · rintro ⟨h4, h5, h6, h7, first, last, hs, h9, h10, h11, h12, Gamma, hG, g, hg, l, hl, c, l', ht,
      rfl, rfl⟩
    obtain ⟨h8, es⟩ := (span_iff lay o.recs _).1 hs
    have e1 : (spanOf lay o.recs (2 ^ 64 - 1, 0)).1 = first := by rw [← es]
    have e2 : (spanOf lay o.recs (2 ^ 64 - 1, 0)).2 = last := by rw [← es]
    obtain ⟨h13, rfl⟩ := (gamma_iff lay o.recs _ Gamma).1 hG
    rw [Array.size_replicate] at h13
    obtain ⟨h17, rfl⟩ := (weightsOnRows_iff S first _ g).1 hg
    obtain ⟨x, hx, hxl⟩ := Option.bind_eq_some_iff.1 hl
    obtain ⟨h22a, h22b, rfl, rfl⟩ := (takeEntry_iff l c l').1 ht
    simp only [e1, e2]
    exact ⟨h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h17, x, l, hx, hxl, h22a, h22b, rfl, rfl⟩
  · rintro ⟨h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h17, x, l, hx, hxl, h22a, h22b, rfl, rfl⟩
    refine ⟨h4, h5, h6, h7, _, _, (span_iff lay o.recs _).2 ⟨h8, rfl⟩, h9, h10, h11, h12, _,
      (gamma_iff lay o.recs _ _).2 ⟨by rw [Array.size_replicate]; exact h13, rfl⟩, _,
      (weightsOnRows_iff S _ _ _).2 ⟨h17, rfl⟩, l, Option.bind_eq_some_iff.2 ⟨x, hx, hxl⟩, _, _,
      (takeEntry_iff l _ _).2 ⟨h22a, h22b, rfl, rfl⟩, rfl, rfl⟩

end VerifiableInference.Desc.First.Pend

#print axioms VerifiableInference.Desc.First.Pend.bind_iff
#print axioms VerifiableInference.Desc.First.Pend.unless_iff
#print axioms VerifiableInference.Desc.First.Pend.takeEntry_iff
#print axioms VerifiableInference.Desc.First.Pend.addClaim_iff
#print axioms VerifiableInference.Desc.First.Pend.added_size
#print axioms VerifiableInference.Desc.First.Pend.gamma_iff
#print axioms VerifiableInference.Desc.First.Pend.span_eq
#print axioms VerifiableInference.Desc.First.Pend.spanFrom_iff
#print axioms VerifiableInference.Desc.First.Pend.span_iff
#print axioms VerifiableInference.Desc.First.Pend.pendingRowO_iff
#print axioms VerifiableInference.Desc.First.Pend.weightsOnRows_iff
#print axioms VerifiableInference.Desc.First.Pend.pendingRowO_means
