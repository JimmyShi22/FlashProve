-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/K9RowsAskLaw.lean: THE LAW OF THE TEST `rowsFitB`
(Johnson/Desc/First/Link/K9RowsAsk.lean): ITS
YES IS THE CLOSED INEQUALITY IN THE LETTERS OF `rowsNumber_layers`, `rowsNumber_att`,
`rowsNumber_head`
(RowsNumberAtBatch.lean, AttSkelAtBatch.lean); AND SO, IN THE GOALS' SCOPE, "THE ROWS FIT" AT EVERY
STATE REACHED
IN FRONT OF EVERY ONE OF THE 25 BATCHINGS. Statements and proofs.

  THE TIES OF THE SECOND TEXTS: `firstB_is` (= firstOf tl tl.NM), `readsB_is` (= readsLenOf at the
    skeleton's pairs), `layPairs_is`, `attPairs_is`, `headTabs_is` (by rfl), `headPairs_is`.
  `rowsFitB_iff`: the test's yes, written out: an "if and only if".
  `fit_layers`, `fit_att`, `fit_head`: **a yes at the segment X ⊢ rowsTerm X.tl ‹the plan's claims›
‹the
    skeleton off the plan› ≤ p.rows, p := IM.k9At Z l.**
  `built_tl`: the blank letters' built segment has the public part's segment's structure (by
    `zip_at` with `blank_built`).
  `RowsAsked Z`: at each l < 25 a segment stands in Z.p.built.links and the test says yes of it.
  `rows_fit_layers`, `rows_fit_att`, `rows_fit_head`: **RowsAsked Z · the scope · reached in front
of the
    batching ⊢ there are the ledger G, the list funs, the structure tl and K9's numbers p, and at
    every structure tl' that reads as tl: G.planClaimsF + top8 tl' funs ≤ p.rows.**
The test takes the places with rounds as an argument: here at `ProofFile.k9Stretches Z`.
Limits. `RowsAsked Z` IS A PREMISE HERE. That the fixed (blanked)
structure
reads as the state's, and that the snapshot's ledger is the state's, is the caller's. No soundness
statement.

-/
import Johnson.Desc.First.Link.K9RowsAsk
import Johnson.Desc.First.Link.Law.AttSkelAtBatch
import Johnson.Desc.First.Link.Law.K9Row11
import Johnson.Desc.ProofFile.Law.MakerPublic
import Johnson.IMR.OwnSeat
import Johnson.IMR.LinkSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K9Asks
open OnBytes OnBytes.Model
open OnBytes.Tie.Pv.Tail.Port (firstOf)
open OnBytes.Tie.Pv.Tail.Closed (shapesOf layShapes laidShapes attShapes attAsks asPart nScores
    place
  rep)
open Cb.Pv.Tail (Tab)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.LinkJoin (rowsTerm readsLenOf planClaimsAt rowsRead rowsNumber_layers
  rowsNumber_att rowsNumber_head)
open VerifiableInference.Desc.Kinds.Head.Law (tabsOfPlan)
open Johnson.Desc.First.Walk.Tied (Reach)

/-! ## The ties -/

theorem foldl_add {α : Type} (f : α → ℕ) : ∀ (l : List α) (a : ℕ),
    l.foldl (fun n x => n + f x) a = a + (l.map f).sum
  | [], a => by simp
  | x :: l, a => by
    rw [List.foldl_cons, foldl_add f l, List.map_cons, List.sum_cons, Nat.add_assoc]

theorem sum_range (f : ℕ → ℕ) : ∀ n, ((List.range n).map f).sum = ∑ x ∈ Finset.range n, f x
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_range f n, Finset.sum_range_succ]
    simp

theorem firstB_is (tl : HTailF2) : firstB tl = firstOf tl tl.NM := by
  unfold firstB firstOf
  rw [foldl_add, Nat.zero_add, sum_range]

/-- A table's matrix and rows in a block. -/
def pairOf (t : Tab) : ℕ × ℕ := (t.mat, t.len)

theorem readsB_is (NM : ℕ) (mats : Array TMat) (sh : List Tab) :
    readsB NM mats (sh.map pairOf) = readsLenOf NM mats sh := by
  unfold readsB readsLenOf
  rw [foldl_add, Nat.zero_add]
  congr 1
  refine List.map_congr_left fun mu _ => ?_
  rw [foldl_add, Nat.zero_add, List.map_map]
  rfl

theorem layPairs_is {P : Layer.Pub} {g : ℕ} {ps : List (ℕ × ℕ)} (h : layPairs P g = some ps) :
    ps = (layShapes P g).map pairOf := by
  unfold layPairs at h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
  unfold layShapes laidShapes
  rw [hx]
  simp [List.map_flatMap, pairOf, Function.comp_def]

theorem rep_is : ∀ (k : ℕ) (l : List (ℕ × ℕ × ℕ)), repB k l = rep k l
  | 0, _ => rfl
  | k + 1, l => by
    show l ++ repB k l = l ++ rep k l
    rw [rep_is k l]

theorem attTriples_is (S : Attention.Shape) (k : ℕ) : attTriples S k = attAsks S k := by
  unfold attTriples attAsks asPart
  simp only [rep_is]

theorem place_pairs : ∀ (l : List (ℕ × ℕ × ℕ)) (p : ℕ),
    (place l p).map pairOf = l.map fun a => (a.1, a.2.1)
  | [], _ => rfl
  | a :: l, p => by
    show pairOf ⟨a.1, a.2.1, p⟩ :: (place l (p + a.2.2)).map pairOf = _
    rw [place_pairs l]
    rfl

theorem attPairs_is (S : Attention.Shape) :
    attPairs S = (attShapes S (nScores S)).map pairOf := by
  unfold attPairs attShapes
  rw [place_pairs, attTriples_is]
  rfl

theorem headTabs_is (h : Head.Shape) (hp : Head.HPlanH2) : headTabs h hp = tabsOfPlan h hp := rfl

theorem headPairs_is {h : Head.Shape} {hp : Head.HPlanH2} {ps : List (ℕ × ℕ)}
    (e : headPairs h hp = some ps) :
    ∃ t0, tabsOfPlan h hp = some t0 ∧ ps = (shapesOf t0.funs).map pairOf := by
  unfold headPairs at e
  obtain ⟨t0, h0, rfl⟩ := Option.map_eq_some_iff.1 e
  refine ⟨t0, h0, ?_⟩
  unfold shapesOf
  rw [List.map_map]
  rfl

/-! ## The test's yes -/

theorem rowsFitB_iff (Z : ProofFile.Pub) (l : ℕ) (X : Stages.LinkH) :
    rowsFitB (ProofFile.k9Stretches Z) Z l X = true ↔ ∃ n ps p, claimsAt Z.p.X l = some n ∧
      pairsAt Z.p.X l = some ps ∧ IM.k9At Z l = some p ∧
      n + (firstB X.tl + readsB X.tl.NM X.tl.mats ps * X.tl.stepF) ≤ p.rows := by
  unfold rowsFitB
  constructor
  · intro h
    split at h
    · rename_i n ps p e1 e2 e3
      exact ⟨n, ps, p, e1, e2, e3, of_decide_eq_true h⟩
    · exact nomatch h
  · rintro ⟨n, ps, p, e1, e2, e3, h⟩
    have e3' : ProofFile.k9Where (ProofFile.k9Stretches Z) l = some p := e3
    rw [e1, e2, e3']
    exact decide_eq_true h

theorem fit_layers {Z : ProofFile.Pub} {g : ℕ} (hg : g < 12) {X : Stages.LinkH}
    (h : rowsFitB (ProofFile.k9Stretches Z) Z (2 * g) X = true) :
    ∃ n p, planClaimsAt Z.p.X (2 * g) = some n ∧ IM.k9At Z (2 * g) = some p ∧
      rowsTerm X.tl n (layShapes Z.p.X.layers g) ≤ p.rows := by
  obtain ⟨n, ps, p, e1, e2, e3, h⟩ := (rowsFitB_iff Z _ X).1 h
  have n24 : 2 * g ≠ 24 := by omega
  have ev : 2 * g % 2 = 0 := by omega
  have dv : 2 * g / 2 = g := by omega
  unfold claimsAt at e1
  unfold pairsAt at e2
  rw [if_neg n24, if_pos ev, dv] at e1 e2
  refine ⟨n, p, ?_, e3, ?_⟩
  · unfold planClaimsAt
    rw [if_pos ev, dv]
    exact e1
  · rw [layPairs_is e2, readsB_is, firstB_is] at h
    exact h

theorem fit_att {Z : ProofFile.Pub} {g : ℕ} {X : Stages.LinkH}
    (h : rowsFitB (ProofFile.k9Stretches Z) Z (2 * g + 1) X = true) :
    ∃ a p, Z.p.X.A[g]? = some a ∧ IM.k9At Z (2 * g + 1) = some p ∧
      rowsTerm X.tl a.nLin (attShapes a.S (nScores a.S)) ≤ p.rows := by
  obtain ⟨n, ps, p, e1, e2, e3, h⟩ := (rowsFitB_iff Z _ X).1 h
  have n24 : 2 * g + 1 ≠ 24 := by omega
  have od : ¬ (2 * g + 1) % 2 = 0 := by omega
  have dv : (2 * g + 1) / 2 = g := by omega
  unfold claimsAt at e1
  unfold pairsAt at e2
  rw [if_neg n24, if_neg od, dv] at e1 e2
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 e1
  obtain ⟨a', ha', rfl⟩ := Option.map_eq_some_iff.1 e2
  obtain rfl : a = a' := Option.some.inj (ha.symm.trans ha')
  refine ⟨a, p, ha, e3, ?_⟩
  rw [attPairs_is, readsB_is, firstB_is] at h
  exact h

theorem fit_head {Z : ProofFile.Pub} {X : Stages.LinkH}
    (h : rowsFitB (ProofFile.k9Stretches Z) Z 24 X = true) :
    ∃ t0 p, tabsOfPlan Z.p.X.hS Z.p.X.H = some t0 ∧ IM.k9At Z 24 = some p ∧
      rowsTerm X.tl Z.p.X.H.nLin (shapesOf t0.funs) ≤ p.rows := by
  obtain ⟨n, ps, p, e1, e2, e3, h⟩ := (rowsFitB_iff Z _ X).1 h
  unfold claimsAt at e1
  unfold pairsAt at e2
  rw [if_pos rfl] at e1 e2
  obtain rfl := Option.some.inj e1
  obtain ⟨t0, h0, rfl⟩ := headPairs_is e2
  refine ⟨t0, p, h0, e3, ?_⟩
  rw [readsB_is, firstB_is] at h
  exact h

/-! ## To the states -/

/-- The blank letters' built segment has the public part's segment's structure. -/
theorem built_tl {mk : ProofFile.LinksBy} {Z : ProofFile.Pub} {G : ProofFile.Ground} (hG : ProofFile.blankBy mk Z = some G)
    {l : ℕ} {Xl : Stages.LinkH} (e3 : G.built[l]? = some Xl) :
    ∃ X, Z.p.built.links[l]? = some X ∧ Xl.tl = X.tl := by
  obtain ⟨links, e⟩ := _root_.Meaning.K2.blank_built hG
  rw [e] at e3
  obtain ⟨b, hb, eT, -, -⟩ := zip_at e3
  exact ⟨b, hb, eT⟩

/-- At each segment's number a segment stands, and the test says yes of it. -/
def RowsAsked (Z : ProofFile.Pub) : Prop :=
  ∀ l < 25, ∃ X, Z.p.built.links[l]? = some X ∧ rowsFitB (ProofFile.k9Stretches Z) Z l X = true

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

theorem rows_fit_layers (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope Pb = true)
    (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {z : ProofFile.InstPub} {s' : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (28 * g + 9) (z, s')) :
    ∃ G funs tl p, s'.fork? = some G ∧ s'.funs? = some funs ∧ s'.tl? = some tl ∧
      IM.k9At Z (2 * g) = some p ∧
      ∀ tl', rowsRead tl' = rowsRead tl → G.planClaimsF + K9L.top8 tl' funs ≤ p.rows := by
  obtain ⟨G, funs, Xl, n, tl, a1, a2, a3, hX, hn, H⟩ := rowsNumber_layers hS hR O hg h
  obtain ⟨X, x1, x2⟩ := built_tl O.blank hX
  obtain ⟨X', y1, y2⟩ := hE (2 * g) (by omega)
  obtain rfl : X = X' := Option.some.inj (x1.symm.trans y1)
  obtain ⟨n', p, b1, b2, b3⟩ := fit_layers hg y2
  have eW : Bs.G₀.W = Z.p.X := ProofFile.Law.blankBy_W O.blank
  rw [eW] at hn H
  obtain rfl : n = n' := Option.some.inj (hn.symm.trans b1)
  refine ⟨G, funs, tl, p, a1, a2, a3, b2, fun tl' ht => ?_⟩
  rw [H tl' ht, x2]
  exact b3

theorem rows_fit_att (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope Pb = true)
    (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {z : ProofFile.InstPub} {s' : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g + 1) + 9) (z, s')) :
    ∃ G funs tl p, s'.fork? = some G ∧ s'.funs? = some funs ∧ s'.tl? = some tl ∧
      IM.k9At Z (2 * g + 1) = some p ∧
      ∀ tl', rowsRead tl' = rowsRead tl → G.planClaimsF + K9L.top8 tl' funs ≤ p.rows := by
  obtain ⟨G, funs, Xl, a, tl, a1, a2, a3, hX, ha, H⟩ := rowsNumber_att hS hR O hg h
  obtain ⟨X, x1, x2⟩ := built_tl O.blank hX
  obtain ⟨X', y1, y2⟩ := hE (2 * g + 1) (by omega)
  obtain rfl : X = X' := Option.some.inj (x1.symm.trans y1)
  obtain ⟨a', p, b1, b2, b3⟩ := fit_att y2
  have eW : Bs.G₀.W = Z.p.X := ProofFile.Law.blankBy_W O.blank
  rw [eW] at ha
  obtain rfl : a = a' := Option.some.inj (ha.symm.trans b1)
  refine ⟨G, funs, tl, p, a1, a2, a3, b2, fun tl' ht => ?_⟩
  rw [H tl' ht, x2]
  exact b3

theorem rows_fit_head (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope Pb = true)
    (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {z : ProofFile.InstPub} {s' : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) 347 (z, s')) :
    ∃ G funs tl p, s'.fork? = some G ∧ s'.funs? = some funs ∧ s'.tl? = some tl ∧
      IM.k9At Z 24 = some p ∧
      ∀ tl', rowsRead tl' = rowsRead tl → G.planClaimsF + K9L.top8 tl' funs ≤ p.rows := by
  obtain ⟨G, funs, Xl, t0, tl, a1, a2, a3, hX, h0, H⟩ := rowsNumber_head hS hR O h
  obtain ⟨X, x1, x2⟩ := built_tl O.blank hX
  obtain ⟨X', y1, y2⟩ := hE 24 (by omega)
  obtain rfl : X = X' := Option.some.inj (x1.symm.trans y1)
  obtain ⟨t0', p, b1, b2, b3⟩ := fit_head y2
  have eW : Bs.G₀.W = Z.p.X := ProofFile.Law.blankBy_W O.blank
  rw [eW] at h0 H
  obtain rfl : t0 = t0' := Option.some.inj (h0.symm.trans b1)
  refine ⟨G, funs, tl, p, a1, a2, a3, b2, fun tl' ht => ?_⟩
  rw [H tl' ht, x2]
  exact b3

end VerifiableInference.Desc.K9Asks

#print axioms VerifiableInference.Desc.K9Asks.foldl_add
#print axioms VerifiableInference.Desc.K9Asks.sum_range
#print axioms VerifiableInference.Desc.K9Asks.firstB_is
#print axioms VerifiableInference.Desc.K9Asks.readsB_is
#print axioms VerifiableInference.Desc.K9Asks.layPairs_is
#print axioms VerifiableInference.Desc.K9Asks.rep_is
#print axioms VerifiableInference.Desc.K9Asks.attTriples_is
#print axioms VerifiableInference.Desc.K9Asks.place_pairs
#print axioms VerifiableInference.Desc.K9Asks.attPairs_is
#print axioms VerifiableInference.Desc.K9Asks.headTabs_is
#print axioms VerifiableInference.Desc.K9Asks.headPairs_is
#print axioms VerifiableInference.Desc.K9Asks.rowsFitB_iff
#print axioms VerifiableInference.Desc.K9Asks.fit_layers
#print axioms VerifiableInference.Desc.K9Asks.fit_att
#print axioms VerifiableInference.Desc.K9Asks.fit_head
#print axioms VerifiableInference.Desc.K9Asks.built_tl
#print axioms VerifiableInference.Desc.K9Asks.rows_fit_layers
#print axioms VerifiableInference.Desc.K9Asks.rows_fit_att
#print axioms VerifiableInference.Desc.K9Asks.rows_fit_head
