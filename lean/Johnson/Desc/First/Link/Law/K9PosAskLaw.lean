-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/K9PosAskLaw.lean: THE LAW OF THE TEST `posPlanB`
(Johnson/Desc/First/Link/K9PosAsk.lean): ITS YES IS THE CLOSED SENTENCE `PosPlan` (PosAtBatch.lean)
AT THE PLAN's SKELETON; AND SO, IN THE GOALS' SCOPE, THE CLAUSE "pos" AT EVERY STATE REACHED IN
FRONT OF EVERY ONE OF THE 25 BATCHINGS. Statements and proofs.

  THE TIES OF THE SECOND TEXTS: `tripleOf`; `layTriples_is`, `placeB_is`, `attPlaced_is`,
    `headTriples_is`; `colsB_is` (by rfl).
  `tableIn_iff`, `all_gives`: the test's yes at a list of tables is `PosPlan` at that list.
  `pos_fit_layers`, `pos_fit_att`, `pos_fit_head`: **a yes at the segment X ⊢ PosPlan X.tl X.Fp ‹the
    skeleton off the plan›.**
  `built_tl_Fp`: the blank letters' built segment has the public part's segment's structure and
    planned ledger (`zip_at` with `blank_built`).
  `PosAsked Z`: at each l < 25 a segment stands in Z.p.built.links and the test says yes of it.
  `pos_asked_layers`, `pos_asked_att`, `pos_asked_head`: **PosAsked Z; the scope; reached (`RchAt`)
    in front of the batching ⊢ `PosAt π (fixed9 φ a.1.2)`**: the clause pos.
Limits. `PosAsked Z` IS A PREMISE: no running text asks the test. No soundness statement.

-/
import Johnson.Desc.First.Link.K9PosAsk
import Johnson.Desc.First.Link.Law.PosAtBatch
import Johnson.Desc.First.Link.Law.K9RowsAskLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K9Asks
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.Tie.Pv.Tail.Port (colsU)
open OnBytes.Tie.Pv.Tail.Closed (shapesOf layShapes laidShapes attShapes attAsks nScores place)
open Cb.Pv.Tail (Tab)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open VerifiableInference.Desc.LinkJoin (PosPlan PosAt pos_layers pos_att pos_head)
open VerifiableInference.Desc.Kinds.Head.Law (tabsOfPlan)
open Johnson.Desc.First.Walk.Tied (RchAt)
open ProofFile (Cl)

/-! ## The ties -/

/-- A table's matrix, rows in a block and first entry. -/
def tripleOf (t : Tab) : ℕ × ℕ × ℕ := (t.mat, t.len, t.start)

theorem layTriples_is {P : Layer.Pub} {g : ℕ} {ts : List (ℕ × ℕ × ℕ)}
    (h : layTriples P g = some ts) : ts = (layShapes P g).map tripleOf := by
  unfold layTriples at h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
  unfold layShapes laidShapes
  rw [hx]
  simp [List.map_flatMap, tripleOf, Function.comp_def]

theorem placeB_is : ∀ (l : List (ℕ × ℕ × ℕ)) (p : ℕ), placeB l p = (place l p).map tripleOf
  | [], _ => rfl
  | a :: l, p => by
    show (a.1, a.2.1, p) :: placeB l (p + a.2.2) =
      tripleOf ⟨a.1, a.2.1, p⟩ :: (place l (p + a.2.2)).map tripleOf
    rw [placeB_is l]
    rfl

theorem attPlaced_is (S : Attention.Shape) :
    attPlaced S = (attShapes S (nScores S)).map tripleOf := by
  unfold attPlaced attShapes
  rw [placeB_is, attTriples_is]
  rfl

theorem headTriples_is {h : Head.Shape} {hp : Head.HPlanH2} {ts : List (ℕ × ℕ × ℕ)}
    (e : headTriples h hp = some ts) :
    ∃ t0, tabsOfPlan h hp = some t0 ∧ ts = (shapesOf t0.funs).map tripleOf := by
  unfold headTriples at e
  obtain ⟨t0, h0, rfl⟩ := Option.map_eq_some_iff.1 e
  refine ⟨t0, h0, ?_⟩
  unfold shapesOf
  rw [List.map_map]
  rfl

theorem colsB_is (F : Fork) (t : ℕ) : colsB F t = colsU F t := rfl

/-! ## The test's yes -/

theorem tableIn_iff (tl : HTailF2) (cols : ℕ) (t : Tab) :
    tableIn tl cols (tripleOf t) = true ↔
      (t.mat < tl.NM → 0 < (tl.mats.getD t.mat {}).m / t.len → 0 < (tl.mats.getD t.mat {}).k →
        t.start + (tl.mats.getD t.mat {}).k * ((tl.mats.getD t.mat {}).m / t.len) ≤ cols) := by
  unfold tableIn tripleOf
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq,
    decide_eq_true_eq]
  constructor
  · rintro (((h | h) | h) | h) a b c
    · exact absurd a h
    · omega
    · omega
    · exact h
  · intro h
    by_cases a : t.mat < tl.NM
    · by_cases b : (tl.mats.getD t.mat {}).m / t.len = 0
      · exact Or.inl (Or.inl (Or.inr b))
      · by_cases c : (tl.mats.getD t.mat {}).k = 0
        · exact Or.inl (Or.inr c)
        · exact Or.inr (h a (Nat.pos_of_ne_zero b) (Nat.pos_of_ne_zero c))
    · exact Or.inl (Or.inl (Or.inl a))

theorem all_gives {X : LinkH} {sh : List Tab}
    (h : ((sh.map tripleOf).all
      (tableIn X.tl (colsB X.Fp ((X.tl.ix.U.getD 2 none).getD 0)))) = true) :
    PosPlan X.tl X.Fp sh := by
  intro t ht
  have := List.all_eq_true.1 h (tripleOf t) (List.mem_map.2 ⟨t, ht, rfl⟩)
  exact (tableIn_iff X.tl _ t).1 this

theorem posPlanB_iff (W : Verify.Public) (l : ℕ) (X : LinkH) :
    posPlanB W l X = true ↔ ∃ ts, triplesAt W l = some ts ∧ ts.isEmpty = false ∧
      ts.all (tableIn X.tl (colsB X.Fp ((X.tl.ix.U.getD 2 none).getD 0))) = true := by
  unfold posPlanB
  constructor
  · intro h
    split at h
    · rename_i ts e
      rw [Bool.and_eq_true] at h
      exact ⟨ts, e, by simpa using h.1, h.2⟩
    · exact nomatch h
  · rintro ⟨ts, e, h0, h⟩
    rw [e]
    show (!ts.isEmpty && _) = true
    rw [h0]
    exact h

theorem pos_fit_layers {W : Verify.Public} {g : ℕ} (hg : g < 12) {X : LinkH}
    (h : posPlanB W (2 * g) X = true) : PosPlan X.tl X.Fp (layShapes W.layers g) := by
  obtain ⟨ts, e, -, h⟩ := (posPlanB_iff W _ X).1 h
  unfold triplesAt at e
  rw [if_neg (by omega), if_pos (by omega), show 2 * g / 2 = g by omega] at e
  rw [layTriples_is e] at h
  exact all_gives h

theorem pos_fit_att {W : Verify.Public} {g : ℕ} {X : LinkH}
    (h : posPlanB W (2 * g + 1) X = true) :
    ∀ p, W.A[g]? = some p → PosPlan X.tl X.Fp (attShapes p.S (nScores p.S)) := by
  intro p hp
  obtain ⟨ts, e, -, h⟩ := (posPlanB_iff W _ X).1 h
  unfold triplesAt at e
  rw [if_neg (by omega), if_neg (by omega), show (2 * g + 1) / 2 = g by omega, hp] at e
  obtain rfl := Option.some.inj e
  have h' : (attPlaced p.S).all
      (tableIn X.tl (colsB X.Fp ((X.tl.ix.U.getD 2 none).getD 0))) = true := h
  rw [attPlaced_is] at h'
  exact all_gives h'

theorem pos_fit_head {W : Verify.Public} {X : LinkH} (h : posPlanB W 24 X = true) :
    ∀ t0, tabsOfPlan W.hS W.H = some t0 → PosPlan X.tl X.Fp (shapesOf t0.funs) := by
  intro t0 h0
  obtain ⟨ts, e, -, h⟩ := (posPlanB_iff W _ X).1 h
  unfold triplesAt at e
  rw [if_pos rfl] at e
  obtain ⟨t0', h0', rfl⟩ := headTriples_is e
  obtain rfl : t0 = t0' := Option.some.inj (h0.symm.trans h0')
  exact all_gives h

/-! ## To the states -/

theorem built_tl_Fp {mk : ProofFile.LinksBy} {Z : ProofFile.Pub} {G : ProofFile.Ground}
    (hG : ProofFile.blankBy mk Z = some G) {l : ℕ} {Xl : LinkH} (e3 : G.built[l]? = some Xl) :
    ∃ X, Z.p.built.links[l]? = some X ∧ Xl.tl = X.tl ∧ Xl.Fp = X.Fp := by
  obtain ⟨links, e⟩ := _root_.Meaning.K2.blank_built hG
  rw [e] at e3
  obtain ⟨b, hb, eT, eF, -⟩ := zip_at e3
  exact ⟨b, hb, eT, eF⟩

/-- At each segment's number a segment stands, and the test says yes of it. -/
def PosAsked (Z : ProofFile.Pub) : Prop :=
  ∀ l < 25, ∃ X, Z.p.built.links[l]? = some X ∧ posPlanB Z.p.X l X = true

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- What the test's yes says at the blank letters' own segment. -/
theorem asked_at (hE : PosAsked Z) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) :
    ∃ X, posPlanB Bs.G₀.W l X = true ∧ Xl.tl = X.tl ∧ Xl.Fp = X.Fp := by
  obtain ⟨X, x1, x2, x3⟩ := built_tl_Fp O.blank e3
  obtain ⟨X', y1, y2⟩ := hE l hl
  obtain rfl : X = X' := Option.some.inj (x1.symm.trans y1)
  rw [← ProofFile.Law.blankBy_W O.blank] at y2
  exact ⟨X, y2, x2, x3⟩

theorem pos_asked_layers (hE : PosAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {Xl : LinkH} (e3 : Bs.G₀.built[2 * g]? = some Xl) {Str : Type}
    (a : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) (28 * g + 9) a)
    {α : Type} (π : α → Option HTailF2 × Option (Array HFun)) (φ : S → α) (u : HTailF2)
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) : PosAt π (fixed9 φ a.1.2) := by
  obtain ⟨X, y, x2, x3⟩ := asked_at hE O (by omega) e3
  exact pos_layers hS hR O hg e3 a h π φ u hπ (by rw [x2, x3]; exact pos_fit_layers hg y)

theorem pos_asked_att (hE : PosAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {Xl : LinkH} (e3 : Bs.G₀.built[2 * g + 1]? = some Xl) {Str : Type}
    (a : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) (14 * (2 * g + 1) + 9) a)
    {α : Type} (π : α → Option HTailF2 × Option (Array HFun)) (φ : S → α) (u : HTailF2)
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) : PosAt π (fixed9 φ a.1.2) := by
  obtain ⟨X, y, x2, x3⟩ := asked_at hE O (by omega) e3
  exact pos_att hS hR O hg e3 a h π φ u hπ (fun p hp => by
    rw [x2, x3]
    exact pos_fit_att y p hp)

theorem pos_asked_head (hE : PosAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {Xl : LinkH} (e3 : Bs.G₀.built[24]? = some Xl) {Str : Type} (a : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) 347 a)
    {α : Type} (π : α → Option HTailF2 × Option (Array HFun)) (φ : S → α) (u : HTailF2)
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) : PosAt π (fixed9 φ a.1.2) := by
  obtain ⟨X, y, x2, x3⟩ := asked_at hE O (by omega) e3
  exact pos_head hS hR O e3 a h π φ u hπ (fun t0 h0 => by
    rw [x2, x3]
    exact pos_fit_head y t0 h0)

end VerifiableInference.Desc.K9Asks

#print axioms VerifiableInference.Desc.K9Asks.layTriples_is
#print axioms VerifiableInference.Desc.K9Asks.placeB_is
#print axioms VerifiableInference.Desc.K9Asks.attPlaced_is
#print axioms VerifiableInference.Desc.K9Asks.headTriples_is
#print axioms VerifiableInference.Desc.K9Asks.colsB_is
#print axioms VerifiableInference.Desc.K9Asks.tableIn_iff
#print axioms VerifiableInference.Desc.K9Asks.all_gives
#print axioms VerifiableInference.Desc.K9Asks.posPlanB_iff
#print axioms VerifiableInference.Desc.K9Asks.pos_fit_layers
#print axioms VerifiableInference.Desc.K9Asks.pos_fit_att
#print axioms VerifiableInference.Desc.K9Asks.pos_fit_head
#print axioms VerifiableInference.Desc.K9Asks.built_tl_Fp
#print axioms VerifiableInference.Desc.K9Asks.asked_at
#print axioms VerifiableInference.Desc.K9Asks.pos_asked_layers
#print axioms VerifiableInference.Desc.K9Asks.pos_asked_att
#print axioms VerifiableInference.Desc.K9Asks.pos_asked_head
