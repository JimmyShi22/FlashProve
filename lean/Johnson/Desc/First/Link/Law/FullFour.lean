-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FullFour.lean: THE PREMISE hFu4 OF THE LAWS ON THE FIRST FOUR CLAIMS OF
THE APPROXIMATE RANGE PROOF's RUN (Johnson/Desc/First/Batch/Law/K8Four.lean; LinkTableMore.lean,
FourAtFront.lean, WorthAtFront.lean: "at every full state that goes on from q the entries which the
four claims name are fixed by q and the data"), AT `Fu := FullAt nU` (GoodFull.lean), BROUGHT DOWN
TO TWO PROMISES ON WHAT IS FIXED BEFORE THE DRAW. Definitions and theorems.
  `Row4 tl k r`: the rows whose weights the four claims read: the planes' array's three, and the
    pieces'. `four8_runs`: every run of entries of the four stands at such a row.
  `frame_of_looks`, `coefOK_frame`, `coefOK_blank`, `row4_coef`: at such a row the routine that lays
    the weights (`Fo.coefAll`, OnBytes/Tie/Pv/Lookup/Ends/FoCoef.lean) lays ONE list on two ledgers
    whose arrays have the same numbers of rows and of virtual rows, whatever the structure's
    fourteen written fields hold: by `coef_bz` and `CoefOK.pieceW`: these weights are
    functions of what was heard, of the two calls' pieces and of the array's number of rows.
  `n4`, `w4`, `ent4`: the entries as functions of q and the data: the weights are those that the
    routine would lay on the snapshot's own ledger (`entBy`, EntryUnit.lean).
  `weights_full`, `hFu4_full`: **hFu4 to the letter, at `ent := ent4 π`**, under okCoef (`Fo.CoefOK`
    at the fixed structure and the snapshot's ledger: it has a Bool, `coefTest`) and okEnts (an
    entry that one of the four FORMS names stands at such a row: vacuous where they name none).
WHY IT CAN BE PAID. "Goes on" (`GoesOn`, Johnson/Desc/First/Batch/Law/FitsAtS.lean) carries the
arrays' looks from the snapshot to every state that goes on from q; a full state's ledger is
`coefAll` of the ledger in front of the run of self tests, which has the same frame. Without the
looks the number of rows at t would be pinned by nothing.
Limits. An implication. Nothing is evaluated. Ok's lower bound is owed elsewhere (`hready`,
LinkOwes.lean), and can be paid only where the row's promise in front holds "reached". Whether the
four forms name an entry is not read. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.FullEq
import Johnson.Desc.First.Link.Law.EntryUnit
import Johnson.Desc.First.Batch.Law.K8Four
import OnBytes.Tie.Pv.Lookup.Ends.FoTailPlanes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open VerifiableInference.Desc.EntryUnit (WeightsAre entBy entry_by)
open _root_.Fo (CoefOK coefAll rowAt allPieces HasRow Frame frame_all coef_bz joinRuns joinRun
  bzRun)

/-! ## 1 The rows, and their weights at two ledgers -/

/-- **The rows whose weights the four claims read**: the planes' array's three, and the pieces'. -/
def Row4 (tl : HTailF2) (k r : ℕ) : Prop :=
  (k = tl.ix.BZ ∧ r < 3) ∨ ∃ a ∈ allPieces tl, a.2.tree = k ∧ a.2.row = r

theorem Frame.symm' {F G : Fork} (h : Frame F G) : Frame G F :=
  ⟨h.1.symm, fun t => ⟨(h.2 t).1.symm, (h.2 t).2.symm⟩⟩

/-- Two ledgers whose arrays have the same looks have the same frame. -/
theorem frame_of_looks {F G : Fork} (h : G.trees.map look = F.trees.map look) : Frame F G := by
  have hs : G.trees.size = F.trees.size := by
    have := congrArg Array.size h
    simpa using this
  refine ⟨hs, fun t => ?_⟩
  have e := congrArg (fun a : Array Look => a[t]?) h
  simp only [Array.getElem?_map] at e
  cases hG : G.trees[t]? with
  | none =>
    cases hF : F.trees[t]? with
    | none =>
      have eY : G.trees.getD t {} = {} := by simp [Array.getD_eq_getD_getElem?, hG]
      have eX : F.trees.getD t {} = {} := by simp [Array.getD_eq_getD_getElem?, hF]
      rw [eY, eX]
      exact ⟨rfl, rfl⟩
    | some X =>
      rw [hG, hF] at e
      exact nomatch e
  | some Y =>
    cases hF : F.trees[t]? with
    | none =>
      rw [hG, hF] at e
      exact nomatch e
    | some X =>
      rw [hG, hF] at e
      have e' : look Y = look X := Option.some.inj e
      have eY : G.trees.getD t {} = Y := by simp [Array.getD_eq_getD_getElem?, hG]
      have eX : F.trees.getD t {} = X := by simp [Array.getD_eq_getD_getElem?, hF]
      rw [eY, eX]
      exact ⟨congrArg (·.2.1) e', congrArg (·.2.2.2) e'⟩

/-- What the declared weights' theorems ask passes to a ledger with the same frame. -/
theorem coefOK_frame {tl : HTailF2} {F G : Fork} (h : Frame F G) (T : CoefOK tl F) :
    CoefOK tl G where
  bz := ⟨h.hasRow T.bz.1, h.hasRow T.bz.2.1, h.hasRow T.bz.2.2⟩
  bzR := (h.2 _).1.trans T.bzR
  mats := T.mats
  apart := T.apart
  piece := fun a ha => ⟨h.hasRow (T.piece a ha).1, (T.piece a ha).2⟩

/-- It reads none of the structure's fourteen written fields. -/
theorem coefOK_blank {u tl : HTailF2} {F : Fork} (T : CoefOK (blank u tl) F) : CoefOK tl F :=
  ⟨T.bz, T.bzR, T.mats, T.apart, T.piece⟩

/-- **At such a row the routine lays one list of weights on two ledgers with the same frame**,
whatever the fourteen written fields hold. -/
theorem row4_coef (u tl : HTailF2) (g : Forest.Heard) {F G : Fork} (h : Frame F G)
    (T : CoefOK (blank u tl) F) {k r : ℕ} (hr : Row4 (blank u tl) k r) :
    (rowAt (coefAll tl g G) k r).coef = (rowAt (coefAll (blank u tl) g F) k r).coef := by
  have TG : CoefOK tl G := coefOK_frame h (coefOK_blank T)
  rcases hr with ⟨rfl, h3⟩ | ⟨a, ha, rfl, rfl⟩
  · obtain ⟨a0, a1, a2⟩ := coef_bz tl g G TG.bz.1 TG.bz.2.1 TG.bz.2.2 TG.mats
    obtain ⟨b0, b1, b2⟩ := coef_bz (blank u tl) g F T.bz.1 T.bz.2.1 T.bz.2.2 T.mats
    have a0' : (rowAt (coefAll tl g G) (blank u tl).ix.BZ 0).coef = _ := a0
    have a1' : (rowAt (coefAll tl g G) (blank u tl).ix.BZ 1).coef = _ := a1
    have a2' : (rowAt (coefAll tl g G) (blank u tl).ix.BZ 2).coef = _ := a2
    match r, h3 with
    | 0, _ => rw [a0', b0]
    | 1, _ => rw [a1', b1]
    | 2, _ => rw [a2', b2]
  · rw [TG.pieceW g a ha, T.pieceW g a ha, (h.2 a.2.tree).1]
    rfl

/-- Every run of entries of the four claims stands at such a row. -/
theorem four8_runs (tl : HTailF2) (g : Forest.Heard) :
    ∀ cl ∈ four8 tl g, ∀ r ∈ cl.runs.toList, Row4 tl r.tree r.row := by
  intro cl hcl r hr
  unfold four8 at hcl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl | rfl | rfl
  · have hr' : r ∈ joinRuns tl g := by simpa using hr
    unfold joinRuns at hr'
    obtain ⟨q, hq, hr'⟩ := List.mem_flatMap.1 hr'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr'
    refine Or.inr ⟨(q, p), ?_, rfl, rfl⟩
    unfold allPieces
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact List.mem_append_left _ (List.mem_map.2 ⟨p, hp, rfl⟩)
    · exact List.mem_append_right _ (List.mem_map.2 ⟨p, hp, rfl⟩)
  · obtain rfl : r = _ := by simpa using hr
    exact Or.inl ⟨rfl, show (0 : ℕ) < 3 by decide⟩
  · obtain rfl : r = _ := by simpa using hr
    exact Or.inl ⟨rfl, show (1 : ℕ) < 3 by decide⟩
  · obtain rfl : r = _ := by simpa using hr
    exact Or.inl ⟨rfl, show (2 : ℕ) < 3 by decide⟩

/-! ## 2 The entries, as functions of what is fixed and the data -/

section
variable {α : Type} (π : α → Option HTailF2 × Option (Array HFun))

/-- The number of rows of array k in the snapshot's ledger. -/
def n4 (q : α × Option Pub9) (k : ℕ) : ℕ :=
  match q.2 with
  | some v => (v.F.trees.getD k {}).R
  | none => 0

/-- The weights that the routine would lay on the snapshot's own ledger. -/
def w4 (q : α × Option Pub9) (k r j : ℕ) : E :=
  match (π q.1).1, q.2 with
  | some tlb, some v =>
    match tlb.heard with
    | some g => (rowAt (coefAll tlb g v.F) k r).coef.getD j zeroE
    | none => zeroE
  | _, _ => zeroE

/-- **The entries under these weights.** -/
def ent4 : α × Option Pub9 → Bound GE8 → ℕ → ℕ → ℕ → GE8 := entBy Reading.gl n4 (w4 π)

variable (φ : S → α) (Ok : α × Option Pub9 → Prop) (nU : Array ℕ) (u : HTailF2)
  (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?))
  (okCoef : ∀ q tlb v, Ok q → (π q.1).1 = some tlb → q.2 = some v → CoefOK tlb v.F)
include hπ okCoef

/-- **At a full state that goes on from q, at such a row, the weights are those that q names.** -/
theorem weights_full (q : α × Option Pub9) (t : S) (b : K9.Part) (tlb : HTailF2)
    (g : Forest.Heard) (hf : Fx9 φ Ok q t) (hfull : FullAt nU t) (hb : atS.get? t = some b)
    (h1 : (π q.1).1 = some tlb) (hg : tlb.heard = some g) (k r : ℕ) (hr : Row4 tlb k r) :
    WeightsAre b.F k r (n4 q k) (w4 π q k r) := by
  obtain ⟨hOk, hφ, v, b', hv, hb', hgo⟩ := hf
  obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hb)
  obtain ⟨e', hT⟩ := hfull
  obtain ⟨Fc, tlX, g', _, _, k3, k4, k5⟩ := k8_tests_coefAll nU e' t hT
  have eF : b'.F = coefAll tlX g' Fc := Option.some.inj ((K9.get_fork t b' hb).symm.trans k5)
  have htl : t.tl? = some tlX := by
    have hb2 := hb
    rw [k4] at hb2
    obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.1 (part_back e' tlX _ b' hb2)
    obtain ⟨_, _, _, _, _, f4, _, _⟩ := get_put e' a' ha' tlX (coefAll tlX g' Fc)
    rw [k4]
    exact f4
  have e1 : tlb = blank u tlX := by
    have q2 : (π q.1).1 = some (blank u tlX) := by
      rw [← hφ, hπ, htl]
      rfl
    exact Option.some.inj (h1.symm.trans q2)
  subst e1
  obtain rfl : g' = g := Option.some.inj (k3.symm.trans (show tlX.heard = some g from hg))
  have T := okCoef q _ v hOk h1 hv
  have fr : Frame v.F Fc :=
    (frame_of_looks (goesOn_looks hgo)).trans (Frame.symm' (eF ▸ frame_all tlX g' Fc))
  have hR : (b'.F.trees.getD k {}).R = (v.F.trees.getD k {}).R :=
    ((frame_of_looks (goesOn_looks hgo)).2 k).1
  refine ⟨?_, fun j _ => ?_⟩
  · simp only [n4, hv]
    exact hR
  · simp only [w4, h1, hv, hg]
    show (rowAt b'.F k r).coef.getD j zeroE = _
    rw [eF, row4_coef u tlX g' fr T hr]

/-- **hFu4: THE ENTRIES' HALF OF THE FOUR VALUES, AT `FullAt nU`, FROM TWO PROMISES ON WHAT IS FIXED
BEFORE THE DRAW.** -/
theorem hFu4_full
    (okEnts : ∀ q tlb g, Ok q → (π q.1).1 = some tlb → tlb.heard = some g →
      ∀ cl ∈ four8 tlb g, ∀ x ∈ cl.form.ents.toList, Row4 tlb x.tree x.row) :
    ∀ q t b y tlb g, Fx9 φ Ok q t → FullAt nU t → atS.get? t = some b →
      (π q.1).1 = some tlb → tlb.heard = some g → ∀ cl ∈ four8 tlb g,
      (∀ x ∈ cl.form.ents.toList, (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx =
        ent4 π q y x.tree x.row x.idx) ∧
      ∀ r ∈ cl.runs.toList, ∀ i < r.n,
        (worldAt Reading.gl b.L b.F y).entry r.tree r.row (r.first + i) =
          ent4 π q y r.tree r.row (r.first + i) := by
  intro q t b y tlb g hf hfull hb h1 hg cl hcl
  refine ⟨fun x hx => ?_, fun r hr i _ => ?_⟩
  · exact entry_by Reading.gl φ Ok n4 (w4 π) q t b y hf hb x.tree x.row x.idx
      (weights_full π φ Ok nU u hπ okCoef q t b tlb g hf hfull hb h1 hg _ _
        (okEnts q tlb g hf.1 h1 hg cl hcl x hx))
  · exact entry_by Reading.gl φ Ok n4 (w4 π) q t b y hf hb r.tree r.row (r.first + i)
      (weights_full π φ Ok nU u hπ okCoef q t b tlb g hf hfull hb h1 hg _ _
        (four8_runs tlb g cl hcl r hr))

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.row4_coef
#print axioms VerifiableInference.Desc.LinkJoin.four8_runs
#print axioms VerifiableInference.Desc.LinkJoin.weights_full
#print axioms VerifiableInference.Desc.LinkJoin.hFu4_full
