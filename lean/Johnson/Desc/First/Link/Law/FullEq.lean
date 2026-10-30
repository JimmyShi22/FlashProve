-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/FullEq.lean: THE FIELD fuEq OF THE THREE SORTS' TAKES (PayLayers.lean,
PayAttention.lean, PayHead.lean: what the approximate range proof's run of claims takes of a FULL
state), AT `Fu := FullAt nU` (GoodFull.lean: the state stands behind a yes of that proof's run of
self tests), BROUGHT DOWN TO FOUR PROMISES ON WHAT IS FIXED BEFORE THE DRAW. Theorems.

What is said.
  `part_back`: where kind K9's lens finds a part behind a writing of the proof's structure and of
    the ledger, it finds one in front.
  `coefF_runs`: the routine that lays the rows' weights, where the lookup has been heard,
    returns the library's ledger `Fo.coefAll`: so the laws on that routine speak of the
    ledger that the run of self tests leaves (`coefBody_all`).
  `rk_rows`: a yes of the test by a second computation: the digits' array has 2 nbW + 2 virtual
    rows, nbW the number of blocks that this test computes afresh (`HTailF2.wants`).
  `colsU_goes`: an array's width goes on from the snapshot.
  `fuEq_full`: **the field, to the letter, at `FullAt nU`.** Its first clause (the test by a second
    computation says yes of the state's own structure and ledger) IS PAID OUTRIGHT. The second,
    under okBlocks. The third: the weight 1 on a table's one row is LAID BY THE RUN ITSELF
    (`unitRow_run`, OnBytes/Tie/Pv/Tail/EndChain.lean), under okApart and okLooks; the places, under
    okPos.
THE FOUR PREMISES: ALL ON THE PROMISE Ok ALONE: tests on the public parameters and the snapshot.
  okBlocks: the structure's number of blocks is the one computed afresh · okPos: each place that a
    read names lies within its table's width in the snapshot's ledger · okApart: each read's table
    is one of the four vectors, and its array's number is another than the digits', the planes', the
    symbols' and the pieces' · okLooks: BY THE LOOKS OF THE SNAPSHOT's LEDGER each read's table's
    array is of the kind "table", has ONE row, and has a virtual row (`unitLook`, LooksAre.lean).
WHY okLooks SERVES. "Goes on" (`GoesOn`, Johnson/Desc/First/Batch/Law/FitsAtS.lean) carries the
arrays' LOOKS (kind, rows, columns, virtual rows) from the snapshot to every state that goes on from
q (`goesOn_looks`). The run of self tests reads no number of rows at a table's vector: so without
that tie a sentence on the looks, asked of ALL full states that go on from q, could be paid by
nobody: alter the number of rows in the ledger: the state would still go on and still be full.

Limits. An implication. Nothing is evaluated. Ok's LOWER BOUND IS OWED ELSEWHERE: `hready`
(LinkOwes.lean) asks Ok at EVERY state with the row's promise in front: okLooks can be paid there
only where that promise holds "reached" (the forms over Rch), at every reached state, whichever
prover: each of the four must read no sent value: of okPos that is not held. Nothing on soundness.
Words. "The verifier's state": what the verifier carries from one sub-protocol to the next.

-/
import Johnson.Desc.First.Link.Law.GoodFull
import Johnson.Desc.First.Link.Law.PayLayers
import Johnson.Desc.First.Link.Law.LooksAre
import Johnson.Desc.First.Batch.Law.K8CoefAll
import OnBytes.Tie.Pv.Tail.EndChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Tie.Pv.Tail (UnitRow unitRow_run)
open OnBytes.Tie.Pv.Tail.Port (readsList uOf posOf colsU UApart hasRow shapeAt coefficientsF_shape
  bind_ok get_ok modify_ok)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims (rkSelfTestP coefBody)
open VerifiableInference.Desc.First.TailClaims.Law (blank coefBody_all)
open VerifiableInference.Desc.PhiAll

/-- Where the lens finds a part behind the two writings, it finds one in front. -/
theorem part_back (e : S) (tl : HTailF2) (G : Fork) (b : K9.Part)
    (h : atS.get? ((e.putTl tl).putFork G) = some b) : (atS.get? e).isSome = true := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := e
  cases here with
  | lay x => rfl
  | att x => rfl
  | head x =>
    by_cases ho : x.opened = true
    · cases hs : x.slot with
      | none => simp [atS, S.putTl, S.putFork, S.link?, S.fork?, S.tl?, K9.usedOf, ho, hs] at h
      | some n => simp [atS, S.link?, S.fork?, S.tl?, K9.usedOf, ho, hs]
    · simp [atS, S.putTl, S.putFork, S.link?, S.fork?, S.tl?, K9.usedOf, ho] at h
  | between => simp [atS, S.putTl, S.putFork, S.link?] at h
  | fin x => simp [atS, S.putTl, S.putFork, S.link?] at h
  | mem x => simp [atS, S.putTl, S.putFork, S.link?] at h

/-- The routine coefficientsF returns the library's ledger. -/
theorem coefF_runs (tl : HTailF2) (g : Forest.Heard) (hg : tl.heard = some g) (F : Fork) (c : Ctx) :
    tl.coefficientsF F c = .ok (((), Fo.coefAll tl g F), c) := by
  rw [Fo.coefficientsF_eq]
  exact (bind_ok _ _ F c _).2 ⟨g, F, c, (get_ok _ F F c c g).2 ⟨hg, rfl, rfl⟩,
    (modify_ok _ F _ c c ()).2 ⟨rfl, rfl⟩⟩

/-- A yes of the test by a second computation: the number of the digits' array's virtual rows. -/
theorem rk_rows (tl : HTailF2) (F : Fork) (h : rkSelfTestP tl F = .ok ()) :
    ∃ nbW W, tl.wants = some (nbW, W) ∧ (F.trees.getD tl.ix.ZZ {}).rows.size = 2 * nbW + 2 := by
  unfold rkSelfTestP at h
  cases hg : tl.heard with
  | none => simp [hg] at h
  | some g =>
    cases hj : tl.joinObj9 with
    | none => simp [hg, hj] at h
    | some jo =>
      cases hw : tl.wants with
      | none => simp [hg, hj, hw] at h
      | some x =>
        obtain ⟨nbW, W⟩ := x
        refine ⟨nbW, W, rfl, ?_⟩
        simp only [hg, hj, hw] at h
        by_contra hc
        have hb : ((F.trees.getD tl.ix.ZZ {}).rows.size == 2 * nbW + 2) = false :=
          beq_false_of_ne hc
        rw [hb] at h
        have h' : (Except.error "internal-t2f-untiled tileSelfTestF:1594" : Except String Unit) =
            .ok () := h
        cases h'

/-- An array's width goes on from the snapshot. -/
theorem colsU_goes {v : Pub9} {b : K9.Part} (h : GoesOn v b) (t : ℕ) :
    colsU b.F t = colsU v.F t := by
  have e := congrArg (fun a => (a[t]?).getD 0) (goesOn_widths h)
  simpa [colsU, Array.getElem?_map] using e

variable {β : Type}

/-- **THE FIELD fuEq AT `FullAt nU`.** -/
theorem fuEq_full (u : HTailF2) (ψ : S → β) (Ok : Q β → Prop) (nU : Array ℕ)
    (okBlocks : ∀ q tlb, Ok q → (pi8 q.1).1 = some tlb →
      tlb.wants.map (·.1) = some tlb.zzBlocks)
    (okPos : ∀ q tlb funs v, Ok q → pi8 q.1 = (some tlb, some funs) → q.2 = some v →
      ∀ x ∈ readsList tlb funs, ∀ d, d < (tlb.mats.getD x.1.mat {}).k →
        posOf tlb x.1 x.2 d < colsU v.F (uOf tlb x.1))
    (okApart : ∀ q tlb funs, Ok q → pi8 q.1 = (some tlb, some funs) →
      ∀ x ∈ readsList tlb funs, ∃ n0, n0 < 4 ∧ tlb.ix.U.getD n0 none = some (uOf tlb x.1) ∧
        tlb.ix.ZZ ≠ uOf tlb x.1 ∧ tlb.ix.BZ ≠ uOf tlb x.1 ∧
        (∀ mu, mu < tlb.NM → tlb.gtTree.getD mu 0 ≠ uOf tlb x.1) ∧
        ∀ k p, p ∈ (tlb.zOf k).pieces.toList → p.tree ≠ uOf tlb x.1)
    (okLooks : ∀ q tlb funs v, Ok q → pi8 q.1 = (some tlb, some funs) → q.2 = some v →
      ∀ x ∈ readsList tlb funs, unitLook (v.F.trees.toList.map look) (uOf tlb x.1) = true) :
    ∀ q t b ts funs, Fx9 (phiAll u ψ) Ok q t → FullAt nU t → atS.get? t = some b →
      t.tl? = some ts → t.funs? = some funs →
      rkSelfTestP ts b.F = .ok () ∧
        (b.F.trees.getD ts.ix.ZZ {}).rows.size = 2 * ts.zzBlocks + 2 ∧
        ∀ x ∈ readsList ts funs, UnitRow b.F (uOf ts x.1) ∧
          ∀ d, d < (ts.mats.getD x.1.mat {}).k → posOf ts x.1 x.2 d < colsU b.F (uOf ts x.1) := by
  intro q t b ts funs hf hfull hb hts hfu
  obtain ⟨e, he⟩ := hfull
  obtain ⟨F, tl, g, hF, htl, hg, _, h3, rfl⟩ := k8Tests_ok nU e _ he
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 (part_back e tl _ b hb)
  obtain ⟨a₁, ha₁, f1, _, _, f4, _, _⟩ := get_put e a ha tl (coefBody tl g F)
  have eb : a₁ = b := Option.some.inj (ha₁.symm.trans hb)
  subst eb
  have et : tl = ts := Option.some.inj (f4.symm.trans hts)
  subst et
  obtain ⟨hOk, hφ, v, b', hv, hb', hgo⟩ := hf
  have eb' : a₁ = b' := Option.some.inj (hb.symm.trans hb')
  subst eb'
  have hq1 : pi8 q.1 = (some (blank u tl), some funs) := by
    rw [← hφ]
    show ((S.tl? _).map (blank u), S.funs? _) = _
    rw [hts, hfu]
    rfl
  have hlk : LooksAre (v.F.trees.toList.map look) a₁.F := by
    have e := congrArg Array.toList (goesOn_looks hgo)
    simpa [LooksAre, Array.toList_map] using e
  have hsh : ∀ x ∈ readsList tl funs, hasRow a₁.F (uOf tl x.1) 0 ∧
      ((a₁.F.trees.getD (uOf tl x.1) {}).kind == HKind.table) = true ∧
      (a₁.F.trees.getD (uOf tl x.1) {}).R = 1 := fun x hx =>
    shape_at hlk _ (okLooks q _ funs v hOk hq1 hv x hx)
  have hrk : rkSelfTestP tl a₁.F = .ok () := by
    rw [f1]
    exact h3
  refine ⟨hrk, ?_, fun x hx => ⟨?_, fun d hd => ?_⟩⟩
  · obtain ⟨nbW, W, hw, hr⟩ := rk_rows tl a₁.F hrk
    have e1 : (blank u tl).wants.map (·.1) = some (blank u tl).zzBlocks :=
      okBlocks q _ hOk (by rw [hq1])
    have e2 : tl.wants.map (·.1) = some tl.zzBlocks := e1
    rw [hw] at e2
    have e3 : nbW = tl.zzBlocks := Option.some.inj e2
    rw [hr, e3]
  · obtain ⟨n0, a1, a2, a3, a4, a5, a6⟩ := okApart q _ funs hOk hq1 x hx
    obtain ⟨s1, s2, s3⟩ := hsh x hx
    let c : Ctx := { ch := { dry := false, entries := [] } }
    have hrun := coefF_runs tl g hg F c
    obtain ⟨k1, k2⟩ := coefficientsF_shape tl F _ c c hrun
    rw [f1, coefBody_all] at s1 s2 s3 ⊢
    have k := k1 (uOf tl x.1)
    unfold shapeAt at k
    have kk : (((Fo.coefAll tl g F).trees.getD (uOf tl x.1) {}).kind) =
        (F.trees.getD (uOf tl x.1) {}).kind := congrArg (·.1) k
    have kR : (((Fo.coefAll tl g F).trees.getD (uOf tl x.1) {}).R) =
        (F.trees.getD (uOf tl x.1) {}).R := congrArg (·.2.1) k
    have kr : (((Fo.coefAll tl g F).trees.getD (uOf tl x.1) {}).rows.size) =
        (F.trees.getD (uOf tl x.1) {}).rows.size := congrArg (·.2.2.2) k
    exact unitRow_run tl n0 (uOf tl x.1) F _ c c
      ⟨a1, a2, ⟨by rw [← k2]; exact s1.1, by rw [← kr]; exact s1.2⟩, by rw [← kk]; exact s2, a3, a4,
        a5, a6⟩ (by rw [← kR]; exact s3) hrun
  · rw [colsU_goes hgo]
    exact okPos q _ funs v hOk hq1 hv x hx d hd

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.part_back
#print axioms VerifiableInference.Desc.LinkJoin.coefF_runs
#print axioms VerifiableInference.Desc.LinkJoin.rk_rows
#print axioms VerifiableInference.Desc.LinkJoin.colsU_goes
#print axioms VerifiableInference.Desc.LinkJoin.fuEq_full
