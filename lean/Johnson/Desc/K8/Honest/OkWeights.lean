-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/OkWeights.lean: BEHIND A YES OF THE BATCHING BLOCK EVERY WEIGHT THAT THE
LEDGER BEARS ON A COLUMN OF A VIRTUAL ROW IS A WORD BELOW THE PRIME; SO AN EQUALITY OF VALUES WITH
SUCH A WORD IS AN EQUALITY OF WORDS. Definitions and lemmas; none of the library's goals. No prover
stands in them; nothing on completeness, soundness or hiding.

  `OkArr`, `OkTrees`, `OkW`, `okArr_getD`, `okArr_weights`, `okW_iff`   the sentence of an array of
      weights, of a ledger's arrays, and by `weightsOf`; the last two say the same
  `okArr_modify`, `okArr_runLoop`, `okTrees_row`   a writing of one entry by a function whose
      outputs are such words; a run's loop; a writing of one virtual row's weights
  `addEntry_ok`, `addRun_ok`, `addForm_ok`, `addRuns_ok`, `addOne_ok`, **`addList_ok`**   the adding
      of claims keeps it: each of its writings on a weight is an addE
  `okTrees_empty`, `okW_of_sums`, `okW_coefBody`   a ledger that bears nothing has it; whatever
      keeps the ledger's sums keeps it; so the step that lays the rows' weights
  **`behind_ok`**   the sentence of the title, under `Gathers`. ITS FIRST STEPS ARE THOSE OF
      `behind_total` (Johnson/Desc/K8/Honest/BehindTotal.lean), WRITTEN A FURTHER TIME
  **`word_of_val`**   from values to words
By: Part.MaskedSum.okE_add: an output of addE is a word below the prime, whatever went in
(Johnson/Top/H/P1Tie/Words.lean) · K9L.drawnClean_ok: the ledger that the batching's draw yields,
filled, bears nothing (Johnson/Desc/First/Batch/Law/AtBlock.lean) · foldE_inv
(Johnson/Desc/First/Link/Law/LooksClose.lean) · `weights_of_sums`
(Johnson/Desc/K8/Honest/BehindWeight.lean) · ProdV.gl_inj (Johnson/Desc/First/ProdV/Drawn.lean).
Limits. On the words' range alone: nothing on any weight's value. `Gathers` is a premise.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.BehindWeight
import Johnson.Desc.First.Link.Law.LooksClose
import Johnson.Desc.First.ProdV.Drawn
import Johnson.Top.H.P1Tie.Words

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.K9L (ok_bind)
open VerifiableInference.Desc.LinkJoin (foldE_inv)

/-- Every entry is a word below the prime. -/
def OkArr (L : Array E) : Prop := ∀ (i : Nat) (v : E), L[i]? = some v → OnBytes.okE v = true

/-- So of every virtual row's weights on the columns, in every array. -/
def OkTrees (tr : Array HTree) : Prop :=
  ∀ (t : Nat) (X : HTree), tr[t]? = some X → ∀ (r : Nat) (R : HRow), X.rows[r]? = some R →
    OkArr R.L

/-- **Every weight that the ledger bears on a column is a word below the prime.** -/
def OkW (F : Fork) : Prop := ∀ t r i, OnBytes.okE ((weightsOf F t r).getD i zeroE) = true

theorem okArr_modify {L : Array E} (h : OkArr L) (k : Nat) (f : E → E)
    (hf : ∀ v, OnBytes.okE (f v) = true) : OkArr (L.modify k f) := by
  intro i v hv
  rw [Array.getElem?_modify] at hv
  split at hv
  · obtain ⟨u, -, rfl⟩ := Option.map_eq_some_iff.1 hv
    exact hf u
  · exact h i v hv

theorem okArr_runLoop (kc : E) (w : Array E) (w0 first : Nat) :
    ∀ (count i : Nat) (L : Array E), OkArr L → OkArr (runLoop kc w w0 first count i L)
  | 0, _, _, h => h
  | c + 1, i, L, h => by
    unfold runLoop
    dsimp only
    refine okArr_runLoop kc w w0 first c (i + 1) _ ?_
    split
    · exact h
    · exact okArr_modify h _ _ fun _ => Part.MaskedSum.okE_add _ _

/-- A writing of one virtual row's weights on the columns. -/
theorem okTrees_row {tr : Array HTree} (h : OkTrees tr) (t r : Nat) (g : HRow → Array E)
    (hg : ∀ R, OkArr R.L → OkArr (g R)) :
    OkTrees (tr.modify t fun X =>
      { X with rows := X.rows.modify r fun R => { R with L := g R } }) := by
  intro t' X' hX' r' R' hR'
  rw [Array.getElem?_modify] at hX'
  split at hX'
  · obtain ⟨X, hX, rfl⟩ := Option.map_eq_some_iff.1 hX'
    have hR2 : (X.rows.modify r fun R => { R with L := g R })[r']? = some R' := hR'
    rw [Array.getElem?_modify] at hR2
    split at hR2
    · obtain ⟨R, hR, rfl⟩ := Option.map_eq_some_iff.1 hR2
      exact hg R (h _ X hX _ R hR)
    · exact h _ X hX _ R' hR2
  · exact h _ X' hX' _ R' hR'

theorem addEntry_ok {w : E} {tr tr' : Array HTree} {x : Ent} (h : K9.addEntry w tr x = .ok tr')
    (ht : OkTrees tr) : OkTrees tr' := by
  unfold K9.addEntry at h
  obtain ⟨_, _, h⟩ := ok_bind h
  rw [← Except.ok.inj h]
  exact okTrees_row ht x.tree x.row
    (fun r => r.L.modify (x.idx - r.L0) fun v => addE v (mulE w x.coef))
    fun R hR => okArr_modify hR _ _ fun _ => Part.MaskedSum.okE_add _ _

theorem addRun_ok {w : E} {tr tr' : Array HTree} {r : Run2} (h : K9.addRun w tr r = .ok tr')
    (ht : OkTrees tr) : OkTrees tr' := by
  unfold K9.addRun at h
  obtain ⟨_, _, h⟩ := ok_bind h
  rw [← Except.ok.inj h]
  exact okTrees_row ht r.tree r.row
    (fun R => runLoop (mulE w r.coef) r.w r.w0 (r.first - R.L0) r.n 0 R.L)
    fun R hR => okArr_runLoop _ _ _ _ _ _ _ hR

theorem addForm_ok {F G : Fork} {w : E} {a : Aff} (h : K9.addForm F w a = .ok G)
    (hF : OkTrees F.trees) : OkTrees G.trees := by
  unfold K9.addForm at h
  dsimp only at h
  obtain ⟨tr, h1, h⟩ := ok_bind h
  obtain ⟨LS, _, h⟩ := ok_bind h
  rw [← Except.ok.inj h]
  rw [← Array.foldlM_toList] at h1
  exact foldE_inv (K9.addEntry w) OkTrees (fun _ _ _ e hb => addEntry_ok e hb) _ _ _ h1 hF

theorem addRuns_ok {F G : Fork} {w : E} {runs : Array Run2} (h : K9.addRuns F w runs = .ok G)
    (hF : OkTrees F.trees) : OkTrees G.trees := by
  unfold K9.addRuns at h
  dsimp only at h
  obtain ⟨tr, h1, h⟩ := ok_bind h
  rw [← Except.ok.inj h]
  rw [← Array.foldlM_toList] at h1
  exact foldE_inv (K9.addRun w) OkTrees (fun _ _ _ e hb => addRun_ok e hb) _ _ _ h1 hF

theorem addOne_ok {F G : Fork} {cl : Claim} (h : K9.addOne F cl = .ok G) (hF : OkTrees F.trees) :
    OkTrees G.trees := by
  unfold K9.addOne at h
  dsimp only at h
  obtain ⟨x, hx, h⟩ := ok_bind h
  obtain ⟨G₁, h1, h⟩ := ok_bind h
  have e0 : x.2.trees = F.trees := by
    unfold K9.weightNext at hx
    obtain ⟨_, _, hx⟩ := ok_bind hx
    obtain ⟨_, _, hx⟩ := ok_bind hx
    obtain ⟨_, _, hx⟩ := ok_bind hx
    rw [← Except.ok.inj hx]
  exact addRuns_ok h (addForm_ok h1 (by rw [e0]; exact hF))

/-- **The adding of a list of claims keeps it.** -/
theorem addList_ok {F G : Fork} {cls : List Claim} (h : K9.addList F cls = .ok G)
    (hF : OkTrees F.trees) : OkTrees G.trees :=
  foldE_inv K9.addOne (fun H => OkTrees H.trees) (fun _ _ _ e hb => addOne_ok e hb) cls F G h hF

theorem okArr_getD {L : Array E} (h : OkArr L) (i : Nat) :
    OnBytes.okE (L.getD i zeroE) = true := by
  rw [Array.getD_eq_getD_getElem?]
  cases hv : L[i]? with
  | none => rfl
  | some v => exact h i v hv

theorem okArr_weights {F : Fork} (h : OkTrees F.trees) (t r : Nat) : OkArr (weightsOf F t r) := by
  intro i v hv
  simp only [weightsOf, Array.getD_eq_getD_getElem?] at hv
  cases hX : F.trees[t]? with
  | none =>
    rw [hX] at hv
    simp at hv
  | some X =>
    rw [hX, Option.getD_some] at hv
    cases hR : X.rows[r]? with
    | none =>
      rw [hR] at hv
      simp at hv
    | some R =>
      rw [hR, Option.getD_some] at hv
      exact h t X hX r R hR i v hv

/-- The two forms say the same. -/
theorem okW_iff (F : Fork) : OkW F ↔ OkTrees F.trees := by
  constructor
  · intro h t X hX r R hR i v hv
    have k := h t r i
    simp only [weightsOf, Array.getD_eq_getD_getElem?, hX, hR, hv, Option.getD_some] at k
    exact k
  · exact fun h t r i => okArr_getD (okArr_weights h t r) i

/-- A ledger that bears nothing has it. -/
theorem okTrees_empty {F : Fork} (h : K9.ledgerEmpty F = true) : OkTrees F.trees := by
  unfold K9.ledgerEmpty at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hT, -⟩, -⟩ := h
  intro t X hX r R hR i v hv
  obtain ⟨a1, rfl⟩ := Array.getElem?_eq_some_iff.1 hX
  obtain ⟨a2, rfl⟩ := Array.getElem?_eq_some_iff.1 hR
  obtain ⟨a3, rfl⟩ := Array.getElem?_eq_some_iff.1 hv
  have k1 := Array.all_eq_true_iff_forall_mem.1 hT _ (Array.getElem_mem a1)
  have k2 := Array.all_eq_true_iff_forall_mem.1 k1 _ (Array.getElem_mem a2)
  have k3 := Array.all_eq_true_iff_forall_mem.1 k2 _ (Array.getElem_mem a3)
  rw [OnBytes.Model.isZeroE_eq k3]
  rfl

/-- Whatever keeps the ledger's sums keeps it. -/
theorem okW_of_sums {F G : Fork} (h : K9L.sums G = K9L.sums F) (hF : OkW F) : OkW G :=
  fun t r i => by rw [weights_of_sums h t r]; exact hF t r i

/-- So the step that lays the rows' weights. -/
theorem okW_coefBody (tl : HTailF2) (g : Forest.Heard) {F : Fork} (hF : OkW F) :
    OkW (coefBody tl g F) := okW_of_sums (congrArg (·.1) (K9L.core_coefBody tl g F)) hF

/-- **BEHIND A YES OF THE BATCHING BLOCK EVERY WEIGHT ON A COLUMN IS A WORD BELOW THE PRIME.** -/
theorem behind_ok (p : K9.Where) (g : S → Except String (List Claim × S))
    (batch : S → List Fmt.RoundView → Except String S) (s t' : S) (tl : HTailF2)
    (funs : Array HFun) (nf nb : Nat) (a : Nat → Nat → Nat → Nat → Cb.Gl.E)
    (hb : ∀ rs t, batch s rs = .ok t → (K9.batch K9.atS p g).decide s rs [] = .ok t)
    (hG : Gathers p g s tl funs nf nb a) (x : Cb.Gl.E)
    (hbt : batch s [⟨[], chiAt x⟩] = .ok t') :
    ∃ (tl' : HTailF2) (G : Fork), tlForkP.get? t' = some (tl', G) ∧ OkW G := by
  obtain ⟨t, e, cls, y', G, hdr, hg, hy, hadd, ht'⟩ := batch_ok p g s t' (chiAt x) (hb _ _ hbt)
  obtain ⟨xx, yy, tl', fr, k8, bk, n₀, F₁, F₂, gx, gy, gcore, -, gtl, -, -,
    -, -, -, -, -, -, -⟩ := hG.each (chiAt x) t e cls hdr hg
  obtain rfl : yy = y' := Option.some.inj (gy.symm.trans hy)
  obtain ⟨a0, x0, o, ha0, -, hdc, htt⟩ := drawnAt_ok p s t (chiAt x) hdr
  obtain ⟨c1, -⟩ := K9L.drawnClean_ok _ _ _ _ _ _ _ hdc
  obtain ⟨a', ha', hF', -, -⟩ :=
    K9L.atS_reads s { a0 with owed := o.owed, L := o.L, F := o.F } (by rw [ha0]; rfl)
  have hxx : xx.F = o.F := by
    rw [htt] at gx
    rw [Option.some.inj (gx.symm.trans ha')]
    exact hF'
  have hsums : K9L.sums yy.F = K9L.sums xx.F := congrArg (·.1) gcore
  have h0 : OkW yy.F := okW_of_sums hsums ((okW_iff _).2 (by rw [hxx]; exact okTrees_empty c1))
  have hbs := behind_set e yy G tl' gy gtl
  rw [← ht'] at hbs
  exact ⟨tl', G, hbs, (okW_iff _).2 (addList_ok hadd ((okW_iff _).1 h0))⟩

/-- **From values to words.** -/
theorem word_of_val {G : Fork} (h : OkW G) {t r i : Nat} {b : E} (hb : OnBytes.okE b = true)
    (e : Reading.gl.val ((weightsOf G t r).getD i zeroE) = Reading.gl.val b) :
    (weightsOf G t r).getD i zeroE = b := ProdV.gl_inj _ _ (h t r i) hb e

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.okArr_modify
#print axioms VerifiableInference.Desc.First.K8.Honest.okArr_runLoop
#print axioms VerifiableInference.Desc.First.K8.Honest.okTrees_row
#print axioms VerifiableInference.Desc.First.K8.Honest.addEntry_ok
#print axioms VerifiableInference.Desc.First.K8.Honest.addRun_ok
#print axioms VerifiableInference.Desc.First.K8.Honest.addForm_ok
#print axioms VerifiableInference.Desc.First.K8.Honest.addRuns_ok
#print axioms VerifiableInference.Desc.First.K8.Honest.addOne_ok
#print axioms VerifiableInference.Desc.First.K8.Honest.addList_ok
#print axioms VerifiableInference.Desc.First.K8.Honest.okArr_getD
#print axioms VerifiableInference.Desc.First.K8.Honest.okArr_weights
#print axioms VerifiableInference.Desc.First.K8.Honest.okW_iff
#print axioms VerifiableInference.Desc.First.K8.Honest.okTrees_empty
#print axioms VerifiableInference.Desc.First.K8.Honest.okW_of_sums
#print axioms VerifiableInference.Desc.First.K8.Honest.okW_coefBody
#print axioms VerifiableInference.Desc.First.K8.Honest.behind_ok
#print axioms VerifiableInference.Desc.First.K8.Honest.word_of_val
