-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/K8Disc.lean
(kind K9's soundness lemma; toward hok): THEOREM: THE DISCIPLINE ON THE EXPONENTS (Law/ExpsOk.lean)
AT THE SMALLNESS TEST's RUN OF CLAIMS "K8.equations", at the terms of Law/K8Run.lean.
The run's terms are four numbered terms (the first four claims', each under its own number's power)
followed by the ties' and the reads' single equations (tmRest), whose exponents lie behind the
plan's number of claims.
  tmRest_exps   the exponents of tmRest differ from each other and lie in
                [plan, plan + top), top := firstOf tlb NM + (the number of reads) * stepF: by the
                library's rising_rowsTail and bounds_rowsTail. plan: the snapshot's ledger's number.
  k8_disc       **the two clauses that DiscFrom asks of the run**, at the window of numbers
                [n, n + len8) and the window of equations [plan, plan + top): so at t = 0: no run
                in front of it may have laid an equation.
PREMISES: what the fixed part holds (h1, h2) - hmS: each shape's number of rows of symbols is the
library's symRows (a fact on the record, to stand in the promise Ok) - the four values are four
(hl4) - n + 4 is at most the plan's number (hn).
Not claimed: that top is the number "laid" which K9's door counts; other files hold that from a
yes of the door.

-/
import Johnson.Desc.First.Batch.Law.K8Run
import Johnson.Desc.First.Batch.Law.PlainRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Tie.Pv.Tail.Port OnBytes.Road.Rows

variable {α : Type}

/-- The number of indices that the ties and the reads take. -/
def top8 (tlb : HTailF2) (funs : Array HFun) : ℕ :=
  firstOf tlb tlb.NM + (readsList tlb funs).length * tlb.stepF

/-- The exponents of the ties' and the reads' equations. -/
theorem tmRest_exps (π : α → Option HTailF2 × Option (Array HFun)) (q : α × Option Pub9)
    (y : Bound GE8) (tlb : HTailF2) (funs : Array HFun) (v : Pub9)
    (h1 : π q.1 = (some tlb, some funs)) (h2 : q.2 = some v)
    (hmS : ∀ mu, mu < tlb.NM → (tlb.shp.getD mu {}).mS = Alg.symRows (tlb.shp.getD mu {}).m) :
    ((tmRest π q y).map (·.1)).Nodup ∧
      ∀ x ∈ tmRest π q y, v.F.planClaimsF ≤ x.1 ∧ x.1 < v.F.planClaimsF + top8 tlb funs := by
  have e : tmRest π q y = (rowsTail Reading.gl tlb funs v.F.planClaimsF).map
      fun r => (r.1, r.2 (cellsA v.arrayOf y)) := by
    simp only [tmRest, h1, h2]
  rw [e]
  refine ⟨?_, fun x hx => ?_⟩
  · rw [List.map_map]
    exact nodup_of_rising (rising_rowsTail Reading.gl tlb funs v.F.planClaimsF hmS)
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
    exact bounds_rowsTail Reading.gl tlb funs v.F.planClaimsF hmS r hr

/-- **The discipline's two clauses at K8's run.** -/
theorem k8_disc (π : α → Option HTailF2 × Option (Array HFun)) (q : α × Option Pub9)
    (y : Bound GE8) (tlb : HTailF2) (funs : Array HFun) (v : Pub9) (n : ℕ) (l4 : List GE8)
    (h1 : π q.1 = (some tlb, some funs)) (h2 : q.2 = some v)
    (hmS : ∀ mu, mu < tlb.NM → (tlb.shp.getD mu {}).mS = Alg.symRows (tlb.shp.getD mu {}).m)
    (hl4 : l4.length = 4) (hn : n + 4 ≤ v.F.planClaimsF) :
    ((numbered n l4 ++ tmRest π q y).map (·.1)).Nodup ∧
      ∀ x ∈ numbered n l4 ++ tmRest π q y,
        InWin n (len8 π q) v.F.planClaimsF 0 (top8 tlb funs) x.1 := by
  obtain ⟨r1, r2⟩ := tmRest_exps π q y tlb funs v h1 h2 hmS
  have hlen : len8 π q = 4 + (tlb.NM + (readsList tlb funs).length) := by
    simp only [len8, h1]
  refine ⟨?_, fun x hx => ?_⟩
  · rw [List.map_append, List.nodup_append]
    refine ⟨numbered_exps l4 n, r1, fun a ha b hb => ?_⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hb
    have w1 := (numbered_mem l4 n x hx).2
    have w2 := (r2 z hz).1
    omega
  · rcases List.mem_append.1 hx with h | h
    · have w := numbered_mem l4 n x h
      exact Or.inl ⟨w.1, by omega⟩
    · have w := r2 x h
      exact Or.inr ⟨by omega, by omega⟩

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.tmRest_exps
#print axioms VerifiableInference.Desc.K9L.k8_disc
