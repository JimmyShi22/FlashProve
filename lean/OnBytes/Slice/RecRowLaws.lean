-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/RecRowLaws.lean: three small laws on a stored table's record, and one on sums, said
again in a file that imports little.

OnBytes/Slice/BlkRecRow.lean needs: that the coefficients LinF.recW of the program's row of a
record's answer (OnBytes/Slice/BlkLinRecAt.lean) are the matrix of the sample map recZ
(OnBytes/Slice/RecordRead.lean); that a key which holds a record (KeyIs,
OnBytes/Slice/KeyOfRec.lean) has the record's seeds, one by one; that the program's sum of the
answers under the weights of a point is the sum over the rows. The three are proved in
files of this project that are not in this library (recW_recZ in one; Mk2.seed_at, Mk2.target_rec in
another, the last with Mk2.wOf and Mk2.read_weights of a third), whose imports hold some 150 modules
on another
block of the program that these three do not use. Here their text stands again under new names. The
text of recW_recZR and seed_atR is that of recW_recZ and Mk2.seed_at; that of sum_list_rangeR is
that of ProxRun.sum_list_range (OnBytes/Slice/BlkProxFold.lean). target_recR is Mk2.target_rec with
Mk2.read_weights put in: the weights are the program's table, read, and not a function of the point
read; and the typed point is readP v gamma, where Mk2.target_rec has a letter γ with a hypothesis.

Main theorems: recW_recZR, seed_atR, sum_list_rangeR, target_recR.

Not claimed. That a key holds a record. That the sample map has the library's property Sample.OK.
Nothing on a run, and nothing on soundness.

-/
import OnBytes.Slice.BlkLinRecAt
import OnBytes.Slice.KeyOfRec
import OnBytes.Slice.RecordRead

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run

/-- **The coefficients of the program's row of the record's answer a are the matrix of the sample
map at the record's seed.** -/
theorem recW_recZR (l lg s : ℕ) (h3 : 3 * s ≤ l) (ρ : (recZ l lg s).D) (a : Fin s) (j : Fin l) :
    LinF.recW l s (List.ofFn (ρ a).1) (ρ a).2.val a.val j.val = (recZ l lg s).mat ρ a j := by
  unfold LinF.recW
  by_cases h1 : j.val < l - 3 * s
  · rw [if_pos h1, recZ_before l lg s ρ a j h1, List.length_ofFn]
    refine eqW_congr _ _ _ _ fun t ht => ?_
    rw [dif_pos ht, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos ht]
    rfl
  · have hq : (j.val - (l - 3 * s)) / 3 < s := by
      have := j.isLt
      omega
    rw [if_neg h1, if_pos j.isLt,
      recZ_pad l lg s ρ a j ⟨(j.val - (l - 3 * s)) / 3, hq⟩
        ⟨(j.val - (l - 3 * s)) % 3, Nat.mod_lt _ (by decide)⟩ (by
          show j.val = l - 3 * s + 3 * ((j.val - (l - 3 * s)) / 3) + (j.val - (l - 3 * s)) % 3
          omega)]
    by_cases h2 : (j.val - (l - 3 * s)) / 3 = a.val
    · rw [if_pos h2, if_pos (Fin.ext h2)]
    · rw [if_neg h2, if_neg fun h => h2 (congrArg Fin.val h)]

section
variable {B : Type} {val : B → GE} {v lg s : ℕ} {sh : Params.IndexShape} {key : TableKey}
  {rec : RecP B v lg s}

/-- The key's seed number a, read, is the record's. -/
theorem seed_atR (hK : KeyIs val sh key rec) (a : Fin s) :
    ∃ sd, key.seeds[a.val]? = some sd ∧ sd.z.map readE = List.ofFn (rec.1 a).1 ∧
      readE sd.beta = val (rec.1 a).2 := by
  have h := congrArg (fun l => l[a.val]?) hK.seeds
  simp only [List.getElem?_map, List.getElem?_ofFn, dif_pos a.isLt] at h
  cases hs : key.seeds[a.val]? with
  | none =>
    rw [hs] at h
    cases h
  | some sd =>
    rw [hs] at h
    have h2 := Option.some.inj h
    exact ⟨sd, rfl, congrArg Prod.fst h2, congrArg Prod.snd h2⟩

/-- A sum over a list of the first numbers, as a sum over a finite set. -/
theorem sum_list_rangeR (F : ℕ → GE) : ∀ n : ℕ,
    ((List.range n).map F).sum = ∑ b ∈ Finset.range n, F b
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_list_rangeR F n,
      Finset.sum_range_succ]
    simp

/-- **The folded answers**: the program's sum over the numbers of the table's rows, under the
program's table of the weights of the point gamma, is the sum over the rows under the weights of
gamma read in the field. -/
theorem target_recR (hK : KeyIs val sh key rec) (gamma : List E) (hl : gamma.length = v)
    (a : Fin s) :
    ((List.range sh.rows).map fun j => readE ((foldeqWeights gamma).getD j zeroE) *
      readE (key.record.getD (j * sh.answers + a.val) zeroE)).sum =
      ∑ r : Fin v → Bool, Alg.eqk (readP v gamma) r * rec.2 (r, a) := by
  have hrows : sh.rows = 2 ^ v := by
    unfold Params.IndexShape.rows
    rw [hK.vars]
  rw [hrows, hK.answers, sum_list_rangeR, ← sum_rowNo v fun j =>
    readE ((foldeqWeights gamma).getD j zeroE) * readE (key.record.getD (j * s + a.val) zeroE)]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hw : readE ((foldeqWeights gamma).getD (Sz.rowNo r) zeroE) =
      if Sz.rowNo r < 2 ^ gamma.length then eqW gamma.length (readL gamma) (Sz.rowNo r) else 0 :=
    readV_eqTable gamma (Sz.rowNo r)
  rw [hK.record r a, hw, hl, if_pos (rowNo_lt r), eqW_rowNo]
  rfl

end

end OnBytes.Slice
