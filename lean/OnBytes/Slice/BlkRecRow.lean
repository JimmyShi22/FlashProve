-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkRecRow.lean: the row of a stored table's record in the program's link, in the
field, in the terms of the sample map recZ of one row.

Where stored tables have a record, the program's link (OnBytes/Iop/Link.lean) puts aside, for each
of the two tables and each seed of its record, one row on the table's folded row
(OnBytes/Iop/Foldeq.lean: foldeqJoined, foldeqRecordRow). OnBytes/Slice/BlkLinRec.lean and
BlkLinRecAt.lean read such a row entry by entry (LinF.recW), and OnBytes/Slice/RecRowLaws.lean shows
that these coefficients are the matrix of the sample map recZ (OnBytes/Slice/RecordRead.lean). This
file puts the three together where a folded row is arranged as in the link (Sz.layU): the row has
the coefficients Sz.recC (OnBytes/Slice/RowsXRec.lean) and the library's fold of the record's
answers as its target. It is general in the number s of answers.

Main definition.
 KeyHasR   "the program's key of a table holds the record rec": KeyIs (OnBytes/Slice/KeyOfRec.lean)
           without its clause on the number of the statement's item, which is 1 for the copy.
Main theorems.
 foldeqRecordRow_inv   what the program's row is made of.
 coefAt_recRow         its coefficient at row r, place p of the folded row's main table is Sz.recC.
 coefAt_recRow_else    it is 0 on every other table.
 recRow_target         its target is the library's fold of the record's answers (LdIx.tgt).
 recRow_kind           its kind is .plain: what the order of the test's rows reads.
 recRow_main           it has no term on a mask table.
 recRow_plain          its terms have no written-out factor, and it has no form: what PlainRow
                       (OnBytes/Slice/BlkPlain.lean) asks: another sense of the word than the
                       kind's.
 recRows_getD          the rows of a key's seeds, one by one.
 keyHasR_recOfKey      a key holds the record that is read off it (recOfKey,
                       OnBytes/Slice/BlkKeyRec.lean).
 keyHasR_keyOf         each record is held by some key, whatever the item's number, at a shape with
                       the record's three numbers.

Not claimed. That a run of the program's link yields these rows. That a key which a reader makes has
factors with words below the prime: keyHasR_recOfKey asks it. For seeds that the program draws:
seedOK_recordSeeds (OnBytes/Slice/SeedWords.lean); no theorem here calls it
(OnBytes/Slice/KeyTableRec.lean does, for the keys that tableKey returns). Nothing on where a
record's seeds come from, on what a record is good for, or on soundness.

-/
import OnBytes.Slice.BlkLink
import OnBytes.Slice.RecRowLaws
import OnBytes.Slice.BlkKeyRec
import OnBytes.Slice.RowsXRec

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run

/-! ## A key and a record -/

/-- **The program's key of a table holds the record rec**, at a table of the shape sh, whatever the
number of the statement's item that the key names: the shape has the record's three numbers, the
key's sizes fit the shape, and, read in the field, the key's seeds and answers are the record's. -/
def KeyHasR (v lg s : ℕ) (sh : Params.IndexShape) (key : TableKey) (rec : RecP NZ v lg s) : Prop :=
  KeyIs (fun β : NZ => β.val) sh { key with item := 0 } rec

/-- A key holds the record that is read off it, if its sizes fit the shape, no seed's factor is the
program's 0, and the factors have words below the prime. -/
theorem keyHasR_recOfKey (sh : Params.IndexShape) (key : TableKey) (hf : key.fits sh = true)
    (hz : (key.seeds.all fun x => !isZeroE x.beta) = true)
    (hok : ∀ x ∈ key.seeds, okE x.beta = true) :
    KeyHasR sh.v sh.cubeBits sh.answers sh key (recOfKey sh key) :=
  keyIs_recOfKey sh { key with item := 0 } rfl hf hz hok

/-- For each record and each number of an item there is a key that holds the record, at a shape with
the record's three numbers: the written key (keyOf, OnBytes/Slice/KeyOfRec.lean) with that number.
So KeyHasR alone is no empty hypothesis; this is no guard that the hypotheses of a theorem that asks
KeyHasR among others hold together. -/
theorem keyHasR_keyOf {v lg s : ℕ} (rec : RecP NZ v lg s) (sh : Params.IndexShape) (hv : sh.v = v)
    (hs : sh.answers = s) (hl : sh.cubeBits = lg) (item : ℕ) :
    KeyHasR v lg s sh { keyOf (fun β : NZ => β.val) rec with item := item } rec :=
  keyIs_keyOf (fun β : NZ => β.val) rec sh hv hs hl

/-- The key has a seed for each answer. -/
theorem KeyHasR.seeds_length {v lg s : ℕ} {sh : Params.IndexShape} {key : TableKey}
    {rec : RecP NZ v lg s} (hK : KeyHasR v lg s sh key rec) : key.seeds.length = s := by
  have h5 := congrArg List.length hK.seeds
  rw [List.length_map, List.length_ofFn] at h5
  exact h5

/-- The key's seed number a, read, is the record's. -/
theorem KeyHasR.seed_at {v lg s : ℕ} {sh : Params.IndexShape} {key : TableKey}
    {rec : RecP NZ v lg s} (hK : KeyHasR v lg s sh key rec) (a : Fin s) :
    key.seeds.length = s ∧ (key.seeds.getD a.val default).z.map readE = List.ofFn (rec.1 a).1 ∧
      readE (key.seeds.getD a.val default).beta = (rec.1 a).2.val := by
  obtain ⟨sd, h1, h2, h3⟩ := seed_atR hK a
  have h4 : key.seeds[a.val]? = some sd := h1
  rw [List.getD_eq_getElem?_getD, h4]
  exact ⟨hK.seeds_length, h2, h3⟩

/-! ## What the row is made of -/

/-- Coefficients on single entries change neither the terms nor the forms of a row. -/
theorem unitFold_terms {α : Type} (o : ℕ) (part : OnBytes.Part) (f : α → ℕ) (c : α → E) :
    ∀ (l : List α) (r : Row),
    (l.foldl (fun r q => r.addUnit o part (f q) (c q)) r).terms = r.terms ∧
      (l.foldl (fun r q => r.addUnit o part (f q) (c q)) r).forms = r.forms
  | [], _ => ⟨rfl, rfl⟩
  | q :: l, r => unitFold_terms o part f c l (r.addUnit o part (f q) (c q))

/-- What the program's row of the record's answer number i is made of: the equality vector at the
seed's point, cut at the length of a row's message and placed on the folded row's table; a mend on
the single entry of each pad; the fold of the answers as the target. -/
theorem foldeqRecordRow_inv (Sf : Params.FoldeqShape) (seed : SampleSeed) (record : Array E)
    (i : ℕ) (eqGamma : Array E) (u : FoldedRow) (row : Row)
    (h : foldeqRecordRow Sf seed record i eqGamma u = some row) :
    seed.z.length = Sf.index.cubeBits ∧ record.size = Sf.index.rows * Sf.index.answers ∧ ∃ cut,
      tensorBelow (Tensor.eq seed.z) 0 Sf.index.cubeBits Sf.index.code.ell = some cut ∧
      row = { (LinF.padList Sf.index.answers).foldl (fun (r : Row) q =>
          r.addUnit u.oracle .main (u.lay.index (Sf.index.padPlace q.1 q.2))
            (subE (if q.1 == i then mulE seed.beta (thetaE q.2) else zeroE)
              ((Tensor.eq seed.z).entry (Sf.index.padPlace q.1 q.2)))) (u.addAll {} cut) with
        target := (List.range Sf.index.rows).foldl (fun t r =>
          maddE t (eqGamma.getD r zeroE) (record.getD (r * Sf.index.answers + i) zeroE))
          zeroE } := by
  unfold foldeqRecordRow at h
  by_cases hg : (seed.z.length == Sf.index.cubeBits &&
      record.size == Sf.index.rows * Sf.index.answers) = true
  · simp only [hg, guard, if_true, Option.bind_eq_bind, Option.pure_def, Option.bind_some] at h
    obtain ⟨cut, hcut, hr⟩ := Option.bind_eq_some_iff.1 h
    obtain rfl := Option.some.inj hr
    have hfold := foldl_pairs (fun (r : Row) a t =>
      r.addUnit u.oracle .main (u.lay.index (Sf.index.padPlace a t))
        (subE (if a == i then mulE seed.beta (thetaE t) else zeroE)
          ((Tensor.eq seed.z).entry (Sf.index.padPlace a t)))) (List.range 3)
      (List.range Sf.index.answers) (u.addAll {} cut)
    simp only [Bool.and_eq_true, beq_iff_eq] at hg
    refine ⟨hg.1, hg.2, cut, hcut, ?_⟩
    unfold LinF.padList
    rw [← hfold]
  · simp [hg, guard] at h

/-! ## The row, in the field -/

/-- **The program's row of the record's answer number i, in the field.** On the folded row's oracle
message it has the coefficients of Sz.recC at the record's seed ρ: the matrix of the sample map of
one row on the entries of a row's message, and 0 beyond. ρ is read at i alone. No hypothesis names
lg, but hz gives the point lg coordinates and the program's guard gives it cubeBits: so lg is the
shape's cubeBits wherever the call returns a row. -/
theorem coefAt_recRow (S : Sz) (Sf : Params.FoldeqShape) (lg s : ℕ) (seed : SampleSeed)
    (record : Array E) (i : Fin s) (eqGamma : Array E) (u : FoldedRow) (row : Row)
    (hell : Sf.index.code.ell = S.P.T.l) (hans : Sf.index.answers = s) (h3 : 3 * s ≤ S.P.T.l)
    (hl2 : S.P.C.l = 2 ^ S.P.aP) (hu : u.lay = S.layU) (ρ : (recZ S.P.T.l lg s).D)
    (hz : seed.z.map readE = List.ofFn (ρ i).1) (hβ : readE seed.beta = (ρ i).2.val)
    (h : foldeqRecordRow Sf seed record i.val eqGamma u = some row) (r p : ℕ)
    (hr : r < 2 ^ S.P.aR) (hp : p < 2 ^ S.P.aP) :
    coefAt row u.oracle .main (r + 2 ^ S.P.aR * p) =
      S.recC (recZ S.P.T.l lg s) ρ i (r * 2 ^ S.P.aP + p) := by
  obtain ⟨hi, -⟩ := within_table S.P.aR S.P.aP r p hr hp
  have hRl : S.P.R * S.P.C.l ≤ 2 ^ (S.P.aR + S.P.aP) := by
    rw [Nat.pow_add, hl2]
    exact Nat.mul_le_mul_right _ (le_two_pow_clog S.P.R)
  have hTl : S.P.T.l ≤ 2 ^ (S.P.aR + S.P.aP) := le_trans S.fitM hRl
  have hread := (read_recordRow Sf seed record i.val eqGamma u row
    (by rw [hu]; exact ceilLog2_le _ _ (by rw [hell]; exact hTl))
    (le_two_pow_ceilLog2 _) h).2
  have e : coefAt row u.oracle .main (r + 2 ^ S.P.aR * p) =
      (readRow row).coef u.oracle .main (r + 2 ^ S.P.aR * p) := rfl
  rw [e, hread, hu, hell, hans, hz, hβ,
    LinF.rec_coef S.layU u.oracle S.P.T.l s _ _ i.val _ hTl h3 _ hi, entryAt_layU S r p hr]
  unfold Sz.recC
  by_cases h1 : r * 2 ^ S.P.aP + p < S.P.T.l
  · rw [dif_pos h1]
    exact recW_recZR S.P.T.l lg s h3 ρ i ⟨_, h1⟩
  · rw [dif_neg h1]
    unfold LinF.recW
    rw [if_neg fun h2 => h1 (lt_of_lt_of_le h2 (Nat.sub_le _ _)), if_neg h1]

/-- The program's row of a record's answer is 0 on every table but the main table of the folded
row's oracle message. -/
theorem coefAt_recRow_else (Sf : Params.FoldeqShape) (seed : SampleSeed) (record : Array E)
    (i : ℕ) (eqGamma : Array E) (u : FoldedRow) (row : Row)
    (h : foldeqRecordRow Sf seed record i eqGamma u = some row) (o : ℕ) (part : OnBytes.Part)
    (j : ℕ)
    (ho : ¬ (o = u.oracle ∧ part = .main)) : coefAt row o part j = 0 := by
  obtain ⟨-, -, cut, -, rfl⟩ := foldeqRecordRow_inv Sf seed record i eqGamma u row h
  have hf : (u.oracle == o && OnBytes.Part.main == part) = false := by
    rw [Bool.and_eq_false_iff]
    by_cases h1 : o = u.oracle
    · exact Or.inr (beq_eq_false_iff_ne.2 fun h2 => ho ⟨h1, h2.symm⟩)
    · exact Or.inl (beq_eq_false_iff_ne.2 fun h2 => h1 h2.symm)
  show coefAt (List.foldl _ (u.addAll {} cut) (LinF.padList Sf.index.answers)) o part j = 0
  unfold FoldedRow.addAll
  rw [coefAt_unitFold, coefAt_addLaid, coefAt_empty, hf]
  simp

/-- **The target of the program's row of the record's answer number i is the library's fold of the
record's answers**, at the point gamma read in the field, if the key holds the record and the
weights are those of gamma. -/
theorem recRow_target (S : Sz) (Sf : Params.FoldeqShape) (lg s : ℕ) (key : TableKey)
    (seed : SampleSeed) (i : Fin s) (gamma : List E) (u : FoldedRow) (row : Row)
    (rec : (S.ixR (recZ S.P.T.l lg s)).Rec) (hK : KeyHasR S.P.v lg s Sf.index key rec)
    (hg : gamma.length = S.P.v)
    (h : foldeqRecordRow Sf seed key.record i.val (foldeqWeights gamma) u = some row) :
    readE row.target = (S.ixR (recZ S.P.T.l lg s)).tgt rec (readP S.P.v gamma) i := by
  obtain ⟨-, -, cut, -, rfl⟩ := foldeqRecordRow_inv Sf seed key.record i.val _ u row h
  show readE (List.foldl _ zeroE (List.range Sf.index.rows)) = _
  rw [readE_maddFold (fun j => (foldeqWeights gamma).getD j zeroE)
    (fun j => key.record.getD (j * Sf.index.answers + i.val) zeroE), readE_zero, zero_add]
  exact target_recR hK gamma hg i

/-- The program's row of a record's answer is a plain row. -/
theorem recRow_kind (Sf : Params.FoldeqShape) (seed : SampleSeed) (record : Array E) (i : ℕ)
    (eqGamma : Array E) (u : FoldedRow) (row : Row)
    (h : foldeqRecordRow Sf seed record i eqGamma u = some row) : row.kind = .plain := by
  obtain ⟨-, -, cut, -, rfl⟩ := foldeqRecordRow_inv Sf seed record i eqGamma u row h
  show (List.foldl _ (u.addAll {} cut) (LinF.padList Sf.index.answers)).kind = _
  exact (unitFold_keeps _ _ _ _ _ _).1.trans (addLaid_keeps u.oracle u.lay cut {}).2

/-- The program's row of a record's answer has no term on a mask table. -/
theorem recRow_main (Sf : Params.FoldeqShape) (seed : SampleSeed) (record : Array E) (i : ℕ)
    (eqGamma : Array E) (u : FoldedRow) (row : Row)
    (h : foldeqRecordRow Sf seed record i eqGamma u = some row) :
    ∀ t ∈ row.terms.toList, t.part = .main := by
  obtain ⟨-, -, cut, -, rfl⟩ := foldeqRecordRow_inv Sf seed record i eqGamma u row h
  show ∀ t ∈ (List.foldl _ (u.addAll {} cut) (LinF.padList Sf.index.answers)).terms.toList,
    t.part = .main
  rw [(unitFold_terms _ _ _ _ _ _).1]
  unfold FoldedRow.addAll
  exact addLaid_main _ _ _ _ fun t ht => by cases ht

/-- The terms of the program's row of a record's answer have no written-out factor, and the row has
no form. -/
theorem recRow_plain (Sf : Params.FoldeqShape) (seed : SampleSeed) (record : Array E) (i : ℕ)
    (eqGamma : Array E) (u : FoldedRow) (row : Row)
    (h : foldeqRecordRow Sf seed record i eqGamma u = some row) :
    (∀ t ∈ row.terms.toList, t.v.denseVars = []) ∧ row.forms = #[] := by
  obtain ⟨-, -, cut, hcut, rfl⟩ := foldeqRecordRow_inv Sf seed record i eqGamma u row h
  show (∀ t ∈ (List.foldl _ (u.addAll {} cut) (LinF.padList Sf.index.answers)).terms.toList,
      t.v.denseVars = []) ∧
    (List.foldl _ (u.addAll {} cut) (LinF.padList Sf.index.answers)).forms = #[]
  rw [(unitFold_terms _ _ _ _ _ _).1, (unitFold_terms _ _ _ _ _ _).2]
  unfold FoldedRow.addAll
  refine ⟨addLaid_plain _ _ _ _
    (fun t ht => (tensorBelow_shape_at (Tensor.eq seed.z) rfl 0 _ _ cut hcut t ht).2)
    (fun t ht => by cases ht), ?_⟩
  rw [(addLaid_terms _ _ _ _).2]

/-! ## The rows of a key's seeds -/

/-- The rows of a key's seeds, one by one: there is a row for each seed, and row number i is the
row of seed number i and answer number i. -/
theorem recRows_getD (Sf : Params.FoldeqShape) (key : TableKey) (eqGamma : Array E)
    (u : FoldedRow) (rows : List Row)
    (h : (key.seeds.zipIdx.mapM fun x =>
      foldeqRecordRow Sf x.1 key.record x.2 eqGamma u) = some rows) :
    rows.length = key.seeds.length ∧ ∀ i, i < key.seeds.length →
      foldeqRecordRow Sf (key.seeds.getD i default) key.record i eqGamma u =
        some (rows.getD i default) := by
  obtain ⟨h1, h2⟩ := mapM_getD _ (default, 0) default key.seeds.zipIdx rows h
  rw [List.length_zipIdx] at h1 h2
  refine ⟨h1, fun i hi => ?_⟩
  have h3 := h2 i hi
  have e : key.seeds.zipIdx.getD i (default, 0) = (key.seeds.getD i default, i) := by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_zipIdx]; exact hi), List.getElem_zipIdx,
      List.getD_eq_getElem _ _ hi, Nat.zero_add]
  rw [e] at h3
  exact h3

end OnBytes.Slice
