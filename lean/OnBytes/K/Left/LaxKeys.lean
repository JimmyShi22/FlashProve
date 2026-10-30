-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/LaxKeys.lean: the two keys of stored tables that the program makes of what it read
and drew are the two keys that are written of the typed instance. So the decision of a run
(`decRun`, OnBytes/TypedOracleCompiler/Slice/EntryRunMain.lean) at that instance is the program's own decision.

A key holds a table's answers and its record's seeds as the program's elements: triples of words. A
typed instance holds them read in the field, and `keysOfX` (OnBytes/TypedOracleCompiler/Slice/KeysOfX.lean) writes
them back with words below the prime. The two agree because the program's own have such words: its
readers refuse an answer in another form, and its draw gives none.

Main names:
  `readTable_answers`: each answer that `readTable` returns has words below the prime.
  `key_answers`, `entry_answers`: so has each answer of the table that `Key.readTable` returns, and
    of the further table that `Entry.read` returns.
  `key_written`: a key that `tableKey` returns, at a table with such answers and the seeds l, is the
    key written of l and the answers as they are read in the field, with its own item.
  `keys_at`: under `PortYesAt` and `G.SaysLines`: the keys written of the instance
    `xOfAskedC lg s ⟨table, further, l0, l1, o⟩` are the program's two keys.
  `dec_at`: so `decRun` at that instance is `entryDecR` at the program's two keys.
  `dec_yes`: `ground` (OnBytes/K/Left/LaxGround.lean) with its clause on the decision said of
    `decRun` at the typed instance, at numbers v, lg, s that are the shape's.
  `record_field`, `small_record_field`: the test on the field, at both grounds.

Hypotheses: `PortYesAt`; `G.SaysLines F.pol`; tests on G: its tables have a record; its field is the
one in which the program computes; v, lg and s are the numbers of its tables' shape.

Limits: values alone. Nothing on soundness; no probability.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Left.LaxGround
import OnBytes.Slice.KeyOfRecBack
import OnBytes.Slice.KeyTableRec
import OnBytes.TypedOracleCompiler.Slice.EntryRunMain

set_option autoImplicit false

namespace OnBytes.K.Left
open OnBytes.Tie
open OnBytes.Slice
open TypedOracleCompiler.Slice

/-! ## The answers that the program reads have words below the prime -/

/-- An element that the reader of elements has read is in the field's range. -/
theorem rdElt_ok {f : Fmt.Fld} {b : ByteArray} {i j : ℕ} {w : UInt64}
    (h : Fmt.rdElt f b i = some (w, j)) : f.ok w = true := by
  unfold Fmt.rdElt at h
  split at h
  · split at h
    · rename_i hw
      cases h
      exact hw
    · cases h
  · cases h

/-- A yes of the reader of a pair is a yes of the first reader and then of the second. -/
theorem rdPair_some {α β : Type} {ra : Fmt.Rd α} {rb : Fmt.Rd β} {b : ByteArray} {i k : ℕ} {x : α}
    {y : β} (h : Fmt.rdPair ra rb b i = some ((x, y), k)) :
    ∃ j, ra b i = some (x, j) ∧ rb b j = some (y, k) := by
  unfold Fmt.rdPair at h
  split at h
  · rename_i x' j hx
    split at h
    · rename_i y' k' hy
      cases h
      exact ⟨j, hx, hy⟩
    · cases h
  · cases h

/-- An element of the extension that its reader has read is in range. -/
theorem rdExt_ok {f : Fmt.Fld} {b : ByteArray} {i j : ℕ} {t : UInt64 × UInt64 × UInt64}
    (h : Fmt.rdExt f b i = some (t, j)) : f.okE t = true := by
  obtain ⟨t1, t2, t3⟩ := t
  unfold Fmt.rdExt at h
  obtain ⟨j1, h1, h'⟩ := rdPair_some h
  obtain ⟨j2, h2, h3⟩ := rdPair_some h'
  unfold Fmt.Fld.okE
  rw [rdElt_ok h1, rdElt_ok h2, rdElt_ok h3]
  rfl

/-- What holds of whatever a reader returns holds of every member of the list that it reads. -/
theorem rdMany_all {α : Type} (r : Fmt.Rd α) (P : α → Prop)
    (hP : ∀ b i x j, r b i = some (x, j) → P x) :
    ∀ (n : ℕ) (b : ByteArray) (i : ℕ) (l : List α) (k : ℕ),
      Fmt.rdMany r n b i = some (l, k) → ∀ x ∈ l, P x := by
  intro n
  induction n with
  | zero =>
    intro b i l k h x hx
    unfold Fmt.rdMany at h
    cases h
    cases hx
  | succ n ih =>
    intro b i l k h x hx
    unfold Fmt.rdMany at h
    split at h
    · rename_i y j hy
      split at h
      · rename_i l' k' hl
        cases h
        rcases List.mem_cons.1 hx with rfl | h2
        · exact hP _ _ _ _ hy
        · exact ih _ _ _ _ hl x h2
      · cases h
    · cases h

/-- Each answer that `readTable` returns has words below the prime. -/
theorem readTable_answers {count : ℕ} {b : ByteArray} {i k : ℕ} {t : Params.TableName}
    (h : readTable .two count b i = .ok (t, k)) : ∀ a ∈ t.answers, okE a = true := by
  unfold readTable at h
  split at h
  · cases h
  · rename_i root j hd
    split at h
    · cases h
    · rename_i ys k' hy
      injection h with h'
      have e : t = ⟨root, ys.map E.ofTriple⟩ := (congrArg (·.1) h').symm
      subst e
      intro a ha
      obtain ⟨y, hy', rfl⟩ := List.mem_map.1 ha
      rw [okE_triple, E.triple_ofTriple]
      rw [rdManyT_eq] at hy
      exact rdMany_all _ _ (fun _ _ _ _ h => rdExt_ok h) _ _ _ _ _ hy y hy'

/-- So has each answer of the table that `Key.readTable` returns. -/
theorem key_answers {s : Params.IndexShape} {c file : ByteArray} {t : Params.TableName} {j : ℕ}
    (h : Key.readTable s c file = .ok (t, j)) : ∀ a ∈ t.answers, okE a = true := by
  unfold Key.readTable at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i table k ht
        split at h
        · cases h
          exact readTable_answers ht
        · cases h

/-- And each answer of the further table that `Entry.read` returns. -/
theorem entry_answers {p : Params.Link} {first : Params.TableName} {file : ByteArray}
    {r : Entry.EntryRead} (hf : p.given.plan.field = .two)
    (hr : Entry.read p first file = .ok r) : ∀ a ∈ r.further.answers, okE a = true := by
  unfold Entry.read at hr
  dsimp only at hr
  rw [hf] at hr
  split at hr
  · simp [Entry.no] at hr
  · split at hr
    · simp [Entry.noParameters] at hr
    · split at hr
      · simp [Entry.no] at hr
      · rename_i further j ht
        split at hr
        · split at hr
          · simp [Entry.noParameters] at hr
          · split at hr
            · simp [Entry.no] at hr
            · split at hr
              · simp [Entry.no] at hr
              · injection hr with hr'
                subst hr'
                exact readTable_answers ht
        · simp [Entry.no] at hr

/-! ## The written key is the program's -/

/-- A key that `tableKey` returns, at a table whose answers have words below the prime and at the
seeds l, is the key that is written of l and the answers as they are read in the field, with its
own item. -/
theorem key_written {cfg : ByteArray} {sh : Params.IndexShape} {t : Params.TableName} {item : ℕ}
    {l : List (List E × E)}
    (hk : tableKey .two cfg sh t item =
      some { item := item, record := t.answers.toArray, seeds := l.map fun x => ⟨x.1, x.2⟩ })
    (ha : ∀ a ∈ t.answers, okE a = true) :
    ({ item := item, record := t.answers.toArray, seeds := l.map fun x => ⟨x.1, x.2⟩ } : TableKey) =
      { keyOf (fun β : NZ => β.val)
          (seedOf sh.cubeBits sh.answers l, anT sh.v sh.answers (t.answers.map E.triple)) with
        item := item } := by
  have hfit := (Params.tableKey_fits hk).1
  have h1 := keyOf_recOfKey sh _ hfit (tableKey_nz hk)
    (fun a h => ha a (by simpa using h))
    (fun x hx => ⟨(tableKey_seeds hk x hx).2.1, (tableKey_seeds hk x hx).1⟩)
  have hlen : l.length = sh.answers := by
    unfold TableKey.fits at hfit
    simp only [Bool.and_eq_true, beq_iff_eq, List.length_map] at hfit
    exact hfit.1.2
  have e : recOfKey sh
      { item := item, record := t.answers.toArray, seeds := l.map fun x => ⟨x.1, x.2⟩ } =
      (seedOf sh.cubeBits sh.answers l, anT sh.v sh.answers (t.answers.map E.triple)) := by
    refine Prod.ext (funext fun i => ?_) (funext fun q => ?_)
    · have hi : i.val < l.length := by
        rw [hlen]
        exact i.isLt
      have g1 : (l.map fun x => (⟨x.1, x.2⟩ : SampleSeed)).getD i.val default =
          ⟨l[i.val].1, l[i.val].2⟩ := by
        rw [List.getD_eq_getElem _ _ (by rwa [List.length_map]), List.getElem_map]
      have g2 : l.getD i.val ([], oneE) = l[i.val] := List.getD_eq_getElem _ _ hi
      show ((fun c : Fin sh.cubeBits => readE
          (((l.map fun x => (⟨x.1, x.2⟩ : SampleSeed)).getD i.val default).z.getD c.val zeroE)),
        asFactor (readE ((l.map fun x => (⟨x.1, x.2⟩ : SampleSeed)).getD i.val default).beta)) =
        seedOf1 sh.cubeBits (l.getD i.val ([], oneE))
      rw [g1, g2]
      rfl
    · show readE (t.answers.toArray.getD (Sz.rowNo q.1 * sh.answers + q.2.val) zeroE) =
        toE ((t.answers.map E.triple).getD (Sz.rowNo q.1 * sh.answers + q.2.val) (0, 0, 0))
      rw [readE_def, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
        List.getD_eq_getElem?_getD, List.getElem?_map]
      cases t.answers[Sz.rowNo q.1 * sh.answers + q.2.val]? with
      | none => rfl
      | some e => rfl
  rw [e] at h1
  exact h1

/-! ## At the entry file, from the exit code 0 -/

/-- The keys written of the typed instance are the program's two keys. r, l0, l1: what
`read_at` (OnBytes/K/Left/Conv.lean) names. -/
theorem keys_at (G : EntryGround) (hA : (G.q.link.table.answers == 0) = false)
    (hF : G.q.given.plan.field = .two)
    {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) (hl : G.SaysLines F.pol)
    {l0 l1 : List (List E × E)}
    (a0 : seedsUnder recordSeeds
      (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL])) table = some l0)
    (a1 : seedsUnder recordSeeds
      (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL])) further = some l1)
    (o : Fmt.ChainOut) :
    keysOfX G.q.link.table.v G.q.link.table.cubeBits G.q.link.table.answers
        (anT G.q.link.table.v G.q.link.table.answers)
        (xOfAskedC G.q.link.table.cubeBits G.q.link.table.answers
          ⟨table, further, l0, l1, o⟩) =
      ({ item := 0, record := table.answers.toArray, seeds := l0.map fun x => ⟨x.1, x.2⟩ },
        { item := 1, record := further.answers.toArray, seeds := l1.map fun x => ⟨x.1, x.2⟩ }) := by
  obtain ⟨p, -, hk, -, -, -, -⟩ := entry_facts h
  obtain ⟨j, hj⟩ := Model.Verify.keyCheck_table hk
  obtain ⟨r, l0', l1', hr, hf, b0, b1, -, -⟩ := read_at G hA h hl
  obtain rfl : l0' = l0 := Option.some.inj (b0.symm.trans a0)
  obtain rfl : l1' = l1 := Option.some.inj (b1.symm.trans a1)
  have hF' : (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL])).given.plan.field =
      .two := hF
  have ans0 := key_answers hj
  have ans1 := entry_answers hF' hr
  rw [hf] at ans1
  obtain ⟨_, S, _, hS, -, -⟩ := entry_read_spec _ table F.ent r hr
  obtain ⟨⟨k0, k1, hk0, hk1, -⟩, -⟩ := Params.entrySpec_eq_all hS
  rw [hf] at hk1
  rw [hF'] at hk0 hk1
  obtain ⟨m0, hm0, rfl⟩ := keyWith_seeds hk0 hA
  obtain ⟨m1, hm1, rfl⟩ := keyWith_seeds hk1 hA
  -- by the named equation, not by unfolding: see `Tie.seedsUnder_eq`
  rw [seedsUnder_eq, nameUnder, hF'] at b0 b1
  obtain rfl : m0 = l0' := Option.some.inj (hm0.symm.trans b0)
  obtain rfl : m1 = l1' := Option.some.inj (hm1.symm.trans b1)
  rw [xOfAskedC_eq]
  unfold keysOfX xOfAsked
  exact Prod.ext (key_written hk0 ans0).symm (key_written hk1 ans1).symm

/-- So the decision of a run at that instance is the program's own decision at its two keys. -/
theorem dec_at (G : EntryGround) (hA : (G.q.link.table.answers == 0) = false)
    (hF : G.q.given.plan.field = .two)
    {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) (hl : G.SaysLines F.pol)
    {l0 l1 : List (List E × E)}
    (a0 : seedsUnder recordSeeds
      (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL])) table = some l0)
    (a1 : seedsUnder recordSeeds
      (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL])) further = some l1)
    (o : Fmt.ChainOut) :
    decRun (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL])) G.q.link.table.v
        G.q.link.table.cubeBits G.q.link.table.answers
        (xOfAskedC G.q.link.table.cubeBits G.q.link.table.answers
          ⟨table, further, l0, l1, o⟩) =
      entryDecR (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL]))
        { item := 0, record := table.answers.toArray, seeds := l0.map fun x => ⟨x.1, x.2⟩ }
        { item := 1, record := further.answers.toArray, seeds := l1.map fun x => ⟨x.1, x.2⟩ } := by
  unfold decRun
  rw [keys_at G hA hF h hl a0 a1 o]

/-- The full-size ground's field is the one in which the program computes. -/
theorem record_field : recordGround.q.given.plan.field = .two := by decide +kernel

/-- So is the small ground's. -/
theorem small_record_field : smallRecordGround.q.given.plan.field = .two := by decide +kernel

/-- The decision of a run says yes on the view of what the strict reader read. `ground`'s
clauses, with the decision said of `decRun` at the typed instance. -/
theorem dec_yes (G : EntryGround) (hA : (G.q.link.table.answers == 0) = false)
    (hF : G.q.given.plan.field = .two) {v lg s : ℕ} (hv : G.q.link.table.v = v)
    (hlg : G.q.link.table.cubeBits = lg) (hs : G.q.link.table.answers = s)
    {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) (hl : G.SaysLines F.pol) :
    ∃ (r : Entry.EntryRead) (l0 l1 : List (List E × E)) (i : ℕ),
      Entry.read (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL])) table F.ent =
        .ok r ∧ r.further = further ∧
      seedsUnder recordSeeds (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL]))
        table = some l0 ∧
      seedsUnder recordSeeds (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL]))
        further = some l1 ∧
      Fmt.readChainX (m := Id) (Fmt.HO Fmt.oracle)
        (TypedOracleCompiler.Run.PQ.withStatement (specAt G (Params.configurationDigest [F.pol, F.lay, F.KL]))
          (stmAt table.answers further.answers table.root further.root))
        Session.start.seen F.ent i = some (r.chain.out, r.chain.next) ∧
      decRun (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL])) v lg s
        (xOfAskedC lg s ⟨table, further, l0, l1, r.chain.out⟩)
        (Fmt.viewX
          (TypedOracleCompiler.Run.PQ.withStatement (specAt G (Params.configurationDigest [F.pol, F.lay, F.KL]))
            (stmAt table.answers further.answers table.root further.root)) r.chain.out) = true := by
  subst hv hlg hs
  obtain ⟨r, l0, l1, i, hr, hf, a0, a1, -, -, e, hd, -⟩ := ground G hA h hl
  refine ⟨r, l0, l1, i, hr, hf, a0, a1, e, ?_⟩
  rw [dec_at G hA hF h hl a0 a1 r.chain.out]
  exact hd

end OnBytes.K.Left
