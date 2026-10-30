-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/LinkRecordLaws.lean: the verifier program's block of an entry's chain is the block of
OnBytes/Maker/Link.lean at the pair of records over the field that are read off the two tables'
keys.

A key holds elements of the program: triples of words. Two such elements with different words can be
read as one element of the field, and `keyOf` writes words below the prime. So a key is the key
written of the record that is read off it only if its own words are below the prime.

Main theorems.
  `linkRec_rounds`: at the numbers of the tables' shape, the key written of any record fits the
    shape. So, where the dry run at keys of zeros succeeds, the dry run of the block states
    `linkRounds p` at every instance: what `iorLink` (OnBytes/Maker/Link.lean) leaves to its caller,
    with no condition on the instance.
  `key_back`: a key whose sizes fit the shape, none of whose factors is the program's 0, and whose
    words are all below the prime is the key written of the record that is read off it (`recOfKey`,
    OnBytes/Slice/BlkKeyRec.lean), with the key's own item.
  `link_value_rec`: if `Tie.entrySpec` gives a block and a description at two tables, the tables'
    answers have words below the prime, and the seeds of the two tables' keys pass the tests on
    factors and words (`SeedsClean`), then the block is `linkBlock keyRec p` at the pair of the
    records read off the keys, and the description is `linkSpec p` with the link's statement.
  `clean_keyRec`: the key written of any record passes all these tests, so they can be met.
  `linkValueAt_of_ok`, `linkValueAt_isLocal`: the value at the records, all from the parameter
    bytes, is `iorLink` at `linkRounds p` where the dry run at keys of zeros succeeds; it is local.

What is not claimed. That the answers of a table have words below the prime: `tableKey` takes any
answers. The program's reader of a table's answers (`readTable`, OnBytes/Entry/Table.lean) says in
its head that it takes canonical forms alone; no law on that is stated or used here. That the seeds
which the program draws pass `SeedsClean`. In `link_value_rec` all of these are hypotheses. Without
the test on words `key_back` is false. Where a factor of a key reads as 0 in the field, `recOfKey`
lays 1 in its place, so the record that is read off is then another key's; `SeedsClean` shuts that
case out. Nothing on where the seeds come from, on a decoder or on soundness.

What a caller has to bring. `linkRec_rounds`: that the dry run at keys of zeros succeeds.
`link_value_rec`: the four hypotheses on answers and seeds.

`mk_okE_writeE`, `mk_writeE_readE`, `mk_list_eq_of_read` and `mk_seeds_eq_of_read` are small laws on
reading and writing elements.


-/
import OnBytes.Maker.LinkRecord
import OnBytes.Maker.LinkValueLaws
import OnBytes.Slice.BlkKeyRec
import OnBytes.Field.ExtEq

set_option autoImplicit false

namespace OnBytes.Maker

open _root_.Run _root_.Run.PQ OnBytes.Slice
open OnBytes.Tie (entrySpec)

/-- At the numbers of the tables' shape the key written of a record fits the shape. -/
theorem keyRec_fits (p : OnBytes.Params.Link) (rec : RecAt p) :
    (keyRec rec).fits p.link.table = true :=
  keyOf_fits _ rec p.link.table rfl rfl rfl

/-- **The rounds at every instance**: if the dry run at keys of zeros succeeds, the dry run of the
block at any pair of records states `linkRounds p`. -/
theorem linkRec_rounds (p : OnBytes.Params.Link)
    (hp : (OnBytes.Params.entryRoundsAny p).isSome = true) (rr : RecAt p × RecAt p) :
    (linkBlock keyRec p rr).rounds (Entry.start p) = some (linkRounds p) :=
  linkRounds_owed keyRec p hp rr (keyRec_fits p rr.1) (keyRec_fits p rr.2)

/-- What is written has words below the prime. -/
theorem mk_okE_writeE (x : GE) : okE (writeE x) = true := by
  unfold writeE
  rw [okE_triple, E.triple_ofTriple]
  simp only [Fmt.Fld.okE, ofE, ok_ofF, Bool.and_self]

/-- An element with words below the prime is written back as it was. -/
theorem mk_writeE_readE (a : E) (ha : okE a = true) : writeE (readE a) = a :=
  readE_inj _ _ (mk_okE_writeE _) ha (readE_writeE _)

/-- Two lists of elements with words below the prime that are read as the same elements of the
field are one list. -/
theorem mk_list_eq_of_read : ∀ (l l' : List E), (∀ a ∈ l, okE a = true) → (∀ a ∈ l', okE a = true) →
    l.map readE = l'.map readE → l = l'
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by cases h
  | _ :: _, [], _, _, h => by cases h
  | a :: l, b :: l', h1, h2, h => by
    rw [List.map_cons, List.map_cons] at h
    obtain ⟨e1, e2⟩ := List.cons.inj h
    rw [readE_inj a b (h1 a List.mem_cons_self) (h2 b List.mem_cons_self) e1,
      mk_list_eq_of_read l l' (fun x hx => h1 x (List.mem_cons_of_mem _ hx))
        (fun x hx => h2 x (List.mem_cons_of_mem _ hx)) e2]

/-- The same for two lists of seeds. -/
theorem mk_seeds_eq_of_read : ∀ (l l' : List SampleSeed),
    (∀ x ∈ l, okE x.beta = true ∧ ∀ a ∈ x.z, okE a = true) →
    (∀ x ∈ l', okE x.beta = true ∧ ∀ a ∈ x.z, okE a = true) →
    (l.map fun x => (x.z.map readE, readE x.beta)) =
      (l'.map fun x => (x.z.map readE, readE x.beta)) → l = l'
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by cases h
  | _ :: _, [], _, _, h => by cases h
  | ⟨z, b⟩ :: l, ⟨z', b'⟩ :: l', h1, h2, h => by
    rw [List.map_cons, List.map_cons] at h
    obtain ⟨e1, e2⟩ := List.cons.inj h
    have ez : z.map readE = z'.map readE := congrArg Prod.fst e1
    have eb : readE b = readE b' := congrArg Prod.snd e1
    have a1 := h1 ⟨z, b⟩ List.mem_cons_self
    have a2 := h2 ⟨z', b'⟩ List.mem_cons_self
    rw [mk_list_eq_of_read z z' a1.2 a2.2 ez, readE_inj b b' a1.1 a2.1 eb,
      mk_seeds_eq_of_read l l' (fun x hx => h1 x (List.mem_cons_of_mem _ hx))
        (fun x hx => h2 x (List.mem_cons_of_mem _ hx)) e2]

/-- A key that holds the record rec (`KeyIs`, OnBytes/Slice/KeyOfRec.lean) and has words below the
prime in its answers and in every seed's point and factor is the key that is written of rec. -/
theorem keyRec_of_keyIs {v lg s : ℕ} {sh : OnBytes.Params.IndexShape} {key : TableKey}
    {rec : RecF v lg s} (hK : KeyIs (fun β : Fac => β.val) sh key rec)
    (hr : ∀ a ∈ key.record, okE a = true)
    (hs : ∀ x ∈ key.seeds, okE x.beta = true ∧ ∀ a ∈ x.z, okE a = true) : key = keyRec rec := by
  have hfit : key.fits sh = true := hK.fits
  unfold TableKey.fits OnBytes.Params.IndexShape.rows at hfit
  simp only [Bool.and_eq_true, beq_iff_eq] at hfit
  have hsize : key.record.size = 2 ^ v * s := by
    rw [hfit.1.1, hK.vars, hK.answers]
  -- the answers
  have hrec : key.record = (keyOf (fun β : Fac => β.val) rec).record := by
    refine Array.ext (by rw [hsize, keyOf_size]) fun n h1 h2 => ?_
    have hn : n < 2 ^ v * s := hsize ▸ h1
    have hs0 : 0 < s := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hn
    have hq : n / s < 2 ^ v := by
      rw [Nat.div_lt_iff_lt_mul hs0]
      exact hn
    have hk := hK.record (vtx v (n / s)) ⟨n % s, Nat.mod_lt _ hs0⟩
    have hk' : readE (key.record.getD (Sz.rowNo (vtx v (n / s)) * s + n % s) zeroE) =
        rec.2 (vtx v (n / s), ⟨n % s, Nat.mod_lt _ hs0⟩) := hk
    have hrv : Sz.rowNo (vtx v (n / s)) = n / s := by
      unfold vtx
      rw [rowNo_testBit, Nat.mod_eq_of_lt hq]
    rw [hrv, Nat.div_add_mod' n s, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem h1, Option.getD_some] at hk'
    have e : (keyOf (fun β : Fac => β.val) rec).record[n] =
        writeE (rec.2 (vtx v (n / s), ⟨n % s, Nat.mod_lt _ hs0⟩)) := by
      unfold keyOf
      simp
    rw [e, ← hk', mk_writeE_readE _ (hr _ (Array.getElem_mem h1))]
  -- the seeds
  have hseeds : key.seeds = (keyOf (fun β : Fac => β.val) rec).seeds := by
    have h2 : (key.seeds.map fun x => (x.z.map readE, readE x.beta)) =
        (keyOf (fun β : Fac => β.val) rec).seeds.map fun x => (x.z.map readE, readE x.beta) :=
      hK.seeds.trans (keyOf_seeds (fun β : Fac => β.val) rec).symm
    have hok : ∀ x ∈ (keyOf (fun β : Fac => β.val) rec).seeds,
        okE x.beta = true ∧ ∀ a ∈ x.z, okE a = true := by
      intro x hx
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
      refine ⟨mk_okE_writeE _, fun a ha => ?_⟩
      obtain ⟨t, rfl⟩ := (List.mem_ofFn' _ _).1 ha
      exact mk_okE_writeE _
    exact mk_seeds_eq_of_read _ _ hs hok h2
  have hitem : key.item = 0 := hK.item
  cases key
  simp only at hrec hseeds hitem
  subst hrec hseeds hitem
  rfl

/-- **The way back.** A key whose sizes fit the shape, none of whose factors is the program's 0, and
whose words are all below the prime is the key written of the record that is read off it, with the
key's own item. -/
theorem key_back (sh : OnBytes.Params.IndexShape) (key : TableKey) (hf : key.fits sh = true)
    (hz : (key.seeds.all fun x => !isZeroE x.beta) = true)
    (hr : ∀ a ∈ key.record, okE a = true)
    (hs : ∀ x ∈ key.seeds, okE x.beta = true ∧ ∀ a ∈ x.z, okE a = true) :
    key = { keyRec (recOfKey sh key) with item := key.item } := by
  have h0 : ({ key with item := 0 } : TableKey) = keyRec (recOfKey sh key) :=
    keyRec_of_keyIs (sh := sh) (key := { key with item := 0 })
      (keyIs_recOfKey sh { key with item := 0 } rfl hf hz fun x hx => (hs x hx).1) hr hs
  rw [← h0]

/-- The tests on a key's seeds: no factor is the program's 0, and the words of every point and
factor are below the prime. -/
def SeedsClean (key : TableKey) : Prop :=
  (key.seeds.all fun x => !isZeroE x.beta) = true ∧
    ∀ x ∈ key.seeds, okE x.beta = true ∧ ∀ a ∈ x.z, okE a = true

/-- The key written of a record passes the tests: its answers have words below the prime, and its
seeds are clean. -/
theorem clean_keyRec {v lg s : ℕ} (rec : RecF v lg s) :
    (∀ a ∈ (keyRec rec).record, okE a = true) ∧ SeedsClean (keyRec rec) := by
  refine ⟨fun a ha => ?_, List.all_eq_true.2 fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨n, rfl⟩ := Array.mem_ofFn.1 ha
    exact mk_okE_writeE _
  · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
    show (!isZeroE (writeE (rec.1 i).2.val)) = true
    cases h : isZeroE (writeE (rec.1 i).2.val) with
    | false => rfl
    | true => exact absurd ((readE_writeE _).symm.trans (readE_of_isZeroE _ h)) (rec.1 i).2.2
  · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
    refine ⟨mk_okE_writeE _, fun a ha => ?_⟩
    obtain ⟨t, rfl⟩ := (List.mem_ofFn' _ _).1 ha
    exact mk_okE_writeE _

/-- **The program's block at the records.** If `Tie.entrySpec` gives a block and a description at
two tables: each table has a key; if both tables' answers have words below the prime and both keys'
seeds pass the tests `SeedsClean`, the block is the link's block at the pair of the records that are
read off the keys. The description is `linkSpec p` with the link's statement on the two tables. -/
theorem link_value_rec {p : OnBytes.Params.Link} {first further : OnBytes.Params.TableName}
    {block : Blk Unit} {S : Fmt.SpecX} (h : entrySpec p first further = some (block, S)) :
    ∃ k0 k1, tableKey p.given.plan.field p.given.cfg p.link.table first 0 = some k0 ∧
      tableKey p.given.plan.field p.given.cfg p.link.table further 1 = some k1 ∧
      ((∀ a ∈ first.answers, okE a = true) → (∀ a ∈ further.answers, okE a = true) →
        SeedsClean k0 → SeedsClean k1 →
        block = linkBlock keyRec p (recOfKey p.link.table k0, recOfKey p.link.table k1)) ∧
      S = reStated (linkSpec p) (OnBytes.Params.Link.statement first further) := by
  obtain ⟨k0, k1, h0, h1, hb, hS⟩ := link_value h
  refine ⟨k0, k1, h0, h1, fun a0 a1 c0 c1 => ?_, hS⟩
  have f0 := OnBytes.Params.tableKey_fits h0
  have f1 := OnBytes.Params.tableKey_fits h1
  have r0 : ∀ a ∈ k0.record, okE a = true := by
    rw [OnBytes.Params.tableKey_record h0]
    exact fun a ha => a0 a (List.mem_toArray.1 ha)
  have r1 : ∀ a ∈ k1.record, okE a = true := by
    rw [OnBytes.Params.tableKey_record h1]
    exact fun a ha => a1 a (List.mem_toArray.1 ha)
  have e0 := key_back p.link.table k0 f0.1 c0.1 r0 c0.2
  have e1 := key_back p.link.table k1 f1.1 c1.1 r1 c1.2
  rw [f0.2] at e0
  rw [f1.2] at e1
  rw [hb]
  unfold linkBlock
  exact congrArg₂ (linkVerify p.link)
    ((item_laid f0.2).trans e0) ((item_laid f1.2).trans e1)

/-- Where the dry run at keys of zeros succeeds, the value at the records is `iorLink` at
`linkRounds p`. -/
theorem linkValueAt_of_ok (p : OnBytes.Params.Link) (h : linkOk p = true) :
    linkValueAt p =
      iorLink (ckP p.given.plan.field) (linkDepth p) keyRec p (linkRounds p) :=
  linkValue_of_ok _ _ keyRec p h

/-- The value at the records is local. -/
theorem linkValueAt_isLocal (p : OnBytes.Params.Link) : (linkValueAt p).IsLocal :=
  linkValue_isLocal _ _ keyRec p

end OnBytes.Maker

