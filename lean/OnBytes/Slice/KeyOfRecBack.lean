-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/KeyOfRecBack.lean: a key of a stored table whose words are all below the prime IS the
key that is written of the record that it holds.

OnBytes/Slice/KeyOfRec.lean writes a record over the field as the program's key of a table (keyOf)
and says when a key holds a record (KeyIs; OnBytes/Slice/BlkRecRow.lean: KeyHasR, the same whatever
the item's number). "Holds" speaks of the key's elements as they are read in the field, and two
elements of the program with different words can be read alike, so a record does not determine the
key that holds it. Among the keys with words below the prime it does: this file shows that such a
key is keyOf of the record, but for the item's number.

Main theorems.
 okE_writeE          what is written has words below the prime.
 writeE_readE        an element with words below the prime is written back as it was.
 keyOf_nz            no factor of a written key is the program's 0.
 list_eq_of_read, seeds_eq_of_read   lists with such words that are read alike are one list.
 keyOf_of_keyHasR    THE WAY BACK: a key that holds rec, with words below the prime in its answers
                     and in every seed's point and factor, is keyOf of rec with the key's own item.
 keyOf_recOfKey      the same at the record that is read off the key (recOfKey,
                     OnBytes/Slice/BlkKeyRec.lean): from the key's sizes, its factors' test, and the
                     words.

Not claimed. That a key which a program makes has words below the prime. Nothing on where the seeds
come from, on any sample map, on a decoder or on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.BlkRecRow

set_option autoImplicit false

namespace OnBytes.Slice
open Cb

/-- What is written has words below the prime. -/
theorem okE_writeE (x : GE) : okE (writeE x) = true := by
  unfold writeE
  rw [okE_triple, E.triple_ofTriple]
  simp only [Fmt.Fld.okE, ofE, ok_ofF, Bool.and_self]

/-- An element with words below the prime is written back as it was. -/
theorem writeE_readE (a : E) (ha : okE a = true) : writeE (readE a) = a :=
  readE_inj _ _ (okE_writeE _) ha (readE_writeE _)

/-- No factor of a written key is the program's 0: the written key passes the test on factors of the
block that folds a stored table's rows (foldeqRequire, OnBytes/Iop/Foldeq.lean). -/
theorem keyOf_nz {v lg s : ℕ} (rec : RecP NZ v lg s) :
    ((keyOf (fun β : NZ => β.val) rec).seeds.all fun x => !isZeroE x.beta) = true :=
  List.all_eq_true.2 fun x hx => by
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
    show (!isZeroE (writeE (rec.1 i).2.val)) = true
    cases h : isZeroE (writeE (rec.1 i).2.val) with
    | false => rfl
    | true => exact absurd ((readE_writeE _).symm.trans (readE_of_isZeroE _ h)) (rec.1 i).2.2

/-- Two lists of elements with words below the prime that are read alike are one list. -/
theorem list_eq_of_read : ∀ (l l' : List E), (∀ a ∈ l, okE a = true) → (∀ a ∈ l', okE a = true) →
    l.map readE = l'.map readE → l = l'
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by cases h
  | _ :: _, [], _, _, h => by cases h
  | a :: l, b :: l', h1, h2, h => by
    rw [List.map_cons, List.map_cons] at h
    obtain ⟨e1, e2⟩ := List.cons.inj h
    rw [readE_inj a b (h1 a List.mem_cons_self) (h2 b List.mem_cons_self) e1,
      list_eq_of_read l l' (fun x hx => h1 x (List.mem_cons_of_mem _ hx))
        (fun x hx => h2 x (List.mem_cons_of_mem _ hx)) e2]

/-- Two lists of seeds with words below the prime that are read alike are one list. -/
theorem seeds_eq_of_read : ∀ (l l' : List SampleSeed),
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
    rw [list_eq_of_read z z' a1.2 a2.2 ez, readE_inj b b' a1.1 a2.1 eb,
      seeds_eq_of_read l l' (fun x hx => h1 x (List.mem_cons_of_mem _ hx))
        (fun x hx => h2 x (List.mem_cons_of_mem _ hx)) e2]

/-- THE WAY BACK. A key that holds the record rec and has words below the prime in its answers
and in every seed's point and factor is the key that is written of rec, with its own item. -/
theorem keyOf_of_keyHasR {v lg s : ℕ} {sh : Params.IndexShape} {key : TableKey}
    {rec : RecP NZ v lg s} (hK : KeyHasR v lg s sh key rec)
    (hr : ∀ a ∈ key.record, okE a = true)
    (hs : ∀ x ∈ key.seeds, okE x.beta = true ∧ ∀ a ∈ x.z, okE a = true) :
    key = { keyOf (fun β : NZ => β.val) rec with item := key.item } := by
  have hfit : key.fits sh = true := hK.fits
  unfold TableKey.fits Params.IndexShape.rows at hfit
  simp only [Bool.and_eq_true, beq_iff_eq] at hfit
  have hsize : key.record.size = 2 ^ v * s := by
    rw [hfit.1.1, hK.vars, hK.answers]
  -- the answers
  have hrec : key.record = (keyOf (fun β : NZ => β.val) rec).record := by
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
    have e : (keyOf (fun β : NZ => β.val) rec).record[n] =
        writeE (rec.2 (vtx v (n / s), ⟨n % s, Nat.mod_lt _ hs0⟩)) := by
      unfold keyOf
      simp
    rw [e, ← hk', writeE_readE _ (hr _ (Array.getElem_mem h1))]
  -- the seeds
  have hseeds : key.seeds = (keyOf (fun β : NZ => β.val) rec).seeds := by
    have h0 : (key.seeds.map fun x => (x.z.map readE, readE x.beta)) =
        List.ofFn fun i : Fin s => (List.ofFn (rec.1 i).1, (rec.1 i).2.val) := hK.seeds
    have h1 := keyOf_seeds (fun β : NZ => β.val) rec
    have h2 : (key.seeds.map fun x => (x.z.map readE, readE x.beta)) =
        (keyOf (fun β : NZ => β.val) rec).seeds.map fun x => (x.z.map readE, readE x.beta) :=
      h0.trans h1.symm
    have hok : ∀ x ∈ (keyOf (fun β : NZ => β.val) rec).seeds,
        okE x.beta = true ∧ ∀ a ∈ x.z, okE a = true := by
      intro x hx
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
      refine ⟨okE_writeE _, fun a ha => ?_⟩
      obtain ⟨t, rfl⟩ := (List.mem_ofFn' _ _).1 ha
      exact okE_writeE _
    exact seeds_eq_of_read _ _ hs hok h2
  cases key
  simp only at hrec hseeds
  subst hrec hseeds
  rfl

/-- The same at the record that is read off the key. -/
theorem keyOf_recOfKey (sh : Params.IndexShape) (key : TableKey) (hf : key.fits sh = true)
    (hz : (key.seeds.all fun x => !isZeroE x.beta) = true)
    (hr : ∀ a ∈ key.record, okE a = true)
    (hs : ∀ x ∈ key.seeds, okE x.beta = true ∧ ∀ a ∈ x.z, okE a = true) :
    key = { keyOf (fun β : NZ => β.val) (recOfKey sh key) with item := key.item } :=
  keyOf_of_keyHasR (keyHasR_recOfKey sh key hf hz fun x hx => (hs x hx).1) hr hs

end OnBytes.Slice
