-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkKeyRec.lean: a key of a stored table that the program's block takes holds a record
over the field.

OnBytes/Slice/KeyOfRec.lean says when the program's key of a table holds a record over the field
(KeyIs), and writes for each record a key that holds it. This file goes the other way: it reads a
record off a key (recOfKey), and shows that the key holds it (keyIs_recOfKey) if the table's root is
the statement's item 0, the key's sizes fit the shape, no seed's factor is the program's 0, and the
factors are elements of the program with words below the prime. The second and third are what the
block of a shared chain finds before anything is read (that it finds them is not shown in this
library).
The last is asked because the program's test for 0 compares words: an element with a word that is
not below the prime can be read as 0 in the field and pass that test.

Main definitions: `asFactor`, `recOfKey`.
Main theorems: `asFactor_val`, `keyIs_recOfKey`.

Not claimed. That a key which a reader makes has factors with words below the prime, or the item 0.
Nothing on where the seeds come from.

-/
import OnBytes.Slice.KeyOfRec

set_option autoImplicit false

namespace OnBytes.Slice
open Cb

/-- An element of the field as a factor other than 0; 1 for 0. -/
noncomputable def asFactor (x : GE) : {β : GE // β ≠ 0} :=
  if h : x ≠ 0 then ⟨x, h⟩ else ⟨1, one_ne_zero⟩

/-- It is the element, if that is not 0. -/
theorem asFactor_val {x : GE} (h : x ≠ 0) : (asFactor x).val = x := by
  unfold asFactor
  rw [dif_pos h]

/-- **The record that stands in a key**, at a table of the shape sh: the seeds and the answers, read
in the field. -/
noncomputable def recOfKey (sh : Params.IndexShape) (key : TableKey) :
    RecP {β : GE // β ≠ 0} sh.v sh.cubeBits sh.answers :=
  (fun i => (fun t => readE ((key.seeds.getD i.val default).z.getD t.val zeroE),
      asFactor (readE (key.seeds.getD i.val default).beta)),
    fun q => readE (key.record.getD (Sz.rowNo q.1 * sh.answers + q.2.val) zeroE))

/-- **The key holds it.** -/
theorem keyIs_recOfKey (sh : Params.IndexShape) (key : TableKey) (h0 : key.item = 0)
    (hf : key.fits sh = true) (hz : (key.seeds.all fun x => !isZeroE x.beta) = true)
    (hok : ∀ x ∈ key.seeds, okE x.beta = true) :
    KeyIs (fun β : {β : GE // β ≠ 0} => β.val) sh key (recOfKey sh key) := by
  have h1 := hf
  unfold TableKey.fits at h1
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h1
  obtain ⟨⟨_, hlen⟩, hzl⟩ := h1
  refine ⟨h0, rfl, rfl, rfl, hf, ?_, fun _ _ => rfl⟩
  refine List.ext_getElem (by rw [List.length_map, List.length_ofFn, hlen]) fun i hi _ => ?_
  have hi' : i < key.seeds.length := by rwa [List.length_map] at hi
  have hmem : key.seeds[i] ∈ key.seeds := List.getElem_mem hi'
  have hg : key.seeds.getD i default = key.seeds[i] := List.getD_eq_getElem _ _ hi'
  rw [List.getElem_map, List.getElem_ofFn]
  show _ = (List.ofFn fun t : Fin sh.cubeBits =>
      readE ((key.seeds.getD i default).z.getD t.val zeroE),
    (asFactor (readE (key.seeds.getD i default).beta)).val)
  rw [hg]
  refine Prod.ext ?_ ?_
  · show key.seeds[i].z.map readE = _
    have hl := hzl _ hmem
    refine List.ext_getElem (by rw [List.length_map, List.length_ofFn, hl]) fun t ht _ => ?_
    have ht' : t < key.seeds[i].z.length := by rwa [List.length_map] at ht
    rw [List.getElem_map, List.getElem_ofFn, List.getD_eq_getElem _ _ ht']
  · show readE key.seeds[i].beta = _
    have hne : readE key.seeds[i].beta ≠ 0 := by
      intro hc
      have h2 := (isZeroE_iff _ (hok _ hmem)).2 hc
      have h3 := (List.all_eq_true.1 hz) _ hmem
      rw [h2] at h3
      cases h3
    rw [asFactor_val hne]

end OnBytes.Slice
