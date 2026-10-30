-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/IdTableSpell.lean: how the answers of a typed record are spelled as the list of
elements that a key file holds, so that the list which a table holds comes back from the record that
is read off the table.

Definitions, statements and proofs. No hash stands in this file.

A stored table's record has, for each of 2 ^ v rows, s answers. A file holds them as a list of
elements of the program, three words each; a typed record holds them as a function into the field
(`recAns`, OnBytes/Slice/RecordRead.lean: entry r * s + i is the answer of row r under seed i).
The commitment ID hashes the list's bytes. So a code of typed keys under which the hash is the ID
must spell the function as that very list.

Main names:
  `spellAns v s a`: the list of 2 ^ v * s elements, entry n the element with words below the prime
    that is read as the answer of row n / s under seed n % s (`writeE`,
    OnBytes/Slice/KeyOfRec.lean).
  `spellAns_inj`: it is one to one.
  `spell_recAns`: if `recAns v s k = some a` and every answer in k has its three words below the
    prime (`okE`), then `spellAns v s a` is the list of k's answers.
  `written_okE`, `written_back`: what `writeE` writes has its words below the prime; an element with
    words below the prime is written back as it was.
  `spell_list`, `spell_triples`: the same for a bare list of 2 ^ v * s elements: read by `readE`;
    read by `toE` off the list of the elements' triples of words, 0 beyond the end.
  `spellAns_okE`: every element of the spelling has its words below the prime.
  `readE_clash`: `readE` is not one to one: two different elements of the program are read as one
    element of the field (`toF`, OnBytes/Slice/Field.lean, reduces a word from the prime on). With
    `spellAns_okE`: a list that holds an element with a word not below the prime is no spelling.
`spellAns` is a plain definition over `writeE`; nothing in it is taken by choice.

Limits: nothing on which tables a program accepts. Nothing on seeds. Nothing on soundness. For
proofs only; no program imports this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.RecordRead
import OnBytes.Slice.KeyOfRec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.K.IdTable
open OnBytes.Slice OnBytes.Tie Cb

variable (v s : ℕ)

/-- The answers of a typed record, as the list that a file holds. -/
def spellAns (a : (Fin v → Bool) × Fin s → GE) : List E :=
  List.ofFn fun n : Fin (2 ^ v * s) =>
    writeE (a (vtx v (n.val / s), ⟨n.val % s, Nat.mod_lt _ (pos_of_place n)⟩))

theorem spellAns_length (a : (Fin v → Bool) × Fin s → GE) : (spellAns v s a).length = 2 ^ v * s :=
  List.length_ofFn

/-- The place of the answer of row r under seed i lies within the list. -/
theorem place_lt (r : Fin v → Bool) (i : Fin s) : Sz.rowNo r * s + i.val < 2 ^ v * s := by
  have h1 : (Sz.rowNo r + 1) * s ≤ 2 ^ v * s := Nat.mul_le_mul_right s (rowNo_lt r)
  have h2 : Sz.rowNo r * s + i.val < (Sz.rowNo r + 1) * s := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_lt_add_left i.isLt _
  exact Nat.lt_of_lt_of_le h2 h1

/-- The list, read back. -/
theorem spellAns_read (a : (Fin v → Bool) × Fin s → GE) (r : Fin v → Bool) (i : Fin s) :
    readE ((spellAns v s a).getD (Sz.rowNo r * s + i.val) zeroE) = a (r, i) := by
  have hs : 0 < s := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hlt := place_lt v s r i
  have hd : (Sz.rowNo r * s + i.val) / s = Sz.rowNo r := by
    rw [Nat.mul_comm, Nat.mul_add_div hs, Nat.div_eq_of_lt i.isLt, Nat.add_zero]
  have hm : (Sz.rowNo r * s + i.val) % s = i.val := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt i.isLt]
  have e : (spellAns v s a).getD (Sz.rowNo r * s + i.val) zeroE =
      writeE (a (vtx v ((Sz.rowNo r * s + i.val) / s),
        ⟨(Sz.rowNo r * s + i.val) % s, Nat.mod_lt _ hs⟩)) := by
    rw [List.getD_eq_getElem _ _ (by rw [spellAns_length]; exact hlt)]
    unfold spellAns
    rw [List.getElem_ofFn]
  have hp : ((vtx v ((Sz.rowNo r * s + i.val) / s),
      ⟨(Sz.rowNo r * s + i.val) % s, Nat.mod_lt _ hs⟩) : (Fin v → Bool) × Fin s) = (r, i) :=
    Prod.ext (show vtx v ((Sz.rowNo r * s + i.val) / s) = r by
      rw [hd]
      exact funext fun t => testBit_rowNo r t) (Fin.ext hm)
  rw [e, readE_writeE, hp]

/-- **The spelling is one to one.** -/
theorem spellAns_inj : Function.Injective (spellAns v s) := fun a a' h =>
  funext fun x => by
    obtain ⟨r, i⟩ := x
    rw [← spellAns_read v s a r i, ← spellAns_read v s a' r i, h]

/-- What is written has its three words below the prime. -/
theorem written_okE (x : GE) : okE (writeE x) = true := by
  unfold writeE
  rw [okE_triple, E.triple_ofTriple]
  unfold Fmt.Fld.okE ofE
  rw [ok_ofF, ok_ofF, ok_ofF]
  rfl

/-- An element with words below the prime is written back as it was. -/
theorem written_back (x : E) (h : okE x = true) : writeE (readE x) = x :=
  readE_inj _ _ (written_okE _) h (readE_writeE _)

/-- Every element of the spelling has its words below the prime. -/
theorem spellAns_okE (a : (Fin v → Bool) × Fin s → GE) : ∀ x ∈ spellAns v s a, okE x = true := by
  intro x hx
  unfold spellAns at hx
  obtain ⟨n, rfl⟩ := (List.mem_ofFn' _ _).1 hx
  exact written_okE _

/-- The prime, as a word, is read as 0. -/
theorem toF_prime : toF (UInt64.ofNat Fmt.Fld.two.p) = 0 := by
  unfold toF
  rw [UInt64.toNat_ofNat_of_lt' Fmt.Fld.two.p_lt, two_p]
  exact ZMod.natCast_self Code.pGold

/-- Two different elements of the program are read as one element of the field. -/
theorem readE_clash : ∃ x y : E, x ≠ y ∧ readE x = readE y := by
  refine ⟨E.ofTriple (0, 0, 0), E.ofTriple (UInt64.ofNat Fmt.Fld.two.p, 0, 0), fun h => ?_, ?_⟩
  · have h1 : (0 : UInt64) = UInt64.ofNat Fmt.Fld.two.p := congrArg E.c0 h
    have h2 : (0 : UInt64).toNat = Fmt.Fld.two.p := by
      rw [h1, UInt64.toNat_ofNat_of_lt' Fmt.Fld.two.p_lt]
    exact absurd h2.symm (Nat.ne_of_gt Fmt.Fld.two.p_pos)
  · have z : toF 0 = 0 := by
      unfold toF
      simp
    rw [readE_ofTriple, readE_ofTriple]
    unfold toE
    rw [toF_prime, z]

/-- **The list that a table holds comes back from the answers that are read off it**, if every
answer's words are below the prime. -/
theorem spell_recAns (k : IdKey) (a : (Fin v → Bool) × Fin s → GE) (h : recAns v s k = some a)
    (hk : ∀ x ∈ k.2.2.answers, okE x = true) : spellAns v s a = k.2.2.answers := by
  unfold recAns at h
  by_cases hl : k.2.2.answers.length = 2 ^ v * s
  · rw [if_pos hl] at h
    obtain rfl := Option.some.inj h
    refine List.ext_getElem (by rw [spellAns_length, hl]) fun n h1 h2 => ?_
    have hn : n < 2 ^ v * s := by rwa [spellAns_length] at h1
    have hs : 0 < s := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hn
    have hq : n / s < 2 ^ v := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hn)
    have hr : Sz.rowNo (vtx v (n / s)) = n / s := by
      show Sz.rowNo (fun t : Fin v => (n / s).testBit t.val) = _
      rw [rowNo_testBit, Nat.mod_eq_of_lt hq]
    unfold spellAns
    rw [List.getElem_ofFn]
    show writeE (readE (k.2.2.answers.getD (Sz.rowNo (vtx v (n / s)) * s + n % s) zeroE)) = _
    rw [hr, Nat.div_add_mod' n s, List.getD_eq_getElem _ _ h2]
    exact written_back _ (hk _ (List.getElem_mem h2))
  · rw [if_neg hl] at h
    cases h

/-- The same for a bare list. -/
theorem spell_list (l : List E) (hl : l.length = 2 ^ v * s) (hk : ∀ x ∈ l, okE x = true) :
    spellAns v s (fun x => readE (l.getD (Sz.rowNo x.1 * s + x.2.val) zeroE)) = l :=
  spell_recAns v s (default, ByteArray.empty, ⟨ByteArray.empty, l⟩) _
    (by unfold recAns; exact if_pos hl) hk

/-- The same, the list read off its elements' triples of words. -/
theorem spell_triples (l : List E) (hl : l.length = 2 ^ v * s) (hk : ∀ x ∈ l, okE x = true) :
    spellAns v s (fun x => toE ((l.map E.triple).getD (Sz.rowNo x.1 * s + x.2.val) (0, 0, 0))) =
      l := by
  have e : (fun x : (Fin v → Bool) × Fin s =>
      toE ((l.map E.triple).getD (Sz.rowNo x.1 * s + x.2.val) (0, 0, 0))) =
      fun x => readE (l.getD (Sz.rowNo x.1 * s + x.2.val) zeroE) := by
    funext x
    rw [readE_def, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases l[Sz.rowNo x.1 * s + x.2.val]? with
    | none => rfl
    | some e => rfl
  rw [e]
  exact spell_list v s l hl hk

end OnBytes.K.IdTable
