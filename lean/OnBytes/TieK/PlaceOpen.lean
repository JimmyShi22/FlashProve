-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TieK/PlaceOpen.lean: the two things that the program hashes outside a chain when it reads a
key file or a proof file, each opened into named values.

`Proof.readPlace` (OnBytes/Proof/Place.lean) reads, behind a first chain, a word, a salt and one
sibling for each level of the binding tree, hashes the leaf and climbs to the root. What it returns
keeps the word, the root and the place behind the path. It keeps neither the salt nor the siblings.
`readPlace_open` names both, and says the root as a function of them (`rootOf`).
`tableKey` (OnBytes/Entry/Table.lean) makes, from a table's root and answers, the seeds of the
table's record. `tableKey_open` names the seeds.

Main definitions: `pathAt`, `rootOf`.
Main theorems: `climb_open`, `readPlace_open`, `tableKey_open`.
It claims nothing on soundness. The program does not import this file.

-/
import OnBytes.Proof.Place
import OnBytes.Entry.Table
import OnBytes.Params.ConfigureLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.TieK
open OnBytes.Proof

/-- The siblings of a path: n strings of 32 bytes from the byte i of b on. -/
def pathAt (b : ByteArray) : Nat → Nat → Option (List ByteArray)
  | 0, _ => some []
  | n + 1, i =>
    match Fmt.slice b i 32 with
    | none => none
    | some sib => (pathAt b n (i + 32)).map (sib :: ·)

/-- The root to which the vertex x at the place p of its level leads along the siblings. At each
level the lowest bit of p says on which side the sibling is: at 1 it is the left child. -/
def rootOf (cfg : ByteArray) : ByteArray → Nat → List ByteArray → ByteArray
  | x, _, [] => x
  | x, p, sib :: l =>
    rootOf cfg (if p % 2 == 1 then Fmt.vertexB cfg sib x else Fmt.vertexB cfg x sib) (p / 2) l

/-- What `climb` has done if it returns. -/
theorem climb_open (cfg b : ByteArray) :
    ∀ (levels : Nat) (x : ByteArray) (p i : Nat) (y : ByteArray × Nat),
      climb cfg b levels x p i = some y →
      ∃ path, pathAt b levels i = some path ∧ path.length = levels ∧
        y = (rootOf cfg x p path, i + 32 * levels) := by
  intro levels
  induction levels with
  | zero =>
    intro x p i y h
    unfold climb at h
    injection h with h'
    exact ⟨[], rfl, rfl, h'.symm⟩
  | succ n ih =>
    intro x p i y h
    unfold climb at h
    split at h
    · cases h
    · rename_i sib hs
      obtain ⟨path, h1, h2, h3⟩ := ih _ _ _ _ h
      refine ⟨sib :: path, ?_, ?_, ?_⟩
      · unfold pathAt
        rw [hs, h1]
        rfl
      · simp [h2]
      · rw [h3]
        have e : i + 32 + 32 * n = i + 32 * (n + 1) := by omega
        rw [e]
        rfl

/-- **What `readPlace` has done if it returns.** w: the word; salt: the leaf's salt; path: the
siblings, the leaf's first. -/
theorem readPlace_open (s : Params.LinBindingShape) (cfg closing b : ByteArray) (i : Nat)
    (pl : Place) (h : readPlace s cfg closing b i = some pl) :
    bindingOk s = true ∧
    ∃ w i1 salt path,
      Fmt.rdWord b i = some (w, i1) ∧ w.toNat < 2 ^ s.logLeaves ∧
      Fmt.slice b i1 s.saltBytes = some salt ∧
      pathAt b s.logLeaves (i1 + s.saltBytes) = some path ∧ path.length = s.logLeaves ∧
      pl = ⟨w.toNat,
        rootOf cfg (Fmt.bindLeaf s.logLeaves w.toNat cfg closing salt) w.toNat path,
        2 ^ s.logLeaves, i1 + s.saltBytes + 32 * s.logLeaves⟩ := by
  unfold readPlace at h
  split at h
  · cases h
  · rename_i hok
    split at h
    · cases h
    · rename_i w i1 hw
      split at h
      · cases h
      · rename_i hlt
        split at h
        · cases h
        · rename_i salt hsalt
          cases hc : climb cfg b s.logLeaves
              (Fmt.bindLeaf s.logLeaves w.toNat cfg closing salt) w.toNat (i1 + s.saltBytes) with
          | none => rw [hc] at h; cases h
          | some y =>
            rw [hc] at h
            injection h with h'
            obtain ⟨path, h1, h2, h3⟩ := climb_open _ _ _ _ _ _ _ hc
            subst h3
            exact ⟨by simpa using hok, w, i1, salt, path, hw, by omega, hsalt, h1, h2, h'.symm⟩

/-- **What `tableKey` has done if it returns.** seeds: the seeds of the table's record. -/
theorem tableKey_open (f : Fmt.Fld) (cfg : ByteArray) (s : Params.IndexShape)
    (table : Params.TableName) (item : Nat) (key : TableKey)
    (h : tableKey f cfg s table item = some key) :
    ∃ seeds,
      recordSeeds f
        (Fmt.tableName table.root cfg s.code.logN s.code.ell s.code.r s.v s.answers
          s.saltBytes)
        s.cubeBits s.answers = some seeds ∧
      key = { item := item, record := table.answers.toArray,
              seeds := seeds.map fun x => ⟨x.1, x.2⟩ } ∧
      key.fits s = true := by
  unfold tableKey at h
  dsimp only at h
  obtain ⟨seeds, h1, h2⟩ := Params.opt_bind h
  split at h2
  · rename_i hfit
    injection h2 with h2'
    subst h2'
    exact ⟨seeds, h1, rfl, hfit⟩
  · cases h2

end OnBytes.TieK
