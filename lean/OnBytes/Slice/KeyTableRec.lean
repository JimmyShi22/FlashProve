-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/KeyTableRec.lean: the key that the program makes of a table's root and answers
(`Params.TableName`) holds the record that is read off it; a key holds at most one record; and the
number of answers of a record that a key holds is the format's.

OnBytes/Slice/BlkRecRow.lean says when a key of the program holds a record over the field
(`KeyHasR`), and that a key holds what is read off it if its sizes fit the shape, no seed's factor
is the program's 0 and each factor's words are below the prime (`keyHasR_recOfKey`). The reader of
an entry file makes its two keys by `tableKey` (OnBytes/Entry/Table.lean): the seeds are those of
`recordSeeds`, and a key is returned only if its sizes fit. OnBytes/Slice/SeedWords.lean shows that
every seed that `recordSeeds` gives is in order. This file joins them.

Main theorems.
 `tableKey_seeds_of`, `tableKey_seeds`   every seed of a key that `tableKey` returns is in order
                     (`SeedOK`); the first: for the text of `tableKey` with any seeds in order in
                     the place of those of `recordSeeds`.
 `tableKey_okE`, `tableKey_nz`   so each factor has words below the prime, and none is the
                     program's 0.
 `keyHasR_tableKey`  such a key holds the record that is read off it. Stated for callers at a
                     shape's own three numbers; OnBytes/Slice/SmallRecTable.lean and
                     FullRecTable.lean, which have the numbers as numerals, go by
                     `keyHasR_recAtR` and the two laws above.
 `KeyHasR.unique`    a key holds at most one record.
 `link_cut_eq`, `link_answers_eq`   where a key of the link's first table holds a record of n
                     answers: the entries that the link compares are those before the 3 n pad
                     entries; and n is the format's number of answers, if both numbers of pads fit a
                     row's message. No instance is stated: at the two settings both facts hold by
                     evaluation (`sr_cut`, `sr_lg`, `fr_cut`, `fr_lg`).

Not claimed. That `tableKey` returns a key. Nothing on the answers in a key, which are those of the
`Params.TableName`: they are read in the field as they stand. That the answers' words are below the
prime: `tableKey` does not test it; the way back
(OnBytes/Slice/KeyOfRecBack.lean) asks it. That a seed is near uniform, or what a record is
good for. Nothing on any hash function: `recordSeeds` is evaluated nowhere. Nothing on soundness.

-/
import OnBytes.Params.EntryRoundsRecord
import OnBytes.Slice.BlkLinkJoin
import OnBytes.Slice.BlkRecRow
import OnBytes.Slice.SeedWords

set_option autoImplicit false

namespace OnBytes.Slice
open Params (IndexShape TableName LinkShape)

section
variable {cfg : ByteArray} {s : IndexShape} {t : TableName} {item : ℕ} {k : TableKey}

/-- The text of `tableKey` behind its seeds, with the seeds as a letter o: if the seeds are in
order, so is every seed of the key that is returned. -/
theorem tableKey_seeds_of (o : Option (List (List E × E)))
    (ho : ∀ l, o = some l → ∀ y ∈ l, SeedOK y)
    (hb : (o.bind fun y =>
      if ({ item := item, record := t.answers.toArray,
            seeds := y.map fun x => ⟨x.1, x.2⟩ } : TableKey).fits s then
        some ({ item := item, record := t.answers.toArray,
                seeds := y.map fun x => ⟨x.1, x.2⟩ } : TableKey)
      else none) = some k) : ∀ x ∈ k.seeds, SeedOK (x.z, x.beta) := by
  obtain ⟨y, hy0, hy⟩ := Option.bind_eq_some_iff.mp hb
  split at hy
  · cases hy
    intro x hx
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
    exact ho y hy0 w hw
  · cases hy

/-- Every seed of a key that `tableKey` returns is in order. -/
theorem tableKey_seeds (h : tableKey .two cfg s t item = some k) :
    ∀ x ∈ k.seeds, SeedOK (x.z, x.beta) := by
  unfold tableKey at h
  dsimp only at h
  exact tableKey_seeds_of _ (fun l hl => seedOK_recordSeeds _ _ _ l hl) h

/-- Each factor of such a key has words below the prime. -/
theorem tableKey_okE (h : tableKey .two cfg s t item = some k) :
    ∀ x ∈ k.seeds, okE x.beta = true := fun x hx => (tableKey_seeds h x hx).2.1

/-- No factor of such a key is the program's 0. -/
theorem tableKey_nz (h : tableKey .two cfg s t item = some k) :
    (k.seeds.all fun x => !isZeroE x.beta) = true :=
  List.all_eq_true.2 fun x hx => by
    rw [(tableKey_seeds h x hx).2.2.1]
    rfl

/-- **The key that the program makes of a table's root and answers holds the record that is read
off it.** -/
theorem keyHasR_tableKey (h : tableKey .two cfg s t item = some k) :
    KeyHasR s.v s.cubeBits s.answers s k (recOfKey s k) :=
  keyHasR_recOfKey s k (Params.tableKey_fits h).1 (tableKey_nz h) (tableKey_okE h)

end

/-- **A key holds at most one record.** -/
theorem KeyHasR.unique {v lg n : ℕ} {sh : IndexShape} {key : TableKey} {r r' : RecP NZ v lg n}
    (h : KeyHasR v lg n sh key r) (h' : KeyHasR v lg n sh key r') : r = r' := by
  have hf := List.ofFn_injective (h.seeds.symm.trans h'.seeds)
  refine Prod.ext (funext fun i => ?_) (funext fun q => ?_)
  · have hi := congrFun hf i
    exact Prod.ext (List.ofFn_injective (congrArg Prod.fst hi))
      (Subtype.ext (congrArg Prod.snd hi))
  · exact (h.record q.1 q.2).symm.trans (h'.record q.1 q.2)

section
variable {S : Sz} {lg n : ℕ} {Λ : LinkShape} {codes : Codes} (hS : LinkSizes S Λ codes)
  (hF : LinkFit S Λ (Λ.side false 1) (Λ.side true 1)) {k0 : TableKey} {rec : RecP NZ S.P.v lg n}
  (hk0 : KeyHasR S.P.v lg n (Λ.side false 1).index k0 rec)
include hS hF hk0

/-- The entries that the link compares are those before the pads of the n answers. -/
theorem link_cut_eq : S.P.cut = S.P.T.l - 3 * n := by
  have h1 : Λ.cut = Λ.table.code.ell - 3 * Λ.table.answers := rfl
  have h2 : Λ.table.answers = n := hk0.answers
  have h3 : Λ.table.code.ell = S.P.T.l := congrArg (·.l) hF.code0
  rw [← hS.cut, h1, h2, h3]

/-- The number of answers is the format's, if both numbers of pads fit a row's message. -/
theorem link_answers_eq (h3 : 3 * n ≤ S.P.T.l) (h3' : 3 * S.P.s ≤ S.P.T.l) : S.P.s = n := by
  have h := link_cut_eq hS hF hk0
  unfold Fmt.M3.Par.cut at h
  omega

end

end OnBytes.Slice

#print axioms OnBytes.Slice.tableKey_seeds_of
#print axioms OnBytes.Slice.tableKey_seeds
#print axioms OnBytes.Slice.tableKey_okE
#print axioms OnBytes.Slice.tableKey_nz
#print axioms OnBytes.Slice.keyHasR_tableKey
#print axioms OnBytes.Slice.KeyHasR.unique
#print axioms OnBytes.Slice.link_cut_eq
#print axioms OnBytes.Slice.link_answers_eq
