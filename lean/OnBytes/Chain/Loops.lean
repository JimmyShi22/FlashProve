-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Chain/Loops.lean: readers of Fmt/ as loops.

Fmt/ states "n values one after the other" and "the items of a message" by recursion on the
result: the function calls itself and then puts one value in front. A compiled program then needs
stack in proportion to the number of values. Here the same readers collect the values in an array
and call themselves last, so they run in constant stack. Each is proved equal to the reader of
Fmt/.
The format page is docs/format/FORMAT.md. A number such as R7.14 is a rule of that page.

Main definitions: `rdManyT`, `rdListT`, `readItemsT`, `rdOpeningT`, `rdPlanT`, `paramsReadT`,
`readListT`, `rootsT`, `notRoot`.
Main theorems: each of the readers is the reader of Fmt/: `rdManyT_eq`, `rdListT_eq`,
`readItemsT_eq`, `rdOpeningT_eq`, `rdPlanT_eq`, `paramsReadT_eq`, `readListT_eq`, `rootsT_eq`; and
`noRoots_eq`.
-/
import Fmt.Rules8X
import OnBytes.Chain.Climb

namespace OnBytes

open Fmt (Rd Fld Item ItemValue Shape)

/-- Reads n values with r from byte i of b on and appends them to acc. -/
def manyLoop {α : Type} (r : Rd α) (b : ByteArray) : Nat → Nat → Array α → Option (List α × Nat)
  | 0, i, acc => some (acc.toList, i)
  | n + 1, i, acc =>
    match r b i with
    | some (x, j) => manyLoop r b n j (acc.push x)
    | none => none

/-- `manyLoop` returns the members of acc followed by what `Fmt.rdMany` returns. -/
theorem manyLoop_eq {α : Type} (r : Rd α) (b : ByteArray) : ∀ (n i : Nat) (acc : Array α),
    manyLoop r b n i acc = (Fmt.rdMany r n b i).map fun x => (acc.toList ++ x.1, x.2)
  | 0, i, acc => by simp [manyLoop, Fmt.rdMany]
  | n + 1, i, acc => by
    simp only [manyLoop, Fmt.rdMany]
    cases r b i with
    | none => rfl
    | some x =>
      obtain ⟨x, j⟩ := x
      simp only [manyLoop_eq r b n j (acc.push x)]
      cases Fmt.rdMany r n b j with
      | none => rfl
      | some y =>
        obtain ⟨l, k⟩ := y
        simp

/-- n values, one after the other: `Fmt.rdMany` as a loop. -/
def rdManyT {α : Type} (r : Rd α) (n : Nat) : Rd (List α) := fun b i => manyLoop r b n i #[]

/-- `rdManyT` equals `Fmt.rdMany`. -/
theorem rdManyT_eq {α : Type} (r : Rd α) (n : Nat) : rdManyT r n = Fmt.rdMany r n := by
  funext b i
  unfold rdManyT
  rw [manyLoop_eq]
  cases Fmt.rdMany r n b i with
  | none => rfl
  | some y => rfl

/-- Reads items of the kinds ts from byte i of b on and appends the values read to acc. -/
def itemsLoop (f : Fld) (b : ByteArray) : List Item → Nat → Array ItemValue → Option (List ItemValue × Nat)
  | [], i, acc => some (acc.toList, i)
  | t :: ts, i, acc =>
    match Fmt.readItem f t b i with
    | some (x, j) => itemsLoop f b ts j (acc.push x)
    | none => none

/-- `itemsLoop` returns the members of acc followed by what `Fmt.readItems` returns. -/
theorem itemsLoop_eq (f : Fld) (b : ByteArray) : ∀ (ts : List Item) (i : Nat) (acc : Array ItemValue),
    itemsLoop f b ts i acc = (Fmt.readItems f ts b i).map fun x => (acc.toList ++ x.1, x.2)
  | [], i, acc => by simp [itemsLoop, Fmt.readItems]
  | t :: ts, i, acc => by
    simp only [itemsLoop, Fmt.readItems]
    cases Fmt.readItem f t b i with
    | none => rfl
    | some x =>
      obtain ⟨x, j⟩ := x
      simp only [itemsLoop_eq f b ts j (acc.push x)]
      cases Fmt.readItems f ts b j with
      | none => rfl
      | some y =>
        obtain ⟨l, k⟩ := y
        simp

/-- The items of a message: `Fmt.readItems` as a loop. -/
def readItemsT (f : Fld) (ts : List Item) : Rd (List ItemValue) := fun b i => itemsLoop f b ts i #[]

/-- `readItemsT` equals `Fmt.readItems`. -/
theorem readItemsT_eq (f : Fld) (ts : List Item) : readItemsT f ts = Fmt.readItems f ts := by
  funext b i
  unfold readItemsT
  rw [itemsLoop_eq]
  cases Fmt.readItems f ts b i with
  | none => rfl
  | some y => rfl

/-- The bytes of an opening, cut into columns with their salts and the given digests:
`Fmt.rdOpening` with loops. -/
def rdOpeningT (f : Fld) (salt : Nat) (sh : Shape) (xs : List Nat) :
    Rd (List (List UInt64 × ByteArray) × List ByteArray) :=
  Fmt.rdPair (rdManyT (Fmt.rdPair (rdManyT (Fmt.rdElt f) sh.W) (Fmt.rdBytes salt)) xs.length)
    (rdManyT Fmt.rdDigest (walkPlacesT sh.a xs).length)

/-- `rdOpeningT` equals `Fmt.rdOpening`. -/
theorem rdOpeningT_eq (f : Fld) (salt : Nat) (sh : Shape) (xs : List Nat) :
    rdOpeningT f salt sh xs = Fmt.rdOpening f salt sh xs := by
  unfold rdOpeningT Fmt.rdOpening
  simp only [rdManyT_eq, walkPlacesT_eq]

/-- The plan in a chain's parameter bytes: eight words, then the entries. `Fmt.rdPlan`, with the
entries read by a loop. Refuses a field's number other than 1 or 2, a hash's number other than 1,
and a number of entries greater than the number of bytes left (format page, R1.9: each value of a
list has at least one byte). So the bytes bound the number of the loop's steps. -/
def rdPlanT : Rd Fmt.Plan := fun b i =>
  match Fmt.rdMany Fmt.rdWord 8 b i with
  | some ([f, hsh, salt, nonce, posB, samples, saved, n], j) =>
    match Fmt.fldOf f.toNat with
    | some fld =>
      if hsh == 1 && decide (j + n.toNat ≤ b.size) then
        (rdManyT Fmt.rdEntry n.toNat b j).map fun x =>
          (⟨fld, salt.toNat, nonce.toNat, posB.toNat, samples.toNat, saved.toNat, x.1⟩, x.2)
      else none
    | none => none
  | _ => none

/-- `rdPlanT` equals `Fmt.rdPlan`. -/
theorem rdPlanT_eq : rdPlanT = Fmt.rdPlan := by
  funext b i
  unfold rdPlanT Fmt.rdPlan
  simp only [rdManyT_eq]
  rfl

/-- What a chain's parameter bytes hold: the item of the format's version, the plan, the item of
the configuration's digest, then further items up to the last byte. `Fmt.paramsRead`, with the
plan's entries read by a loop; the further items are read by `Fmt.rdItems`, which is not a loop.
Refuses a first item that is not the version of the plan's field, an item after the plan that is
not the configuration's or whose value does not have 32 bytes, and bytes that are left over or
missing. -/
def paramsReadT (b : ByteArray) : Option Fmt.Params :=
  match Fmt.rdItem b 0 with
  | some ((vn, vv), i) =>
    match rdPlanT b i with
    | some (P, j) =>
      if vn == Fmt.versionName && vv == Fmt.versionValue P.field then
        match Fmt.rdItem b j with
        | some ((cn, cv), k) =>
          if cn == Fmt.configName && cv.size == 32 then
            (Fmt.rdItems b.size b k).map fun x => ⟨P, cv, x.1⟩
          else none
        | none => none
      else none
    | none => none
  | none => none

/-- `paramsReadT` equals `Fmt.paramsRead`. -/
theorem paramsReadT_eq (b : ByteArray) : paramsReadT b = Fmt.paramsRead b := by
  unfold paramsReadT Fmt.paramsRead
  rw [rdPlanT_eq]
  rfl

/-- A list with the word of its length in front: `Fmt.rdList` as a loop. Refuses a length greater
than the number of bytes left (format page, R1.9: each value of a list has at least one byte). So
the bytes bound the number of the loop's steps. -/
def rdListT {α : Type} (r : Rd α) : Rd (List α) := fun b i =>
  match Fmt.rdWord b i with
  | some (n, j) => if j + n.toNat ≤ b.size then rdManyT r n.toNat b j else none
  | none => none

/-- `rdListT` equals `Fmt.rdList`. -/
theorem rdListT_eq {α : Type} (r : Rd α) : rdListT r = Fmt.rdList r := by
  funext b i
  unfold rdListT Fmt.rdList
  simp only [rdManyT_eq]
  rfl

/-- The listed positions of a round, compared with the list l that was derived: `Fmt.readList` with
the positions read by a loop. No byte is read where the plan lists no positions or the round draws
none. -/
def readListT (P : Fmt.Plan) (poss : Nat) (l : List Nat) : Rd Unit := fun b i =>
  if P.posB == 0 || poss == 0 then some ((), i)
  else
    match rdManyT (Fmt.readLE P.posB) l.length b i with
    | some (l', j) => if l' == l then some ((), j) else none
    | none => none

/-- `readListT` equals `Fmt.readList`. -/
theorem readListT_eq (P : Fmt.Plan) (poss : Nat) (l : List Nat) :
    readListT P poss l = Fmt.readList P poss l := by
  funext b i
  unfold readListT Fmt.readList
  rw [rdManyT_eq]
  rfl

/-- The roots among the values read from a message, in their order: `Fmt.rootsOf` without deep
recursion. -/
def rootsT (l : List Fmt.ItemValue) : List ByteArray :=
  l.filterMap fun
    | .root d => some d
    | _ => none

/-- `rootsT` equals `Fmt.rootsOf`. -/
theorem rootsT_eq : ∀ l : List Fmt.ItemValue, rootsT l = Fmt.rootsOf l
  | [] => rfl
  | g :: l => by
    have ih := rootsT_eq l
    unfold rootsT at ih ⊢
    cases g <;> simp only [List.filterMap_cons, Fmt.rootsOf, ih]

/-- True for every value read from a message except a root. -/
def notRoot : ItemValue → Bool
  | .root _ => false
  | _ => true

/-- `Fmt.noRoots` keeps the values that are not roots: it is the filter by `notRoot`. -/
theorem noRoots_eq : ∀ (l : List ItemValue), Fmt.noRoots l = l.filter notRoot
  | [] => rfl
  | g :: l => by
    cases g <;> simp [Fmt.noRoots, notRoot, noRoots_eq l]

end OnBytes
