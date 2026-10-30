-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Chain/Index.lean: the record of vertices with a map beside each root's list.

`Fmt.addSeen` compares each vertex of a new opening with each vertex met before under the same
root. Here each root's list has a map beside it. The map gives, for a depth and a place, the
values met there, in the order in which they were met. A new vertex is then compared only with the
values at its own depth and place. A value is entered each time it is met. So in an honest file
the values at one depth and place are copies of one value, one for each opening that met the
vertex. (TreeValues in blocks/tree/tree.h, the C++ counterpart, keeps one value for each vertex.)
The map is a hash map with Lean's own hash. Its keys are no bytes of a file: the verifier derives
depth and place from its own draws. Not claimed: how evenly that hash spreads such keys.

Main definitions: `Idx`, `Idx.put`, `valuesAt`, `Fits`, `agreeIdx`, `Rooted`, `addRooted`,
`Keeper.indexed`.
Main theorems: `fits_putAll`, `agreeIdx_eq`, `addRooted_eq`.
-/
import OnBytes.Chain.Keeper
import Std.Data.HashMap

namespace OnBytes

/-- For a depth and a place: the values met there. -/
abbrev Idx : Type := Std.HashMap (Nat × Nat) (List ByteArray)

/-- Enters one vertex: its value is appended to the values met at its depth and place, also if it
is among them already. -/
def Idx.put (m : Idx) (v : Met) : Idx :=
  m.insert (v.1, v.2.1) (m.getD (v.1, v.2.1) [] ++ [v.2.2])

/-- Enters vertices one after the other. -/
def Idx.putAll (m : Idx) (l : List Met) : Idx := l.foldl Idx.put m

/-- The values that a list of vertices has at a depth and a place, in the list's order. -/
def valuesAt (old : List Met) (k : Nat × Nat) : List ByteArray :=
  (old.filter fun o => (o.1, o.2.1) == k).map fun o => o.2.2

/-- The map holds exactly what the list holds. -/
def Fits (m : Idx) (old : List Met) : Prop := ∀ (k : Nat × Nat), m.getD k [] = valuesAt old k

/-- The empty map fits the empty list. -/
theorem fits_empty : Fits ∅ [] := by
  intro k
  simp [valuesAt]

/-- If a map fits a list, the map with v entered fits the list with v appended. -/
theorem fits_put {m : Idx} {old : List Met} (h : Fits m old) (v : Met) :
    Fits (m.put v) (old ++ [v]) := by
  intro k
  unfold Idx.put valuesAt
  rw [Std.HashMap.getD_insert, List.filter_append, List.map_append]
  by_cases hk : ((v.1, v.2.1) == k) = true
  · have hk' : (v.1, v.2.1) = k := eq_of_beq hk
    rw [if_pos hk, h (v.1, v.2.1), hk']
    simp [valuesAt, hk']
  · rw [if_neg hk, h k]
    simp [valuesAt, hk]

/-- If a map fits a list, the map with the vertices of l entered fits the list with l appended. -/
theorem fits_putAll : ∀ (l : List Met) {m : Idx} {old : List Met}, Fits m old →
    Fits (m.putAll l) (old ++ l)
  | [], m, old, h => by
    rw [List.append_nil]
    exact h
  | v :: l, m, old, h => by
    have h2 := fits_putAll l (fits_put h v)
    rw [List.append_assoc] at h2
    exact h2

/-- No new vertex has a value other than those met at its depth and place. -/
def agreeIdx (m : Idx) (new : List Met) : Bool :=
  new.all fun v => (m.getD (v.1, v.2.1) []).all fun w => w == v.2.2

/-- At one vertex: the test on the values at its depth and place is the test on the whole list. -/
theorem all_valuesAt (v : Met) : ∀ (old : List Met),
    ((valuesAt old (v.1, v.2.1)).all fun w => w == v.2.2) =
      old.all fun o => !(o.1 == v.1 && o.2.1 == v.2.1) || o.2.2 == v.2.2
  | [] => rfl
  | o :: old => by
    have ih := all_valuesAt v old
    unfold valuesAt at ih ⊢
    have hb : ((o.1, o.2.1) == (v.1, v.2.1)) = (o.1 == v.1 && o.2.1 == v.2.1) := rfl
    rw [List.filter_cons, hb, List.all_cons]
    cases hc : (o.1 == v.1 && o.2.1 == v.2.1) with
    | true =>
      rw [if_pos rfl, List.map_cons, List.all_cons, ih]
      rfl
    | false =>
      rw [if_neg Bool.false_ne_true, ih]
      rfl

/-- With a map that fits the old list the fast test is `Fmt.agree`. -/
theorem agreeIdx_eq {m : Idx} {old : List Met} (h : Fits m old) (new : List Met) :
    agreeIdx m new = Fmt.agree old new := by
  unfold agreeIdx Fmt.agree
  congr 1
  funext v
  rw [h (v.1, v.2.1), all_valuesAt]

/-- The record of one root: the root, the vertices met under it, and the map beside them. -/
structure Rooted where
  /-- the root's 32 bytes -/
  root : ByteArray
  /-- the vertices met under `root`, in the order in which they were met -/
  met  : List Met
  /-- the values of the vertices in `met`, by depth and place -/
  idx  : Idx
  /-- `idx` holds exactly what `met` holds -/
  fits : Fits idx met

/-- The record of a root under which the given vertices were met. -/
def Rooted.of (root : ByteArray) (met : List Met) : Rooted :=
  ⟨root, met, Idx.putAll ∅ met, by
    have h := fits_putAll met fits_empty
    rw [List.nil_append] at h
    exact h⟩

/-- The record e with the vertices `new` entered after those that it holds. Nothing is compared. -/
def Rooted.more (e : Rooted) (new : List Met) : Rooted :=
  ⟨e.root, e.met ++ new, e.idx.putAll new, fits_putAll new e.fits⟩

/-- A root's record as an entry of the list of Fmt/. -/
def Rooted.pair (e : Rooted) : ByteArray × List Met := (e.root, e.met)

/-- The loop of `addRooted`. acc: the roots' records that were passed, the last one first. -/
def rootedLoop (root : ByteArray) (new : List Met) :
    List Rooted → List Rooted → Option (List Rooted)
  | [], acc => some (acc.reverseAux [Rooted.of root new])
  | e :: l, acc =>
    if e.root == root then
      (if agreeIdx e.idx new then some (acc.reverseAux (e.more new :: l)) else none)
    else rootedLoop root new l (e :: acc)

/-- Enters the vertices of one accepted opening under a root, as `Fmt.addSeen` does. Returns none
if a new vertex differs in value from an old one at the same depth and place under that root. The
new vertices are not compared with each other, and under a root that was not met before nothing
is compared. -/
def addRooted (root : ByteArray) (new : List Met) (l : List Rooted) : Option (List Rooted) :=
  rootedLoop root new l []

/-- The loop gives what `Fmt.addSeen` gives, after the records that were passed. -/
theorem rootedLoop_eq (root : ByteArray) (new : List Met) : ∀ (l acc : List Rooted),
    (rootedLoop root new l acc).map (fun l' => l'.map Rooted.pair) =
      (Fmt.addSeen root new (l.map Rooted.pair)).map fun l' => acc.reverse.map Rooted.pair ++ l'
  | [], acc => by
    show some ((acc.reverseAux [Rooted.of root new]).map Rooted.pair) =
      some (acc.reverse.map Rooted.pair ++ [(root, new)])
    rw [List.reverseAux_eq, List.map_append]
    rfl
  | e :: l, acc => by
    have ih := rootedLoop_eq root new l (e :: acc)
    show Option.map _ (if e.root == root then
        (if agreeIdx e.idx new then some (acc.reverseAux (e.more new :: l)) else none)
      else rootedLoop root new l (e :: acc)) =
      Option.map _ (if e.root == root then
        (if Fmt.agree e.met new then some ((e.root, e.met ++ new) :: l.map Rooted.pair) else none)
      else (Fmt.addSeen root new (l.map Rooted.pair)).map fun l' => (e.root, e.met) :: l')
    rw [agreeIdx_eq e.fits new]
    cases (e.root == root) with
    | true =>
      cases Fmt.agree e.met new with
      | true =>
        show some ((acc.reverseAux (e.more new :: l)).map Rooted.pair) = some _
        rw [List.reverseAux_eq, List.map_append]
        rfl
      | false => rfl
    | false =>
      show Option.map _ (rootedLoop root new l (e :: acc)) = _
      rw [ih]
      cases Fmt.addSeen root new (l.map Rooted.pair) with
      | none => rfl
      | some l' =>
        show some ((e :: acc).reverse.map Rooted.pair ++ l') =
          some (acc.reverse.map Rooted.pair ++ (e.root, e.met) :: l')
        rw [List.reverse_cons, List.map_append, List.append_assoc]
        rfl

/-- Entering with maps is `Fmt.addSeen`. -/
theorem addRooted_eq (root : ByteArray) (new : List Met) (l : List Rooted) :
    (addRooted root new l).map (fun l' => l'.map Rooted.pair) =
      Fmt.addSeen root new (l.map Rooted.pair) := by
  rw [addRooted, rootedLoop_eq]
  cases Fmt.addSeen root new (l.map Rooted.pair) with
  | none => rfl
  | some _ => rfl

/-- The record of vertices with a map beside each root's list. -/
def Keeper.indexed : Keeper (List Rooted) where
  toSeen := fun l => l.map Rooted.pair
  ofSeen := fun s => s.map fun x => Rooted.of x.1 x.2
  add := addRooted
  toSeen_ofSeen := fun s => by
    induction s with
    | nil => rfl
    | cons x s ih => exact congrArg (fun l => x :: l) ih
  toSeen_add := addRooted_eq

end OnBytes
