-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/SaysLinesPrefix.lean: what the reader of a parameter file reads of the first 32 lines
does not hang on the bytes behind them. So `EntryGround.SaysLines` (OnBytes/Tie/EntryGround.lean),
once it holds of some bytes, holds of every file that begins with these bytes.

`Params.lines` (OnBytes/Params/File.lean) is a reader of the text that is left: it gives a value and
the remaining text, or the name of a refusal. `Keeps r` says of such a reader r: where r gives a
value a and leaves t' on a text t, it gives a and leaves t' ++ u on t ++ u, whatever u. The one
reader that looks at the text, `Params.words`, cuts at the first line feed, and has the property;
the others are made of it by sequencing and by tests on values.

Main names:
  `Keeps`; `keeps_words`; `Keeps.bind`; `keeps_lines`.
  `readLines_append`: where `Params.readLines` gives x on b, it gives x's lines on b ++ rest.
  `saysLines_append`: G.SaysLines b → G.SaysLines (b ++ rest).
  `full_says_of_prefix`, `small_says_of_prefix`: every file that begins with the 32 lines `full32`
    (`small32`) of OnBytes/K/Left/TestSaysLines.lean, each with its line feed, has the full-size
    (small) ground's lines. So a user's test is: head -n 32 policy.txt | sha256sum, held against the
    sums in that file's head.

Limits: one way: nothing on a file that the reader refuses. Nothing on what stands behind the 32
lines. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Left.TestSaysLines

set_option autoImplicit false

namespace OnBytes.K.Left
open OnBytes.Tie
open OnBytes.Params

/-- Where the reader gives a value on a text, it gives the same value on every longer text, and
leaves what it left with the further bytes behind it. -/
def Keeps {α : Type} (r : Reading α) : Prop :=
  ∀ (t t' u : List UInt8) (a : α), r t = .ok (a, t') → r (t ++ u) = .ok (a, t' ++ u)

theorem Keeps.pure {α : Type} (a : α) : Keeps (Pure.pure a : Reading α) := by
  intro t t' u b h
  cases h
  rfl

theorem Keeps.refuse {α : Type} (why : String) : Keeps (refuse why : Reading α) := by
  intro t t' u b h
  cases h

theorem Keeps.demand (b : Bool) (why : String) : Keeps (demand b why) := by
  unfold Params.demand
  split
  · exact Keeps.pure ()
  · exact Keeps.refuse why

theorem Keeps.bind {α β : Type} {r : Reading α} {f : α → Reading β} (hr : Keeps r)
    (hf : ∀ a, Keeps (f a)) : Keeps (r >>= f) := by
  intro t t' u b h
  have h' : (match r t with
    | .ok (a, s) => f a s
    | .error e => .error e) = .ok (b, t') := by
    cases hx : r t with
    | error e =>
      have : (r >>= f) t = .error e := by
        show (r t >>= fun p => f p.1 p.2) = _
        rw [hx]
        rfl
      rw [this] at h
      cases h
    | ok p =>
      have : (r >>= f) t = f p.1 p.2 := by
        show (r t >>= fun p => f p.1 p.2) = _
        rw [hx]
        rfl
      rw [this] at h
      exact h
  cases hx : r t with
  | error e =>
    rw [hx] at h'
    cases h'
  | ok p =>
    rw [hx] at h'
    show (r (t ++ u) >>= fun p => f p.1 p.2) = _
    rw [hr t p.2 u p.1 hx]
    exact hf p.1 p.2 t' u b h'

/-- The search for a byte finds it at the same place in a longer text. -/
theorem cutAtFrom_append (c : UInt8) : ∀ (t seen l rest u : List UInt8),
    cutAtFrom c seen t = some (l, rest) → cutAtFrom c seen (t ++ u) = some (l, rest ++ u)
  | [], _, _, _, _, h => by cases h
  | x :: t, seen, l, rest, u, h => by
    unfold cutAtFrom at h
    show cutAtFrom c seen (x :: (t ++ u)) = _
    unfold cutAtFrom
    split
    · rename_i hx
      rw [if_pos hx] at h
      cases h
      rfl
    · rename_i hx
      rw [if_neg hx] at h
      exact cutAtFrom_append c t _ l rest u h

/-- The reader of a line's values. -/
theorem keeps_words (head : String) (count : Option Nat) : Keeps (words head count) := by
  intro t t' u a h
  unfold words at h ⊢
  cases hc : cutAt 0x0A t with
  | none =>
    rw [hc] at h
    cases h
  | some p =>
    have hc' : cutAt 0x0A (t ++ u) = some (p.1, p.2 ++ u) := cutAtFrom_append _ _ _ _ _ _ hc
    rw [hc] at h
    rw [hc']
    dsimp only at h ⊢
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i h1
        rw [if_neg h1]
        split at h
        · cases h
        · rename_i h2
          rw [if_neg h2]
          cases h
          rfl

/-- One step of the proofs below: a reader made by sequencing, by tests on values and by cases. -/
macro "keeps_step" : tactic =>
  `(tactic| first
    | exact Keeps.pure _
    | exact Keeps.refuse _
    | exact Keeps.demand _ _
    | exact keeps_words _ _
    | assumption
    | (refine Keeps.bind ?_ (fun _ => ?_))
    | split)

theorem keeps_numbers (head : String) (count : Option Nat) : Keeps (numbers head count) := by
  unfold numbers
  repeat keeps_step

theorem keeps_one (head : String) (lo hi : Nat) : Keeps (Params.one head lo hi) := by
  have := keeps_numbers head (some 1)
  unfold Params.one
  repeat keeps_step

theorem keeps_versionLine : Keeps versionLine := by
  unfold versionLine
  repeat keeps_step

theorem keeps_workLine (head : String) (sec : Nat) : Keeps (workLine head sec) := by
  have := keeps_numbers head (some 3)
  unfold workLine
  repeat keeps_step

theorem keeps_groupLines (name : String) : Keeps (groupLines name) := by
  have h1 := keeps_numbers ("group " ++ name) (some 5)
  have h2 := keeps_numbers ("stages " ++ name) none
  unfold groupLines
  repeat keeps_step

/-- The reader of the 32 lines. -/
theorem keeps_lines : Keeps lines := by
  have h0 := keeps_versionLine
  have h1 := keeps_one
  have h2 := keeps_workLine
  have h3 := keeps_groupLines
  have h4 := keeps_numbers "table" (some 6)
  unfold lines
  refine Keeps.bind h0 fun _ => ?_
  iterate 4 refine Keeps.bind (h1 _ _ _) fun _ => ?_
  refine Keeps.bind (Keeps.demand _ _) fun _ => ?_
  iterate 2 refine Keeps.bind (h1 _ _ _) fun _ => ?_
  iterate 5 refine Keeps.bind (h2 _ _) fun _ => ?_
  refine Keeps.bind (h1 _ _ _) fun _ => ?_
  refine Keeps.bind (Keeps.demand _ _) fun _ => ?_
  refine Keeps.bind (h1 _ _ _) fun _ => ?_
  iterate 8 refine Keeps.bind (h3 _) fun _ => ?_
  refine Keeps.bind (h1 _ _ _) fun _ => ?_
  iterate 2 refine Keeps.bind (Keeps.demand _ _) fun _ => ?_
  refine Keeps.bind h4 fun _ => ?_
  split
  · iterate 2 refine Keeps.bind (Keeps.demand _ _) fun _ => ?_
    exact Keeps.pure _
  · exact Keeps.refuse _

/-- The walk of `ByteArray.toList`: what was gathered, then the bytes from place i on. -/
theorem toList_loop (bs : ByteArray) : ∀ (n i : Nat) (r : List UInt8), bs.size - i = n →
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i
  | 0, i, r, h => by
    rw [ByteArray.toList.loop.eq_def, if_neg (by omega), List.drop_of_length_le, List.append_nil]
    show bs.data.toList.length ≤ i
    rw [Array.length_toList]
    show bs.size ≤ i
    omega
  | n + 1, i, r, h => by
    have hi : i < bs.size := by omega
    have hi' : i < bs.data.toList.length := by
      rw [Array.length_toList]
      exact hi
    rw [ByteArray.toList.loop.eq_def, if_pos hi, toList_loop bs n (i + 1) _ (by omega),
      List.drop_eq_getElem_cons hi', List.reverse_cons, List.append_assoc]
    congr 2
    show [bs.get! i] ++ _ = _
    have e : bs.get! i = bs.data.toList[i] := by
      show bs.data[i]! = _
      rw [getElem!_pos bs.data i hi, Array.getElem_toList]
      rfl
    rw [e]
    rfl

/-- The bytes of a byte string as a list. -/
theorem toList_data (bs : ByteArray) : bs.toList = bs.data.toList := by
  unfold ByteArray.toList
  rw [toList_loop bs _ 0 [] rfl]
  rfl

/-- Where the reader of a parameter file gives lines on b, it gives the same lines on b ++ rest. -/
theorem readLines_append (b rest : ByteArray) (x : Lines × ByteArray)
    (h : readLines b = .ok x) : ∃ y, readLines (b ++ rest) = .ok (x.1, y) := by
  unfold readLines at h ⊢
  cases hl : lines b.toList with
  | error e =>
    rw [hl] at h
    cases h
  | ok p =>
    rw [hl] at h
    have e : (b ++ rest).toList = b.toList ++ rest.toList := by
      rw [toList_data, toList_data, toList_data, ByteArray.data_append, Array.toList_append]
    rw [e, keeps_lines _ _ rest.toList _ hl]
    cases h
    exact ⟨_, rfl⟩

/-- What holds of some bytes holds of every file that begins with them. -/
theorem saysLines_append (G : EntryGround) (b rest : ByteArray) (h : G.SaysLines b) :
    G.SaysLines (b ++ rest) := by
  unfold EntryGround.SaysLines at h ⊢
  cases hr : readLines b with
  | error e =>
    rw [hr] at h
    cases h
  | ok x =>
    obtain ⟨y, hy⟩ := readLines_append b rest x hr
    rw [hr] at h
    rw [hy]
    exact h

/-- Every file that begins with the full-size example's 32 lines has the full-size ground's lines.
-/
theorem full_says_of_prefix (rest : ByteArray) :
    recordGround.SaysLines (TestSaysLines.bytesOf TestSaysLines.full32 ++ rest) :=
  saysLines_append _ _ _ TestSaysLines.full_says

/-- Every file that begins with the small examples' 32 lines has the small ground's lines. -/
theorem small_says_of_prefix (rest : ByteArray) :
    smallRecordGround.SaysLines (TestSaysLines.bytesOf TestSaysLines.small32 ++ rest) :=
  saysLines_append _ _ _ TestSaysLines.small_says

end OnBytes.K.Left
