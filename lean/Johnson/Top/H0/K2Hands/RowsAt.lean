-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/RowsAt.lean: the rows that a code switch lays, ONE BY ONE: at which
place of the list each stands.

RowsOrder.lean's switchRows_iff gives the list whole: the carried claim; the kept members' old
sample rows; the generator rows, draw by draw. The library's names for the typed rows
(Cb.LdLocD.RowN, Cb/Req1/LdSegAfterRows.lean) are: one for the claim; one for each answer of each
held message's sample; one for each coordinate of each long symbol read. Here the list is read at
the place of each such name:
  rows_claim    place 0: the carried claim
  rows_sample   place 1 + (the sample rows of the members in front) + s: sample row s of kept member
                a
  rows_gen      place 1 + (all sample rows) + i * R + c: row c of the generator rows of draw i,
                where every draw has R generator rows (a premise: hR)
  Laid, laid_of  THE RECORD THAT THE LATER FILES SPEND: what a yes of switchRows lays down, by name:
                the frame W is made; the carried claim's row; every old sample row reads the
                member's main table alone; the array heard has (listed positions) * (old rows)
                entries; every draw is a listed position; and rows = the carried claim :: the kept
                members' sample rows ++ the generator rows, draw by draw. laid_of: a yes of
                switchRows gives W and carried with Laid
  allSamples    the number of all old sample rows
On the way, of any lists: before (the lengths of the blocks in front, added up), flatMap_at (blocks
of any lengths), flatMap_block and before_const (blocks of one length), length_flatMap_before. What
this is not: nothing is read in the field; that R is the number of the old rows, and which row c is
which coordinate, is not said here. No soundness is claimed.
-/
import Johnson.Top.H0.K2Hands.RowsOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes OnBytes.Slice

/-! ## A list made of blocks -/

/-- The lengths of the blocks in front of block a, added up. -/
def before {α β : Type} (f : α → List β) (l : List α) (a : Nat) : Nat :=
  ((l.take a).map fun x => (f x).length).sum

theorem flatMap_at {α β : Type} (f : α → List β) : ∀ (l : List α) (a s : Nat) (x : α),
    l[a]? = some x → s < (f x).length → (l.flatMap f)[before f l a + s]? = (f x)[s]?
  | [], _, _, _, h, _ => by simp at h
  | y :: l, 0, s, x, h, hs => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [before, List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, List.flatMap_cons]
    exact List.getElem?_append_left hs
  | y :: l, a + 1, s, x, h, hs => by
    simp only [List.getElem?_cons_succ] at h
    have ih := flatMap_at f l a s x h hs
    have e : before f (y :: l) (a + 1) + s = (f y).length + (before f l a + s) := by
      simp only [before, List.take_succ_cons, List.map_cons, List.sum_cons]
      omega
    rw [e, List.flatMap_cons, List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left]
    exact ih

theorem before_const {α β : Type} (f : α → List β) (R : Nat) : ∀ (l : List α) (a : Nat),
    (∀ x ∈ l, (f x).length = R) → a ≤ l.length → before f l a = a * R
  | _, 0, _, _ => by simp [before]
  | [], a + 1, _, h => by simp at h
  | y :: l, a + 1, hR, h => by
    have ih := before_const f R l a (fun x hx => hR x (List.mem_cons_of_mem _ hx))
      (Nat.le_of_succ_le_succ h)
    unfold before at ih ⊢
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, ih,
      hR y (List.mem_cons_self ..), Nat.succ_mul]
    omega

theorem flatMap_block {α β : Type} (f : α → List β) (R : Nat) (l : List α)
    (hR : ∀ x ∈ l, (f x).length = R) (i c : Nat) (x : α) (hx : l[i]? = some x) (hc : c < R) :
    (l.flatMap f)[i * R + c]? = (f x)[c]? := by
  have hi : i < l.length := (List.getElem?_eq_some_iff.1 hx).1
  have hm : x ∈ l := List.mem_of_getElem? hx
  rw [← before_const f R l i hR (Nat.le_of_lt hi)]
  exact flatMap_at f l i c x hx (by rw [hR x hm]; exact hc)

theorem length_flatMap_before {α β : Type} (f : α → List β) (l : List α) :
    (l.flatMap f).length = before f l l.length := by
  simp [before, List.length_flatMap]

/-! ## The rows of a switch, one by one -/

section
variable {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat} {anew : Array Nat}
  {pos : Positions} {y : Array E} {rows : List Row}

/-- The number of all old sample rows. -/
def allSamples (S : Statement) (W : SwitchFrame) : Nat :=
  before (fun k => (samplesOf S k).map (sampleRow W k)) W.kept W.kept.length

/-- What a yes of switchRows lays down, by name. -/
structure Laid (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : Nat) (anew : Array Nat)
    (pos : Positions) (y : Array E) (rows : List Row) (W : SwitchFrame) (carried : Row) : Prop where
  frame : switchFrame S old T g anew = some W
  claim : switchCarried W old = some carried
  reads : ∀ k ∈ W.kept, ∀ sample ∈ samplesOf S k, readsMain k.old sample = true
  size : y.size = pos.all.size * old.rows
  listed : ∀ x ∈ pos.draws.toList, (pos.indexOf x).isSome = true
  rows : rows = carried :: (W.kept.flatMap fun k => (samplesOf S k).map (sampleRow W k)) ++
    pos.draws.toList.flatMap fun x => switchGenerators W old x (symAtB old pos y x)

theorem laid_of (h : switchRows S old T g anew pos y = some rows) :
    ∃ W carried, Laid S old T g anew pos y rows W carried := by
  obtain ⟨hz, hl, W, c, sm, hW, hc, hs, rfl⟩ := (switchRows_iff S old T g anew pos y rows).1 h
  obtain ⟨hr, rfl⟩ := (switchOldSamples_iff S W sm).1 hs
  exact ⟨W, c, hW, hc, hr, hz, hl, rfl⟩

variable {W : SwitchFrame} {carried : Row} (L : Laid S old T g anew pos y rows W carried)
include L

theorem rows_claim : rows[0]? = some carried := by
  rw [L.rows]
  rfl

theorem rows_sample (a s : Nat) (k : KeptPlace) (sample : Row) (hk : W.kept[a]? = some k)
    (hs : (samplesOf S k)[s]? = some sample) :
    rows[1 + (before (fun k => (samplesOf S k).map (sampleRow W k)) W.kept a + s)]? =
      some (sampleRow W k sample) := by
  have hlt : s < ((samplesOf S k).map (sampleRow W k)).length := by
    rw [List.length_map]
    exact (List.getElem?_eq_some_iff.1 hs).1
  have h1 := flatMap_at (fun k => (samplesOf S k).map (sampleRow W k)) W.kept a s k hk hlt
  have h2 : ((samplesOf S k).map (sampleRow W k))[s]? = some (sampleRow W k sample) := by
    rw [List.getElem?_map, hs]
    rfl
  rw [L.rows, Nat.add_comm 1, List.cons_append, List.getElem?_cons_succ,
    List.getElem?_append_left ((List.getElem?_eq_some_iff.1 (h1.trans h2)).1)]
  exact h1.trans h2

theorem rows_gen (R : Nat)
    (hR : ∀ x ∈ pos.draws.toList, (switchGenerators W old x (symAtB old pos y x)).length = R)
    (i c x : Nat) (hx : pos.draws.toList[i]? = some x) (hc : c < R) :
    rows[1 + (allSamples S W + (i * R + c))]? =
      (switchGenerators W old x (symAtB old pos y x))[c]? := by
  rw [L.rows, Nat.add_comm 1, List.cons_append, List.getElem?_cons_succ]
  have hlen : (W.kept.flatMap fun k => (samplesOf S k).map (sampleRow W k)).length =
      allSamples S W :=
    length_flatMap_before _ _
  rw [List.getElem?_append_right (by rw [hlen]; exact Nat.le_add_right _ _), hlen,
    Nat.add_sub_cancel_left]
  exact flatMap_block _ R _ hR i c x hx hc

end

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.laid_of
#print axioms VerifiableInference.Desc.First.K2Hands.rows_claim
#print axioms VerifiableInference.Desc.First.K2Hands.rows_sample
#print axioms VerifiableInference.Desc.First.K2Hands.rows_gen
