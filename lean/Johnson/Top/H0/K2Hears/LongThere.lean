-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/LongThere.lean: the code switch: WHETHER THE FRONT READS ANYTHING OFF
THE ORACLES AT A POSITION HANGS NEITHER ON THE POSITION NOR ON THE ORACLES: every refusal inside
K2Hears/LongOne.lean's longFront is a look-up in the book or a test on sizes.
  Sz, SzC        two tables, two columns, of the same sizes
  OR             two optional values are both there and related, or both lack
  layFrom_size, layRows_sz, layMember_sz, layMembers_sz  the laying's being there, and its sizes,
                 hang on the sizes alone
  rowsAt_there   so rowsAt is there at the one family of columns just if at the other
  colOne_sz      LongCols.lean's colOne at two positions and two readings of the oracles: both there
                 with the same sizes, or both lacking
  longFront_there  THE STATEMENT: (longFront p s x orc q).isSome = (longFront p s x orc' q').isSome
WHAT IT IS FOR. K2Hands/StrMade.lean's open word is 0 at a position at which longFront has nothing.
With this file, where longFront is there at ONE position (at a yes: at each drawn one,
LongOne.lean's heard_is_front) it is there at all: so the made word holds what the front reads at
every position.
LIMITS. Nothing on what is read. No soundness is claimed.
-/
import Johnson.Top.H0.K2Hears.LongOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own
open OnBytes

/-- Two tables of the same sizes. -/
def Sz (t u : Tables) : Prop :=
  t.main.size = u.main.size ∧ t.mask.size = u.mask.size ∧ t.kept.size = u.kept.size

/-- Two columns of the same sizes. -/
def SzC (c d : Column) : Prop := c.main.size = d.main.size ∧ c.mask.size = d.mask.size

/-- Both there and related, or both lacking. -/
def OR {α : Type} (R : α → α → Prop) : Option α → Option α → Prop
  | some a, some b => R a b
  | none, none => True
  | _, _ => False

theorem layFrom_size : ∀ (l : List E) (table : Array E) (f : Nat),
    (layFrom table f l).size = table.size
  | [], _, _ => rfl
  | e :: es, table, f => by
    unfold layFrom
    rw [layFrom_size es, Array.size_setIfInBounds]

theorem layRows_sz (t u : Array E) (first : Option Nat) (c d : Array E) (h1 : t.size = u.size)
    (h2 : c.size = d.size) :
    OR (fun a b => a.size = b.size) (layRows t first c) (layRows u first d) := by
  unfold layRows
  have hl : c.toList.length = d.toList.length := by simpa using h2
  cases hc : c.toList with
  | nil =>
    rw [hc] at hl
    have hd : d.toList = [] := List.eq_nil_of_length_eq_zero hl.symm
    rw [hd]
    exact h1
  | cons e es =>
    rw [hc] at hl
    cases hd : d.toList with
    | nil => rw [hd] at hl; cases hl
    | cons e' es' =>
      rw [hd] at hl
      cases first with
      | none => trivial
      | some f =>
        dsimp only
        rw [hl, h1]
        by_cases hf : f + (e' :: es').length ≤ u.size
        · rw [if_pos hf, if_pos hf]
          show (layFrom t f _).size = (layFrom u f _).size
          rw [layFrom_size, layFrom_size, h1]
        · rw [if_neg hf, if_neg hf]
          trivial

theorem layMember_sz (L : GroupLayout) (w : Nat) (c d : Column) (t u : Tables) (hc : SzC c d)
    (ht : Sz t u) : OR Sz (layMember L w c t) (layMember L w d u) := by
  unfold layMember
  have h1 := layRows_sz t.mask u.mask (L.maskFirst.getD w none) c.mask d.mask ht.2.1 hc.2
  cases ha : layRows t.mask (L.maskFirst.getD w none) c.mask with
  | none =>
    cases hb : layRows u.mask (L.maskFirst.getD w none) d.mask with
    | none => trivial
    | some b => rw [ha, hb] at h1; exact h1.elim
  | some a =>
    cases hb : layRows u.mask (L.maskFirst.getD w none) d.mask with
    | none => rw [ha, hb] at h1; exact h1.elim
    | some b =>
      rw [ha, hb] at h1
      simp only [Option.bind_some]
      by_cases hk : L.kept.getD w false = true
      · rw [if_pos hk, if_pos hk]
        exact ⟨ht.1, h1, by simp [Array.size_append, ht.2.2, hc.1]⟩
      · rw [if_neg hk, if_neg hk]
        have h2 := layRows_sz t.main u.main (L.mainFirst.getD w none) c.main d.main ht.1 hc.1
        cases hx : layRows t.main (L.mainFirst.getD w none) c.main with
        | none =>
          cases hy : layRows u.main (L.mainFirst.getD w none) d.main with
          | none => trivial
          | some y => rw [hx, hy] at h2; exact h2.elim
        | some x =>
          cases hy : layRows u.main (L.mainFirst.getD w none) d.main with
          | none => rw [hx, hy] at h2; exact h2.elim
          | some y =>
            rw [hx, hy] at h2
            exact ⟨h2, h1, ht.2.2⟩

theorem layMembers_sz (L : GroupLayout) (A B : Array (Array Column)) (i j : Nat)
    (h : ∀ w : Nat, OR SzC ((A[w]?).bind (fun (c : Array Column) => c[i]?))
      ((B[w]?).bind (fun (c : Array Column) => c[j]?))) :
    ∀ (ws : List Nat) (t u : Tables), Sz t u →
      OR Sz (layMembers L A i ws t) (layMembers L B j ws u)
  | [], _, _, ht => ht
  | w :: ws, t, u, ht => by
    unfold layMembers
    have hw := h w
    cases ha : (A[w]?).bind (fun (c : Array Column) => c[i]?) with
    | none =>
      cases hb : (B[w]?).bind (fun (c : Array Column) => c[j]?) with
      | none => trivial
      | some b => rw [ha, hb] at hw; exact hw.elim
    | some a =>
      cases hb : (B[w]?).bind (fun (c : Array Column) => c[j]?) with
      | none => rw [ha, hb] at hw; exact hw.elim
      | some b =>
        rw [ha, hb] at hw
        simp only [Option.bind_some]
        have hm := layMember_sz L w a b t u hw ht
        cases hx : layMember L w a t with
        | none =>
          cases hy : layMember L w b u with
          | none => trivial
          | some y => rw [hx, hy] at hm; exact hm.elim
        | some x =>
          cases hy : layMember L w b u with
          | none => rw [hx, hy] at hm; exact hm.elim
          | some y =>
            rw [hx, hy] at hm
            simp only [Option.bind_some]
            exact layMembers_sz L A B i j h ws x y hm

/-- **rowsAt is there at the one family of columns just if at the other.** -/
theorem rowsAt_there (s : SingleRows) (A B : Array (Array Column)) (i j : Nat)
    (h : ∀ w : Nat, OR SzC ((A[w]?).bind (fun (c : Array Column) => c[i]?))
      ((B[w]?).bind (fun (c : Array Column) => c[j]?))) :
    (rowsAt s A #[] i).isSome = (rowsAt s B #[] j).isSome := by
  unfold rowsAt
  dsimp only
  have hl := layMembers_sz s.layout A B i j h (List.range s.layout.members.size)
    ⟨Array.replicate (2 ^ s.layout.k) zeroE, Array.replicate (2 ^ s.layout.h) zeroE, #[]⟩
    ⟨Array.replicate (2 ^ s.layout.k) zeroE, Array.replicate (2 ^ s.layout.h) zeroE, #[]⟩
    ⟨rfl, rfl, rfl⟩
  have hf := h s.layout.members.size
  generalize layMembers s.layout A i (List.range s.layout.members.size)
    ⟨Array.replicate (2 ^ s.layout.k) zeroE, Array.replicate (2 ^ s.layout.h) zeroE, #[]⟩ = ra
    at hl ⊢
  generalize layMembers s.layout B j (List.range s.layout.members.size)
    ⟨Array.replicate (2 ^ s.layout.k) zeroE, Array.replicate (2 ^ s.layout.h) zeroE, #[]⟩ = rb
    at hl ⊢
  generalize (A[s.layout.members.size]?).bind (fun (c : Array Column) => c[i]?) = fa at hf ⊢
  generalize (B[s.layout.members.size]?).bind (fun (c : Array Column) => c[j]?) = fb at hf ⊢
  cases ra with
  | none =>
    cases rb with
    | none => rfl
    | some b => exact hl.elim
  | some a =>
    cases rb with
    | none => exact hl.elim
    | some b =>
      have hk : a.kept.size = b.kept.size := hl.2.2
      simp only [Option.bind_some, hk]
      by_cases h1 : b.kept.size = s.keptRows
      · by_cases h2 : s.masks = 2
        · cases fa with
          | none =>
            cases fb with
            | none => simp [h1, h2]
            | some d => exact hf.elim
          | some c =>
            cases fb with
            | none => exact hf.elim
            | some d =>
              have hm : c.mask.size = d.mask.size := hf.2
              by_cases h3 : d.mask.size = 2 ^ s.layout.h
              · simp [h1, h2, hm, h3]
              · simp [h1, h2, hm, h3]
        · simp [h1, h2]
      · simp [h1]

end VerifiableInference.Desc.Own

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Own (OR SzC rowsAt rowsAt_there)
open _root_.Tw.K2 (switchNotices)

theorem colOne_sz (S : Statement) (B : TreeBook) (ft logN : Nat)
    (orc orc' : Nat → Nat → List UInt64) (o : Nat) (pl : Nat × Nat) (q q' : Nat) :
    OR SzC (colOne S B ft logN orc o pl q) (colOne S B ft logN orc' o pl q') := by
  unfold colOne
  cases B.trees[pl.1]? with
  | none => trivial
  | some tree =>
    cases S.oracles[o]? with
    | none => trivial
    | some x => exact ⟨by simp [Blk.columnOf], by simp [Blk.columnOf]⟩

theorem openedOne_sz (S : Statement) (B : TreeBook) (ft logN : Nat)
    (orc orc' : Nat → Nat → List UInt64) (idp : Array (Nat × Nat × Nat)) (q q' w : Nat) :
    OR SzC (((openedOne S B ft logN orc idp q)[w]?).bind (fun (c : Array Column) => c[0]?))
      (((openedOne S B ft logN orc' idp q')[w]?).bind (fun (c : Array Column) => c[0]?)) := by
  unfold openedOne
  rw [Array.getElem?_map, Array.getElem?_map]
  cases idp[w]? with
  | none => trivial
  | some y =>
    have h := colOne_sz S B ft logN orc orc' y.1 y.2 q q'
    cases ha : colOne S B ft logN orc y.1 y.2 q with
    | none =>
      cases hb : colOne S B ft logN orc' y.1 y.2 q' with
      | none => simp [OR, ha, hb]
      | some b => rw [ha, hb] at h; exact h.elim
    | some a =>
      cases hb : colOne S B ft logN orc' y.1 y.2 q' with
      | none => rw [ha, hb] at h; exact h.elim
      | some b =>
        rw [ha, hb] at h
        simpa [OR, ha, hb] using h

/-- **Whether the front reads anything hangs neither on the position nor on the oracles.** -/
theorem longFront_there (p : P2) (s : S) (x : _root_.Tw.K2.Front)
    (orc orc' : Nat → Nat → List UInt64) (q q' : Nat) :
    (longFront p s x orc q).isSome = (longFront p s x orc' q').isSome := by
  unfold longFront
  cases bookAt (par9 p).firstTree x.st s.book s.roots (switchNotices x.T x.others) with
  | none => rfl
  | some B =>
    simp only [Option.bind_some]
    cases (singleRowsOracles x.f.rows).mapM fun o => B.place[o]? with
    | none => rfl
    | some places =>
      simp only [Option.bind_some]
      exact rowsAt_there _ _ _ 0 0 fun w => openedOne_sz _ _ _ _ _ _ _ _ _ w

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.longFront_there
