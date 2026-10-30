-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoTieInv.lean.
The tie of a sub-proof's lookup: what holds between the byte-level verifier's loop and the flat
function after n steps, and that a step keeps it.

States:
  tieOff: the number of slots that the first n steps take.
  TieInv: after n steps: the state fits; the slots taken; each claim so far is the flat function's
    row; the slots of Z, of the last power and of the planes' roots are forms (FormIs) with the
    value shown as public part and, on the mask row, the step's challenge at the value's place.
  tieInv_zero: it holds before the first step. tieStep_is: a step that returns keeps it, its six
    calls are three rounds on which the flat function takes its step, and it leads to a later state,
    in which the step's own slots, and no others, are newly filled and nothing else is turned:
    what lies under every other slot, free or filled, stays.
Premises of tieStep_is: the flat function's places of the step's masks lie from the step's first
slot on (Fo.LedAt); the public factor reads as the flat function's.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoTieKit
import OnBytes.Tie.Pv.Lookup.Forest.FoLedAt
import OnBytes.Tie.Pv.Lookup.Forest.FoStretch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun

/-- The slots that the first n steps of the tie take. -/
def tieOff : ℕ → ℕ
  | 0 => 0
  | n + 1 => 7 + 6 * n

section
variable {K : Type} [CommRing K] (ρ : Reading K) (N : Nums Pl K) (lam : K) (base : ℕ)

/-- What holds after n steps. -/
structure TieInv (n : ℕ) (s : Forest.TieStep) (F : Fork) (scs : List (Sc K)) : Prop where
  len : scs.length = n
  sized : Sized F
  next : F.next = base + tieOff n
  rowsN : s.rows.size = n
  rows : ∀ i < n, RowIs ρ F (s.rows.getD i {})
    ((tieRowsR N lam scs.reverse).reverse.getD i ⟨[], 0⟩)
  sZ : 0 < n → s.sZ = base + 4 ∧ FormIs ρ F (Aff.slot s.sZ) ((scs.getD 0 Sc.zero).v 0)
    [((N.ledTie 0).sh 0, (scs.getD 0 Sc.zero).be)]
  sP : FormIs ρ F (if n = 0 then Aff.ofConst zeroE else Aff.slot s.sP) (tgEnd 0 0 scs)
    (tieInc N scs.reverse)
  sGN : s.sG.size = n
  sG : ∀ i < n, FormIs ρ F (Aff.slot (s.sG.getD i 0)) ((scs.getD i Sc.zero).v (ptAt i))
    [((N.ledTie i).sh (ptAt i), (scs.getD i Sc.zero).be)]

theorem tieInv_zero (F : Fork) (hF : Sized F) (hb : F.next = base) :
    TieInv ρ N lam base 0 {} F [] :=
  { len := rfl
    sized := hF
    next := hb
    rowsN := rfl
    rows := fun i hi => absurd hi (Nat.not_lt_zero i)
    sZ := fun h => absurd h (Nat.lt_irrefl 0)
    sP := zero_formIs ρ F
    sGN := rfl
    sG := fun i hi => absurd hi (Nat.not_lt_zero i) }

theorem getD_read (l : List E) (i : ℕ) : (l.map ρ.val).getD i 0 = ρ.val (l.getD i zeroE) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? with
  | none => exact ρ.zero.symm
  | some x => rfl

theorem tieRowsR_len : ∀ l : List (Sc K), (tieRowsR N lam l).length = l.length
  | [] => rfl
  | _ :: l => congrArg (· + 1) (tieRowsR_len l)

omit [CommRing K] in
theorem push_getD {α : Type} (a : Array α) (x d : α) (i : ℕ) :
    (a.push x).getD i d = if i < a.size then a.getD i d else if i = a.size then x else d := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_push]
  by_cases h1 : i = a.size
  · subst h1
    simp
  · by_cases h2 : i < a.size
    · simp [h1, h2]
    · simp [h1, h2]

omit [CommRing K] in
theorem snoc_getD {α : Type} (l : List α) (x d : α) (i : ℕ) :
    (l ++ [x]).getD i d = if i < l.length then l.getD i d else if i = l.length then x else d := by
  by_cases h2 : i < l.length
  · rw [if_pos h2, List.getD_append _ _ _ _ h2]
  · have h3 : l.length ≤ i := Nat.le_of_not_lt h2
    rw [if_neg h2, List.getD_append_right _ _ _ _ h3]
    by_cases h1 : i = l.length
    · subst h1
      simp
    · rw [if_neg h1]
      have : i - l.length = (i - l.length - 1) + 1 := by omega
      rw [this]
      rfl

omit [CommRing K] in
theorem arr_getD (v : Array E) (i : ℕ) : v.toList.getD i zeroE = v.getD i zeroE := by
  rw [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, Array.getElem?_toList]

/-- A step of the tie that returns. -/
theorem tieStep_is (a : E) (ha : ρ.val a = fac N lam)
    (n : ℕ) (hLed : LedAt (N.ledTie n) (base + tieOff n) [3] (if n = 0 then 3 else 2))
    (s s' : Forest.TieStep)
    (F G : Fork) (c c' : Ctx) (scs : List (Sc K)) (inv : TieInv ρ N lam base n s F scs)
    (h : Forest.tieStep a s n F c = .ok ((s', G), c')) :
    ∃ mu eps sent beta v sc,
      Evs (stepEvs mu eps sent beta (if n = 0 then 3 else 2) v) c c' ∧
      (∀ rest, takeSc (flEv ρ (stepEvs mu eps sent beta (if n = 0 then 3 else 2) v) ++ rest)
        (tgEnd 0 0 scs) [0] true = (sc, rest)) ∧
      Later F G ∧ Same (took F (1 + (3 + if n = 0 then 3 else 2))) G ∧
      (∀ j, Filled G j ↔ Filled F j ∨
        (F.next ≤ j ∧ j < F.next + (1 + (3 + if n = 0 then 3 else 2)))) ∧
      TieInv ρ N lam base (n + 1) s' G (scs ++ [sc]) ∧
      (∀ j, (j < F.next ∨ F.next + (1 + (3 + if n = 0 then 3 else 2)) ≤ j) →
        G.vp.getD j zeroE = F.vp.getD j zeroE ∧ G.mf.getD j zeroE = F.mf.getD j zeroE) ∧
      sent.size = 3 ∧ v.size = (if n = 0 then 3 else 2) := by
  obtain ⟨target, mu, eps, sent, beta, v, G1, vP, vG, summand, hpp, hev, hs, hv, hG1, hvP, hvG,
    hsum, hG, rfl⟩ := tieStep_ok a s n F G c c' s' h
  obtain ⟨C, hC⟩ : ∃ C, C = (if n = 0 then Aff.ofConst zeroE else Aff.slot s.sP) := ⟨_, rfl⟩
  rw [← hC] at hpp hG
  have hsP := inv.sP
  rw [← hC] at hsP
  have htg : ρ.val target = tgEnd 0 0 scs := (hsP F (Later.refl F)).1 target hpp
  obtain ⟨sc, hsc⟩ : ∃ sc : Sc K, sc = ⟨ρ.val eps, [ρ.val beta],
      ρ.val (tiePsc C target mu eps beta F.next sent).claim, v.toList.map ρ.val⟩ := ⟨_, rfl⟩
  have hF1 : Sized (took (took F 1) (3 + if n = 0 then 3 else 2)) :=
    took_sized _ (took_sized _ inv.sized)
  obtain ⟨hS1, hZ1, hin1, hout1⟩ := hideRun_ok _ _ _ _ _ hF1 hG1
  obtain ⟨hS2, hZ2, hin2, hout2⟩ := hideRun_ok _ _ _ _ _ hZ1 hG
  have hL1 : Later F G1 :=
    ((took_later F 1).trans (took_later _ _)).trans (hideRun_later hF1 hG1)
  have hL2 : Later G1 G := hideRun_later hZ1 hG
  have hwl : (tiePsc C target mu eps beta F.next sent).walk.1.length = 4 := by
    have := congrArg List.length (tie_walk ρ C target mu eps beta F.next sent).1
    simpa using this
  rw [← inv.next] at hLed
  have l2 := hLed.sh
  rw [← hv] at l2
  have hv' : ∀ i, sc.v i = ρ.val (v.getD i zeroE) := by
    intro i
    rw [hsc]
    show (v.toList.map ρ.val).getD i 0 = _
    rw [getD_read, arr_getD]
  have hbe : sc.be = ρ.val beta := by rw [hsc]; rfl
  -- the end values' slots
  have hEnd : ∀ i, i < v.size → FormIs ρ G (Aff.slot (F.next + 1 + 3 + i)) (sc.v i)
      [((N.ledTie n).sh i, sc.be)] := by
    intro i hi
    obtain ⟨_, _, e3, e4, e5⟩ := hin1 i hi
    have := (slot_formIs ρ e3).later ρ hL2
    rw [e4, e5] at this
    rw [hv', hbe, l2 i hi]
    exact this
  have hnx : nxAt n + 1 = ptAt n ∧ ptAt n < v.size ∧
      (if n = 0 then F.next + 1 + 3 + 1 else F.next + 1 + 3) = F.next + 1 + 3 + nxAt n := by
    unfold nxAt ptAt
    by_cases h0 : n = 0 <;> simp [h0, hv]
  obtain ⟨hn1, hn2, hn3⟩ := hnx
  rw [hn3] at hvP hvG
  have evP : ρ.val vP = sc.v (nxAt n) := by
    rw [(shown_val hvP).2.2, (hin1 (nxAt n) (by omega)).2.2.2.1, hv']
  have evG : ρ.val vG = sc.v (ptAt n) := by
    rw [(shown_val hvG).2.2, Nat.add_assoc (F.next + 1 + 3), hn1,
      (hin1 (ptAt n) hn2).2.2.2.1, hv']
  have hS0 : ρ.val summand = tieS0 N lam n sc := by
    unfold tieS0
    by_cases h0 : n = 0
    · rw [if_pos h0] at hsum ⊢
      obtain ⟨vZ, hvZ, rfl⟩ := hsum
      have evZ : ρ.val vZ = sc.v 0 := by
        have h3 : 0 < v.size := by omega
        have := (hin1 0 h3).2.2.2.1
        rw [Nat.add_zero] at this
        rw [(shown_val hvZ).2.2, this, hv']
      have e1 : nxAt n = 1 := by simp [nxAt, h0]
      have e2 : ptAt n = 2 := by simp [ptAt, h0]
      rw [e1] at evP
      rw [e2] at evG
      rw [ρ.sub, ρ.mul, ρ.mul, ρ.mul, evZ, evP, evG, ha]
      ring
    · rw [if_neg h0] at hsum ⊢
      have e1 : nxAt n = 0 := by simp [nxAt, h0]
      have e2 : ptAt n = 1 := by simp [ptAt, h0]
      rw [e1] at evP
      rw [e2] at evG
      rw [hsum, ρ.mul, ρ.mul, evP, evG]
      ring
  -- the step's claim
  have hRow : RowIs ρ G ((tiePsc C target mu eps beta F.next sent).rowForm summand {})
      (rowU (N.ledTie n) [3] sc (tieInc N scs.reverse) (tieS0 N lam n sc)) := by
    intro H hH mask entry
    rw [← hS0, hsc]
    refine tieRow_value ρ (H.worldOf ρ mask entry) mask C target mu eps beta summand F.next sent
      _ _ (N.ledTie n) (hLed.hide K [ρ.val beta] mask rfl) ?_ ?_
    · intro i hi
      obtain ⟨_, _, e3, e4, e5⟩ := hin2 i (by rw [Array.size_replicate, hwl]; exact hi)
      obtain ⟨_, k2, k3⟩ := hH.keep _ e3
      show ρ.val (H.vp.getD (F.next + i) zeroE) - ρ.val (H.mf.getD (F.next + i) zeroE) *
        mask (F.next + i) = _
      rw [k2, k3, e4, e5, ρ.sub, ρ.zero, ρ.one]
      have : (Array.replicate (tiePsc C target mu eps beta F.next sent).walk.1.length zeroE).getD i
          zeroE = zeroE := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
        split_ifs <;> rfl
      rw [this, ρ.zero]
      ring
    · rw [htg]
      exact (hsP H ((hL1.trans hL2).trans hH)).2 mask entry
  have hrev : (scs ++ [sc]).reverse = sc :: scs.reverse := by
    rw [List.reverse_append]
    rfl
  have hlr : scs.reverse.length = n := by rw [List.length_reverse, inv.len]
  have hsz : (Array.replicate (tiePsc C target mu eps beta F.next sent).walk.1.length
      zeroE).size = 4 := by rw [Array.size_replicate, hwl]
  refine ⟨mu, eps, sent, beta, v, sc, hev, fun rest => ?_, hL1.trans hL2, ?_, ?_, ?_, ?_, hs, hv⟩
  rotate_right
  · intro j hj
    rw [← hv] at hj
    have o2 := hout2 j (by rw [hsz]; omega)
    have o1 := hout1 j (by omega)
    exact ⟨o2.1.trans o1.1, o2.2.1.trans o1.2.1⟩
  · rw [← htg, hsc]
    exact step_take ρ C target mu eps beta F.next sent _ v hs rest
  · rw [← took_took]
    exact hS1.trans hS2
  · intro j
    rw [← hv]
    by_cases hA : F.next ≤ j ∧ j < F.next + 4
    · have e := (hin2 (j - F.next) (by rw [hsz]; omega)).2.2.1
      rw [show F.next + (j - F.next) = j by omega] at e
      exact ⟨fun _ => Or.inr ⟨hA.1, by omega⟩, fun _ => e⟩
    · have o2 := (hout2 j (by rw [hsz]; omega)).2.2
      by_cases hB : F.next + 1 + 3 ≤ j ∧ j < F.next + 1 + 3 + v.size
      · have e := (hin1 (j - (F.next + 1 + 3)) (by omega)).2.2.1
        rw [show F.next + 1 + 3 + (j - (F.next + 1 + 3)) = j by omega] at e
        exact ⟨fun _ => Or.inr ⟨by omega, by omega⟩, fun _ => o2.2 e⟩
      · have o1 := (hout1 j (by omega)).2.2
        refine (o2.trans o1).trans ⟨fun hf => Or.inl hf, fun hf => ?_⟩
        rcases hf with hf | hf
        · exact hf
        · omega
  · refine
      { len := by rw [List.length_append, inv.len]; rfl
        sized := hZ2
        next := ?_
        rowsN := by rw [Array.size_push, inv.rowsN]
        rows := ?_
        sZ := ?_
        sP := ?_
        sGN := by rw [Array.size_push, inv.sGN]
        sG := ?_ }
    · rw [hS2.next, hS1.next]
      show F.next + 1 + (3 + if n = 0 then 3 else 2) = base + tieOff (n + 1)
      rw [inv.next]
      cases n with
      | zero => simp [tieOff]
      | succ m =>
        simp only [tieOff, Nat.succ_ne_zero, if_false]
        omega
    · intro i hi
      rw [push_getD, inv.rowsN, hrev]
      show RowIs ρ G _ ((rowU (N.ledTie scs.reverse.length) [3] sc (tieInc N scs.reverse)
        (tieS0 N lam scs.reverse.length sc) :: tieRowsR N lam scs.reverse).reverse.getD i ⟨[], 0⟩)
      rw [List.reverse_cons, snoc_getD, List.length_reverse, tieRowsR_len, hlr]
      by_cases hi' : i < n
      · rw [if_pos hi', if_pos hi']
        exact (inv.rows i hi').later ρ (hL1.trans hL2)
      · have hin : i = n := by omega
        rw [if_neg hi', if_neg hi', if_pos hin, if_pos hin, ← hC]
        exact hRow
    · intro _
      by_cases h0 : n = 0
      · subst h0
        have h3 : 0 < v.size := by omega
        have e := hEnd 0 h3
        have hb : F.next = base := by rw [inv.next]; rfl
        have hnil : scs = [] := List.length_eq_zero_iff.mp inv.len
        subst hnil
        refine ⟨by simp only [if_true]; omega, ?_⟩
        simp only [if_true]
        exact e
      · have hpos : 0 < n := Nat.pos_of_ne_zero h0
        obtain ⟨z1, z2⟩ := inv.sZ hpos
        have e0 : (scs ++ [sc]).getD 0 Sc.zero = scs.getD 0 Sc.zero := by
          rw [snoc_getD, if_pos (by rw [inv.len]; exact hpos)]
        rw [e0]
        simp only [if_neg h0]
        exact ⟨z1, z2.later ρ (hL1.trans hL2)⟩
    · rw [if_neg (Nat.succ_ne_zero n), hrev]
      have e := hEnd (nxAt n) (by omega)
      have et : tgEnd 0 0 (scs ++ [sc]) = sc.v (nxAt n) := by
        unfold tgEnd
        rw [List.getLast?_append, List.length_append, inv.len]
        simp
      rw [et]
      show FormIs ρ G (Aff.slot (if n = 0 then F.next + 1 + 3 + 1 else F.next + 1 + 3)) _
        [((N.ledTie scs.reverse.length).sh (nxAt scs.reverse.length), sc.be)]
      rw [hn3, hlr]
      exact e
    · intro i hi
      rw [push_getD, inv.sGN, snoc_getD, inv.len]
      by_cases hi' : i < n
      · rw [if_pos hi', if_pos hi']
        exact (inv.sG i hi').later ρ (hL1.trans hL2)
      · have hin : i = n := by omega
        rw [if_neg hi', if_neg hi', if_pos hin, if_pos hin, hin, hn3,
          Nat.add_assoc (F.next + 1 + 3), hn1]
        exact hEnd (ptAt n) hn2

end
end Fo
