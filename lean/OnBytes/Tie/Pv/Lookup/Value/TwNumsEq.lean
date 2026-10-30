-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Value/TwNumsEq.lean.
One public quantity, described twice, tied: the numbers and places read off the typed value
`keyA E S` are the record `numsJ E S`, which is made for the flat function `TwV.vOf`.

Statements and proofs. `numsOf A st kAt` (Cb/Pv/Lookup/Out/TwTraceOf.lean) reads the public numbers
and places off a typed value; `numsJ E S` (OnBytes/Tie/Pv/Lookup/Out/TwVN.lean) reads them off
OnBytes/Tie/Pv/Lookup/Port/TwNums.lean.
Main names:
  `numsOf_keyA`: `numsOf (keyA E S) () (kAt E S) = numsJ E S`: an equation of records, general in S
    under the two clauses of `Lkp.Public.orderOK` on the last key level's order.
  `numsOf_keyA_ok`: the same at every S with `S.ok`. `o65_nums`: at the small lookup, no premise.
  `ofFn_default`, `ofFn_keyW`: the orders as lists.
  `tv_deg_end`, `tv_nx`, `tv_pt`: `TwV.dgE`, `TwV.nxAt`, `TwV.ptAt` (Cb/Pv/Lookup/Out/TwV.lean) are
    the closing's degrees and numbers of shown values of OnBytes/Tie/Pv/Lookup/Port/TwNums.lean.
  `tv_deg_tie`, `tv_deg_key`, `tv_deg_tab`, `tv_deg_bit`: the lists [3] and replicate .. 2 ++ [2],
    typed here as they stand inside definitions of Cb/Pv/Lookup/Out/TwV.lean, are `Sc.degs`.
Limits: an equation between two readings of public data; it says nothing on a transcript. The left
sides of `tv_deg_tie` to `tv_deg_bit` name nothing of Cb/Pv/Lookup/Out/TwV.lean: if its lists
turned, these four would still hold.

-/
import Cb.Pv.Lookup.Out.TwTraceOf
import OnBytes.Tie.Pv.Lookup.Out.TwVN
import OnBytes.Tie.Pv.Lookup.Port.TwTies

set_option autoImplicit false

namespace Tw3
open TwV Cb Cb.Tw Cb.LdLkp
open TwNums (Sizes Sc o65S)
open TwNums.Sizes (Ent)

/-! ### the names of PIdx and the mask entries -/
section
variable {E : Type}

theorem pEnt_pEnd : ∀ l : List (PFmt E), pEnt l (pEnd l) = .const
  | [] => rfl
  | _ :: l => by
    show (match pEnt l (pEnd l) with
      | .coef j t => Ent.coef (j + 1) t
      | e => e) = _
    rw [pEnt_pEnd l]

theorem pEnt_pAt : ∀ (l : List (PFmt E)) (r t : ℕ),
    pEnt l (pAt l r t) = if t < (l.map PFmt.n).getD r 0 then .coef r t else .const
  | [], _, _ => by simp [pEnt]
  | f :: l, 0, t => by
    show pEnt (f :: l) (if h : t < f.n then .inl ⟨t, h⟩ else .inr (pEnd l)) = if t < f.n then _ else
        _
    by_cases h : t < f.n
    · rw [dif_pos h, if_pos h]; rfl
    · rw [dif_neg h, if_neg h]; exact pEnt_pEnd (f :: l)
  | f :: l, r + 1, t => by
    show (match pEnt l (pAt l r t) with
      | .coef j t => Ent.coef (j + 1) t
      | e => e) = if t < (l.map PFmt.n).getD r 0 then _ else _
    rw [pEnt_pAt l r t]
    by_cases h : t < (l.map PFmt.n).getD r 0
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]

/-- a sumcheck's places at the builder are the clamped places of
OnBytes/Tie/Pv/Lookup/Port/TwNums.lean -/
theorem led_eq (S : Sizes) (l : List (PFmt E)) (c : Sc) (hd : l.map PFmt.n = c.degs) (pl : Ent → ℕ)
    (sh : ℕ → JOf S)
    (hs : ∀ a, sh a = mkM S (pl (Ent.clamp c (.shown a)))) :
    ledOf l (fun i => mkM S (pl (pEnt l i))) sh = ledJ S fun e => pl (Ent.clamp c e) := by
  have e1 : (fun r t => mkM S (pl (pEnt l (pAt l r t)))) = fun r t => mkM S
      (pl (Ent.clamp c (.coef r t))) := by
    funext r t
    rw [pEnt_pAt, hd]
    rfl
  have e2 : mkM S (pl (pEnt l (pEnd l))) = mkM S (pl (Ent.clamp c .const)) := by
    rw [pEnt_pEnd]
    rfl
  have e3 : sh = fun a => mkM S (pl (Ent.clamp c (.shown a))) := funext hs
  show (⟨fun r t => mkM S (pl (pEnt l (pAt l r t))), mkM S (pl (pEnt l (pEnd l))), sh⟩ : Led
      (JOf S)) =
    ⟨fun r t => mkM S (pl (Ent.clamp c (.coef r t))), mkM S (pl (Ent.clamp c .const)),
        fun a => mkM S (pl (Ent.clamp c (.shown a)))⟩
  rw [e1, e2, e3]

end

/-! ### the orders as lists -/

theorem ofFn_permOfList (k : ℕ) (l : List ℕ) (h : l.Perm (List.range k)) :
    (List.ofFn fun j : Fin k => ((E3.permOfList k l h j : Fin k) : ℕ)) = l := by
  have hl : l.length = k := by rw [h.length_eq, List.length_range]
  refine List.ext_getElem (by rw [List.length_ofFn, hl]) fun i h1 h2 => ?_
  rw [List.getElem_ofFn]
  rfl

theorem ofFn_default (k : ℕ) : (List.ofFn fun j : Fin k => ((E3.ordDefault k j : Fin k) : ℕ)) =
    OnBytes.Lkp.defaultOrder k := by
  rw [E3.ordDefault_eq, ofFn_permOfList]
  rfl

theorem ofFn_keyW (v : ℕ) (first : List ℕ) (k : ℕ) (h1 : ∀ j ∈ first, j + 1 < v) (h2 : first.Nodup)
    :
    (List.ofFn fun j : Fin k => ((E3.ordKeyW v first k j : Fin k) : ℕ)) =
      if k + 1 = v then OnBytes.Lkp.orderBeginning first k else OnBytes.Lkp.defaultOrder k := by
  unfold E3.ordKeyW
  by_cases hk : k + 1 = v
  · have h : k + 1 = v ∧ (∀ j ∈ first, j < k) ∧ first.Nodup :=
    ⟨hk, fun j hj => by have := h1 j hj; omega, h2⟩
    rw [dif_pos h, if_pos hk]
    exact ofFn_permOfList k _ _
  · rw [dif_neg (fun h => hk h.1), if_neg hk]
    exact ofFn_default k

/-! ### the records -/
section
variable (E : Type) [Field E] [Fintype E] (S : Sizes)

theorem tie_sh (l a : ℕ) : tiePl (keyA E S) l a = mkM S
    (S.pTie l (Ent.clamp (S.scTie l) (.shown a))) := by
  cases l with
  | zero =>
    rcases a with _ | _ | a
    · rfl
    · rfl
    · show mkM S (S.pTie 0 (.shown 2)) = mkM S (S.pTie 0 (.shown (min (a + 2) 2)))
      rw [Nat.min_eq_right (by omega)]
  | succ l =>
    rcases a with _ | a
    · rfl
    · show mkM S (S.pTie (l + 1) (.shown 1)) = mkM S (S.pTie (l + 1) (.shown (min (a + 1) 1)))
      rw [Nat.min_eq_right (by omega)]

theorem two_sh (pl : Ent → ℕ) (c : Sc) (hc : c.shown = 2) (a : ℕ) :
    mkM S (pl (.shown (TwNums.shownBool (decide (a ≠ 0))))) = mkM S (pl (Ent.clamp c (.shown a))) :=
      by
  show _ = mkM S (pl (if c.shown = 0 then .const else .shown (min a (c.shown - 1))))
  rw [hc, if_neg (by decide)]
  rcases a with _ | a
  · rfl
  · show mkM S (pl (.shown 1)) = mkM S (pl (.shown (min (a + 1) 1)))
    rw [Nat.min_eq_right (by omega)]

theorem mix_degs : ∀ (k : ℕ) (dg : Fin k → ℕ), (pfMix E k dg).map PFmt.n = List.ofFn dg
  | 0, _ => rfl
  | k + 1, dg => by
    show dg 0 :: (pfMix E k fun i => dg i.succ).map PFmt.n = _
    rw [mix_degs k, List.ofFn_succ]

/-- the closing's formats have the degrees of OnBytes/Tie/Pv/Lookup/Port/TwNums.lean: general in S
-/
theorem degs_endS : (pfMix E (S.w + S.d) (dgEnd S.w S.d (E3.ordDefault (S.w + S.d)))).map PFmt.n =
    S.scEnd.degs := by
  rw [mix_degs]
  show _ = S.ordE.map fun t => if t < S.w then 1 else 2
  rw [show S.ordE = OnBytes.Lkp.defaultOrder (S.w + S.d) from rfl, ← ofFn_default, List.map_ofFn]
  rfl

theorem numsOf_keyA (h1 : ∀ j ∈ S.first, j + 1 < S.v) (h2 : S.first.Nodup) :
    numsOf (keyA E S) () (kAt E S) = numsJ E S := by
  have hoK : (fun l => List.ofFn fun j : Fin (0 + l) => (((keyA E S).oK l j : Fin (0 + l)) : ℕ)) =
      S.ordK := by
    funext l
    refine (ofFn_keyW S.v S.first (0 + l) h1 h2).trans ?_
    rw [Nat.zero_add]
    rfl
  have hoT : (fun l => List.ofFn fun j : Fin ((keyA E S).w + l) =>
      (((keyA E S).oT l j : Fin ((keyA E S).w + l)) : ℕ)) = S.ordT :=
    funext fun l => ofFn_default (S.w + l)
  have hoE : (List.ofFn fun j : Fin ((keyA E S).w + (keyA E S).d) =>
      (((keyA E S).oE j : Fin _) : ℕ)) = S.ordE := ofFn_default (S.w + S.d)
  have hoB : (List.ofFn fun j : Fin ((keyA E S).w + (keyA E S).d) =>
      (((keyA E S).oB j : Fin _) : ℕ)) = S.ordB := ofFn_default (S.w + S.d)
  have hTie : (fun l => ledOf _ ((keyA E S).wAt l) (tiePl (keyA E S) l)) = fun j => ledJ S
      (S.pTieC j) :=
    funext fun l => led_eq S _ (S.scTie l) (degs_tie E S l) (S.pTie l) _ (tie_sh E S l)
  have hK : (fun l => ledOf _ ((keyA E S).wK l) fun a => (keyA E S).cK l (decide (a ≠ 0))) = fun l
      => ledJ S (S.pKeyC l) :=
    funext fun l => led_eq S _ (S.scKey l) (degs_key E S l) (S.pKey l) _ (two_sh S (S.pKey l) _ rfl)
  have hT : (fun l => ledOf _ ((keyA E S).wT l) fun a => (keyA E S).cT l (decide (a ≠ 0))) = fun l
      => ledJ S (S.pTabC l) :=
    funext fun l => led_eq S _ (S.scTab l) (degs_tab E S l) (S.pTab l) _ (two_sh S (S.pTab l) _ rfl)
  have hB : (ledOf _ (keyA E S).wB fun _ => (keyA E S).cB) = ledJ S S.pBitC :=
    led_eq S _ S.scBit (degs_bit E S) S.pBit _ fun a => by
      show mkM S (S.pBit (.shown 0)) = mkM S (S.pBit (.shown (min a 0)))
      rw [Nat.min_eq_right (Nat.zero_le a)]
  have hE0 :=
    led_eq S _ S.scEnd (degs_endS E S) S.pEnd (fun a => mkM S
        (S.pEnd (Ent.clamp S.scEnd (.shown a)))) fun _ => rfl
  have hE : (ledOf _ (keyA E S).wE fun _ => (keyA E S).cB) =
      ⟨(ledJ S S.pEndC).pw, (ledJ S S.pEndC).c0, fun _ => mkM S (S.pBit (.shown 0))⟩ :=
    congrArg₂ (fun a b => (⟨a, b, fun _ => mkM S (S.pBit (.shown 0))⟩ : Led (JOf S)))
        (congrArg Led.pw hE0) (congrArg Led.c0 hE0)
  unfold numsOf numsJ
  rw [hoK, hoT, hoE, hoB, hTie, hK, hT, hE, hB]
  rfl

end

/-! ### what Cb/Pv/Lookup/Out/TwV.lean types a second time beside `Sc` of
OnBytes/Tie/Pv/Lookup/Port/TwNums.lean: the degrees by round and the numbers of the shown values.
The first four left sides are typed here a third time; the last three name that file's
definitions. -/
section
variable (S : Sizes)
theorem tv_deg_tie (j : ℕ) : ([3] : List ℕ) = (S.scTie j).degs := rfl
theorem tv_deg_key (l : ℕ) : List.replicate (0 + l) 2 ++ [2] = (S.scKey l).degs := by
  rw [Nat.zero_add]; rfl
theorem tv_deg_tab (l : ℕ) : List.replicate (S.w + l) 2 ++ [2] = (S.scTab l).degs := rfl
theorem tv_deg_bit : List.replicate (S.w + S.d) 2 ++ [2] = S.scBit.degs := rfl
theorem tv_deg_end (K : Type) [Field K] : TwV.dgE (numsJ K S) = S.scEnd.degs := rfl
/-- the value that the next step takes up is the power; the other the plane's product: in the
numbering of the shown values of OnBytes/Tie/Pv/Lookup/Port/TwNums.lean -/
theorem tv_nx : ∀ l, TwV.nxAt l = if l = 0 then TwNums.shownTie0 (some false) else TwNums.shownBool
    false
  | 0 => rfl
  | _ + 1 => rfl
theorem tv_pt : ∀ l, TwV.ptAt l = if l = 0 then TwNums.shownTie0 (some true) else TwNums.shownBool
    true
  | 0 => rfl
  | _ + 1 => rfl
end

/-- at every S with `S.ok` -/
theorem numsOf_keyA_ok (E : Type) [Field E] [Fintype E] (S : Sizes) (h : S.ok = true) : numsOf
    (keyA E S) () (kAt E S) = numsJ E S := by
  unfold Sizes.ok at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact numsOf_keyA E S h.1.2 h.2

/-- at the small lookup: no premise -/
theorem o65_nums : numsOf o65A () (kAt Cb.Gl.E o65S) = numsJ Cb.Gl.E o65S :=
  numsOf_keyA Cb.Gl.E o65S (by decide) (by decide)

end Tw3
#print axioms Tw3.numsOf_keyA
#print axioms Tw3.o65_nums
#print axioms Tw3.numsOf_keyA_ok
