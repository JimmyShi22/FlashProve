-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Out/TwRoot.lean.
The two targets at which the trees of the assembled lookup start are those of the flat function.

Statements and proofs: algebra on states alone; no transcript, no block.
Main names:
  `tK_eq`: the target of the masked claim on the keys' product (`A.tK`) is `TwV.tK` at a trace whose
    tie is `tieN` (Cb/Pv/Lookup/Out/TwTraceOf.lean), the oldest first.
  `tgT0_eq`: the target that the planes' point hands to the table's level 0, the sum over θ of
    eq(ϱ, θ) · `A.tgtT x θ`, is `TwV.tgT0` at that trace with join := ϱ as a list. Its premise hx:
    the target x.1 of the tie's open claim is the shown value that the newest step hands on. On a
    run it holds, by the definition `TieF.nxt`: `tie_tg`, Cb/Pv/Lookup/Out/TwLev.lean.
  Beside them: `tieN_len`; `tie_last`, `tie_lt` (the members of the reversed list); `bK_snd`,
    `bT_snd`, `nx_val` (three readings, by induction down the nest); `tgtT_eq` (corner by corner).
Limits: equations at states, reached by a run or not; nothing on what a verifier accepts. st and kAt
enter through `numsOf` alone, of which `TwV.tgT0` reads only n and w.
Not claimed: anything on soundness, completeness or hiding.

-/
import Cb.Pv.Lookup.Out.TwTraceOf

set_option autoImplicit false

namespace Tw3
open TwV Cb Cb.Tw Cb.LdLkp

section
variable {E : Type} [Field E] [Fintype E] (D : TieF E)

theorem tieN_len : ∀ (l : ℕ) (s : (D.lv l).T.St), (tieN D l s).length = l
  | 0, _ => rfl
  | l + 1, s => congrArg (· + 1) (tieN_len l s.st)

/-- the newest step stands last in the reversed list -/
theorem tie_last (l : ℕ) (s : (D.lv (l + 1)).T.St) (z : Sc E) :
    (tieN D (l + 1) s).reverse.getD l z = scOf (D.lv l).T.par (tieSh D l) s := by
  show (scOf (D.lv l).T.par (tieSh D l) s :: tieN D l s.st).reverse.getD l z = _
  rw [List.reverse_cons, List.getD_append_right _ _ _ _ (by rw [List.length_reverse, tieN_len])]
  rw [List.length_reverse, tieN_len, Nat.sub_self]
  rfl

/-- the older steps stand where they stood -/
theorem tie_lt (l : ℕ) (s : (D.lv (l + 1)).T.St) (z : Sc E) (j : ℕ) (hj : j < l) :
    (tieN D (l + 1) s).reverse.getD j z = (tieN D l s.st).reverse.getD j z := by
  show (scOf (D.lv l).T.par (tieSh D l) s :: tieN D l s.st).reverse.getD j z = _
  rw [List.reverse_cons, List.getD_append _ _ _ _ (by rw [List.length_reverse, tieN_len]; exact hj)]

theorem bK_snd : ∀ (l : ℕ) (s : (D.lv (l + 1)).T.St),
    (D.bK l s).2 = ((tieN D (l + 1) s).reverse.getD 0 Sc.zero).v 0
  | 0, s => by
    rw [tie_last D 0 s]
    rfl
  | l + 1, s => by
    rw [tie_lt D (l + 1) s _ 0 (Nat.succ_pos l)]
    exact bK_snd l s.st

theorem bT_snd : ∀ (l : ℕ) (s : (D.lv (l + 1)).T.St) (j : ℕ), j ≤ l →
    (D.bT l s j).2 = ((tieN D (l + 1) s).reverse.getD j Sc.zero).v (ptAt j)
  | 0, s, j, hj => by
    obtain rfl : j = 0 := Nat.le_zero.1 hj
    rw [tie_last D 0 s]
    rfl
  | l + 1, s, j, hj => by
    by_cases h : j = l + 1
    · subst h
      rw [tie_last D (l + 1) s]
      show (if l + 1 = l + 1 then (D.be (l + 1) s, s.vals true) else D.bT l s.st (l + 1)).2 = _
      rw [if_pos rfl]
      rfl
    · rw [tie_lt D (l + 1) s _ j (by omega)]
      show (if j = l + 1 then (D.be (l + 1) s, s.vals true) else D.bT l s.st j).2 = _
      rw [if_neg h]
      exact bT_snd l s.st j (by omega)

theorem nx_val (l : ℕ) (s : (D.lv (l + 1)).T.St) :
    (show (D.lv l).T.par.Out from s).vals (D.lv l).nx = ((tieN D (l + 1) s).reverse.getD l
        Sc.zero).v (nxAt l) := by
  rw [tie_last D l s]
  cases l <;> rfl

end

section
variable {E : Type} [Field E] [Fintype E] (A : LkAsmH E)

theorem tK_eq (x : A.X2) (t : TwV.Trace E) (ht : t.tie = (tieN A.H.tie (A.n + 1) x.2).reverse) :
    A.tK x = TwV.tK t := by
  unfold TwV.tK LkAsmH.tK
  rw [ht]
  exact bK_snd A.H.tie A.n x.2

theorem tgtT_eq (st : A.St) (kAt : ℕ → A.J ⊕ E) (x : A.X2)
    (hx : x.1 = (show (A.H.tie.lv A.n).T.par.Out from x.2).vals (A.H.tie.lv A.n).nx) (t : TwV.Trace
        E)
    (ht : t.tie = (tieN A.H.tie (A.n + 1) x.2).reverse) (θ : Fin (A.w + 0) → Bool) :
    A.tgtT x θ = TwV.tgtT (numsOf A st kAt) t (numLE θ) := by
  unfold TwV.tgtT LkAsmH.tgtT
  show _ = if numLE θ < A.n + 1 then _ else if numLE θ = A.n + 1 then (t.tie.getD A.n Sc.zero).v
      (nxAt A.n) else 1
  rw [ht]
  by_cases h1 : numLE θ < A.n + 1
  · rw [if_pos h1, if_pos h1]
    exact bT_snd A.H.tie A.n x.2 _ (by omega)
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : numLE θ = A.n + 1
    · rw [if_pos h2, if_pos h2, hx]
      exact nx_val A.H.tie A.n x.2
    · rw [if_neg h2, if_neg h2]

theorem tgT0_eq (st : A.St) (kAt : ℕ → A.J ⊕ E) (x : A.X2)
    (hx : x.1 = (show (A.H.tie.lv A.n).T.par.Out from x.2).vals (A.H.tie.lv A.n).nx) (ϱ : Fin (A.w +
        0) → E)
    (t : TwV.Trace E) (ht : t.tie = (tieN A.H.tie (A.n + 1) x.2).reverse) (hj : t.join = List.ofFn
        ϱ) :
    (A.R.toIn.nxX x ϱ).1 = TwV.tgT0 (numsOf A st kAt) t := by
  unfold TwV.tgT0
  rw [hj, sum_map_range]
  show (∑ θ : Fin (A.w + 0) → Bool, Alg.eqk ϱ θ * A.tgtT x θ) =
    ∑ th ∈ Finset.range (2 ^ (A.w + 0)), eqN (List.ofFn ϱ) th * TwV.tgtT (numsOf A st kAt) t th
  rw [← ldLkpNum_sum E (A.w + 0)]
  exact Finset.sum_congr rfl fun θ _ => by rw [eqN_ofFn, tgtT_eq A st kAt x hx t ht θ]

end
end Tw3
#print axioms Tw3.tK_eq
#print axioms Tw3.tgT0_eq
