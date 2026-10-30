-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoVal.lean: a definition of «the letters of an assembled lookup are
those of the lookup that the sub-proofs' verifier runs», and that the builder forA meets it.

The knowledge-soundness statement of a sub-proof's lookup (HC,
OnBytes/Tie/Pv/Lookup/Holes/HoleC.lean) is stated for every record A0 of the chain's letters: sizes,
padding, orders of binding, places of the planes' bits and of the mask entries. It says nothing on
which record belongs to a given forest. IsPortAt h A bc zero mk says it, field by field, in
functions of the verifier's record of public numbers h (OnBytes.Model.Forest.Shape): the verifier's
own functions for sizes and orders, those of OnBytes/Tie/Pv/Lookup/Port/FoNums.lean for padding and
masks:
 - sizes: 2^(v' + 1) keys with v' + 1 = h.v, 2^d rows with d = h.d, 2^5 planes, all 32 of which
   count (n counts the tie's steps less one);
 - padding: for each call the row of the joined table that its padding keys hold, and how many keys
   hold it;
 - orders: round j of a sumcheck binds the variable that the verifier's list names in place j;
   variable t is bit t of an index. At a key level the list is the one that Forest.pad passes to
   Forest.level; at a table level orderDefault; at the leaves and at the bits the verifier walks the
   point's array from place 0 up, and place i of an array of k coordinates holds variable k - 1 - i;
 - bits: bit j of the count of row u = (t | c) is the caller's entry bc t c j if c is the number of
   a call, and the entry zero otherwise (the verifier has no cell there);
 - masks: each of the ten families of mask places is the caller's entry mk s, where s is the number,
   counted from the lookup's first scalar, of the scalar that the place masks.
The three letters St, key and tab are not named: ShiftQ.asmH overwrites them with the state that
holds the shift and with the shifted joint vectors.

Main definitions: IsPortAt, HCval. Main theorems: hCval (forA meets IsPortAt wherever FoNums.ok h
holds), IsPortAt.premises (IsPortAt, FoNums.ok h and 2^d (2^32 - 1) < p give the seven premises of
HC).
Not claimed: that the product of (alpha - row)^count over the pairs of the field pads is the public
factor that Forest.draws computes (that the counts sum to Shape.padding is pads_sum,
OnBytes/Tie/Pv/Lookup/Forest/FoPadSum.lean);
that the numbering of scalars in FoNums.S is the order in which the verifier takes its slots, or
that it numbers as many as Forest.elems h.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoTies

set_option autoImplicit false

namespace Cb.Fo
open Iop Prob Hiop IOR Cb Cb.LdLkp Cb.Lkp
open Cb.Tw (pEnt)

/-- The letters of A are those of the verifier's lookup at the public numbers h, over the caller's
places bc, zero, mk. -/
structure IsPortAt {E : Type} [Field E] [Fintype E] (h : Sh) (A : LkAsmH E) (bc : ℕ → ℕ → ℕ → A.J)
    (zero : A.J) (mk : ℕ → A.J) : Prop where
  v : A.v' + 1 = h.v
  d : A.d = h.d
  w : A.w = 5
  n : A.n = 30
  pads : A.pads = (List.range h.NC).map fun c => (FoNums.padRow h c, FoNums.padCount h c)
  oK : ∀ l, E3.asList (A.oK l) =
    if (0 + l) + 1 = h.v then OnBytes.Model.Forest.orderForestRange (0 + l) h.rK else
        OnBytes.Model.orderDefault (0 + l)
  oT : ∀ l, E3.asList (A.oT l) = OnBytes.Model.orderDefault (A.w + l)
  oE : E3.asList A.oE = (List.range (A.w + A.d)).map fun i => A.w + A.d - 1 - i
  oB : E3.asList A.oB = (List.range (A.w + A.d)).map fun i => A.w + A.d - 1 - i
  bAt : ∀ u j, A.bAt u j = if u % 2 ^ h.cK < h.NC then bc (u / 2 ^ h.cK) (u % 2 ^ h.cK) j else zero
  wAt : ∀ j i, A.wAt j i = mk ((FoNums.S h).pTie j (pEnt _ i))
  cZ : A.cZ = mk ((FoNums.S h).pTie 0 (.shown 0))
  cAt : ∀ j b, A.cAt j b = mk
      ((FoNums.S h).pTie j (.shown ((if j = 0 then 1 else 0) + if b then 1 else 0)))
  wK : ∀ l i, A.wK l i = mk ((FoNums.S h).pKey l (pEnt _ i))
  cK : ∀ l b, A.cK l b = mk ((FoNums.S h).pKey l (.shown (if b then 1 else 0)))
  wT : ∀ l i, A.wT l i = mk ((FoNums.S h).pTab l (pEnt _ i))
  cT : ∀ l b, A.cT l b = mk ((FoNums.S h).pTab l (.shown (if b then 1 else 0)))
  wE : ∀ i, A.wE i = mk ((FoNums.S h).pEnd (pEnt _ i))
  wB : ∀ i, A.wB i = mk ((FoNums.S h).pBit (pEnt _ i))
  cB : A.cB = mk ((FoNums.S h).pBit (.shown 0))

/-- The builder's letters meet IsPortAt, at every forest whose public numbers pass FoNums.ok. -/
def HCval : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (St₀ J₀ : Type) [Fintype J₀] [DecidableEq J₀] (h : Sh)
      (L : Lay E St₀ J₀),
    FoNums.ok h = true →
    IsPortAt h (forA E h L) (fun t c j => some (L.bc t c j)) none (fun s => some (L.mkS s))

theorem hCval : HCval := by
  intro E _ _ St₀ J₀ _ _ h L H
  refine
    { v := (ok_v H).symm, d := rfl, w := rfl, n := rfl, pads := rfl, oK := tie_oK E h L H, oT :=
        tie_oT E h L,
      oE := tie_oE E h L, oB := tie_oB E h L, bAt := ?_, wAt := fun _ _ => rfl, cZ := rfl, cAt :=
          ?_,
      wK := fun _ _ => rfl, cK := ?_, wT := fun _ _ => rfl, cT := ?_, wE := fun _ => rfl, wB :=
          fun _ => rfl, cB := rfl }
  · intro u j
    by_cases hc : u % 2 ^ h.cK < h.NC
    · rw [if_pos hc]
      exact tie_bAt_cell E h L u j hc
    · rw [if_neg hc]
      exact (tie_bAt_none E h L u j hc fun _ => 0).1
  · intro j b
    by_cases hj : j = 0 <;> cases b <;> simp [forA, hj, TwNums.shownTie0, TwNums.shownBool]
  · intro l b
    cases b <;> rfl
  · intro l b
    cases b <;> rfl

/-- IsPortAt, the test on the public numbers and «the counts' sum cannot wrap around» give the seven
premises of HC. -/
theorem IsPortAt.premises {E : Type} [Field E] [Fintype E] {h : Sh} {A : LkAsmH E}
    {bc : ℕ → ℕ → ℕ → A.J} {zero : A.J} {mk : ℕ → A.J}
    (I : IsPortAt h A bc zero mk) (H : FoNums.ok h = true) {p : ℕ} (hp : 2 ^ h.d * (2 ^ 32 - 1) < p)
        :
    Port.OK h ∧ h.NC ≤ p ∧ h.v = A.v' + 1 ∧ h.d = A.d ∧ A.H.lkb.Adm p ∧ padsOK (A.v' + 1) A.d A.pads
        = true ∧ A.n + 1 + 1 = 2 ^ A.w := by
  obtain ⟨⟨_, _, _, _, a5, _⟩, _, _, d, e, _⟩ := ok_parts H
  refine ⟨ok_portOK H, ok_NC H hp, I.v.symm, I.d.symm, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · show A.n + 2 ≤ 2 ^ A.w
    rw [I.n, I.w]
    decide
  · show 2 ^ (A.v' + 1) < 2 ^ (A.n + 2)
    rw [I.v, I.n]
    exact Nat.pow_lt_pow_right (by norm_num) a5
  · show 2 ^ A.d * (2 ^ (A.n + 2) - 1) < p
    rw [I.d, I.n]
    exact hp
  · rw [I.v, I.d, I.pads]
    unfold padsOK padNum
    rw [Bool.and_eq_true]
    exact ⟨List.all_eq_true.2 fun x hx => decide_eq_true (d x hx), decide_eq_true e⟩
  · rw [I.n, I.w]
    decide

end Cb.Fo
