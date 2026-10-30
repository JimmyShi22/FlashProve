-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchFresh.lean: the closing of a segment (K10): the pairing of the field fresh of
`CarryOwed` (Honest/K10/Xch/CarryTop.lean), "the witness's table at the fresh mask's message pairs with the coefficients
of the run that the part spends", from one sentence on that table: entry by entry it is what a sending lays where a fold's
fresh table rides (`K1.Ride.lay`, Honest/K1/Coins.lean), at the spent run's own values in their order.

Why that is enough. The library's packing of coefficients pairs with their polynomial (`pairs_packed`,
Johnson/Prover/Link/FoldHolds.lean). The sending's laying is that packing (`packing_at`, Honest/K12/PackingAt.lean), at the
coefficients `hideAt`; and the coefficients that the closing's part reads off the spent run, `coefU` of `uOfBook`, are
`hideAt` of the same values (`coefU_byName`, Honest/K12/FreshAtJob.lean).

  `pairs_of_packedN`   a table that is the packing by numbers, entry by entry, pairs
  `wordsAll`, `coefU_book`   2 k + 1 words as a function on all numbers; their coefficients are `hideAt` of their values
  `pairs_of_lay`       a table that is the sending's laying of the words' values pairs with the words' coefficients
  **`pairs_of_coef`**    the same at every W that the run gives (`CoefOf`, Honest/K10/Xch/Shown.lean)
  `freshB_wordsOn`     the fresh table that the closing's laws read off words made of tables: an entry of the table of the
                    mask's message, where that message has 2 ^ h mask rows
  **`fresh_of_tabs`**    so the field fresh's pairing, from tables T whose table at the mask's message is the laying

Limits. The sentence on the table is a premise, shown here of no witness. hl, "the stage has room for the packing", hn, "the
run has the stage's number of variables", and the mask's message's shape are premises. No head, thread or prover is named.
-/
import Johnson.Desc.ProofFile.Honest.K10.Xch.Shown
import Johnson.Desc.K10.Honest.LeftClaim
import Johnson.Prover.Link.BodyPack
import Johnson.Desc.ProofFile.Honest.K12.PackingAt
import Johnson.Desc.ProofFile.Honest.K12.FreshAtJob
import Johnson.Desc.Means.ItemsTab

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes.Slice (GE Sg readE Sz testBit_rowNo rowNo_lt ceilLog2_two_pow)
open OnBytes.Means (wordsOn realRows Extends extends_begun)
open Cb (HIdx sVars)
open Johnson.Prover.Link (Pairs packed packedN pairs_packed coefU uOfBook)
open VerifiableInference.Desc.First.Close (Rec)
open ProofFile.Honest.K12 (hideAt packing_at)
open ProofFile.Honest.K12.Light (coefAt coefU_byName)
open ProofFile.Honest.K10.LeftIs (stageB freshB)
open ProofFile.Honest.K10.YesFree (BaseData)

/-- A table that is the library's packing by numbers, entry by entry, pairs with the coefficients. -/
theorem pairs_of_packedN (s : Sg) (hl : s.h + 2 * s.g + 1 ≤ s.Z.l) (W : HIdx (sVars GE 2 (s.h + s.g)) → GE)
    (φ : s.cFr.J → GE) (h : ∀ x : s.cFr.J, φ x = packedN s W (Sz.rowNo x.1) x.2.val) :
    Pairs s s.Z.l W φ := by
  have e : φ = packed s hl W := funext fun x => by
    rw [h x]
    unfold packedN
    rw [dif_pos ⟨hl, x.2.isLt⟩]
    exact congrArg (packed s hl W) (Prod.ext (funext (testBit_rowNo x.1)) rfl)
  rw [e]
  exact pairs_packed s hl W

/-- 2 k + 1 words as a function on all numbers: 0 beyond them. -/
def wordsAll {k : Nat} (u : Fin (2 * k + 1) → OnBytes.E) (n : Nat) : OnBytes.E :=
  if h : n < 2 * k + 1 then u ⟨n, h⟩ else OnBytes.zeroE

/-- The coefficients that the closing's part reads off 2 k + 1 words are `hideAt` of the words' values. -/
theorem coefU_book (k : Nat) (u : Fin (2 * k + 1) → OnBytes.E) :
    coefU k (uOfBook k fun i => (u i).triple) = hideAt k fun n => readE (wordsAll u n) := by
  have e1 : (uOfBook k fun i => (u i).triple).w = fun l t => (wordsAll u (coefAt k l t)).triple := by
    funext l t
    show (if h : coefAt k l t < 2 * k + 1 then (u ⟨coefAt k l t, h⟩).triple else Fmt.Fld.zeroE) =
      (if h : coefAt k l t < 2 * k + 1 then u ⟨coefAt k l t, h⟩ else OnBytes.zeroE).triple
    by_cases h : coefAt k l t < 2 * k + 1
    · rw [dif_pos h, dif_pos h]
    · rw [dif_neg h, dif_neg h]
      rfl
  have e2 : (uOfBook k fun i => (u i).triple).w0 = (wordsAll u (2 * (k - 1))).triple := by
    have hlt : 2 * (k - 1) < 2 * k + 1 := by omega
    show (u ⟨2 * (k - 1), _⟩).triple = _
    unfold wordsAll
    rw [dif_pos hlt]
  have e : uOfBook k (fun i => (u i).triple) =
      ⟨fun l t => (wordsAll u (coefAt k l t)).triple, (wordsAll u (2 * (k - 1))).triple⟩ := by
    calc uOfBook k (fun i => (u i).triple)
        = ⟨(uOfBook k fun i => (u i).triple).w, (uOfBook k fun i => (u i).triple).w0⟩ := rfl
      _ = _ := by rw [e1, e2]
  rw [e, coefU_byName k k rfl (wordsAll u) (fun n => readE (wordsAll u n)) fun _ _ => rfl]
  rfl

/-- A table that is the sending's laying of the words' values pairs with the words' coefficients. -/
theorem pairs_of_lay (s : Sg) (hl : s.h + 2 * s.g + 1 ≤ s.Z.l) (u : Fin (2 * (s.h + s.g) + 1) → OnBytes.E)
    (φ : s.cFr.J → GE)
    (h : ∀ x : s.cFr.J, φ x =
      (⟨s.h + s.g, s.h⟩ : K1.Ride).lay (fun n => readE (wordsAll u n)) (Sz.rowNo x.1) x.2.val) :
    Pairs s s.Z.l (coefU (s.h + s.g) (uOfBook (s.h + s.g) fun i => (u i).triple)) φ := by
  rw [coefU_book]
  exact pairs_of_packedN s hl _ φ fun x => by rw [h x, packing_at s hl]

/-- **The same at every list of coefficients that the run gives.** -/
theorem pairs_of_coef (s : Sg) (hl : s.h + 2 * s.g + 1 ≤ s.Z.l) {n' : Nat} (hn : n' = s.h + s.g)
    (u : Fin (2 * n' + 1) → OnBytes.E) (W : HIdx (sVars GE 2 (s.h + s.g)) → GE) (hW : CoefOf u W)
    (φ : s.cFr.J → GE)
    (h : ∀ x : s.cFr.J, φ x =
      (⟨s.h + s.g, s.h⟩ : K1.Ride).lay (fun n => readE (wordsAll u n)) (Sz.rowNo x.1) x.2.val) :
    Pairs s s.Z.l W φ := by
  subst hn
  obtain ⟨u', hu, rfl⟩ := hW
  have e : u' = u := funext fun i => hu i i rfl
  subst e
  exact pairs_of_lay s hl u' φ h

/-- The fresh table that the closing's laws read, at words made of tables: an entry of the mask's message's table. -/
theorem freshB_wordsOn {D : BaseData} {r : Rec} (T : Nat → Bool → Nat → Nat → GE) {y : OnBytes.Oracle}
    (hy : r.st.oracles[D.m]? = some y) (hr : y.shape.maskRows = 2 ^ (stageB D r).h) (x : (stageB D r).cFr.J) :
    freshB D r (wordsOn r.st T) x = T D.m true (Sz.rowNo x.1) x.2.val := by
  have hE : Extends r.st (D.S1 r) := extends_begun r.st r.frame.group D.G
  obtain ⟨y', hy', ey⟩ := hE.shape D.m y hy
  have e1 : ((D.S1 r).oracles.getD D.m default).shape.maskRows = 2 ^ (stageB D r).h := by
    rw [Array.getD_eq_getD_getElem?, hy']
    show y'.shape.maskRows = _
    rw [ey, hr]
  have hb : r.st.rowBits D.m .mask = (stageB D r).h := by
    unfold OnBytes.Statement.rowBits
    rw [hy]
    show OnBytes.ceilLog2 y.shape.maskRows = _
    rw [hr, ceilLog2_two_pow]
  have hq : realRows r.st D.m .mask = 2 ^ (stageB D r).h := by
    unfold realRows
    rw [hy]
    exact hr
  have hlt : Sz.rowNo x.1 < 2 ^ (stageB D r).h := rowNo_lt x.1
  unfold freshB wordsOn
  rw [e1, ceilLog2_two_pow, hb, hq]
  have m1 : (Sz.rowNo x.1 + x.2.val * 2 ^ (stageB D r).h) % 2 ^ (stageB D r).h = Sz.rowNo x.1 := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
  have m2 : (Sz.rowNo x.1 + x.2.val * 2 ^ (stageB D r).h) / 2 ^ (stageB D r).h = x.2.val := by
    rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlt, Nat.zero_add]
  rw [m1, m2, if_pos hlt]
  rfl

/-- **The field fresh's pairing, from tables whose table at the mask's message is the sending's laying of the spent run's
values.** -/
theorem fresh_of_tabs {D : BaseData} {r : Rec} (T : Nat → Bool → Nat → Nat → GE) {y : OnBytes.Oracle}
    (hy : r.st.oracles[D.m]? = some y) (hr : y.shape.maskRows = 2 ^ (stageB D r).h)
    (hl : (stageB D r).h + 2 * (stageB D r).g + 1 ≤ (stageB D r).Z.l) {n' : Nat}
    (hn : n' = (stageB D r).h + (stageB D r).g) (u : Fin (2 * n' + 1) → OnBytes.E)
    (hT : ∀ b j, b < 2 ^ (stageB D r).h → j < (stageB D r).Z.l → T D.m true b j =
      (⟨(stageB D r).h + (stageB D r).g, (stageB D r).h⟩ : K1.Ride).lay (fun n => readE (wordsAll u n)) b j)
    (W : HIdx (sVars GE 2 ((stageB D r).h + (stageB D r).g)) → GE) (hW : CoefOf u W) :
    Pairs (stageB D r) (stageB D r).Z.l W (freshB D r (wordsOn r.st T)) :=
  pairs_of_coef (stageB D r) hl hn u W hW _ fun x => by
    rw [freshB_wordsOn T hy hr x]
    exact hT _ _ (rowNo_lt x.1) x.2.isLt

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.pairs_of_packedN
#print axioms ProofFile.Honest.K10.wordsAll
#print axioms ProofFile.Honest.K10.coefU_book
#print axioms ProofFile.Honest.K10.pairs_of_lay
#print axioms ProofFile.Honest.K10.pairs_of_coef
#print axioms ProofFile.Honest.K10.freshB_wordsOn
#print axioms ProofFile.Honest.K10.fresh_of_tabs
