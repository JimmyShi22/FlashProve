-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchCongrPay.lean: the closing of a segment (K10): three laws, one for each of the
premises hOwn, hGam and hK of `closingFrom_congr` (Pay/XchCongr.lean), at two callers of which one has heard a longer list of
challenges than the other and both are lent coins off one look-up.

  `at_prefix`            the one call of a filling of the main rows (`RowData.at_`, Honest/RowData.lean) reads of the challenges
                       heard the first `heardAt` alone: by its text, at every filling. So it returns the same at a list and at
                       a longer one, where the shorter holds that many
  **`ownBy_prefix`**       for hOwn: so the segments' own main rows (`ownBy`, Honest/K2/AtPlan.lean) at one segment, at two
                       functions of shapes that agree there
  **`challenges_prefix`**  for hGam: the folds' challenges, as the shared text reads them, where their numbers lie inside the
                       shorter list
  **`carried_same`**       for hK: two parts' carried stretches of one number are one, where the two entries of the book have
                       one owner, start and count

Limits. That the shorter list holds enough, that the numbers lie inside it, and that the book's entries agree, are premises.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchLent
import Johnson.Desc.ProofFile.Honest.K2.AtPlan
import Johnson.Desc.ProofFile.Honest.K2.Closing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open ProofFile.Honest.K2 (Stretch ownBy challengesOr0)

/-- The one call of a filling returns the same at a list of challenges and at a longer one. -/
theorem at_prefix (D : RowData) (R : Readers) (heard' t : List Fmt.Drawn) (a : MsgAddr)
    (hle : D.heardAt a ≤ heard'.length) (r j : Nat) :
    D.at_ R (heard' ++ t) a r j = D.at_ R heard' a r j := by
  unfold RowData.at_
  rw [List.take_append_of_le_length hle]

/-- **For hOwn.** -/
theorem ownBy_prefix (D : RowData) (R : Readers) (addrs : Nat → Nat → Option MsgAddr)
    (shapes shapes' : Nat → Nat → OnBytes.OracleShape) (heard' t : List Fmt.Drawn) (seg : Nat)
    (hs : shapes seg = shapes' seg)
    (hle : ∀ m a, addrs seg m = some a → D.heardAt a ≤ heard'.length) :
    ownBy D R addrs shapes (heard' ++ t) seg = ownBy D R addrs shapes' heard' seg := by
  funext m b j
  unfold ownBy
  cases ha : addrs seg m with
  | none => rfl
  | some a =>
    show K2.asRow ((shapes seg m).mainDeg == 3) (D.at_ R (heard' ++ t) a b j) =
      K2.asRow ((shapes' seg m).mainDeg == 3) (D.at_ R heard' a b j)
    rw [hs, at_prefix D R heard' t a (hle m a ha)]

/-- **For hGam.** -/
theorem challenges_prefix (heard' t : List Fmt.Drawn) (numbers : List Nat) (h : ∀ i ∈ numbers, i < heard'.length) :
    challengesOr0 (heard' ++ t) numbers = challengesOr0 heard' numbers := by
  unfold challengesOr0
  refine List.map_congr_left fun i hi => ?_
  have e : ((heard' ++ t).drop i).head? = (heard'.drop i).head? := by
    rw [List.head?_drop, List.head?_drop, List.getElem?_append_left (h i hi)]
  rw [e]

/-- **For hK.** -/
theorem carried_same {look : Addr → (d : Due) × Cs d} {ds ds' : List (String × Due)} {l l' : List Ahead}
    {y : CsAll ds} {y' : CsAll ds'} (h : lend look ds l = .ok y) (h' : lend look ds' l' = .ok y') {n : Nat}
    {a a' : Ahead} (hn : l[n]? = some a) (hn' : l'[n]? = some a') (ho : a.owner = a'.owner)
    (hs : a.start = a'.start) (hc : a.count = a'.count) :
    Stretch.carried ds y n = Stretch.carried ds' y' n := by
  obtain ⟨x, hx, e⟩ := carried_cut look ds l y h n a hn
  obtain ⟨x', hx', e'⟩ := carried_cut look ds' l' y' h' n a' hn'
  rw [e, e']
  obtain ⟨n1, o1, s1, c1, p1, b1⟩ := a
  obtain ⟨n2, o2, s2, c2, p2, b2⟩ := a'
  dsimp only at ho hs hc hx hx' x x' ⊢
  subst ho hs hc
  obtain rfl : x = x' := Option.some.inj (hx.symm.trans hx')
  rfl

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.at_prefix
#print axioms ProofFile.Honest.K10.ownBy_prefix
#print axioms ProofFile.Honest.K10.challenges_prefix
#print axioms ProofFile.Honest.K10.carried_same
