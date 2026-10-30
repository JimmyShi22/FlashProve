-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Inner/KeptHold.lean: A KEPT ROW's GENERATOR ROW SAYS TRUE OF THE HONEST NEW
MESSAGES OF A CODE SWITCH, where its target is the row's code word's symbol. Statements and proofs.

  `keptTail_fits`   a kept row's tail lies inside the rest
  `keptGen_pieces`  the row's coefficients: a form carried over, and a stretch of the rest
  `keptGen_holds`   the row says true

By: `genKept_at`, `formAt_keptForm` (Johnson/Top/H0/H2K/GenRowsAt.lean); `tailPieces_of_frame`
(Johnson/Top/H0/K2Hands/Pays.lean); Inner/KeptRows.lean.

Limits. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Inner.KeptRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.Slice (GE rdE readE coefAt formAt stretchAt codeOf wM wT)
open OnBytes.Means (Says value)
open Johnson.Prover.Send (Rows)
open Johnson.Prover.Link (symG)
open H2K.Lift (genKept keptForm)
open Finset (range)

variable {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat} {anew : Array Nat}
  {W : Left} {V : Nat → Rows}

/-- A kept row's tail lies inside the rest. n: the row's number among all kept rows. -/
theorem keptTail_fits (A : AtSwitch S old T g anew W V) (n : Nat) (hn : n < old.keptRows) :
    (switchParts S old).keptTailAt.getD n 0 + (S.codes.base.getD old.code default).r ≤
      (rest (sizesAt S old T) W).length := by
  rw [(restIsParts S old T W A.target.masks A.fits).1]
  have h := (Johnson.Top.H.parts_laws S old).1
  unfold Johnson.Top.H.restHead at h
  have e : (switchParts S old).keptTailAt.getD n 0 =
      old.masks * (S.codes.mask.getD old.maskCode default).ell +
        (S.codes.base.getD old.code default).r + (S.codes.base.getD old.code default).r * n :=
    startsFrom_getD _ _ old.keptRows n hn
  have hmul : (S.codes.base.getD old.code default).r * n + (S.codes.base.getD old.code default).r ≤
      old.keptRows * (S.codes.base.getD old.code default).r := by
    calc (S.codes.base.getD old.code default).r * n + (S.codes.base.getD old.code default).r
        = (n + 1) * (S.codes.base.getD old.code default).r := by ring
      _ ≤ old.keptRows * (S.codes.base.getD old.code default).r := Nat.mul_le_mul_right _ hn
  rw [e]
  omega

/-- The number of a kept row lies below the count of all kept rows. -/
theorem keptNo_lt (A : AtSwitch S old T g anew W V) {Fr : SwitchFrame}
    (hFr : switchFrame S old T g anew = some Fr) (a : Nat) (k : KeptPlace)
    (hk : Fr.kept[a]? = some k) (b : Nat) (hb : b < k.rows) :
    ((Fr.kept.take a).map (·.rows)).sum + b < old.keptRows := by
  rw [rows_count A hFr, List.map_take]
  exact Johnson.Top.H.sum_take_lt _ _ _ k.rows (by rw [List.getElem?_map, hk]; rfl) hb

/-- The row's coefficients: a form carried over, and a stretch of the rest. -/
theorem keptGen_pieces (A : AtSwitch S old T g anew W V) {Fr : SwitchFrame}
    (hFr : switchFrame S old T g anew = some Fr)
    (hlog : (S.codes.base.getD old.code default).logN ≤ 32) (a : Nat) (k : KeptPlace)
    (hk : Fr.kept[a]? = some k) (b : Nat) (hb : b < k.rows) (x : Nat)
    (hx : x < 2 ^ (S.codes.base.getD old.code default).logN) (t : E) :
    coefAt (genKept Fr k b (((Fr.kept.take a).map (·.rows)).sum + b) x t) = fun o p J =>
      coefAt (Fr.addKept {} k (keptForm Fr k b x)) o p J +
      stretchPiece S T g
        ((switchParts S old).keptTailAt.getD (((Fr.kept.take a).map (·.rows)).sum + b) 0)
        (S.codes.base.getD old.code default).r
        (wT (codeOf (S.codes.base.getD old.code default)) x) o p J := by
  have I := frameIs hFr
  funext o p J
  have hT := VerifiableInference.Desc.First.K2Hands.tailPieces_of_frame S old T g anew Fr hFr a k hk
    (rows_count A hFr) b hb
  have h := H2K.Lift.genKept_at Fr k b (((Fr.kept.take a).map (·.rows)).sum + b) _ hT
    (VerifiableInference.Desc.First.K2Hands.places_inc S old T g anew Fr hFr A.check _ _)
    (by rw [I.code]; exact hlog) x (by rw [I.code]; exact hx) t o p J
  rw [h]
  congr 1
  show (if Fr.g == o && Fr.restPart == p then
    stretchAt Fr.places (Fr.parts.keptTailAt.getD (((Fr.kept.take a).map (·.rows)).sum + b) 0)
      Fr.code.r (wT (codeOf Fr.code) x) J else 0) = _
  rw [I.gIs, I.restPart, I.places, I.parts, I.code]
  rfl

/-- **A kept row's generator row.** -/
theorem keptGen_holds (A : AtSwitch S old T g anew W V)
    (hn : ∀ o ∈ anew.toList, o < S.oracles.size) {Fr : SwitchFrame}
    (hFr : switchFrame S old T g anew = some Fr)
    (hlog : (S.codes.base.getD old.code default).logN ≤ 32) (a : Nat) (k : KeptPlace)
    (hk : Fr.kept[a]? = some k) (b : Nat) (hb : b < k.rows) (x : Nat)
    (hx : x < 2 ^ (S.codes.base.getD old.code default).logN) (t : E)
    (ht : readE t = symG (codeOf (S.codes.base.getD old.code default)) x ((W.kept a).main b)
      ((W.kept a).tail b)) :
    Says rdE S (genKept Fr k b (((Fr.kept.take a).map (·.rows)).sum + b) x t)
      (newWords (sizesAt S old T) g anew V) := by
  have I := frameIs hFr
  have hpow : (S.codes.base.getD old.code default).ell =
      2 ^ (S.codes.base.getD old.code default).logEll := A.target.power.2.symm
  obtain ⟨s, _, _, _, _, _, _, e4, e5, _, e7⟩ := kept_at hFr a k hk
  have hb2 : b < 2 ^ k.rowBits := by
    rw [e5]
    exact Nat.lt_of_lt_of_le (e4 ▸ hb) (SwitchPlaces.le_two_pow_ceilLog2' _)
  have R := (restIsParts S old T W A.target.masks A.fits).2.2.2.1
  have h1 := value_worth A hn (genKept Fr k b (((Fr.kept.take a).map (·.rows)).sum + b) x t)
  rw [keptGen_pieces A hFr hlog a k hk b hb x hx t, worthOf_add, worth_addKept A hFr a k hk,
    worth_stretchPiece A _ _ _ (keptTail_fits A _ (keptNo_lt A hFr a k hk b hb))] at h1
  have ha : ∑ J ∈ range (2 ^ (k.rowBits + (S.codes.base.getD old.code default).logEll)),
      formAt (keptForm Fr k b x) J *
        (W.kept a).entryIn (S.oracles.getD k.old default).shape J =
      ∑ j ∈ range (S.codes.base.getD old.code default).ell,
        wM (codeOf (S.codes.base.getD old.code default)) x j * (W.kept a).main b j := by
    have step : ∑ J ∈ range (2 ^ (k.rowBits + (S.codes.base.getD old.code default).logEll)),
        formAt (keptForm Fr k b x) J *
          (W.kept a).entryIn (S.oracles.getD k.old default).shape J =
        ∑ J ∈ range (2 ^ (k.rowBits + (S.codes.base.getD old.code default).logEll)),
          (if J % 2 ^ k.rowBits = b then
            wM (codeOf (S.codes.base.getD old.code default)) x (J / 2 ^ k.rowBits) else 0) *
          (W.kept a).entryIn (S.oracles.getD k.old default).shape J := by
      apply Finset.sum_congr rfl
      intro J hJ
      have hf := H2K.Lift.formAt_keptForm Fr k b x J (by rw [I.code]; exact hpow)
        (by rw [I.code]; exact hlog) (by rw [I.code]; exact hx) hb2
        (by rw [I.code]; exact Finset.mem_range.1 hJ)
      rw [I.code] at hf
      rw [hf]
    rw [step, Lists.row_pick _ _ b hb2, ← hpow]
    apply Finset.sum_congr rfl
    intro j _
    have hm : (b + 2 ^ k.rowBits * j) % 2 ^ ceilLog2 s.mainRows = b := by
      rw [← e5, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb2]
    have hd : (b + 2 ^ k.rowBits * j) / 2 ^ ceilLog2 s.mainRows = j := by
      rw [← e5, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hb2, Nat.zero_add]
    rw [← e7]
    unfold Held.entryIn Held.entry
    rw [hm, hd, if_pos (e4 ▸ hb)]
  have hbb : ∑ q ∈ range (S.codes.base.getD old.code default).r,
      wT (codeOf (S.codes.base.getD old.code default)) x q *
        (rest (sizesAt S old T) W).getD
          ((switchParts S old).keptTailAt.getD (((Fr.kept.take a).map (·.rows)).sum + b) 0 + q)
          zeroG =
      ∑ q ∈ range (S.codes.base.getD old.code default).r,
        wT (codeOf (S.codes.base.getD old.code default)) x q * (W.kept a).tail b q := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [← R _ (a, b) q (keptRow_at hFr a k hk b hb) (Finset.mem_range.1 hq)]
  have htg : rdE.val
      (genKept Fr k b (((Fr.kept.take a).map (·.rows)).sum + b) x t).target = readE t := rfl
  unfold Says
  rw [h1, htg, ht, ← sym_split, ha, hbb]

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.keptGen_holds
