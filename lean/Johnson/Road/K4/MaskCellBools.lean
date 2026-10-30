-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/MaskCellBools.lean: two records of conditions, on the plan and on a record's part,
under which two readings of a mask row and of a cell are one (`MaskOne`,
Johnson/Road/K4/K4PinsMaskQ.lean; `CellOne`, Johnson/Road/K4/K4PinsCellQ.lean), each as a test with
code, and for each test the law: a yes gives the record.

The two records hold data beside their conditions (numbers that a search finds), so each law says
that there is such a record.

Definitions and statements.
  `maskOneB A own a`, `maskOne_of_B`: all six conditions of `MaskOne` are tests on finite data: no
    side premise is left.
  `apartB`, `pairsApartB`, `blocksOneB bs R P`, `blocksOne_of_B`: every block passes the programs'
    own test `laidBlockOk` (OnBytes/Iop/ReqRows.lean) at R and P, and no two blocks hold one
    element: a yes gives `BlocksOne` (K4PinsCellQ.lean), by `blocksOne_of`
    (Johnson/Road/K4/K4PinsBlocks.lean). `BlocksOne` itself speaks of all tables of field elements;
    the test is on the blocks' numbers alone.
  `cellOneB A own a T r c`, `cellOne_of_B`: the conditions of `CellOne`, the last of them by
    `blocksOneB`: no side premise is left.
No evaluation is made here.

What of OnBytes/Model/ is used: nothing by name.

Limits. One way: a yes gives the record. That a test says yes at any plan is not said. Nothing on
soundness.
-/
import Johnson.Road.K4.K4PinsMaskQ
import Johnson.Road.K4.K4PinsCellQ
import Johnson.Road.K4.K4PinsBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Road.K4.SeamBools
open Johnson.Pack OnBytes.Road.K4
open VerifiableInference.Desc.First.Look (sigListCalls seatCalls laidPlace laidHolds messagesAt
  keptAt)
open OnBytes.Params (LaidBlock)
open VerifiableInference.Desc.K9 (seatAt)
open VerifiableInference.Desc.K9L (maskOracle)

variable {Cells : Type} (A : PinPlan Cells)

/-! ## The mask row -/

/-- The conditions of `MaskOne`, with what they name found by the searches that they name. -/
def maskOneB (own : List (ℕ × ℕ)) (a : VerifiableInference.Desc.K9.Part) : Bool :=
  match (messagesAt A.D A.link).findIdx? fun x => x.shape.maskRows != 0 with
  | none => false
  | some mI =>
    if member : (keptAt A.D A.link).length + mI < (sigListCalls A.D A.rad A.link).length then
      decide (0 < ((sigListCalls A.D A.rad A.link).get ⟨_, member⟩).1.maskRows) &&
        match maskOracle a.L.check.frame with
        | none => false
        | some o =>
          decide (seatAt own a.d.book o = some (A.seatT ⟨_, member⟩)) &&
            decide (a.d.st.rowBits o .mask = 0)
    else false

/-- **A yes gives the record.** -/
theorem maskOne_of_B {own : List (ℕ × ℕ)} {a : VerifiableInference.Desc.K9.Part}
    (h : maskOneB A own a = true) : Nonempty (MaskOne A own a) := by
  unfold maskOneB at h
  split at h
  · cases h
  · rename_i mI hI
    split at h
    · rename_i member
      rw [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨h1, h⟩ := h
      split at h
      · cases h
      · rename_i o ho
        rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
        exact ⟨⟨mI, hI, member, h1, o, ho, h.1, h.2⟩⟩
    · cases h

/-! ## A list of blocks -/

/-- No element of an array is held by both blocks: their stretches of rows, or of columns, do not
meet. -/
def apartB (x y : LaidBlock) : Bool :=
  !(OnBytes.laidMeet x.firstI x.bitsI y.firstI y.bitsI &&
    OnBytes.laidMeet x.firstC x.bitsC y.firstC y.bitsC)

theorem apart_of_B {x y : LaidBlock} (h : apartB x y = true) (i c : ℕ)
    (hx : laidHolds x i c = true) : laidHolds y i c = false := by
  cases hy : laidHolds y i c with
  | false => rfl
  | true =>
    unfold laidHolds at hx hy
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hx hy
    have m : (OnBytes.laidMeet x.firstI x.bitsI y.firstI y.bitsI &&
        OnBytes.laidMeet x.firstC x.bitsC y.firstC y.bitsC) = true := by
      simp only [OnBytes.laidMeet, Bool.and_eq_true, decide_eq_true_eq]
      omega
    unfold apartB at h
    rw [m] at h
    cases h

/-- No two blocks of the list hold one element. -/
def pairsApartB : List LaidBlock → Bool
  | [] => true
  | b :: l => l.all (apartB b) && pairsApartB l

theorem pairsApart_of_B : ∀ {bs : List LaidBlock}, pairsApartB bs = true →
    bs.Pairwise fun x y => ∀ i c, laidHolds x i c = true → laidHolds y i c = false
  | [], _ => List.Pairwise.nil
  | b :: l, h => by
    unfold pairsApartB at h
    rw [Bool.and_eq_true] at h
    exact List.pairwise_cons.2
      ⟨fun y hy i c => apart_of_B (List.all_eq_true.1 h.1 y hy) i c, pairsApart_of_B h.2⟩

/-- Every block passes the programs' own test at R and P, and no two hold one element. -/
def blocksOneB (bs : List LaidBlock) (R P : ℕ) : Bool :=
  (bs.all fun b => OnBytes.laidBlockOk b R P) && pairsApartB bs

/-- **A yes gives `BlocksOne`.** -/
theorem blocksOne_of_B {bs : List LaidBlock} {R P : ℕ} (h : blocksOneB bs R P = true) :
    BlocksOne bs R P := by
  unfold blocksOneB at h
  rw [Bool.and_eq_true] at h
  exact blocksOne_of R P bs (fun b hb => List.all_eq_true.1 h.1 b hb) (pairsApart_of_B h.2)

/-! ## A cell -/

/-- The conditions of `CellOne`, with what they name found by the searches that they name. -/
def cellOneB (own : List (ℕ × ℕ)) (a : VerifiableInference.Desc.K9.Part) (T r c : ℕ) : Bool :=
  match (A.D.arrayOf.getD A.link #[])[T]? with
  | none => false
  | some bn =>
    match OnBytes.reqArray A.D.layout bn.1 bn.2 with
    | none => false
    | some ar =>
      match laidPlace ar.blocks r c with
      | none => false
      | some rp =>
        match seatCalls A.D A.link (.cell T r c) with
        | none => false
        | some st =>
          decide (st = ⟨st.msg, false, rp.1, rp.2⟩) &&
            if member : st.msg < (sigListCalls A.D A.rad A.link).length then
              decide (rp.1 < ((sigListCalls A.D A.rad A.link).get ⟨st.msg, member⟩).1.mainRows) &&
                decide (rp.2 <
                  (pMain A.D.codes ((sigListCalls A.D A.rad A.link).get ⟨st.msg, member⟩).1).ell) &&
                decide (a.L.check.rows.layout = A.D.layout) &&
                match a.L.check.frame.whereIs bn.1 ar.message with
                | none => false
                | some o =>
                  decide (seatAt own a.d.book o = some (A.seatT ⟨st.msg, member⟩)) &&
                    decide (rp.1 < 2 ^ a.d.st.rowBits o .main) &&
                    blocksOneB ar.blocks (a.d.st.rowBits o .main) (a.d.st.placeBits o .main)
            else false

/-- **A yes gives the record.** -/
theorem cellOne_of_B {own : List (ℕ × ℕ)} {a : VerifiableInference.Desc.K9.Part} {T r c : ℕ}
    (h : cellOneB A own a T r c = true) :
    Nonempty (CellOne A own a T r c) := by
  unfold cellOneB at h
  split at h
  · cases h
  · rename_i bn hbn
    split at h
    · cases h
    · rename_i ar har
      split at h
      · cases h
      · rename_i rp hrp
        split at h
        · cases h
        · rename_i st hst
          rw [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨hs, h⟩ := h
          split at h
          · rename_i member
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨⟨h1, h2⟩, h3⟩, h⟩ := h
            split at h
            · cases h
            · rename_i o ho
              simp only [Bool.and_eq_true, decide_eq_true_eq] at h
              exact ⟨⟨bn, hbn, ar, har, rp, hrp, st.msg, hst.trans (congrArg some hs), member, h1,
                h2, h3, o, ho, h.1.1, h.1.2, blocksOne_of_B h.2⟩⟩
          · cases h

end Johnson.Road.K4.SeamBools

#print axioms Johnson.Road.K4.SeamBools.maskOne_of_B
#print axioms Johnson.Road.K4.SeamBools.apart_of_B
#print axioms Johnson.Road.K4.SeamBools.pairsApart_of_B
#print axioms Johnson.Road.K4.SeamBools.blocksOne_of_B
#print axioms Johnson.Road.K4.SeamBools.cellOne_of_B
