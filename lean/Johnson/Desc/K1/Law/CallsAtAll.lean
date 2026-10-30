-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/CallsAtAll.lean: THE PREMISE hCalls OF THE LAW ON THE SUB-PROTOCOL K1
(k01_kind_paidThree, Johnson/Desc/AtSeats/K01KindPaidThree.lean): `CallsSeated`
(Johnson/Desc/Kinds/Law/HeadSymsMeet.lean: "what ties the caller's public letters to the table's,
eight facts a matrix"), FROM ONE TEST WITH CODE, at letters and at the closed constant
(`hA.𝔇`, Johnson/P5J/MgAtAll.lean). Definitions (tests with code) and statements with their proofs;
nothing is evaluated.

  `colFourB`, `colFour_of`   the antecedent "column c of matrix a is one of the four ranges'"
      (`ColFour`, Johnson/Desc/Kinds/Law/K6Cut.lean) is, in each of its four arms, "c below a
      bound": so whenever it holds at some column it holds at column 0: a test on the matrix alone
  `blocksInB`, `blocksIn_of`   THE THIRD CLAUSE ("for all r c' rp: where the array holds its element
      lies inside member k's table": unbounded) HAS A CRITERION WITH CODE: each block of the array
      is as large in the table as in the matrix and its rectangle ends inside the table: by
      `laidAt_block` and `laidIn_rect` (Johnson/Goal/Meaning/LaidInside.lean)
  `memberNo`, `member_of`   THE SECOND CLAUSE ("whatever the place") is one equation on a number
  `callsB`, `callsSeated_of`   **the test, matrix by matrix, ALL EIGHT CLAUSES, and its law**
  `hCalls_atAll`   **hCalls** at lay6 := `At.layout Zp` · num6 := `At.num Zp` · msR := the
      constant's list of sampled oracle messages · rad6 := fun _ => 0 (the clauses read the
      members' shapes alone) · seatT := the seats of the lookup on the calls at segment
      24 (`P5J.At.seat3At Zp 24 false`)
  `blocksIn_rejects`, `calls_accepts_none`   `blocksInB` rejects a block that ends one row outside.
      `callsB` ACCEPTS WHERE NO MATRIX PASSES `colB`, for want of a case, as CallsSeated's own
      text does: a negative test worth the name needs the public files

OF THE EIGHT CLAUSES THE USER `lab_of_calls`
(Johnson/Desc/Kinds/Law/FourRunsTie.lean) SPENDS THE FIRST ALONE (the segment's list of arrays names
the matrix's symbol array by the matrix's label). The premise is met here whole, as it stands.

What is not claimed. That `callsB` accepts at any files, at these letters or at others: it is to be
evaluated there. No member of the head hA. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.TestsAtAll
import Johnson.Desc.Kinds.Law.HeadSymsMeet
import Johnson.Goal.Meaning.LaidInside

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Model OnBytes.Params
open OnBytes.Maker (WholeD)
open OnBytes.Model.Verify (borderOf)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.First.Look (Sent sigListCalls keptAt bornAt)
open VerifiableInference.Desc.Sound (Mem seatOf)
open VerifiableInference.Desc.Kinds.Head.Law (ColFour CallsSeated)
open Johnson.Pack (pMain)
open ProofFile (Cl)

/-! ## 1 The antecedent -/

/-- The matrix number a has a column among the four ranges'. -/
def colFourB (h : Head.Shape) (L : Head.HL) (b : Head.Border) (a : ℕ) : Bool :=
  (decide (a < h.NHf) && decide (0 < L.k)) || (decide (a = h.NHf) && decide (0 < L.kD)) ||
    (decide (a = h.NHf + 1) && decide (0 < L.kR)) || (decide (a = h.NHf + 3) && decide (0 < b.kxb))

theorem colFour_of {h : Head.Shape} {L : Head.HL} {b : Head.Border} {a c : ℕ}
    (hc : ColFour h L b a c) : colFourB h L b a = true := by
  unfold colFourB
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h3 : 0 < L.k := by omega
    simp [h1, h3]
  · have h3 : 0 < L.kD := by omega
    simp [h1, h3]
  · have h3 : 0 < L.kR := by omega
    simp [h1, h3]
  · have h3 : 0 < b.kxb := by omega
    simp [h1, h3]

/-! ## 2 The third clause -/

/-- Each block of the array is as large in the table as in the matrix, and its rectangle ends inside
a table of so many rows and places. -/
def blocksInB (A : ReqArray) (rows ell : ℕ) : Bool :=
  A.blocks.all fun b =>
    (b.rowBits + b.placeBits == b.bitsI + b.bitsC) && decide (b.firstRow + 2 ^ b.rowBits ≤ rows) &&
      decide (b.firstPlace + 2 ^ b.placeBits ≤ ell)

theorem blocksIn_of {A : ReqArray} {rows ell : ℕ} (h : blocksInB A rows ell = true) :
    ∀ r c' rp, Desc.laidAt A r c' = some rp → rp.1 < rows ∧ rp.2 < ell := by
  intro r c' rp hat
  obtain ⟨b, hb, hin⟩ := _root_.Meaning.laidAt_block hat
  have h1 := List.all_eq_true.1 h b hb
  rw [Bool.and_eq_true, Bool.and_eq_true] at h1
  obtain ⟨_, h2, _, h3⟩ := _root_.Meaning.laidIn_rect (r := rp.1) (p := rp.2) (eq_of_beq h1.1.1) hin
  have h4 : b.firstRow + 2 ^ b.rowBits ≤ rows := of_decide_eq_true h1.1.2
  have h5 : b.firstPlace + 2 ^ b.placeBits ≤ ell := of_decide_eq_true h1.2
  omega

/-- The negative test: a block of one row and one place that ends one row outside. -/
theorem blocksIn_rejects :
    blocksInB ⟨"a", 0, 1, 1, [⟨0, 0, 4, 0, 0, 0, 0, 0, false⟩]⟩ 4 1 = false ∧
      blocksInB ⟨"a", 0, 1, 1, [⟨0, 0, 3, 0, 0, 0, 0, 0, false⟩]⟩ 4 1 = true := by
  decide

/-! ## 3 The second clause -/

/-- The caller's member at which message msg of segment K lies, in segment i's list. -/
def memberNo (D : Sent) (i K msg : ℕ) : Option ℕ :=
  if K == i then some ((keptAt D i).length + msg) else (bornAt D i).idxOf? (K, msg)

theorem member_of {D : Sent} {i K msg k : ℕ} (h : memberNo D i K msg = some k) :
    ∀ rp : ℕ × ℕ, (if K == i then
        some (⟨(keptAt D i).length + msg, false, rp.1, rp.2⟩ : First.Look.Seat)
      else ((bornAt D i).idxOf? (K, msg)).map fun k' => ⟨k', false, rp.1, rp.2⟩) =
      some ⟨k, false, rp.1, rp.2⟩ := by
  intro rp
  unfold memberNo at h
  split at h
  · rename_i hK
    rw [if_pos hK]
    cases h
    rfl
  · rename_i hK
    rw [if_neg hK, h]
    rfl

/-! ## 4 The test and its law -/

/-- **The test, matrix by matrix.** colB: the matrix has a column that counts. -/
def callsB (colB : ℕ → Bool) (arr : ℕ → ℕ → ℕ) (msR : List Mem) (N : Numbers)
    (Wp : Verify.Public) (lay : ReqLayout) (num : ℕ → ℕ → ℕ) (D : Sent) (rad : OracleShape → ℕ)
    (i : ℕ) (seatT : Fin (sigListCalls D rad i).length → ℕ × ℕ) : Bool :=
  (List.finRange (_root_.Meaning.sizesOf Wp 24).NM).all fun μ =>
    !colB μ.val ||
      (Desc.arrayOf lay (_root_.Meaning.ownerK (_root_.Meaning.labAt Wp 24 μ.val))
        (_root_.Meaning.nameOf (_root_.Meaning.ownerA (_root_.Meaning.labAt Wp 24 μ.val)))).all
      fun A =>
        (memberNo D i (_root_.Meaning.ownerK (_root_.Meaning.labAt Wp 24 μ.val)) A.message).any
        fun k =>
          if hk : k < (sigListCalls D rad i).length then
            decide ((D.arrayOf.getD i #[])[(_root_.Meaning.tlAt Wp 24).gtTree.getD μ.val 0]? =
              some (_root_.Meaning.ownerK (_root_.Meaning.labAt Wp 24 μ.val),
                _root_.Meaning.nameOf
                  (_root_.Meaning.ownerA (_root_.Meaning.labAt Wp 24 μ.val)))) &&
            blocksInB A ((sigListCalls D rad i).get ⟨k, hk⟩).1.mainRows
              (pMain D.codes ((sigListCalls D rad i).get ⟨k, hk⟩).1).ell &&
            (N.group 24).contains (seatT ⟨k, hk⟩) &&
            decide (arr (seatT ⟨k, hk⟩).1 (seatT ⟨k, hk⟩).2 =
              num (_root_.Meaning.ownerK (_root_.Meaning.labAt Wp 24 μ.val)) A.message) &&
            (msR.find? fun y => Decidable.decide (seatOf y = seatT ⟨k, hk⟩)).any fun y =>
              decide (((sigListCalls D rad i).get ⟨k, hk⟩).1 = (y.1.l.get y.2).1)
          else false

/-- Where no matrix passes colB it accepts, for want of a case. -/
theorem calls_accepts_none (arr : ℕ → ℕ → ℕ) (msR : List Mem) (N : Numbers) (Wp : Verify.Public)
    (lay : ReqLayout) (num : ℕ → ℕ → ℕ) (D : Sent) (rad : OracleShape → ℕ) (i : ℕ)
    (seatT : Fin (sigListCalls D rad i).length → ℕ × ℕ) :
    callsB (fun _ => false) arr msR N Wp lay num D rad i seatT = true := by
  unfold callsB
  rw [List.all_eq_true]
  intro μ _
  rfl

/-- **CallsSeated, whole, from the test.** -/
theorem callsSeated_of {Cols : ℕ → ℕ → Prop} {colB : ℕ → Bool}
    (hcol : ∀ a c, Cols a c → colB a = true) {arr : ℕ → ℕ → ℕ} {msR : List Mem} {N : Numbers}
    {Wp : Verify.Public} {lay : ReqLayout} {num : ℕ → ℕ → ℕ} {D : Sent} {rad : OracleShape → ℕ}
    {i : ℕ} {seatT : Fin (sigListCalls D rad i).length → ℕ × ℕ}
    (h : callsB colB arr msR N Wp lay num D rad i seatT = true) :
    CallsSeated Cols arr msR N Wp lay num D rad i seatT := by
  intro μ c _ hcols A hA
  have h1 := List.all_eq_true.1 h μ (List.mem_finRange μ)
  rw [hcol μ.val c hcols, Bool.not_true, Bool.false_or, hA] at h1
  cases hm : memberNo D i (_root_.Meaning.ownerK (_root_.Meaning.labAt Wp 24 μ.val)) A.message with
  | none =>
    rw [Option.all_some, hm] at h1
    cases h1
  | some k =>
    rw [Option.all_some, hm, Option.any_some] at h1
    by_cases hk : k < (sigListCalls D rad i).length
    · rw [dif_pos hk] at h1
      simp only [Bool.and_eq_true] at h1
      obtain ⟨⟨⟨⟨c1, c3⟩, c6⟩, c7⟩, c8⟩ := h1
      cases hy : msR.find? fun y => Decidable.decide (seatOf y = seatT ⟨k, hk⟩) with
      | none =>
        rw [hy] at c8
        cases c8
      | some y =>
        rw [hy, Option.any_some] at c8
        exact ⟨k, hk, seatT ⟨k, hk⟩, y, of_decide_eq_true c1, member_of hm, blocksIn_of c3, rfl,
          of_decide_eq_true c8, List.contains_iff_mem.1 c6, of_decide_eq_true c7, hy⟩
    · rw [dif_neg hk] at h1
      cases h1

/-! ## 5 At the constant -/

/-- **hCalls.** -/
theorem hCalls_atAll {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}
    (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
    (h : callsB (colFourB (P5J.At.X Zp).hS (P5J.At.X Zp).HLy (borderOf (P5J.At.X Zp).y))
      hA.𝔇.arr hA.𝔇.ms hA.𝔇.N (P5J.At.X Zp) (P5J.At.layout Zp) (P5J.At.num Zp) hA.𝔇.sent
      (fun _ => 0) 24 (fun j => P5J.At.seat3At Zp 24 false j.val) = true) :
    CallsSeated (ColFour (P5J.At.X Zp).hS (P5J.At.X Zp).HLy (borderOf (P5J.At.X Zp).y)) hA.𝔇.arr
      hA.𝔇.ms hA.𝔇.N (P5J.At.X Zp) (P5J.At.layout Zp) (P5J.At.num Zp) hA.𝔇.sent (fun _ => 0) 24
      (fun j => P5J.At.seat3At Zp 24 false j.val) :=
  callsSeated_of (fun _ _ hc => colFour_of hc) h

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.colFour_of
#print axioms VerifiableInference.Desc.K1.blocksIn_of
#print axioms VerifiableInference.Desc.K1.blocksIn_rejects
#print axioms VerifiableInference.Desc.K1.member_of
#print axioms VerifiableInference.Desc.K1.calls_accepts_none
#print axioms VerifiableInference.Desc.K1.callsSeated_of
#print axioms VerifiableInference.Desc.K1.hCalls_atAll
