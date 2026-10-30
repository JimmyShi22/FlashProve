-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SecAtAll.lean: TWO PREMISES OF THE LAW ON THE SUB-PROTOCOL K1 (hSec, hLaid6 of
k01_kind_paidThree, Johnson/Desc/AtSeats/K01KindPaidThree.lean), AT THE LIBRARY's CLOSED CONSTANT
(`hA.𝔇`, Johnson/P5J/MgAtAll.lean), each in the premise's own type. Definitions (tests with code)
and statements with their proofs; nothing is evaluated.

  `hLaid6_atAll`   **hLaid6** at lay6 := `P5J.At.layout Zp`: the head's own field `plan.laid`
  `mom1B`, `atMoment1_is`   the test "the array is of the open segment's own second sending"
      (`K9.atMoment1`, Johnson/Desc/First/Batch/FormsIn.lean) reads the part through its frame's
      segment and shape alone
  `roomB`, `room_of`   a test on four numbers: each place (r, i) inside sI rows and sC columns is a
      place z < nW read at K columns: no place at all, or sC ≤ K and (sI − 1) K + sC ≤ nW
  `secB`, `hSec_of`, `hSec_atAll`   **hSec FROM ONE TEST WITH CODE** on the planner's list of
      segments, the public parameters, and the two letters shp, lay₀ (the request's shape; the
      rows' layout): at each attention segment, of that segment's list of arrays the one at moment
      1 stands at the number of the array of the reads, and its layout's sizes pass `roomB`
  `room_rejects`, `sec_accepts_empty`   `roomB` rejects one column too many. `secB` ACCEPTS AT AN
      EMPTY LIST OF SEGMENTS, for want of a case: hSec's own text does so too ("for all" over the
      list's entries): a negative test worth the name needs the planner's list at the public files

What is not claimed. That `secB` accepts at any files: it is to be evaluated there. No member of the
head hA. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.TestsAtAll
import Johnson.Desc.First.Att.K05PublicB
import Johnson.Desc.First.Batch.FormsIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Model OnBytes.Params
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.First (S ModelPart)
open VerifiableInference.Desc.First.Att.P (plannedK)
open ProofFile (Cl)

/-- The array b of the layout is of segment l's own second sending, by the shape shp. -/
def mom1B (shp : ReqShape) (l : ℕ) (b : ℕ × String) (A : ReqArray) : Bool :=
  b.1 == l &&
    match (shp.link[b.1]?).bind fun k => k.messages[A.message]? with
    | some m => m.moment == 1
    | none => false

theorem atMoment1_is (a : K9.Part) {shp : ReqShape} {l : ℕ} (hl : a.L.check.frame.link = l)
    (hs : a.L.check.frame.shape = shp) (b : ℕ × String) (A : ReqArray) :
    K9.atMoment1 a b A = mom1B shp l b A := by
  unfold K9.atMoment1 mom1B
  rw [hl, hs]
  cases (shp.link[b.1]?).bind fun k => k.messages[A.message]? <;> rfl

/-- Each place inside sI rows and sC columns is a place below nW, read at K columns. -/
def roomB (K nW sI sC : ℕ) : Bool :=
  sI == 0 || sC == 0 || (decide (sC ≤ K) && decide ((sI - 1) * K + sC ≤ nW))

theorem room_of {K nW sI sC : ℕ} (h : roomB K nW sI sC = true) :
    ∀ r i, r < sI → i < sC → ∃ z < nW, r = z / K ∧ i = z % K := by
  intro r i hr hi
  unfold roomB at h
  rw [Bool.or_eq_true, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · have := eq_of_beq h
    omega
  · have := eq_of_beq h
    omega
  · rw [Bool.and_eq_true] at h
    have hK : sC ≤ K := of_decide_eq_true h.1
    have hN : (sI - 1) * K + sC ≤ nW := of_decide_eq_true h.2
    have hiK : i < K := Nat.lt_of_lt_of_le hi hK
    have hrK : r * K ≤ (sI - 1) * K := Nat.mul_le_mul_right K (by omega)
    refine ⟨K * r + i, ?_, ?_, ?_⟩
    · rw [Nat.mul_comm K r]
      omega
    · rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hiK, Nat.add_zero]
    · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hiK]

/-- The negative test: one column too many. -/
theorem room_rejects : roomB 4 4 1 5 = false ∧ roomB 4 4 2 1 = false ∧ roomB 4 4 1 4 = true := by
  decide

/-- **The test.** built: the planner's list of segments; X: the public parameters. -/
def secB (built : Array Stages.LinkH) (X : Verify.Public) (shp : ReqShape) (lay₀ : ReqLayout) :
    Bool :=
  (List.range 25).all fun l =>
    !((linksFull[l]?).getD .layers == ModelPart.attention) || (X.A[l / 2]?).all fun Ap =>
      ((built.map (·.arrayOf)).getD l #[]).toList.zipIdx.all fun y =>
        (reqArray lay₀ y.1.1 y.1.2).all fun Ar =>
          !mom1B shp l y.1 Ar ||
            (y.2 == Ap.iU3 && roomB (plannedK Ap) Ap.nW Ar.sizeI Ar.sizeC)

/-- At an empty list of segments it accepts, for want of a case. -/
theorem sec_accepts_empty (X : Verify.Public) (shp : ReqShape) (lay₀ : ReqLayout) :
    secB #[] X shp lay₀ = true := by
  unfold secB
  rw [List.all_eq_true]
  intro l _
  cases X.A[l / 2]? <;> simp

/-- **hSec's text, from the test**, at letters. -/
theorem hSec_of {built : Array Stages.LinkH} {X : Verify.Public} {shp : ReqShape}
    {lay₀ : ReqLayout} (h : secB built X shp lay₀ = true) :
    ∀ l, l < 25 → (linksFull[l]?).getD .layers = .attention → ∀ Ap, X.A[l / 2]? = some Ap →
      ∀ (a : K9.Part) t cn Ar, a.L.check.frame.link = l → a.L.check.frame.shape = shp →
      ((built.map (·.arrayOf)).getD l #[])[t]? = some cn → reqArray lay₀ cn.1 cn.2 = some Ar →
      K9.atMoment1 a cn Ar = true →
      t = Ap.iU3 ∧ ∀ r i, r < Ar.sizeI → i < Ar.sizeC →
        ∃ z < Ap.nW, r = z / plannedK Ap ∧ i = z % plannedK Ap := by
  intro l hl hsub Ap hA a t cn Ar hlk hsh harr hreq hm
  have h1 := List.all_eq_true.1 h l (List.mem_range.2 hl)
  rw [hsub, hA] at h1
  have h2 : (((built.map (·.arrayOf)).getD l #[]).toList.zipIdx.all fun y =>
      (reqArray lay₀ y.1.1 y.1.2).all fun Ar =>
        !mom1B shp l y.1 Ar ||
          (y.2 == Ap.iU3 && roomB (plannedK Ap) Ap.nW Ar.sizeI Ar.sizeC)) = true := h1
  have hmem : (cn, t) ∈ ((built.map (·.arrayOf)).getD l #[]).toList.zipIdx :=
    List.mem_zipIdx_iff_getElem?.2 (by rw [Array.getElem?_toList]; exact harr)
  have h3 := List.all_eq_true.1 h2 (cn, t) hmem
  have h4 : ((reqArray lay₀ cn.1 cn.2).all fun Ar =>
      !mom1B shp l cn Ar || (t == Ap.iU3 && roomB (plannedK Ap) Ap.nW Ar.sizeI Ar.sizeC)) =
      true := h3
  rw [hreq] at h4
  have h5 : (!mom1B shp l cn Ar ||
      (t == Ap.iU3 && roomB (plannedK Ap) Ap.nW Ar.sizeI Ar.sizeC)) = true := h4
  rw [← atMoment1_is a hlk hsh, hm, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h5
  exact ⟨eq_of_beq h5.1, room_of h5.2⟩

section
variable {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : First.Look.Place}
  (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
include hA

/-- **hLaid6**, at the constant's own layout. -/
theorem hLaid6_atAll : _root_.Meaning.laidThere (P5J.At.X Zp) (_root_.Meaning.sizesOf (P5J.At.X Zp))
    (P5J.At.layout Zp) = true := hA.plan.laid

/-- **hSec.** -/
theorem hSec_atAll {shp : ReqShape} {lay₀ : ReqLayout}
    (h : secB Zp.made.p.built.links (P5J.At.X Zp) shp lay₀ = true) :
    ∀ l, l < 25 → (linksFull[l]?).getD .layers = .attention → ∀ Ap,
      (P5J.At.X Zp).A[l / 2]? = some Ap →
      ∀ (a : K9.Part) t cn Ar, a.L.check.frame.link = l → a.L.check.frame.shape = shp →
      (hA.𝔇.pubD.d3.arrayOf.getD l #[])[t]? = some cn → reqArray lay₀ cn.1 cn.2 = some Ar →
      K9.atMoment1 a cn Ar = true →
      t = Ap.iU3 ∧ ∀ r i, r < Ar.sizeI → i < Ar.sizeC →
        ∃ z < Ap.nW, r = z / plannedK Ap ∧ i = z % plannedK Ap :=
  hSec_of h

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.atMoment1_is
#print axioms VerifiableInference.Desc.K1.room_of
#print axioms VerifiableInference.Desc.K1.room_rejects
#print axioms VerifiableInference.Desc.K1.sec_accepts_empty
#print axioms VerifiableInference.Desc.K1.hSec_of
#print axioms VerifiableInference.Desc.K1.hLaid6_atAll
#print axioms VerifiableInference.Desc.K1.hSec_atAll
