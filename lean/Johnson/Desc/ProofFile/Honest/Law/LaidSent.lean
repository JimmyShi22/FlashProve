-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/LaidSent.lean: THE ONE SENTENCE THAT JOINS THE LAWS ON THE LAYING:
at a message that fits and a job that fits, whose data is the filling's, each element of each of V's
arrays that is laid in that message, inside the size that V says, stands in what the sender lays, at
one main row and place; no two elements share one; the place is none of the pad's; from it the way
back reads the element. Theorems; no definition outside the instance at the foot. What is WRITTEN
where: no sentence on what a coin is for.

Main names (namespace ProofFile.Honest).
  sent_of_lays   OF ANY FILLING D (RowData): where D lays data, at a main row and place of a sampled
      message, inside its rows and its length and off padInMain's places, the sender's main entry
      (rowsR, Honest/K1/Coins.lean) is D's entry there: two arms, by the degree of the main rows.
      Five of its premises are those of main_data_e and main_data_f, to the letter: a second filling
      calls it as this file does. ASKED BY NAME BESIDE THEM: readyAt.
  lays_of_back, entry_of_back   where laidBack reads an element of one of V's arrays, laidData lays
      data, and its entry is V's value at that element.
  code_of_msgFits, pow_of_lengths   two ties that need not be asked: a message that fits and holds
      an array names a base code of the array of codes; under the sender's own test its length is a
      power of two.
  laid_sent   THE SENTENCE, at laidData (Honest/LaidData.lean).

By calls: once_and_back_msg (Law/LaidOnce.lean); elements_apart_msg (Law/LaidApart.lean); lays_clear
(Law/LaidLaw.lean); main_data_e, main_data_f (K1/DataLaw.lean); fits_lengths (K1/PadLaw.lean).

WHAT STAYS OPEN. (1) FOUR TIES OF THE SEAT TO THE SENDER's JOB ARE PREMISES, PAID BY NOBODY HERE:
the seat names (l, m) at the address; the request's shape has the message M there; the job's message
number k has M's shape; the job's codes are the filling's. (2) The sender reads the filling by
RowData.at_, which asks neither how much has been heard nor its form: so readyAt IS A NAMED PREMISE
of both sentences: as many challenges have been heard as the message's data reads, and they have the
form that it reads. THE EQUATION OF VALUES HOLDS WITHOUT readyAt TOO: no step of its proof spends
it; it is asked by name because without it the right side means nothing (Honest/RowData.lean), and
it is spent on the end's clause that says so. That "heard" is the count at which the sender's part
begins is unproved. (3) "None of the pad's": the places are padInMain's (Honest/RowData.lean). That
the sender's coins in a sampled message's main rows stand at just these places is read off two texts
(K1/DataLaw.lean's head): no statement says it. (4) Over the base field the sender lays 0 where the
filling hands an element of the extension field: no test here bars that. (5) That V says the
layout's sizes is not asked: both bounds on (i, c) are premises. (6) Nothing on the mask table.
Nothing on a sample or its answers. Nothing on any property.

THE PREMISES CAN BE MET: at the foot an instance AS A TERM, so that Lean itself holds every premise:
the layout, shape, codes and seat of the tests of Honest/K1/FirstData.lean, a job of two messages of
that shape, synthetic values, element (5, 1) of the array "M2". The values are synthetic because the
reading of an array's name does not reduce in the kernel: a #guard line ties their size to that of
the first sendings' filling.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.Law.LaidOnce
import Johnson.Desc.ProofFile.Honest.K1.DataLaw
import Johnson.Desc.ProofFile.Honest.K1.PadLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open OnBytes.Params (ReqArray ReqLayout ReqShape ReqMessage)
open OnBytes.Slice (GF GE)
open VerifiableInference.Desc (laidAt)
open Johnson.Prover.Send (shapeAt)

/-- **WHERE A FILLING LAYS DATA, THE SENDER LAYS THAT DATA**: of any filling D: at a main row and
place of a sampled message, inside its rows and its length and off the places of the pad. ASKED BY
NAME: readyAt: the sender reads the filling by the call that asks neither how much has been heard
nor its form; where "ready" says no, an entry's value means nothing. The end's first clause says
what the premise buys: the entry is handed as many challenges as the message's data reads, of the
form that it reads. -/
theorem sent_of_lays (D : RowData) (Rd : Readers) (hd : List Fmt.Drawn)
    (P : VerifiableInference.Desc.K1.Par) (ride : Nat → Option K1.Ride) (sender : Addr) (k : Nat)
    (cs : Cs (K1.dueR P ride)) (r j : Nat) (hl : D.lays ⟨sender, k⟩ r j = true)
    (hready : D.readyAt hd ⟨sender, k⟩ = true) (hr : r < (shapeAt P k).mainRows)
    (hj : j < (P.codes.base.getD (shapeAt P k).code default).ell)
    (ha : (shapeAt P k).answers ≠ 0)
    (hp : (r, j) ∉ padInMain (P.codes.base.getD (shapeAt P k).code default).ell (shapeAt P k)) :
    ((hd.take (D.heardAt ⟨sender, k⟩)).length = D.heardAt ⟨sender, k⟩ ∧
      D.ready (hd.take (D.heardAt ⟨sender, k⟩)) ⟨sender, k⟩ = true) ∧
    (((shapeAt P k).mainDeg == 3) = true →
      (K1.rowsR P ride (D.forSend Rd sender hd) cs k).mainE r j =
        match D.entry Rd (hd.take (D.heardAt ⟨sender, k⟩)) ⟨sender, k⟩ r j with
        | .inr x => x
        | .inl x => algebraMap GF GE x) ∧
    (((shapeAt P k).mainDeg == 3) = false →
      (K1.rowsR P ride (D.forSend Rd sender hd) cs k).mainF r j =
        match D.entry Rd (hd.take (D.heardAt ⟨sender, k⟩)) ⟨sender, k⟩ r j with
        | .inl x => x
        | .inr _ => 0) := by
  have hdat : D.forSend Rd sender hd k r j =
      some (D.entry Rd (hd.take (D.heardAt ⟨sender, k⟩)) ⟨sender, k⟩ r j) := by
    unfold RowData.forSend RowData.at_
    rw [if_pos hl]
  have hrd : (hd.take (D.heardAt ⟨sender, k⟩)).length = D.heardAt ⟨sender, k⟩ ∧
      D.ready (hd.take (D.heardAt ⟨sender, k⟩)) ⟨sender, k⟩ = true := by
    unfold RowData.readyAt RowData.heardOk at hready
    rw [Bool.and_eq_true, decide_eq_true_eq] at hready
    exact ⟨by rw [List.length_take]; omega, hready.2⟩
  refine ⟨hrd, fun h3 => ?_, fun h3 => ?_⟩
  · rw [K1.main_data_e P ride _ cs k r j h3 hr hj ha hp, hdat]
    cases D.entry Rd (hd.take (D.heardAt ⟨sender, k⟩)) ⟨sender, k⟩ r j <;> rfl
  · rw [K1.main_data_f P ride _ cs k r j h3 hr hj ha hp, hdat]
    cases D.entry Rd (hd.take (D.heardAt ⟨sender, k⟩)) ⟨sender, k⟩ r j <;> rfl

section
variable (codes : OnBytes.Codes) (s : ReqShape) (lay : ReqLayout)
  (seat : MsgAddr → Option (Nat × Nat)) (heard : MsgAddr → Nat) (V : ArrayVals)

/-- Where the way back reads an element of one of V's arrays, inside what V says, in a message that
fits, the filling lays data. -/
theorem lays_of_back {x : MsgAddr} {l m r j i c : Nat} {a : ReqArray} {z : Nat × Nat}
    (t1 : seat x = some (l, m)) (hfit : msgFits codes s lay l m = true)
    (hb : laidBack lay l m r j = some (a, i, c)) (hV : V.size l a.name = some z)
    (hz : i < z.1 ∧ c < z.2) : (laidData codes s lay seat heard V).lays x r j = true := by
  show (match seat x with
    | some (l, m) =>
      msgFits codes s lay l m && (laidBack lay l m r j).any fun y =>
        (V.size l y.1.name).any fun z => decide (y.2.1 < z.1 ∧ y.2.2 < z.2)
    | none => false) = true
  rw [t1]
  simp only [hfit, hb, hV, Option.any_some, Bool.true_and, decide_eq_true_eq]
  exact hz

/-- And the filling's entry there is V's value at that element. -/
theorem entry_of_back (Rd : Readers) (h : List Fmt.Drawn) {x : MsgAddr} {l m r j i c : Nat}
    {a : ReqArray} (t1 : seat x = some (l, m)) (hb : laidBack lay l m r j = some (a, i, c)) :
    (laidData codes s lay seat heard V).entry Rd h x r j = V.val Rd h l a.name i c := by
  show (match seat x with
    | some (l, m) =>
      match laidBack lay l m r j with
      | some (y, i, c) => V.val Rd h l y.name i c
      | none => .inl (OnBytes.Slice.toF 0)
    | none => .inl (OnBytes.Slice.toF 0)) = _
  rw [t1]
  simp only [hb]

/-- A message that fits and holds an array names a base code in the array of codes. -/
theorem code_of_msgFits {l m : Nat} {M : ReqMessage} (hfit : msgFits codes s lay l m = true)
    (t2 : (s.link.getD l default).messages[m]? = some M) {a : ReqArray}
    (ha : a ∈ (lay.link.getD l []).filter fun a => a.message == m) :
    ∃ cd, codes.base[M.shape.code]? = some cd := by
  unfold msgFits at hfit
  rw [t2] at hfit
  have hne : ((lay.link.getD l []).filter fun a => a.message == m).isEmpty = false := by
    cases hq : (lay.link.getD l []).filter fun a => a.message == m with
    | nil => rw [hq] at ha; cases ha
    | cons _ _ => rfl
  simp only [Option.any_some, hne, Bool.false_or, Bool.and_eq_true] at hfit
  have h2 := hfit.2
  unfold VerifiableInference.Desc.Own.reqMessageLaid at h2
  rw [hne, Bool.false_or, Bool.and_eq_true] at h2
  have h3 := h2.2
  split at h3
  · rename_i c pad hc _
    exact ⟨c, hc⟩
  · cases h3

/-- Under the test on the codes' lengths a code of the array has a power of two for its length. -/
theorem pow_of_lengths {n : Nat} {cd : OnBytes.Code}
    (h : VerifiableInference.Desc.Own.lengthsFit codes = true) (hc : codes.base[n]? = some cd) :
    OnBytes.powerOfTwo cd.ell = true := by
  simp only [VerifiableInference.Desc.Own.lengthsFit, Bool.and_eq_true, Array.all_eq_true] at h
  obtain ⟨hn, rfl⟩ := Array.getElem?_eq_some_iff.1 hc
  exact h.1 n hn

/-- **THE ONE SENTENCE.** At a message that fits and a job that fits, whose data is the filling's:
each element of each of V's arrays that is laid in that message stands in what the sender lays, at
one main row and place; from there the way back reads it; the place lies inside the main rows and
the length and off the places of the pad; no other element lies there. -/
theorem laid_sent (Rd : Readers) (hd : List Fmt.Drawn) (P : VerifiableInference.Desc.K1.Par)
    (ride : Nat → Option K1.Ride) (sender : Addr) (k l m : Nat) (M : ReqMessage)
    (cs : Cs (K1.dueR P ride))
    (t1 : seat ⟨sender, k⟩ = some (l, m)) (t2 : (s.link.getD l default).messages[m]? = some M)
    (t3 : shapeAt P k = M.shape) (t4 : P.codes = codes)
    (hfit : msgFits codes s lay l m = true) (hsend : K1.sendFits P ride = true)
    (hready : (laidData codes s lay seat heard V).readyAt hd ⟨sender, k⟩ = true)
    (a : ReqArray) (ha : a ∈ (lay.link.getD l []).filter fun a => a.message == m) (i c : Nat)
    (hi : i < a.sizeI) (hc : c < a.sizeC) (z : Nat × Nat) (hV : V.size l a.name = some z)
    (hz : i < z.1 ∧ c < z.2) :
    ∃ cd r j, codes.base[M.shape.code]? = some cd ∧
      laidAt a i c = some (r, j) ∧ laidBack lay l m r j = some (a, i, c) ∧
      r < M.shape.mainRows ∧ j < cd.ell ∧ (r, j) ∉ padInMain cd.ell M.shape ∧
      (hd.take (heard ⟨sender, k⟩)).length = heard ⟨sender, k⟩ ∧
      (laidData codes s lay seat heard V).ready (hd.take (heard ⟨sender, k⟩)) ⟨sender, k⟩ = true ∧
      ((M.shape.mainDeg == 3) = true →
        (K1.rowsR P ride ((laidData codes s lay seat heard V).forSend Rd sender hd) cs
            k).mainE r j =
          match V.val Rd (hd.take (heard ⟨sender, k⟩)) l a.name i c with
          | .inr x => x
          | .inl x => algebraMap GF GE x) ∧
      ((M.shape.mainDeg == 3) = false →
        (K1.rowsR P ride ((laidData codes s lay seat heard V).forSend Rd sender hd) cs
            k).mainF r j =
          match V.val Rd (hd.take (heard ⟨sender, k⟩)) l a.name i c with
          | .inl x => x
          | .inr _ => 0) ∧
      ∀ a' ∈ (lay.link.getD l []).filter (fun a => a.message == m), ∀ i' c',
        laidAt a' i' c' = some (r, j) → a' = a ∧ i' = i ∧ c' = c := by
  obtain ⟨cd, t5⟩ := code_of_msgFits codes s lay hfit t2 ha
  have t6 : OnBytes.powerOfTwo cd.ell = true :=
    pow_of_lengths codes (t4 ▸ K1.fits_lengths P ride hsend) t5
  obtain ⟨r, j, hp, hb⟩ := once_and_back_msg hfit ha hi hc
  have hl := lays_of_back codes s lay seat heard V t1 hfit hb hV hz
  obtain ⟨b1, b2, b3, b4⟩ := lays_clear codes s lay seat heard V ⟨sender, k⟩ r j l m M cd hl t1 t2
    t5 t6
  have ec : (P.codes.base.getD (shapeAt P k).code default) = cd := by
    rw [t3, t4, Array.getD_eq_getD_getElem?, t5, Option.getD_some]
  have hs := sent_of_lays (laidData codes s lay seat heard V) Rd hd P ride sender k cs r j hl
    hready (by rw [t3]; exact b1) (by rw [ec]; exact b2) (by rw [t3]; exact b4)
    (by rw [ec, t3]; exact b3)
  rw [entry_of_back codes s lay seat heard V Rd _ t1 hb, t3] at hs
  exact ⟨cd, r, j, t5, hp, hb, b1, b2, b3, hs.1.1, hs.1.2, hs.2.1, hs.2.2,
    fun a' ha' i' c' h' => elements_apart_msg hfit ha' ha h' hp⟩

end

/-! ### The premises can be met: an instance, as a term -/

namespace LaidSentToy
open K1.FirstDataToy

/-- A job with the toy's codes that sends two messages of the toy's shape: number 0 is another's,
number 1 the segment's own. -/
def P : VerifiableInference.Desc.K1.Par :=
  { place := (toyTo 0).place, codes := codes, gp := ⟨1, 0⟩, work := 0
    parts := [("toy", #[⟨o, 0⟩, ⟨o, 0⟩])] }

/-- Synthetic values for segment 4's arrays, of the size of the toy's "M2": element (i, c) is
10 i + c. -/
def V : ArrayVals :=
  { size := fun l _ => if l == 4 then some (1366, 2) else none
    val := fun _ _ _ _ i c => .inl (OnBytes.Slice.toF (10 * i.toUInt64 + c.toUInt64)) }

/-- The job fits. (The test on the codes' lengths walks an array, which does not reduce in the
kernel: it is opened by hand; the rest is decided.) -/
theorem toy_sendFits : K1.sendFits P (fun _ => none) = true := by
  have hlen : VerifiableInference.Desc.Own.lengthsFit P.codes = true := by
    simp only [VerifiableInference.Desc.Own.lengthsFit, Bool.and_eq_true, Array.all_eq_true]
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have h1 : P.codes.base.size = 1 := rfl
      obtain rfl : i = 0 := by omega
      show VerifiableInference.Desc.Own.twoPower 2048 = true
      decide
    · have h0 : P.codes.mask.size = 0 := rfl
      omega
  unfold K1.sendFits
  rw [hlen, Bool.true_and]
  decide

/-- **At the toy every premise of laid_sent holds**: at element (5, 1) of the array "M2", whatever
the sender's coins. -/
example (cs : Cs (K1.dueR P fun _ => none)) :
    ∃ cd r j, codes.base[o.code]? = some cd ∧
      laidAt ⟨"M2", 0, 1366, 2, blocks⟩ 5 1 = some (r, j) ∧
      laidBack lay 4 0 r j = some (⟨"M2", 0, 1366, 2, blocks⟩, 5, 1) ∧
      r < o.mainRows ∧ j < cd.ell ∧ (r, j) ∉ padInMain cd.ell o ∧
      (K1.rowsR P (fun _ => none)
        ((laidData codes sh lay seat (fun _ => 0) V).forSend R (toyTo 0) []) cs 1).mainF r j =
        OnBytes.Slice.toF 51 := by
  obtain ⟨cd, r, j, h1, h2, h3, h4, h5, h6, -, -, -, h8, -⟩ :=
    laid_sent codes sh lay seat (fun _ => 0) V R [] P (fun _ => none) (toyTo 0) 1 4 0
      ⟨o, 0, 0, 0⟩ cs (by decide) (by decide) rfl rfl (by decide) toy_sendFits (by decide)
      ⟨"M2", 0, 1366, 2, blocks⟩ (by decide) 5 1 (by decide) (by decide) (1366, 2) rfl
      (by decide)
  exact ⟨cd, r, j, h1, h2, h3, h4, h5, h6, h8 rfl⟩

-- the filling of the first sendings says the same size of "M2" as the synthetic values (by the
-- evaluator: the name's reading does not reduce in the kernel)
#guard (K1.cellsVals OnBytes.HonestTrace.Sz.small).size 4 "M2" == V.size 4 "M2"

end LaidSentToy

end ProofFile.Honest

#print axioms ProofFile.Honest.sent_of_lays
#print axioms ProofFile.Honest.lays_of_back
#print axioms ProofFile.Honest.entry_of_back
#print axioms ProofFile.Honest.code_of_msgFits
#print axioms ProofFile.Honest.pow_of_lengths
#print axioms ProofFile.Honest.laid_sent
#print axioms ProofFile.Honest.LaidSentToy.toy_sendFits
#print axioms ProofFile.Honest.LaidSentToy.P
#print axioms ProofFile.Honest.LaidSentToy.V
