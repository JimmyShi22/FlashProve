-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/StartUnit.lean: at the member of a chain's thread at which the
honest side of an attention segment's own rounds (kind K5) is seated: THE WORTH OF A SOFTMAX-TABLE
UNIT's START FORM: the seventh of the seven scalars that the unit's job lays is the total of the
unit's summand. Statements with their proofs. EVERY STATEMENT IS CONDITIONAL, and all hang on the
ties (K5Script, Honest/K5/Law/Script.lean), WHICH ARE NOT SHOWN.

  ok_front       the seat's test on the public data says yes at the challenges in front of every
                 round of the member
  alone_unit     what the row's jobs send by itself at a unit's part
  last_unit      the last of these scalars is the summand's total
  start_unit_at  **the unit's start form is worth the total of the unit's summand**, at the
                 challenges in front of the unit's part

Limits. Nothing is said on who sees what. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Starts
import Johnson.Desc.K5.Honest.Law.FitsSizes
import Johnson.Desc.K5.Honest.Law.Lengths

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff Fork)
open VerifiableInference.Desc (Block Claim OpenedColumn First.S)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ worldOwn)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First.Att.P (Par Heard)
open H2K5.Honest (shapes slotsTo K5In Laid Pub5 Chal aloneOk aloneKR aloneK leadK sK)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {Z : Seat5} {p : Par} {blk : Block First.S Claim}
  {A : OnBytes.Attention.Plan} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}

/-- What the row's jobs send by itself at the part of the unit number i. -/
theorem alone_unit (P : Pub5) (w : K5In) (c : Chal) {i : Nat} (hi : i < P.x.score.length) :
    (jobs P).alone i w c =
      (if i == 0 then aloneKR P w c else []) ++ leadK P w c i (sK P w c i).total := if_pos hi

/-- **The last of the scalars in front of a unit's sumcheck is the summand's total.** CONDITIONAL:
the test on the public data says yes at the challenges c. -/
theorem last_unit (P : Pub5) (w : K5In) {c : Chal} (ha : aloneOk P c = true) {i : Nat}
    (hi : i < P.x.score.length) :
    ((jobs P).alone i w c).getD ((if i = 0 then P.x.planeMessages * 3 else 0) + 6) zeroE =
      (sK P w c i).total := by
  have h6 := H2K5.Honest.Lengths.aloneK_length ha w hi
  have hl : ∀ sv : E, (leadK P w c i sv).getD 6 zeroE = sv := fun sv => by
    unfold leadK
    rw [List.getD_append_right _ _ _ _ (by rw [h6]), h6]
    rfl
  rw [alone_unit P w c hi]
  by_cases h0 : i = 0
  · subst h0
    have h3 := H2K5.Honest.Lengths.aloneKR_length ha w
    rw [if_pos rfl, if_pos (show ((0 : Nat) == 0) = true from rfl),
      List.getD_append_right _ _ _ _ (by rw [h3]; omega), h3,
      Nat.add_sub_cancel_left]
    exact hl _
  · rw [if_neg h0, if_neg (by simpa using h0), List.nil_append, Nat.zero_add]
    exact hl _

section
variable (Hs : K5Seated T b cells Z p blk) (Sc : K5Script T b cells Z A blk own rdOf)
  {k : Coins Bk} {s : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
  {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn} (hT : Thr T b k s m E)
  (hd : drawsFit blk.rounds ds = true)
  {att : VerifiableInference.Desc.First.AttOwn} (e : s.here = .att att)

include Hs Sc hT hd e in
/-- **The seat's test on the public data says yes in front of every round of the member.**
CONDITIONAL: on the ties; the half's seat; the thread in front. -/
theorem ok_front (n : Nat) : aloneOk Z.P (chalOf Z (m.st.heard ++ ds.take n)) = true := by
  have h := Hs.fits m.st.heard hT.2.1
  unfold Seat5.fits at h
  have h2 := (Bool.and_eq_true_iff.1 h).2
  have hz := fronts_key Sc hT hd e 0 n
  rw [List.take_zero, List.append_nil] at hz
  rw [← H2K5.Honest.aloneOk_congr (P := Z.P) (c := chalOf Z m.st.heard) fun i => by rw [hz]]
  exact h2

variable (hM : T.Moved blk k m E ds y cols) {dc : List Fmt.Drawn} {D : Bound GQ}
  (hD : MaskIs T own rdOf k s att m dc D) {G : Fork} {hd5 : Heard}
  (L : Laid Z.P.x att.F.next (roundsOf y.1) hd5 G)

include Hs Sc hT hd e hM hD L in
/-- **A softmax-table unit's start form is worth the total of the unit's summand**, at the
challenges in front of the unit's part. u: the unit's two numbers; o: what the hearing holds of it.
CONDITIONAL: as sum_slots (Honest/K5/Law/Slots.lean), and Laid. -/
theorem start_unit_at {i : Nat} {u : Nat × Nat} {o : Nat × MaskedSum.Heard}
    (hu : Z.P.x.score[i]? = some u) (ho : hd5.scores[i]? = some o) :
    (Aff.slot (o.1 + 6)).value Reading.gl (worldOwn (behindPart s att G) [] D) =
      Reading.gl.val (sK Z.P (inOf Z.P.S Z.link (cells m.st.input.trace))
        (chalOf Z (m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x i))) i).total := by
  have hi : i < Z.P.x.score.length := (List.getElem?_eq_some_iff.1 hu).1
  have hq := H2K5.Honest.shape_unit Z.P.x i u hu
  obtain ⟨SP, h7⟩ := L.unit i o _ ho hq
  have h := lead_slots Hs Sc hT hd hM e hD hq SP
    ((if i = 0 then Z.P.x.planeMessages * 3 else 0) + 6) (by omega)
  have hv : o.1 + 6 = att.F.next + slotsTo Z.P.x i +
      ((if i = 0 then Z.P.x.planeMessages * 3 else 0) + 6) := by
    have h2 : o.2.first = att.F.next + slotsTo Z.P.x i +
        ((if i = 0 then Z.P.x.planeMessages * 3 else 0) + 7) := SP.first
    omega
  rw [Aff.value_slot, hv, h, last_unit Z.P _ (ok_front Hs Sc hT hd e _) hi]

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.alone_unit
#print axioms ProofFile.Honest.K5.last_unit
#print axioms ProofFile.Honest.K5.ok_front
#print axioms ProofFile.Honest.K5.start_unit_at
