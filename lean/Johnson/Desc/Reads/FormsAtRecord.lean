-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/FormsAtRecord.lean: at a record that lies as Reads/HeadAtRecord.lean asks, the
four forms of the row's letters are the forms that the kind's own claims are made of.

Why. Clause (T) of the row ties the uses to the four forms of the policy at the seat's reader, which
is made of public numbers. The kind's block makes its claims at the reader that its seat reads off
the record. Where the two part, the row speaks of forms that nobody claims.

What is shown. Steps: they speak of the written seat `seatAt` (Johnson/Stored/HeadSeatAt.lean) and
of `lettersAt` (Johnson/Desc/Kinds/HeadFrame.lean).
  `lettersAt_reads`: where all the kind's letters are there, the places of the reads are what the
    seat reads of the record.
  `reads_at`: **the reader of the head's five reads at the record is the seat's of
    Reads/HeadAtRecord.lean.** It spends the clauses laid, cols and tab of `Lies`.
  `policy_congr`: a tool.
  `forms_at`: **the four forms of the letters are the kind's four forms of the policy at the letters
    that the kind's claims read off the record.**

Limits. The head's five reads alone, not the normalization's seven. That the block's claims are
these four forms among others is the kind's text, and is not restated here. Nothing on soundness.


-/
import Johnson.Desc.Reads.HeadAtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.AtSeat

open OnBytes.Model (Aff)
open OnBytes.Model.Head (Covered Tables)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.Reads.AtHead

/-- Where all letters are there, the places of the reads are what the seat reads of the record. -/
theorem lettersAt_reads {S' : Type} {p : Par} {L : Head.Seat S'} {s : S'} {g : Given} {bh : Behind}
    {pl : Places} (h : lettersAt p L s = .ok (g, bh, pl)) :
    L.reads s = some (pl.final, pl.head) := by
  unfold lettersAt at h
  cases hg : given p L s with
  | error e => simp [hg, bind, Except.bind] at h
  | ok g' =>
    cases hH : L.heard s with
    | none => simp [hg, hH, VerifiableInference.Desc.named, bind, Except.bind] at h
    | some H =>
      cases hr : L.reads s with
      | none => simp [hg, hH, hr, VerifiableInference.Desc.named, bind, Except.bind] at h
      | some x =>
        simp only [hg, hH, hr, VerifiableInference.Desc.named, bind, Except.bind, pure,
          Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, -, rfl⟩ := h
        rfl

/-- **The reader of the head's five reads at the record is the seat's**: so the four forms of the
letters are the forms that the kind's block claims there. -/
theorem reads_at (Z : Fill) {s : S} {o : HeadOwn} {cov : Covered}
    {x : OnBytes.Model.Head.Heard} {t : Tables} {g : Given} {bh : Behind} {pl : Places}
    (Q : Lies Z s o cov x t g bh pl) : pl.head = Z.seat.reads := by
  obtain ⟨tr, htr, hK⟩ := Q.cols
  have hr := lettersAt_reads Q.letters
  have hfork : s.fork? = some o.F := by
    unfold S.fork?
    rw [Q.here]
    simp [Q.opened]
  unfold seatAt at hr
  dsimp only at hr
  rw [Q.here, hfork] at hr
  simp only [Q.laid, htr, Option.bind_some] at hr
  split at hr
  · cases hr
  · have e : _ = pl.head := congrArg Prod.snd (Option.some.inj hr)
    rw [← e]
    show (⟨_⟩ : Head.Reads) = ⟨_⟩
    congr 1
    funext r i
    cases r <;>
      (show Aff.ent Z.iU3 _ _ = Aff.ent Z.iU3 _ _
       rw [hK, Q.tab]
       rfl)

/-- The kind's four forms of the policy at equal points and equal readers. -/
theorem policy_congr [Head.Sizes] [Head.Policy] [Head.Request] {I I' : FinalNorm.In}
    {R R' : Head.Reads} (hI : I = I') (hR : R = R') :
    (letI := I; letI := R; Head.policy) = (letI := I'; letI := R'; Head.policy) := by
  subst hI
  subst hR
  rfl

/-- **The four forms of the letters are the kind's four forms of the policy at the letters that the
kind's claims read off the record.** -/
theorem forms_at (Z : Fill) {s : S} {o : HeadOwn} {cov : Covered}
    {x : OnBytes.Model.Head.Heard} {t : Tables} {g : Given} {bh : Behind} {pl : Places}
    (Q : Lies Z s o cov x t g bh pl) :
    Z.letters.letters.forms () s = (letI := g; letI := pl; Head.policy) := by
  have e1 := reads_at Z Q
  obtain ⟨hg, -⟩ := lettersAt_ok Q.letters
  obtain ⟨z, y, hz1, -, -, hgE⟩ := Came.given_ok _ _ _ _ hg
  subst hgE
  have hlk : Z.look s = z := by
    unfold Fill.look
    rw [hz1]
    rfl
  have hpt : Z.letters.points s =
      (@fromLookup (sizesOf Z.h) (OnBytes.Model.Head.keyFloor Z.h) z.1 z.2).norm := by
    show (@fromLookup (sizesOf Z.h) (OnBytes.Model.Head.keyFloor Z.h) (Z.look s).1
      (Z.look s).2).norm = _
    rw [hlk]
  exact @policy_congr (sizesOf Z.h) (parOf Z.h Z.work).policy (requestOf s) _ _ _ _ hpt e1.symm

end VerifiableInference.Reads.AtSeat

#print axioms VerifiableInference.Reads.AtSeat.lettersAt_reads
#print axioms VerifiableInference.Reads.AtSeat.reads_at
#print axioms VerifiableInference.Reads.AtSeat.policy_congr
#print axioms VerifiableInference.Reads.AtSeat.forms_at
