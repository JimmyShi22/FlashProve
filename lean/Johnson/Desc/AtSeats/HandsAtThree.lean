-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/HandsAtThree.lean: WHAT ONE BLOCK OWES TOWARD "the
promise's half that reads the verifier's state alone is handed on" (`IM.Hands`, HandsDef.lean:
a light file), AT THREE BLOCKS: kind K13's block, W's commitment, the first
segment's opening. Statements with their proofs. On words: "the state" is the value of type S that
the description's fold carries from block to block. `hands_M3`, `hands_M4`, `hands_G`: **`IM.Hands
  N links ps E ft k b`** at b := the law's own block. FIVE
    OF THE SIX FIELDS ARE SHOWN (mark, shape, rows, members, book): from what is asked of the
    table at the block's row (`RowM3`, `RowM4`, `RowG`: tests with code; the kernel says yes at
    both written lists) and from what a yes does to the state. THE SIXTH (more: the further Bools
    E at the next border) IS A PREMISE: it hangs on which E is laid.
  At the first segment's opening two premises more, as in the tie there: in front the statement has
    as many groups as the plan says at 0; the test on the plan's own seats (`K1.ownSeatsB`).
  A seated block's debt is its lot's block's (`IM.Hands.under`): so these serve the description's
  own
    blocks at 355, 356 and 2.
What is not claimed. The field more. That the three tests on the table say yes at the filling that
is meant. Nothing on soundness.
-/
import Johnson.IMR.HandsDef
import Johnson.Desc.K13.Law.AtTableFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashBuild
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice
open Desc.Plain
open Johnson.Desc.First.Walk (LayPar)
open VerifiableInference.Desc (Block Place K1.step_ok)
open VerifiableInference.Desc.First (S ModelPart Numbers More)
open VerifiableInference.Desc.K13 (Where atM3 atM4)
open VerifiableInference.Desc.K13.Law
open VerifiableInference.Desc
open ProofFile (Cl)

/-- A yes of a block's step holds a yes of its decision. -/
theorem yes_decides {ft : ℕ} {b : Block S Cl} {s s' : S} (h : IM.Yes ft b s s') :
    ∃ rs gs, b.decide s rs gs = .ok s' := by
  obtain ⟨rs, cols, n, e⟩ := h
  obtain ⟨_, gs, hd⟩ := K1.step_ok ft _ _ _ rs cols n e
  exact ⟨_, gs, hd⟩

/-- **Kind K13's block.** -/
theorem hands_M3 (N : Numbers) (M : More) (links : List ModelPart) (ps : List Place)
    (E : ℕ → S → Bool) (ft k : ℕ) (P : Where) (hT : RowM3 N M links ps k)
    (more : ∀ s s', IM.Yes ft (atM3 P : Block S Cl) s s' → s.failed = none → s'.failed = none →
      IM.XK N links ps E k s = true → E (k + 1) s' = true) :
    IM.Hands N links ps E ft k (atM3 P : Block S Cl) where
  mark := fun s s' hy h => by
    obtain ⟨rs, gs, hd⟩ := yes_decides hy
    obtain ⟨_, _, _, _, e⟩ := atM3_rec hd
    rw [e]
    exact h
  shape := fun s s' hy _ _ _ => by
    obtain ⟨rs, gs, hd⟩ := yes_decides hy
    exact shape_behind hd links _ hT.next
  rows := fun s s' _ _ _ _ => by
    show First.rowsHeld N (openAt links ps (k + 1)) s' = true
    unfold First.rowsHeld
    rw [hT.noRows]
    rfl
  members := fun s s' _ _ _ _ => by
    show First.membersHeld N (openAt links ps (k + 1)) s' = true
    unfold First.membersHeld
    rw [hT.noRows]
    rfl
  book := fun s s' hy _ _ hx => by
    obtain ⟨rs, gs, hd⟩ := yes_decides hy
    have hbk := (IM.xk_parts hx).2.2.2.1
    obtain ⟨e1, e2⟩ := atM3_book hd
    unfold First.bookAt at hbk ⊢
    rw [e1, e2, hT.trees, hT.msgs]
    exact hbk
  more := more

/-- **W's commitment.** -/
theorem hands_M4 (N : Numbers) (M : More) (links : List ModelPart) (ps : List Place)
    (E : ℕ → S → Bool) (ft k : ℕ) (P : Where) (P' : K1.Par)
    (hT : RowM4 N M links ps k (K1.layOf P').shapes.size P'.sent.size)
    (more : ∀ s s', IM.Yes ft (atM4 P (K1.sendAtS P') : Block S Cl) s s' → s.failed = none →
      s'.failed = none → IM.XK N links ps E k s = true → E (k + 1) s' = true) :
    IM.Hands N links ps E ft k (atM4 P (K1.sendAtS P') : Block S Cl) := by
  have two : ∀ s s', IM.Yes ft (atM4 P (K1.sendAtS P') : Block S Cl) s s' → ∃ r₁ r₂ gs,
      (atM4 (Cl := Cl) P (K1.sendAtS P')).decide s [r₁, r₂] gs = .ok s' := fun s s' hy => by
    obtain ⟨rs, cols, n, e⟩ := hy
    exact StepM4.decide (Pp := Unit) (x := ((), s)) (x' := ((), s')) ⟨rfl, ft, rs, cols, n, e⟩
  refine ⟨fun s s' hy h => ?_, fun s s' hy _ _ _ => ?_, fun s s' _ _ _ _ => ?_,
    fun s s' _ _ _ _ => ?_, fun s s' hy _ _ hx => ?_, more⟩
  · obtain ⟨r₁, r₂, gs, hd⟩ := two s s' hy
    rw [(atM4_rec hd).2.2.1]
    exact h
  · obtain ⟨r₁, r₂, gs, hd⟩ := two s s' hy
    obtain ⟨⟨o, ho⟩, hw, _, _, _⟩ := atM4_rec hd
    cases hp : ps[k + 1]? with
    | none => simp [First.shapeAt, First.standOf, S.noneWaits, ho, hw]
    | some p' =>
      simp [First.shapeAt, First.standOf, S.noneWaits, S.link?, ho, hw, hT.next p' hp]
  · show First.rowsHeld N (openAt links ps (k + 1)) s' = true
    unfold First.rowsHeld
    rw [hT.noRows]
    rfl
  · show First.membersHeld N (openAt links ps (k + 1)) s' = true
    unfold First.membersHeld
    rw [hT.noRows]
    rfl
  · obtain ⟨r₁, r₂, gs, hd⟩ := two s s' hy
    have hbk := (IM.xk_parts hx).2.2.2.1
    unfold First.bookAt at hbk
    simp only [Bool.and_eq_true, beq_iff_eq] at hbk
    obtain ⟨⟨b1, b2⟩, b3⟩ := hbk
    have hb := atM4_booked hd
    unfold First.bookAt
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨by rw [hb.trees, b1, hT.trees], hb.full b2⟩, by rw [hb.msgs, b3, hT.msgs]⟩

/-- **The first segment's opening.** -/
theorem hands_G (N : Numbers) (M : More) (links : List ModelPart) (ps : List Place)
    (E : ℕ → S → Bool) (ft k : ℕ) (q : Params.First) (gp : GPar) (nm : String) (X : LayPar)
    (fvs : List Bool) (kCol : ℕ) (mk : List First.Pub)
    (hT : RowG N M links ps k (K1.layOf (K1.firstPar q gp)).shapes.size
      (K1.firstPar q gp).sent.size mk)
    (hgroups : ∀ s, IM.XK N links ps E k s = true → N.groupAt 0 = s.st.groups.size)
    (hown : ∀ s, IM.XK N links ps E k s = true →
      K1.ownSeatsB N (openAt links ps (k + 1)) (K1.firstPar q gp)
        (s.check.frame.atMoment 0).length s.book.trees.size = true)
    (more : ∀ s s', IM.Yes ft (K1.openingZero q gp nm X fvs kCol : Block S Cl) s s' →
      s.failed = none → s'.failed = none → IM.XK N links ps E k s = true →
      E (k + 1) s' = true) :
    IM.Hands N links ps E ft k (K1.openingZero q gp nm X fvs kCol : Block S Cl) := by
  have two : ∀ s s', IM.Yes ft (K1.openingZero q gp nm X fvs kCol : Block S Cl) s s' →
      ∃ r₁ r₂ gs, (K1.openingZero q gp nm X fvs kCol : Block S Cl).decide s [r₁, r₂] gs =
        .ok s' := fun s s' hy => by
    obtain ⟨rs, cols, n, e⟩ := hy
    exact StepG.decide (Pp := Unit) (x := ((), s)) (x' := ((), s')) ⟨rfl, ft, rs, cols, n, e⟩
  refine ⟨fun s s' hy h => ?_, fun s s' hy _ _ _ => ?_, fun s s' hy _ _ hx => ?_,
    fun s s' hy _ _ hx => ?_, fun s s' hy _ _ hx => ?_, more⟩
  · obtain ⟨r₁, r₂, gs, hd⟩ := two s s' hy
    rw [(K1.openingZero_rec hd).2.2.1]
    exact h
  · obtain ⟨r₁, r₂, gs, hd⟩ := two s s' hy
    obtain ⟨hstand, ⟨L, hL, hL0⟩, _, hw, _, _, _⟩ := K1.openingZero_rec hd
    obtain ⟨p', hp, hs', hl'⟩ := hT.next
    rw [hp]
    simp [First.shapeAt, S.noneWaits, hstand, hs', hw, hL, hL0, hl']
  · obtain ⟨r₁, r₂, gs, hd⟩ := two s s' hy
    exact K1.openingZero_rowsHeld hd N _ hT.segs hT.noList (hgroups s hx)
  · obtain ⟨r₁, r₂, gs, hd⟩ := two s s' hy
    have hbk := (IM.xk_parts hx).2.2.2.1
    unfold First.bookAt at hbk
    simp only [Bool.and_eq_true, beq_iff_eq] at hbk
    exact K1.openingZero_membersHeld hd N _ hT.segs (hgroups s hx) hbk.1.2 (hown s hx)
  · obtain ⟨r₁, r₂, gs, hd⟩ := two s s' hy
    obtain ⟨_, _, _, _, hb, _, _⟩ := K1.openingZero_rec hd
    have hbk := (IM.xk_parts hx).2.2.2.1
    unfold First.bookAt at hbk
    simp only [Bool.and_eq_true, beq_iff_eq] at hbk
    obtain ⟨⟨b1, b2⟩, b3⟩ := hbk
    unfold First.bookAt
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨by rw [hb.trees, b1, hT.trees], hb.full b2⟩, by rw [hb.msgs, b3, hT.msgs]⟩

end HashBuild
