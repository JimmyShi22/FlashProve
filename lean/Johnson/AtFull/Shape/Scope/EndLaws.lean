-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/EndLaws.lean: WHAT A STATE AT THE FIRST CHAIN's END OWES THE THIRD CHAIN'S START,
READ OFF ITS SHAPE. The shape keeps of the end, at .mem o, what o.lin lays (endSh,
Johnson/Desc/First/Shape/Chain.lean; laidSh, K13/Honest/ShapeDefs.lean). General in the state and
the parameters; nothing is evaluated.

* numbersSh: Third.numbersOk's text on the statement's shape; numbers_same ties the two.
* **endOk L a**: a Bool on the whole shape: no count waits; the end's record is there, with W's number;
  the plain arm; a mask's number just where the parameters send masks ahead; numbersSh at the three
  numbers.
* **firstOut_of_endOk**: where endOk says yes at a state's shape: no count waits there, firstOfS
  returns, and firstOutFrom returns at what it returns.

Limits. Nothing says that endOk says yes at any shape. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.FrameForm
import Johnson.Desc.Third.Border

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape.Scope
open OnBytes
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape (endSh)
open VerifiableInference.Desc.Third (numbersOk plainArm firstOutFrom firstOfS FirstOut)
open VerifiableInference.Desc.K13.Honest (StSh stSh)

/-- numbersOk's text on the statement's shape. -/
def numbersSh (L : Params.LinShape) (w own : Nat) (mask : Option Nat) (t : StSh) : Bool :=
  match t.msgs[w]?, t.groups[own]? with
  | some x, some G =>
    decide (x.shape = L.w) && G.members.contains w && G.code == L.w.code &&
      G.maskCode == L.ownMaskCode && !G.inRun &&
      (match mask with
        | none => true
        | some m =>
          match t.msgs[m]? with
          | some y => !y.sampled && y.shape.answers == 0
          | none => false)
  | _, _ => false

/-- **numbersOk reads the statement's shape alone.** -/
theorem numbers_same (L : Params.LinShape) (f : FirstOut) :
    numbersOk L f = numbersSh L f.w f.own f.mask (stSh f.st) := by
  unfold numbersOk numbersSh stSh
  simp only [Array.getElem?_map]
  cases f.st.oracles[f.w]? with
  | none => rfl
  | some x =>
    cases f.st.groups[f.own]? with
    | none => rfl
    | some G =>
      cases f.mask with
      | none => rfl
      | some m =>
        dsimp only
        generalize f.st.oracles[m]? = q
        cases q <;> rfl

/-- **What the third chain's start asks of the first chain's end, as a Bool on a shape.** -/
def endOk (L : Params.LinShape) (a : ShA) : Bool :=
  VerifiableInference.Desc.First.Tape.RowsOwed.noneWaits a.1.rowsOwed &&
    match a.1.atEnd with
    | some (_, _, some q) =>
      q.w != noId && plainArm L && q.mask.isSome == L.masksAhead &&
        numbersSh L q.w q.own q.mask a.1.st
    | _ => false

/-- **Where endOk says yes at a state's shape.** -/
theorem firstOut_of_endOk {L : Params.LinShape} {s : S} (h : endOk L (shA s) = true) :
    s.noneWaits = true ∧ ∃ f, firstOfS s = some f ∧
      ∃ o, firstOutFrom L f.st f.book f.roots f.w f.own f.mask f.pending = some o := by
  unfold endOk at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · have e : VerifiableInference.Desc.First.Tape.RowsOwed.noneWaits s.rowsOwed = s.noneWaits := by
      unfold S.noneWaits VerifiableInference.Desc.First.Tape.RowsOwed.noneWaits
      rfl
    rw [← e]
    exact h1
  · have ea : (shA s).1.atEnd = endSh s.here := rfl
    have est : (shA s).1.st = stSh s.st := VerifiableInference.Desc.First.Shape.chainSh_st s
    rw [ea, est] at h2
    cases hh : s.here with
    | mem o =>
      rw [hh] at h2
      cases hl : o.lin with
      | none =>
        have e : endSh (.mem o) = some (o.msg, o.ids, none) := by
          show some (o.msg, o.ids, o.lin.map VerifiableInference.Desc.K13.Honest.laidSh) = _
          rw [hl]
          rfl
        rw [e] at h2
        cases h2
      | some l =>
        have e : endSh (.mem o) =
            some (o.msg, o.ids, some (VerifiableInference.Desc.K13.Honest.laidSh l)) := by
          show some (o.msg, o.ids, o.lin.map VerifiableInference.Desc.K13.Honest.laidSh) = _
          rw [hl]
          rfl
        rw [e] at h2
        simp only [Bool.and_eq_true] at h2
        obtain ⟨⟨⟨hw, hp⟩, hm⟩, hn⟩ := h2
        have hw' : (l.w != noId) = true := hw
        have hfe : s.firstEnd? = some ⟨s.st, s.book, l⟩ := by
          unfold S.firstEnd?
          rw [hh]
          show (o.lin.bind fun l => if (l.w != noId) = true then
            some (⟨s.st, s.book, l⟩ : Proof.FirstEnd) else none) = _
          rw [hl]
          show (if (l.w != noId) = true then some (⟨s.st, s.book, l⟩ : Proof.FirstEnd) else none) = _
          rw [if_pos hw']
        have hr : s.rows = [VerifiableInference.Desc.First.rowOfClaim l.claim] := by
          unfold S.rows
          rw [hh]
          show (match o.lin with | some l => _ | none => _) = _
          rw [hl]
        refine ⟨VerifiableInference.Desc.Third.FirstEnd₃.mk s.st s.book s.roots l.w l.own l.mask
          s.rows, ?_, ?_⟩
        · unfold firstOfS
          rw [hfe]
          rfl
        · show ∃ o', firstOutFrom L s.st s.book s.roots l.w l.own l.mask s.rows = some o'
          rw [hr]
          have hn' : numbersOk L
              { st := s.st, book := s.book, roots := s.roots,
                g := (VerifiableInference.Desc.First.rowOfClaim l.claim).g, w := l.w, own := l.own,
                mask := l.mask } = true := by
            rw [numbers_same]
            exact hn
          refine ⟨FirstOut.mk s.st s.book s.roots (VerifiableInference.Desc.First.rowOfClaim l.claim).g
            l.w l.own l.mask, ?_⟩
          unfold firstOutFrom
          have hc : (plainArm L && l.mask.isSome == L.masksAhead) = true := by
            rw [Bool.and_eq_true]
            exact ⟨hp, hm⟩
          simp only [hc, if_true, hn']
    | between =>
      rw [hh] at h2
      cases h2
    | lay a =>
      rw [hh] at h2
      cases h2
    | att a =>
      rw [hh] at h2
      cases h2
    | head a =>
      rw [hh] at h2
      cases h2
    | fin a =>
      rw [hh] at h2
      cases h2

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.numbers_same
#print axioms Johnson.AtFull.Shape.Scope.firstOut_of_endOk
