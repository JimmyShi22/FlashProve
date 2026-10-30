-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Close/Law/ViewText.lean (kind K10): THE TEXT OF A MEMBER's CHANGE OF SHAPE
(`R.view a`) AT THE PROGRAMS' OWN MEMBER, ON MESSAGES: so the step that CubeAt.lean's Limit (1)
leaves open ("from rowM R (R.G.msg μ, r) ⟨a, j⟩ x to μ's entry at member a") is taken, and
`WordsAre`
(CubeAt.lean) follows for the words that the witness's one reader gives. Statements and proofs.

Why. K10's law's end gives every open item "row" of the segment under `LaidOn`; that is parted into
public ties and `WordsAre` (laidOn_of_cube, laidOn_of_shapes). `WordsAre` speaks of rows BEHIND THE
GROUP's VIEW. At the group of the programs' shapes (`rowsPort`, Johnson/Top/H/SwitchKept.lean; with
kept members: `.keep kp`) every change of shape leaves the pair (message, randomness) as it is:
`pairAt`, `tabSame`, `tabRep` (Johnson/Top/H/MemberOf.lean, TabRep.lean): "nothing moves".

What is said.
  `tabSame_up`, `maskSame_up`, `mainAt_up`, `maskAt_up`: a table's change of shape, on messages: the
    entry at (row j, place x) is the entry at (row j, the place of the same number).
  `membPort_up_main`, `membPort_up_mask`: the same of the member's whole change of shape.
  `rowM_port`, `rowZ_port`: **A MEMBER's ROW BEHIND THE GROUP's VIEW IS THE GROUP's MESSAGE's ENTRY
    AT THAT MEMBER, THAT ROW, THAT PLACE. THE RANDOMNESS IS NOT READ.**
  `wordsAre_of_msgs`: **`WordsAre` at the words of the witness's one reader** (`wordsBy arr seatAt T
    w`, Johnson/Desc/Sound/WordsAt.lean), at every r, for a typed μ that at every member is the
    witness's typed reading (`msgsOf cs l seat arr w`, Johnson/Desc/Sound/MsgSig.lean): under three
    ties of numberings: the statement's codes are cs; the member's number in the statement (no a)
    has the member's seat (seat a.1) by seatAt; the statement's message of that number has the
    written shape.

Limits. General in cs, l, mem, the stage and the corners. hμ (μ is the witness's typed reading at
the members) IS A PREMISE: it is what a pin of each member at that witness says; hs (the numberings'
tie) and hsh are premises too: SHOWN OF NO STATE HERE. Nothing on words (the verifier's side of the
change of shape). Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.CubeAt
import Johnson.Top.H.SwitchKept
import Johnson.Desc.Sound.WordsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Means Cb Johnson.Top.H Johnson.Pack
open VerifiableInference.Desc.Sound (MsgT msgsOf wordsBy tabAt)

section Tables
variable (C C' : Fmt.M1.Code) (a a' n : ℕ) (pos : Fin (2 ^ a) → Fin (2 ^ a'))

/-- A table under the stage's code, on messages: nothing moves. -/
theorem tabSame_up (e : C' = C) (w) (j : Fin n) (x : Fin C.l) (x' : Fin C'.l)
    (hx : x'.val = x.val) : ((tabSame C C' a a' n pos e).up w).1 (j, x) = w.1 (j, x') := by
  subst e
  obtain rfl : x' = x := Fin.ext hx
  rfl

/-- A table of mask rows under the stage's mask code, on messages: nothing moves. -/
theorem maskSame_up (e : C' = C) (w) (j : Fin n) (x : Fin C.l) (x' : Fin C'.l)
    (hx : x'.val = x.val) : ((maskSame C C' a a' n e).up w).1 (j, x) = w.1 (j, x') := by
  subst e
  obtain rfl : x' = x := Fin.ext hx
  rfl

end Tables

section Port
variable (cs : OnBytes.Codes) (sh : OnBytes.OracleShape) (em : ℕ) (s : Sg) (oM oZ : ℕ)
  (hM : sh.mainRows ≠ 0 → cMain cs sh = s.C) (hZ : sh.maskRows ≠ 0 → cMask cs sh = s.Z)

theorem mainAt_up (w) (j : Fin sh.mainRows) (x : Fin s.C.l) (x' : Fin (cMain cs sh).l)
    (hx : x'.val = x.val) : ((Johnson.Top.H.mainAt cs sh s hM).up w).1 (j, x) = w.1 (j, x') := by
  unfold Johnson.Top.H.mainAt
  split
  · next h0 => exact absurd j.isLt (by omega)
  · exact tabSame_up _ _ _ _ _ _ _ w j x x' hx

theorem maskAt_up (w) (j : Fin sh.maskRows) (x : Fin s.Z.l) (x' : Fin (cMask cs sh).l)
    (hx : x'.val = x.val) : ((Johnson.Top.H.maskAt cs sh s hZ).up w).1 (j, x) = w.1 (j, x') := by
  unfold Johnson.Top.H.maskAt
  split
  · next h0 => exact absurd j.isLt (by omega)
  · exact maskSame_up _ _ _ _ _ _ w j x x' hx

/-- The member's whole change of shape, at a main row. -/
theorem membPort_up_main (w) (j : Fin sh.mainRows) (x : Fin s.C.l) (x' : Fin (cMain cs sh).l)
    (hx : x'.val = x.val) :
    ((membPort cs sh em s oM oZ hM hZ).view.up w).1 (.inl (j, x)) = w.1 (.inl (j, x')) := by
  have h := mainAt_up cs sh s hM (fun q => w.1 (.inl q), fun q => w.2 (.inl q)) j x x' hx
  exact h

/-- And at a mask row. -/
theorem membPort_up_mask (w) (j : Fin sh.maskRows) (x : Fin s.Z.l) (x' : Fin (cMask cs sh).l)
    (hx : x'.val = x.val) :
    ((membPort cs sh em s oM oZ hM hZ).view.up w).1 (.inr (j, x)) = w.1 (.inr (j, x')) := by
  have h := maskAt_up cs sh s hZ (fun q => w.1 (.inr q), fun q => w.2 (.inr q)) j x x' hx
  exact h

end Port

variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (mem : Fin l.length → Prop) [DecidablePred mem] (s : Sg) (e : ℕ) (oM oZ : Fin l.length → ℕ)
  (hM : ∀ i, mem i → (l.get i).1.mainRows ≠ 0 → cMain cs (l.get i).1 = s.C)
  (hZ : ∀ i, mem i → (l.get i).1.maskRows ≠ 0 → cMask cs (l.get i).1 = s.Z)
  (kp : {i // mem i} → Prop) [DecidablePred kp]

local notation "RP" => Johnson.Top.H.Rows.keep (rowsPort cs l mem s e oM oZ hM hZ) kp

/-- **A MEMBER's MAIN ROW BEHIND THE GROUP's VIEW IS THE GROUP's MESSAGE's ENTRY THERE.** -/
theorem rowM_port (u : ((RP).G.C.J → GE) × ((RP).G.C.Q → GE)) (a : {i // mem i})
    (j : Fin (l.get a.1).1.mainRows) (x : Fin s.C.l) (x' : Fin (cMain cs (l.get a.1).1).l)
    (hx : x'.val = x.val) : rowM (RP) u ⟨a, j⟩ x = u.1 ⟨a, .inl (j, x')⟩ :=
  membPort_up_main cs (l.get a.1).1 (l.get a.1).2 s (oM a.1) (oZ a.1) (hM a.1 a.2) (hZ a.1 a.2)
    (Reshape.atP u a) j x x' hx

/-- **AND ITS MASK ROW.** -/
theorem rowZ_port (u : ((RP).G.C.J → GE) × ((RP).G.C.Q → GE)) (a : {i // mem i})
    (j : Fin (l.get a.1).1.maskRows) (x : Fin s.Z.l) (x' : Fin (cMask cs (l.get a.1).1).l)
    (hx : x'.val = x.val) : rowZ (RP) u ⟨a, j⟩ x = u.1 ⟨a, .inr (j, x')⟩ :=
  membPort_up_mask cs (l.get a.1).1 (l.get a.1).2 s (oM a.1) (oZ a.1) (hM a.1 a.2) (hZ a.1 a.2)
    (Reshape.atP u a) j x x' hx

/-- **WordsAre AT THE WORDS OF THE WITNESS's ONE READER.** -/
theorem wordsAre_of_msgs {Cells Tok : Type} (T : Statement) (no : {i // mem i} → ℕ)
    (seatAt : ℕ → Option (ℕ × ℕ)) (seat : Fin l.length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
    (w : Wit Cells Tok MsgT) (r : (RP).G.C.Q → GE) (hc : T.codes = cs)
    (hs : ∀ a, seatAt (no a) = some (seat a.1))
    (hsh : ∀ a : {i // mem i}, ∃ y, T.oracles[no a]? = some y ∧ y.shape = (l.get a.1).1)
    (μ : (sigOf cs l).Msg) (hμ : ∀ a : {i // mem i}, μ a.1 = msgsOf cs l seat arr w a.1) :
    WordsAre (RP) T no ((RP).G.msg μ, r) (wordsBy arr seatAt T w) where
  main := by
    intro a idx _ hx
    obtain ⟨y, hy, hys⟩ := hsh a
    have hr : realRows T (no a) .main = (l.get a.1).1.mainRows := by
      unfold realRows
      rw [hy, ← hys]
      rfl
    have ht : tabAt T.codes arr seatAt T w (no a) =
        w.tab cs (l.get a.1).1 (arr (seat a.1).1 (seat a.1).2) (seat a.1).1 (seat a.1).2 := by
      unfold VerifiableInference.Desc.Sound.tabAt
      rw [hs a, hy, hc, ← hys]
    show (if idx % 2 ^ T.rowBits (no a) .main < realRows T (no a) .main then
      tabAt T.codes arr seatAt T w (no a) (Part.main == .mask) (idx % 2 ^ T.rowBits (no a) .main)
        (idx / 2 ^ T.rowBits (no a) .main) else 0) = _
    rw [hr, ht]
    by_cases hj : idx % 2 ^ T.rowBits (no a) .main < (l.get a.1).1.mainRows
    · have h0 : (l.get a.1).1.mainRows ≠ 0 := by omega
      have hl : idx / 2 ^ T.rowBits (no a) .main < (cMain cs (l.get a.1).1).l := by
        rw [hM a.1 a.2 h0]
        exact hx
      rw [if_pos hj, dif_pos (show _ < (RP).nM a from hj)]
      refine Eq.trans ?_
        (rowM_port cs l mem s e oM oZ hM hZ kp _ a ⟨_, hj⟩ ⟨_, hx⟩ ⟨_, hl⟩ rfl).symm
      show _ = μ a.1 (.inl (⟨_, hj⟩, ⟨_, hl⟩))
      rw [hμ a]
      rfl
    · rw [if_neg hj, dif_neg (show ¬ _ < (RP).nM a from hj)]
  mask := by
    intro a idx _ hx
    obtain ⟨y, hy, hys⟩ := hsh a
    have hr : realRows T (no a) .mask = (l.get a.1).1.maskRows := by
      unfold realRows
      rw [hy, ← hys]
      rfl
    have ht : tabAt T.codes arr seatAt T w (no a) =
        w.tab cs (l.get a.1).1 (arr (seat a.1).1 (seat a.1).2) (seat a.1).1 (seat a.1).2 := by
      unfold VerifiableInference.Desc.Sound.tabAt
      rw [hs a, hy, hc, ← hys]
    show (if idx % 2 ^ T.rowBits (no a) .mask < realRows T (no a) .mask then
      tabAt T.codes arr seatAt T w (no a) (Part.mask == .mask) (idx % 2 ^ T.rowBits (no a) .mask)
        (idx / 2 ^ T.rowBits (no a) .mask) else 0) = _
    rw [hr, ht]
    by_cases hj : idx % 2 ^ T.rowBits (no a) .mask < (l.get a.1).1.maskRows
    · have h0 : (l.get a.1).1.maskRows ≠ 0 := by omega
      have hl : idx / 2 ^ T.rowBits (no a) .mask < (cMask cs (l.get a.1).1).l := by
        rw [hZ a.1 a.2 h0]
        exact hx
      rw [if_pos hj, dif_pos (show _ < (RP).nZ a from hj)]
      refine Eq.trans ?_
        (rowZ_port cs l mem s e oM oZ hM hZ kp _ a ⟨_, hj⟩ ⟨_, hx⟩ ⟨_, hl⟩ rfl).symm
      show _ = μ a.1 (.inr (⟨_, hj⟩, ⟨_, hl⟩))
      rw [hμ a]
      rfl
    · rw [if_neg hj, dif_neg (show ¬ _ < (RP).nZ a from hj)]

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.rowM_port
#print axioms VerifiableInference.Desc.First.Close.rowZ_port
#print axioms VerifiableInference.Desc.First.Close.wordsAre_of_msgs
