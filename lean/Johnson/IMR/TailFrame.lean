-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/TailFrame.lean: NOBODY TURNS THE FRAME BETWEEN A LINK's CLOSING AND
THE NEXT LINK's FIRST SUB-PROTOCOL: l < 24: at the proof file's seat, in the goals' scope, from the
fold's return alone.
  tail_frame: with s the state in front of the closing of link l (the cut 14 l + 12) and L the link
    open there: closeFrame, at L's frame and s's statement, has returned some y, and the walk's
    WHOLE frame in front of the next link's first sub-protocol (the cut 14 (l + 1) + 2) is y.1.
So whatever a law says of closeFrame's returned frame (its carried rows among it) holds of the frame
that the next code switching reads.
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USERS: kind K2's and K10's files.
The premises are laws' premises: that a fold returns is shown of no proof here. No soundness.
-/
import Johnson.IMR.GroupTail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.K9
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

theorem tail_frame (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h24 : l < 24)
    {p : ProofFile.InstPub} {R R₃ R₂ : List Fmt.RoundView} {C C₃ C₂ : List VerifiableInference.Desc.OpenedColumn}
    {s t₂ : S}
    (g3 : foldBlocks 0 (c.blocksInOrder.take (14 * l + 12)) (ProofFile.startS Z p) R C = .ok (s, R₃, C₃))
    (f₂ : foldBlocks 0 (c.blocksInOrder.take (14 * (l + 1) + 2)) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂)) :
    ∃ (L : LinkCtx) (Q : Close.Par) (rs : List Fmt.RoundView) (y : ReqFrame × Statement),
      s.link? = some L ∧ L.link = l ∧
      Close.closeFrame (K9.recOf s).owed L.check.frame s.st (Close.entries Q) rs = .ok y ∧
      t₂.check.frame = y.1 := by
  obtain ⟨L, hL, eLn, -⟩ := group_open hS hR O h24 9 (by omega) s R₃ C₃ g3
  obtain ⟨-, fs, hfs, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨Lk, f, bL, bB, bC, eL, hlen, hf, -, -, -, hClear, -, -, -, -, -, -, iC, -, dC⟩ :=
    hfr l (by omega)
  rw [if_neg (by omega : ¬ l = 24)] at hlen
  rw [hlen] at iC
  obtain ⟨Lk', f', bL', -, -, -, -, hf', -, efl', hLay', -, iL', -, dL', -⟩ :=
    hfr (l + 1) (by omega)
  have cut : ∀ n ≤ 4, ∃ t r q,
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 12 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q) := by
    intro n hn
    exact fold_cut (k := 14 * l + 12 + n) (4 - n)
      (by rw [show 14 * l + 12 + n + (4 - n) = 14 * (l + 1) + 2 by omega]; exact f₂)
  obtain ⟨s4, r4, q4, g4⟩ := cut 1 (by omega)
  obtain ⟨s5, r5, q5, g5⟩ := cut 2 (by omega)
  obtain ⟨s6, r6, q6, g6⟩ := cut 3 (by omega)
  obtain ⟨Lk2, pw, Q, eL2, -, -, hall⟩ := IM.close_of hS hR O l (by omega)
  obtain rfl : Lk = Lk2 := Option.some.inj (eL.symm.trans eL2)
  -- the closing
  obtain ⟨b', x, e1, e2, la⟩ := hall 1 .K10 rfl
  have ib := IM.close_numbers hS hR O (by omega : l < 25) eL e1
  rw [hlen, show 14 * l + 7 + 4 + 1 = 14 * l + 12 by omega] at ib
  obtain ⟨rs, gs, d⟩ := fold_next ib g3 g4
  have dx : x.retype.decide s rs gs = .ok s4 :=
    ((IM.yes_alone la (by intro k; cases k) s s4 rs gs).1 d).1
  obtain rfl : K9.closing Q = x := Option.some.inj e2
  obtain ⟨y, hy', hl4, -⟩ := closing_yes (C := Unit) dx hL
  -- the shutting
  obtain ⟨b5', x5, e15, e25, la5⟩ := hall 2 .K9 rfl
  have ib5 := IM.close_numbers hS hR O (by omega : l < 25) eL e15
  rw [hlen, show 14 * l + 7 + 4 + 2 = 14 * l + 12 + 1 by omega] at ib5
  obtain ⟨rs5, gs5, d5⟩ := fold_next ib5 g4 g5
  have dx5 : x5.retype.decide s4 rs5 gs5 = .ok s5 :=
    ((IM.yes_alone la5 (by intro k; cases k) s4 s5 rs5 gs5).1 d5).1
  obtain rfl : K9.shut pw (Q.piece + 1) = x5 := Option.some.inj e25
  obtain ⟨L5, hL5, e5, -⟩ := shut_gby (fun f => f) (C := Unit) pw (Q.piece + 1) s4 rs5 gs5 s5 dx5
    _ hl4
  have e5' : L5.check.frame = y.1 := e5
  -- "cleared" and "laid"
  have iC' : c.blocksInOrder[14 * l + 12 + 2]? = some bC := by
    rw [show 14 * l + 12 + 2 = 14 * l + 7 + 7 by omega]
    exact iC
  obtain ⟨rs6, gs6, d6⟩ := fold_next iC' g5 g6
  rw [dC] at d6
  have k6 := framesOf_clear hfs f (List.mem_of_getElem? hf) s5 s6 ((hClear s5 s6).1 d6).1
  have iL2 : c.blocksInOrder[14 * l + 12 + 3]? = some bL' := by
    rw [show 14 * l + 12 + 3 = 14 * (l + 1) + 1 by omega]
    exact iL'
  have f₂' : foldBlocks 0 (c.blocksInOrder.take (14 * l + 12 + 3 + 1)) (ProofFile.startS Z p) R C =
      .ok (t₂, R₂, C₂) := by
    rw [show 14 * l + 12 + 3 + 1 = 14 * (l + 1) + 2 by omega]
    exact f₂
  obtain ⟨rs7, gs7, d7⟩ := fold_next iL2 g6 f₂'
  rw [dL'] at d7
  have hl7 := ((hLay' s6 t₂).1 d7).1
  rw [efl'] at hl7
  have e7 : t₂ = s6 := (Johnson.Desc.First.Walk.Law.layFront_ok hl7).1
  exact ⟨L, Q, rs, y, hL, eLn, hy', by rw [e7, k6.1, live_open hL5, e5']⟩

end

#print axioms tail_frame

end Meaning.K2
