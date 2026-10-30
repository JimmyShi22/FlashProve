-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/WaitsReached.lean: AT A STATE THAT IS REACHED IN FRONT OF THE SWITCH
INTO A LATER GROUP, IN THE GOALS' SCOPE, NO COUNT OF ROWS WAITS (`LinkPlain.waits`,
Returns/LinkSent.lean). Statements with their proofs: calls, and one proof of the library's typed
again with another clause kept.

HOW. The closing of segment l leaves no count of rows owed (the library's `closing_keeps`). The
three sub-protocols between it and the next switch keep what is owed: the shutting writes the open
segment's context alone (`stand_putLink`); "segment l: cleared" (`clear_carries`); "segment l + 1:
laid" hands the state on as it is (`layFront_ok`).

  `framesOf_clear_owed` every row's "cleared" keeps what is owed: THE LIBRARY's `framesOf_clear`
                    (Johnson/IMR/GroupTail.lean) DRAWS TWO OF `clear_carries`' TEN CLAUSES; ITS
                    PROOF IS TYPED AGAIN HERE, LINE FOR LINE, WITH THE FOURTH
  `shut_owed` the shutting keeps what is owed
  `owed_behind_laid` from the fold's return at the cut 14 (l + 1) + 2, l < 24: nothing is owed
  `link_waits_reached` at a state reached over the wrapped list at 14 (m + 1) + 2, m < 23:
                    `s.noneWaits = true`

By, all the library's: `frame_of` (Johnson/IMR/FrameSeat.lean) · `close_of`
(Johnson/IMR/CloseSeat.lean) · `close_numbers` (Johnson/IMR/FirstSeats.lean) · `yes_alone`
(Johnson/IMR/SeatForm.lean) · `closing_keeps` (Johnson/Desc/First/Close/Law/Leaves.lean) ·
`stand_putLink` (Johnson/Desc/First/Link/Law/RbDef.lean) · `clear_carries`, `layFront_ok`
(Johnson/Top/H0/Walk/FrameLaw.lean) · `mem_of_mapM_ok` (Johnson/Goal/Meaning/KeepsDriver.lean) ·
`bindE` (Johnson/Goal/Meaning/RecRel.lean) · `fold_back`, `fold_next` (Johnson/IMR/FoldTools.lean) ·
`reach_raw`, `Reach.fold` (Johnson/Top/H0/Walk/Reach.lean). Near relatives, not called:
`closing_opn`, `shutting_opn` (Johnson/IMR/FrameAll.lean): the same two seats, read for the open
segment's frame; their lines on the seats stand here again · `xk_reached`
(Johnson/IMR/AtReach.lean): the table's test at a border, which holds "no count waits, or one may",
under a premise that its docstring calls not paid.

Limits. The links' places alone: nothing at the head's or the finish's switch. "Reached" is: over
the list of the wrapped sub-protocols. THE PREMISES IN FRONT ARE SHOWN MET TOGETHER BY NOBODY HERE:
NO MEMBER. This file's imports are heavy. Nothing on any property.



-/
import Johnson.Desc.K2.Honest.Returns.LinkReached
import Johnson.IMR.FrameAll
import Johnson.IMR.GroupTail
import Johnson.Desc.First.Close.Law.Leaves
import Johnson.Desc.First.Link.Law.RbDef

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes OnBytes.Model
open VerifiableInference.Desc (foldBlocks Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (closing_keeps)
open VerifiableInference.Desc.LinkJoin (stand_putLink)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Johnson.Desc.First.Walk.Law (layFront_ok clear_carries)
open Meaning.K2 (mem_of_mapM_ok bindE fold_back fold_next)
open ProofFile (Cl)

open Johnson.Desc.First.Walk Johnson.Desc.First.Walk.Seat VerifiableInference.Desc.First in
/-- Every row's "cleared" keeps what is owed. -/
theorem framesOf_clear_owed {built : Array Stages.LinkH} {first : Params.First}
    {W : Verify.Public} {fs : List LinkFrame} (h : framesOf built first W = .ok fs) :
    ∀ f ∈ fs, ∀ s t, f.clear s = .ok t → t.rowsOwed = s.rowsOwed := by
  have clr : ∀ (X : LinkPub) (counts : S → Except String Unit) (left : S → Option WsForkOut)
      (row : RowFn) (s t : S), clearWith X counts left row s = .ok t →
      t.rowsOwed = s.rowsOwed := fun X counts left row s t k => (clear_carries k).2.2.2.1
  have th : ∀ (X : LinkPub) (lay : WsLay) (lin : Params.LinShape) (s t : S),
      Close.tailHead X lay lin s = .ok t → t.rowsOwed = s.rowsOwed :=
    fun _ _ _ => clr _ _ _ _
  intro f hf
  unfold framesOf at h
  obtain ⟨l, -, e⟩ := mem_of_mapM_ok _ _ _ h f hf
  dsimp only at e
  split at e
  · split at e
    · cases e
    · cases e
      exact th _ _ _
  · split at e
    · split at e
      · cases e
      · cases e
        exact clr _ _ _ _
    · split at e
      · cases e
      · cases e
        exact clr _ _ _ _
      · cases e
        exact clr _ _ _ _

/-- The shutting keeps what is owed. -/
theorem shut_owed {C : Type} (p : K9.Where) (piece : Nat) (s : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (s' : S)
    (h : (K9.shut (Cl := C) p piece).decide s rs gs = .ok s') : s'.rowsOwed = s.rowsOwed := by
  obtain ⟨L₁, -, h⟩ := bindE h
  cases h
  exact (stand_putLink s _).2.1

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-- **Behind "laid" of segment l + 1 nothing is owed.** -/
theorem owed_behind_laid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h24 : l < 24)
    {p : ProofFile.InstPub} {R R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn} {t₀ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * (l + 1) + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀)) :
    t₀.rowsOwed = none := by
  obtain ⟨-, fs, hfs, hfr⟩ := IM.frame_of hS hR O
  -- "segment l + 1: laid" hands the state on
  obtain ⟨_, _, bL, _, _, -, -, -, -, efl, hlay, -, iL, -, dL, -⟩ := hfr (l + 1) (by omega)
  obtain ⟨tm, Rm, Cm, fm⟩ := fold_back (k := 14 * (l + 1) + 1) f₀
  obtain ⟨rsL, gsL, dl⟩ := fold_next iL fm f₀
  rw [dL] at dl
  have hlf := ((hlay tm t₀).1 dl).1
  rw [efl] at hlf
  obtain ⟨et, -⟩ := layFront_ok hlf
  -- "segment l: cleared"
  obtain ⟨Lk, g, _, _, bC, eL, hlen, hg, -, -, -, hclr, -, -, -, -, -, -, iC, -, dC⟩ :=
    hfr l (by omega)
  rw [if_neg (by omega : ¬ l = 24)] at hlen
  rw [hlen, show 14 * l + 7 + 7 = 14 * l + 13 + 1 by omega] at iC
  rw [show 14 * (l + 1) + 1 = 14 * l + 13 + 1 + 1 by omega] at fm
  obtain ⟨u, Ru, Cu, fu⟩ := fold_back (k := 14 * l + 13 + 1) fm
  obtain ⟨rsC, gsC, dc⟩ := fold_next iC fu fm
  rw [dC] at dc
  have e1 := framesOf_clear_owed hfs g (List.mem_of_getElem? hg) u tm ((hclr u tm).1 dc).1
  -- the shutting and the closing
  obtain ⟨Lk', q, Q, eL', -, -, hall⟩ := IM.close_of hS hR O l (by omega)
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  obtain ⟨b₂, x₂, a1, a2, la₂⟩ := hall 2 .K9 rfl
  have i₂ := IM.close_numbers hS hR O (by omega : l < 25) eL a1
  rw [hlen, show 14 * l + 7 + 4 + 2 = 14 * l + 13 by omega] at i₂
  obtain ⟨v, Rv, Cv, fv⟩ := fold_back (k := 14 * l + 13) fu
  obtain ⟨rs₂, gs₂, d₂⟩ := fold_next i₂ fv fu
  have dx₂ : x₂.retype.decide v rs₂ gs₂ = .ok u :=
    ((IM.yes_alone la₂ (by intro k; cases k) v u rs₂ gs₂).1 d₂).1
  obtain rfl : K9.shut q (Q.piece + 1) = x₂ := Option.some.inj a2
  have e2 := shut_owed (C := Unit) q (Q.piece + 1) v rs₂ gs₂ u dx₂
  obtain ⟨b₁, x₁, c1, c2, la₁⟩ := hall 1 .K10 rfl
  have i₁ := IM.close_numbers hS hR O (by omega : l < 25) eL c1
  rw [hlen, show 14 * l + 7 + 4 + 1 = 14 * l + 12 by omega] at i₁
  rw [show 14 * l + 13 = 14 * l + 12 + 1 by omega] at fv
  obtain ⟨w, Rw, Cw, fw⟩ := fold_back (k := 14 * l + 12) fv
  obtain ⟨rs₁, gs₁, d₁⟩ := fold_next i₁ fw fv
  have dx₁ : x₁.retype.decide w rs₁ gs₁ = .ok v :=
    ((IM.yes_alone la₁ (by intro k; cases k) w v rs₁ gs₁).1 d₁).1
  obtain rfl : K9.closing Q = x₁ := Option.some.inj c2
  have e3 := (closing_keeps (Cl := Unit) Q w v rs₁ gs₁ dx₁).2.2.2.2.2
  rw [et, e1, e2, e3]

/-- **`LinkPlain.waits` at a reached state.** -/
theorem link_waits_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {m : Nat} (h23 : m < 23) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s)) :
    s.noneWaits = true := by
  obtain ⟨-, rs, cols, hf⟩ := (reach_raw hr).fold
  unfold S.noneWaits
  rw [owed_behind_laid hS hR O (by omega) hf]

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.framesOf_clear_owed
#print axioms VerifiableInference.Desc.K2.Honest.Returns.shut_owed
#print axioms VerifiableInference.Desc.K2.Honest.Returns.owed_behind_laid
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_waits_reached
