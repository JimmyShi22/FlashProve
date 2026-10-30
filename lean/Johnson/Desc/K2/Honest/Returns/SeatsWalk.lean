-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/SeatsWalk.lean: BETWEEN A SEGMENT's CLOSING AND THE NEXT SEGMENT's
SWITCH, WITH THE STATE IN FRONT OF THE CLOSING NAMED; AND SO THE MESSAGES THAT THE NEXT SWITCH
OPENS, AS NUMBERS. In the goals' scope, from the fold's return alone, segments 1 to 23 for the
numbers. A tool for `ReadFits.own` (Returns/Read.lean; Returns/PartsPlaced.lean;
Returns/CutsKept.lean). Statements with their proofs: calls.

  `closing_behind_laid` l < 24: from the fold's return at the cut 14 (l + 1) + 2: there are the
                    state w of the same fold at the cut 14 l + 12, the segment Lw that is open
                    there, and a yes of the frame's closing AT Lw's OWN FRAME AND w's OWN STATEMENT,
                    whose frame is the walk's at the later cut, and out of whose statement the later
                    one has grown. `closed_behind_laid` (Returns/ClosedReached.lean) says it with
                    "there are a frame and a statement": ITS PROOF STANDS HERE AGAIN, LINE FOR LINE,
                    COPIED BY PROGRAM, WITH THE STATEMENT STRENGTHENED: the witnesses were these
                    terms already
  `closed_of_closing` `closed_behind_laid`'s statement, to the letter, from it in one line: for the
                    day when the folder is tidied
  `fresh_behind_laid` 1 ≤ l < 24: the carried rows' fresh mask is the message right behind the
                    segment's own messages of moment 0, counted from the count n₀ at the cut 14 l +
                    2 of the same fold
  `members_behind_laid` 1 ≤ l < 24: the carried rows' layout's members are n₀, the kept copies, and
                    the own messages of three moments, AS RANGES off the counts at the cuts 14 l +
                    2, 14 l + 5, 14 l + 7 of the same fold

By, all the library's: what `closed_behind_laid` calls (its head lists them) · `closeFrame_reads`
(Johnson/Desc/First/Link/Law/CloseReads.lean) · `mask_named` (Johnson/IMR/MaskNamed.lean) ·
`flags_named` (Johnson/IMR/FlagsNamed.lean) · `tail_rows` (Johnson/IMR/GroupTail.lean) · `fold_cut`
(Johnson/IMR/GroupRest.lean).

Limits. Nothing on segment 0's or segment 24's numbers. That a fold returns is shown of no proof
here. The walk over the seats stands typed a sixth time in this folder. This file's imports are
heavy. Nothing on any property.



-/
import Johnson.Desc.K2.Honest.Returns.ClosedReached
import Johnson.IMR.MaskNamed
import Johnson.Desc.First.Link.Law.CloseReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (foldBlocks Block Chain FileDescription Grows)
open OnBytes.Model (LinkCtx)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (closeFrame)
open VerifiableInference.Desc.LinkJoin (closeFrame_reads)
open Johnson.Desc.First.Walk.Law (layFront_ok)
open Meaning.K2 (Opn frame_walk_link entry_at entry_at_zero framesOf_clear framesOf_grows
  closing_yes shutting_opn fold_back fold_next fold_cut mask_named flags_named tail_rows msgsAt)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **Behind "laid" of the next segment, with the state in front of the closing named.** -/
theorem closing_behind_laid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h24 : l < 24)
    {p : ProofFile.InstPub} {R R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn} {t₀ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * (l + 1) + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀)) :
    ∃ (w : S) (Rw : List Fmt.RoundView) (Cw : List VerifiableInference.Desc.OpenedColumn) (Lw : LinkCtx)
      (Q : First.Close.Par) (rs : List Fmt.RoundView) (x : ReqFrame × Statement),
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 12)) (ProofFile.startS Z p) R C = .ok (w, Rw, Cw) ∧
      w.link? = some Lw ∧ Lw.link = l ∧
      closeFrame (K9.recOf w).owed Lw.check.frame w.st (First.Close.entries Q) rs = .ok x ∧
      t₀.check.frame = x.1 ∧ Grows x.2 t₀.st := by
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
  have hcf := ((hclr u tm).1 dc).1
  have hck := (framesOf_clear hfs g (List.mem_of_getElem? hg) u tm hcf).1
  have hgr : Grows u.st tm.st := (framesOf_grows hfs g (List.mem_of_getElem? hg)).2.2 u tm hcf
  -- the shutting and the closing
  obtain ⟨Lk', q, Q, eL', -, -, hall⟩ := IM.close_of hS hR O l (by omega)
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  obtain ⟨b₂, x₂, a1, a2, la₂⟩ := hall 2 .K9 rfl
  have j₂ := IM.close_numbers hS hR O (by omega : l < 25) eL a1
  have i₂ := j₂
  rw [hlen, show 14 * l + 7 + 4 + 2 = 14 * l + 13 by omega] at i₂
  rw [show 14 * l + Lk.hear.length + 4 + 2 = 14 * l + Lk.hear.length + 6 by omega] at j₂
  obtain ⟨v, Rv, Cv, fv⟩ := fold_back (k := 14 * l + 13) fu
  obtain ⟨rs₂, gs₂, d₂⟩ := fold_next i₂ fv fu
  have dx₂ : x₂.retype.decide v rs₂ gs₂ = .ok u :=
    ((IM.yes_alone la₂ (by intro k; cases k) v u rs₂ gs₂).1 d₂).1
  obtain rfl : K9.shut q (Q.piece + 1) = x₂ := Option.some.inj a2
  have est := shut_st (C := Unit) q (Q.piece + 1) v rs₂ gs₂ u dx₂
  obtain ⟨b₁, x₁, c1, c2, la₁⟩ := hall 1 .K10 rfl
  have i₁ := IM.close_numbers hS hR O (by omega : l < 25) eL c1
  rw [hlen, show 14 * l + 7 + 4 + 1 = 14 * l + 12 by omega] at i₁
  rw [show 14 * l + 13 = 14 * l + 12 + 1 by omega] at fv
  obtain ⟨w, Rw, Cw, fw⟩ := fold_back (k := 14 * l + 12) fv
  obtain ⟨rs₁, gs₁, d₁⟩ := fold_next i₁ fw fv
  have dx₁ : x₁.retype.decide w rs₁ gs₁ = .ok v :=
    ((IM.yes_alone la₁ (by intro k; cases k) w v rs₁ gs₁).1 d₁).1
  obtain rfl : K9.closing Q = x₁ := Option.some.inj c2
  -- in front of the closing a segment is open
  obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_cut (k := 14 * l + 3) 9
    (by rw [show 14 * l + 3 + 9 = 14 * l + 12 by omega]; exact fw)
  obtain ⟨t₃, r₃, c₃, g₃⟩ := fold_cut (k := 14 * l + 3 + 2) 7
    (by rw [show 14 * l + 3 + 2 + 7 = 14 * l + 12 by omega]; exact fw)
  obtain ⟨t₅, r₅, c₅, g₅⟩ := fold_cut (k := 14 * l + 3 + 4) 5
    (by rw [show 14 * l + 3 + 4 + 5 = 14 * l + 12 by omega]; exact fw)
  obtain ⟨f', H⟩ : ∃ f', Opn l f' t₁ := by
    rcases Nat.eq_zero_or_pos l with rfl | h1
    · obtain ⟨f', hA, -⟩ := entry_at_zero hS hR O f₁
      exact ⟨f', hA.opn⟩
    · obtain ⟨t₂, R₂, C₂, f₂⟩ := fold_back (k := 14 * l + 2) f₁
      obtain ⟨_, f', -, hA, -⟩ := entry_at hS hR O h1 h24 f₂ f₁
      exact ⟨f', hA.opn⟩
  obtain ⟨Lw, hLw, -, hLl⟩ := (frame_walk_link hS hR O h24 (n₃ := t₃.st.oracles.size)
    (n₅ := t₅.st.oracles.size) (fun t r q h => by rw [g₃] at h; cases h; rfl)
    (fun t r q h => by rw [g₅] at h; cases h; rfl) f₁ H).1 9 (by omega) w Rw Cw
    (by rw [show 14 * l + 3 + 9 = 14 * l + 12 by omega]; exact fw)
  obtain ⟨x, hx, hv, hvst⟩ := closing_yes (C := Unit) dx₁ hLw
  have Hv : Opn l x.1 v := ⟨_, hv, rfl, hLl⟩
  obtain ⟨Lu, hLu, hLuf, -⟩ := shutting_opn hS hR O (by omega : l < 25) eL j₂ d₂ Hv
  refine ⟨w, Rw, Cw, Lw, Q, rs₁, x, fw, hLw, hLl, hx, ?_, ?_⟩
  · rw [et, hck]
    unfold S.live
    rw [hLu]
    exact hLuf
  · rw [et, ← hvst, ← est]
    exact hgr

/-- `closed_behind_laid` (Returns/ClosedReached.lean), to the letter, from the stronger form. -/
theorem closed_of_closing (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h24 : l < 24)
    {p : ProofFile.InstPub} {R R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn} {t₀ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * (l + 1) + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀)) :
    ∃ (owed : Option Nat) (f : ReqFrame) (S₀ : Statement) (es : List Fmt.Entry)
      (rs : List Fmt.RoundView) (x : ReqFrame × Statement),
      closeFrame owed f S₀ es rs = .ok x ∧ t₀.check.frame = x.1 ∧ Grows x.2 t₀.st := by
  obtain ⟨_, _, _, _, _, _, x, -, -, -, hx, hf, hg⟩ := closing_behind_laid hS hR O h24 f₀
  exact ⟨_, _, _, _, _, x, hx, hf, hg⟩

/-- **The fresh mask that the next switch opens, as a number.** -/
theorem fresh_behind_laid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h1 : 1 ≤ l)
    (h24 : l < 24) {p : ProofFile.InstPub} {R R₂ Ra : List Fmt.RoundView}
    {C C₂ Ca : List VerifiableInference.Desc.OpenedColumn} {t₂ ta : S}
    (fa : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) (ProofFile.startS Z p) R C = .ok (ta, Ra, Ca))
    (f₂ : foldBlocks 0 (c.blocksInOrder.take (14 * (l + 1) + 2)) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂)) :
    t₂.check.frame.rows.fresh = ta.st.oracles.size +
      (1 + (First.K2.targetAt Z.first.shape l).kept.size) + msgsAt Z.first.shape l 0 := by
  obtain ⟨w, Rw, Cw, Lw, Q, rs, x, fw, hLw, -, hx, hf, -⟩ := closing_behind_laid hS hR O h24 f₂
  obtain ⟨_, m, -, -, hm, hfr⟩ := closeFrame_reads hx
  obtain ⟨t₀, R₀, C₀, L, g₀, hL, -, hmask⟩ := mask_named hS hR O h1 h24 (n := 9) (by omega)
    (by rw [show 14 * l + 3 + 9 = 14 * l + 12 by omega]; exact fw)
  obtain rfl : t₀ = ta := congrArg Prod.fst (Except.ok.inj (g₀.symm.trans fa))
  obtain rfl : L = Lw := Option.some.inj (hL.symm.trans hLw)
  rw [hf, hfr]
  exact Option.some.inj (hm.symm.trans hmask)

/-- **The members that the next switch opens, as ranges.** -/
theorem members_behind_laid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h1 : 1 ≤ l)
    (h24 : l < 24) {p : ProofFile.InstPub} {R R₂ : List Fmt.RoundView}
    {C C₂ : List VerifiableInference.Desc.OpenedColumn} {t₂ : S}
    (f₂ : foldBlocks 0 (c.blocksInOrder.take (14 * (l + 1) + 2)) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂)) :
    ∃ (t₀ t₃ t₅ : S) (R₀ R₃ R₅ : List Fmt.RoundView) (C₀ C₃ C₅ : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀) ∧
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 5)) (ProofFile.startS Z p) R C = .ok (t₃, R₃, C₃) ∧
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 7)) (ProofFile.startS Z p) R C = .ok (t₅, R₅, C₅) ∧
      t₂.check.frame.rows.layout.members = #[t₀.st.oracles.size] ++
        (Array.range (First.K2.targetAt Z.first.shape l).kept.size).map
          (· + (t₀.st.oracles.size + 1)) ++
        ((Array.range (msgsAt Z.first.shape l 0)).map
            (· + (t₀.st.oracles.size + (1 + (First.K2.targetAt Z.first.shape l).kept.size))) ++
          (Array.range (msgsAt Z.first.shape l 1)).map (· + t₃.st.oracles.size) ++
          (Array.range (msgsAt Z.first.shape l 2)).map (· + t₅.st.oracles.size)) := by
  obtain ⟨u, Ru, Cu, fu⟩ := fold_cut (k := 14 * l + 9) 7
    (by rw [show 14 * l + 9 + 7 = 14 * (l + 1) + 2 by omega]; exact f₂)
  obtain ⟨L, G, hL, -, -, hG, hmem, -⟩ := tail_rows hS hR O h24 fu f₂
  obtain ⟨t₀, t₃, t₅, R₀, R₃, R₅, C₀, C₃, C₅, L', G', g₀, g₃, g₅, hL', -, hG', em, ek, eo⟩ :=
    flags_named hS hR O h1 h24 (n := 1) (by omega)
      (by rw [show 14 * l + 8 + 1 = 14 * l + 9 by omega]; exact fu)
  obtain rfl : G' = G := Option.some.inj (hG'.symm.trans hG)
  refine ⟨t₀, t₃, t₅, R₀, R₃, R₅, C₀, C₃, C₅, g₀, g₃, g₅, ?_⟩
  rw [hmem, em, ek, eo]

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.closing_behind_laid
#print axioms VerifiableInference.Desc.K2.Honest.Returns.closed_of_closing
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fresh_behind_laid
#print axioms VerifiableInference.Desc.K2.Honest.Returns.members_behind_laid
