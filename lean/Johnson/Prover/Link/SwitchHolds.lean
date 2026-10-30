-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/SwitchHolds.lean: behind a code switch of the proximity test the claim is true
at an honest prover's new message: the values' half of the switch. General in the two stages.

Main names (namespace `Johnson.Prover.Link`).
  `csNext_holds`   the claim in front is true at the three folded messages μ': then the chain's
      claim behind the switch (`csNext`, OnBytes/Slice/CsSim.lean), at the word of (μ', tl) and the
      true answer `gAns`, is true at the new message `gMsg` (Johnson/Prover/Link/SwitchMsg.lean): at
      every seed, every list of positions, every drawn element and all values in the free room
  `claim_behind`   the same at the row that the description's switch and the batching behind it
      return (`Did`, Johnson/Desc/K12/Law/SwDid.lean), read in the field as the soundness side
      reads it (`stmGk`): by `did_sem` (Johnson/Desc/K12/Law/SwClaim.lean), an equation
  `csNext_turned`   a test that can fail: with another answer and a drawn element other than 0 the
      claim behind is false at the new message

By: `LdSw.holds_iff`, `LdSw.un_re`, `LdCode.word_eq` (Cb/Ld/LdSwitchProofs.lean), `ldSw_complete`,
`ldAt_pad` (Cb/Ld/LdSwitchWordsProofs.lean), `csNext_fst` (OnBytes/Slice/CsSim.lean).

Limits. Asked: the laws of the three folded rows' code (`LdCode.Laws`: linear, injective, local):
`laws_of_sized` has them from four inequalities on the stage's sizes (`Sg.Sized`), which the five
stages of the full size meet (`frSg1_sized` to `frSg5_sized`, OnBytes/Slice/FullRecCodes.lean).
`claim_behind` asks `did_sem`'s own premises, among them that the symbols which the switch has read
are those of the word of (μ', tl), and that the answer which it has taken reads as `gAns`. That the
switch says yes is not shown here. Nothing on how a tail or the free room's values are chosen.
Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.SwitchMsg
import Johnson.Desc.K12.Law.SwClaim
import OnBytes.Slice.CsSim
import OnBytes.Slice.Numbers

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb
open H2K.Sw

variable {s s' : Sg} (hf : CsFit s s') (μ' : s.cMid.J → GE) (tl : s.cMid.Q → GE) (fr : ℕ → GE)

/-- **The chain's claim behind a switch is true at the new message.** -/
theorem csNext_holds (hlaws : s.cMid.Laws) (q : GE × (s.cMid.J → GE))
    (hq : (Slf.idf (E := GE) (J := s.cMid.J)).Holds q μ') (ρo : (Fin s'.st.na → GE) × GEˣ)
    (c : (Fin s.t → s.Ps) × GE) :
    (Slf.idf (E := GE) (J := s'.cIn.J)).Holds
      (csNext hf q.1 q.2 (s.cMid.enc μ' tl) ρo (gAns hf μ' tl fr ρo) c) (gMsg hf μ' tl fr) := by
  have h := ((csSw hf).holds_iff q.2 ρo c
    ((csSw hf).W.tgt' q.1 (fun _ => gAns hf μ' tl fr ρo) (s.cMid.T (s.cMid.enc μ' tl)) c)
    (gMsg hf μ' tl fr)).2 (by
      show ldAt _ ((csSw hf).un ((csSw hf).re ((csSw hf).msg (μ', tl) (freeOf hf fr)))) = _
      rw [(csSw hf).un_re, s.cMid.word_eq hlaws μ' tl]
      have e : (fun _ : (csSw hf).Zo.S => gAns hf μ' tl fr ρo) =
          (csSw hf).Zo.val ρo ((csSw hf).msg (μ', tl) (freeOf hf fr)) := funext fun _ => rfl
      rw [e]
      refine ldSw_complete GE _ _ s.Ps _ (csSw hf).W (ldPad q.2) q.1 (Sum.elim μ' tl)
        (freeOf hf fr) ρo c ?_
      rw [ldAt_pad]
      exact hq)
  exact h

/-- The one public premise, from the sizes: as the soundness side has it
(`Sg.fit_cMid`, OnBytes/Slice/Numbers.lean). -/
theorem laws_of_sized (hs : s.Sized) : s.cMid.Laws := (Sg.fit_cMid hs).laws

/-- **The row behind the description's switch is true at the new message.** -/
theorem claim_behind {ft : ℕ} {cols : List Tw.L9.Col} {old : SingleRows} {nc nz gp : ℕ}
    {others : Array OracleNotice} {S S' : Statement} {Bk Bk' : TreeBook} {roots : ℕ}
    {out : Switched} {row : GroupRow} {lay : GroupLayout} {theta : E} {D : Taken}
    (hlaws : s.cMid.Laws)
    (h : Did ft cols old (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp others S Bk roots S' Bk'
        out row lay theta D)
    (P : CsProg s s' S.codes old nc nz) (hkept : old.kept = #[])
    (hG : D.G = { code := nc, maskCode := nz })
    (hd0 : (old.d.getD 0 #[]).size = s.Z.l) (hd1 : (old.d.getD 1 #[]).size = s.Z.l)
    (hc : ∀ v ∈ old.c.tensors, v.vars = ceilLog2 s.C.l)
    (ht : D.rC.drawn.poss.length = s.t) (hx : ∀ x ∈ D.rC.drawn.poss, x < 2 ^ s.C.a)
    (β : GEˣ) (hβ : β.val = readE D.beta) (Qs : Fin s.t → s.Ps)
    (hQ : ∀ i, (Qs i).val = D.rC.drawn.poss.getD i.val 0)
    (hy : ∀ i α, s.cMid.T (s.cMid.enc μ' tl) (Qs i) α =
      symS s old out.positions D.y (Qs i).val α)
    (hold : (Slf.idf (E := GE) (J := s.cMid.J)).Holds (stmS s old) μ')
    (hans : readE D.alpha = gAns hf μ' tl fr
      (readP _ (D.z (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) S), β)) :
    (Slf.idf (E := GE) (J := s'.cIn.J)).Holds (stmGk s' lay.k lay.h row) (gMsg hf μ' tl fr) := by
  rw [did_sem hf h P hkept hG hd0 hd1 hc ht hx β hβ (s.cMid.enc μ' tl) Qs hQ hy, hans]
  exact csNext_holds hf μ' tl fr hlaws (stmS s old) hold _ _

/-- **A test that can fail**: another answer, a drawn element other than 0: the claim behind is
false at the new message. -/
theorem csNext_turned (hlaws : s.cMid.Laws) (q : GE × (s.cMid.J → GE))
    (hq : (Slf.idf (E := GE) (J := s.cMid.J)).Holds q μ') (ρo : (Fin s'.st.na → GE) × GEˣ)
    (c : (Fin s.t → s.Ps) × GE) (ans : GE) (hne : ans ≠ gAns hf μ' tl fr ρo) (hθ : c.2 ≠ 0) :
    ¬ (Slf.idf (E := GE) (J := s'.cIn.J)).Holds
      (csNext hf q.1 q.2 (s.cMid.enc μ' tl) ρo ans c) (gMsg hf μ' tl fr) := by
  intro hbad
  have hgood := csNext_holds hf μ' tl fr hlaws q hq ρo c
  have e1 : (csNext hf q.1 q.2 (s.cMid.enc μ' tl) ρo ans c).1 =
      (csNext hf q.1 q.2 (s.cMid.enc μ' tl) ρo (gAns hf μ' tl fr ρo) c).1 :=
    hbad.symm.trans hgood
  rw [csNext_fst, csNext_fst] at e1
  have e2 : c.2 * ans = c.2 * gAns hf μ' tl fr ρo :=
    add_left_cancel (add_right_cancel e1)
  exact hne (mul_left_cancel₀ hθ e2)

end Johnson.Prover.Link
