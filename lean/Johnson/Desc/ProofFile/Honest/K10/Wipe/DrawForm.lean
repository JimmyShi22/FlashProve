-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Wipe/DrawForm.lean: the closing of a segment (K10): the form of the challenges that
the closing's declared rounds can draw, out of the frame's public test `drawsFit` (Honest/Frame.lean); and with it the
law "the data are made" (Wipe/Speaks.lean) without its condition on the form of "BAT"'s challenge. Lemmas; no
definition.

  `drawFit_bare`     a challenge that a round can draw whose entry draws one element, no position and no matrix entry,
                    and whose name is no sealing round's: one element, no position, no matrix entry, no digest
  **`close_draws_form`**   a list of challenges that the closing's 2 + k declared rounds can draw: "BAT"'s challenge of
                    that form, then 1 + k more, each of one element
  **`askZero_of_draws`**   `askZero_at_head` (Wipe/Speaks.lean) at the first challenge of such a list: under the head
                   (`P5J.AtMg` at the older hash), hf (the description's fold over the members in front returns at
                   sn's rounds and at some columns) and H, hh, hr, hfit

Limits. The premises of `askZero_at_head` stand here too and are shown of no run: hf, on the fold in front; H and hh, on
the record in front; hr and hfit, on the prover's rows. start, xi and J are variables, and J's own place is not tied to
Q. Whether the head can be had at any files is no theorem. That a list of challenges passes `drawsFit` is a premise:
`PlaysS` and `AcceptedS` (Honest/Thread/PaysS.lean) have it among their own. No property of the protocol is claimed:
nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Wipe.Speaks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Block Chain Place OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (Par entries)
open ProofFile.Honest.K10.YesFree (CloseBase BaseData)

/-- What a round can draw whose entry draws one element and nothing else, and whose name is no sealing round's. -/
theorem drawFit_bare {z : Fmt.DeclaredRound} {d : Fmt.Drawn} (h : drawFit z d = true) (h1 : z.entry.drawE = 1)
    (h2 : z.entry.poss = 0) (h3 : z.entry.trits = 0) (h4 : Fmt.kindOf z.entry.name ≠ some .sealed) :
    ∃ e, d = ⟨[e], [], [], none⟩ := by
  obtain ⟨el, po, tri, dg⟩ := d
  simp only [drawFit, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, _⟩, _⟩, _⟩, _⟩, a8⟩ := h
  have e1 : el.length = 1 := a1.trans h1
  have e2 : po.length = 0 := a2.trans h2
  have e3 : tri.length = 0 := a3.trans h3
  have e8 : dg = none := by
    rcases a8 with a8 | a8
    · cases dg with
      | none => rfl
      | some _ => exact nomatch a8
    · exact absurd a8 h4
  match el, e1 with
  | [e], _ =>
    rw [List.length_eq_zero_iff.1 e2, List.length_eq_zero_iff.1 e3, e8]
    exact ⟨e, rfl⟩

/-- **The challenges that the closing's declared rounds can draw**: "BAT"'s has one element, no position, no matrix
entry and no digest; then 1 + k more, each of one element. -/
theorem close_draws_form (P : Par) (ds : List Fmt.Drawn) (h : drawsFit ((closeRounds P).map (·.1)) ds = true) :
    ∃ e d1 gs, ds = ⟨[e], [], [], none⟩ :: d1 :: gs ∧ gs.length = P.k ∧ ∀ d ∈ d1 :: gs, d.elems.length = 1 := by
  obtain ⟨d0, d1, gs, rfl, hk, h1⟩ := close_draws P ds h
  have h0 : drawFit { entry := { name := "BAT", work := P.workField, drawE := 1, rows := P.rows } } d0 = true := by
    have h' : (drawFit { entry := { name := "BAT", work := P.workField, drawE := 1, rows := P.rows } } d0 &&
        drawsFit (((closeRounds P).map (·.1)).drop 1) (d1 :: gs)) = true := h
    exact (Bool.and_eq_true _ _ ▸ h').1
  have hn : Fmt.kindOf "BAT" ≠ some .sealed := by decide
  obtain ⟨e, rfl⟩ := drawFit_bare h0 rfl rfl rfl hn
  exact ⟨e, d1, gs, rfl, hk, fun d hd => h1 d (List.mem_cons_of_mem _ hd)⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl}

/-- **The data are made at the first of any challenges that the closing's rounds can draw**, under the head, hf and the
four named premises H, hh, hr, hfit. -/
theorem askZero_of_draws {W Xi : Type} (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {l : Nat} (hl : l < 25)
    {p : VerifiableInference.Desc.K9.Where} {Q : Par} {b : Block S ProofFile.Cl} (T : Tied cF Zp l p Q b)
    (J : CloseJob W) (start : Xi → S) (xi : W → Xi) (w : W) (sn : Seen) (front : List Fmt.Drawn)
    (ds : List Fmt.Drawn) (hd : drawsFit ((closeRounds J.pub.par).map (·.1)) ds = true)
    (ca : CsAll (closeCarries J.pub)) {cols : List OpenedColumn} {y : S × List Fmt.RoundView × List OpenedColumn}
    (hf : foldBlocks 0 (cF.blocksInOrder.take (14 * l + (if l = 24 then 9 else 7) + 5)) (start (xi w)) sn.rounds cols = .ok y)
    {B : BaseData} (H : CloseBase J.pub.par (VerifiableInference.Desc.K9.recOf y.1) B) (hh : J.pub.par.h = B.Gq.h)
    (R : GroupData) (hr : J.rows w front ca = .ok R) (hfit : rowsFit y.1.st B.G R = true) :
    ∃ d0 d1 gs A, ds = d0 :: d1 :: gs ∧ gs.length = J.pub.par.k ∧ (∀ d ∈ ds, d.elems.length = 1) ∧
      askZero { J with stAt := fun w' s f => stAtZero cF.blocksInOrder start (xi w') Q s f } w sn front d0 ca = some A := by
  obtain ⟨e, d1, gs, rfl, hk, h1⟩ := close_draws_form J.pub.par ds hd
  obtain ⟨A, hA⟩ := askZero_at_head h hl T J start xi w sn front e ca hf H hh R hr hfit
  refine ⟨_, d1, gs, A, rfl, hk, fun d hd' => ?_, hA⟩
  rcases List.mem_cons.1 hd' with rfl | hd'
  · rfl
  · exact h1 d hd'

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.drawFit_bare
#print axioms ProofFile.Honest.K10.close_draws_form
#print axioms ProofFile.Honest.K10.askZero_of_draws
