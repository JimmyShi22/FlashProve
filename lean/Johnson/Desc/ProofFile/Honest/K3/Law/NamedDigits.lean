-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/NamedDigits.lean: the kind "lookup" (K3): behind the whole
seated acceptance of a lookup on the digits, the step without a round that may stand behind it too,
at every link: each of the four families of forms in what was heard (the rows, the key side's end
form, the form on the bits' end slot, the leaves' start form) names no entry, and slots alone that
are there and filled in the ledger behind. A theorem.

Terms. Honest/K3/GLOSSARY.md. `Fo.Tp.PadNames g G` (Johnson/Top/H/Keep/PadNamed.lean) is that
sentence.

What is shown. `padNames_behind_digits`: the title's sentence, with "the ledger behind has its
sizes".

Follows. The statement and the proof are those of the library's `digits_behind_named`
(Johnson/Desc/Sound/MgAt/K3DigitsObjIn.lean), line for line, with all four fields of `PadNames` kept
where that theorem keeps the rows' field alone; and at the last step, where that proof tries two
forms, the one that Lean takes stands alone. That file is imported. The like at the lookup on the
calls is the library's `padNames_behind_calls` (Johnson/Desc/First/Link/Law/K4AtFront.lean); it
assumes that the ledger behind has its sizes, where the theorem here assumes it of the ledger in
front. The library's `four_behind_digits` (Johnson/Desc/First/Link/Law/FourBehindDigits.lean) has
the same hypotheses as the theorem here; it says of the four forms of `four8 tl g` that each slot
lies in the leaves' window or is filled at every later ledger. Its statement does not speak of the
rows.

Related, in this folder. `padNames_of_hearV` (Honest/K3/Law/Thread/PadNamesOf.lean
[not in this library]; not in the library yet) shows `PadNames` at the ledger behind the hearing
that a description seats, from that hearing's return, by this folder's own laws on which slots the
heard forms name; `padNames_at`, in the same file, at the member on the calls of a layers' link. The
first assumes of the ledger in front that it has its sizes and room for the lookup's slots; the
second assumes the lookup's promise in front (`k3OnIn`). The theorem here speaks of the whole seated
acceptance on the digits, the step without a round too, and stands on the library's files alone.

Hypotheses that remain. Those of `digits_behind_named`: B is the value of `K3.theStated` at the
address a (`h`); it passes its test on the plan (`hOk`); a is the digits' address of link i (`hi`,
`hpc`); B's decision accepts from s to s₂ (`hd`); the ledger at s is F (`hF`), and F has its sizes
(`hS`).

Limits. From an acceptance alone. That the ledger in front has its sizes is a hypothesis. Nothing on
whether any state is reached. No instance of the hypotheses together is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.Sound.MgAt.K3DigitsObjIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes OnBytes.Model
open VerifiableInference
open VerifiableInference.OnPublicFiles (theStated_yes_digits decide_named seatDigits_keeps k3_digits_pass
        quietAt_pass quietAt_tlFuns)

/-- **Behind the whole seated acceptance of a lookup on the digits all four families are named.**
Conditional on the hypotheses that the head of this file lists. No instance of these hypotheses is
exhibited in this file. -/
theorem padNames_behind_digits {Cl : Type} (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i true)
    (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂) {F : Fork} (hF : s.fork? = some F)
    (hS : OnBytes.PscRun.Sized F) :
    ∃ (G : Fork) (g : Forest.Heard), s₂.fork? = some G ∧
      (Desc.K3.seatDigits claim).heard s₂ = some g ∧ _root_.Fo.Tp.PadNames g G ∧
      OnBytes.PscRun.Sized G := by
  obtain ⟨P', sent, laid, n, gs', s', -, hyes, hstep⟩ :=
    theStated_yes_digits claim readers X codes shape a B h hOk i hi hpc s s₂ rs gs hd
  obtain ⟨F1, y, hF1, hn1, e1, hN⟩ :=
    decide_named (Desc.K3.seatDigits claim) a.piece laid sent P' [] s s' _ gs' hyes
  obtain rfl : F = F1 := Option.some.inj (hF.symm.trans hF1)
  have hsome : ((Desc.K3.seatDigits claim).fork s).isSome = true := by
    rw [hF1]
    rfl
  have hg1 : (Desc.K3.seatDigits claim).heard s' = some y.1 := by
    rw [e1]
    exact Desc.K3.seatDigits_reads claim _ _ _ hsome hn1
  have hF1' : s'.fork? = some y.2 := by
    rw [e1]
    exact seatDigits_keeps claim _ _ _ hsome hn1
  obtain ⟨G0, Q0⟩ := k3_digits_pass claim a.piece laid sent P' [] s s' _ gs' hyes hF hS
  have eG0 : G0 = y.2 := Option.some.inj (Q0.behind.symm.trans hF1')
  have hSz : OnBytes.PscRun.Sized y.2 := eG0 ▸ Q0.sizedG
  have hNm : _root_.Fo.Tp.PadNames y.1 y.2 := hN hS
  rcases hstep with e | ⟨f, hf, hfs⟩
  · rw [e]
    exact ⟨y.2, y.1, hF1', hg1, hNm, hSz⟩
  · obtain ⟨G₂, Q₂⟩ := quietAt_pass X i f hf s' s₂ hfs hF1' hSz
    obtain ⟨et, -⟩ := quietAt_tlFuns X i f hf s' s₂ hfs
    have hg2 : (Desc.K3.seatDigits claim).heard s₂ = some y.1 := by
      show s₂.tl?.bind (·.heard) = some y.1
      rw [et]
      exact hg1
    refine ⟨G₂, y.1, Q₂.behind, hg2, hNm.later ?_, Q₂.sizedG⟩
    exact Q₂.later

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.padNames_behind_digits
