-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/WrittenOut.lean: A PIECE WITH TWO ROUNDS, NOTHING BEHIND AND THE ERROR 2^-128
    A ROUND IS THE PIECE WRITTEN OUT (`k2Q`, Assembly.lean). One theorem. A law file: no
    sub-protocol imports it.

Why. What is owed at a place of the code switch (`K2PlaceOwes`, Counted.lean) asks the description's
    own piece as one equation: q = `k2Q` …. What others show of that piece are three facts on its
    fields.

What is said. `k2Q_of_facts`: from q.ds = [d₁, d₂], q.back = [] and q.err = the cap at 128 over q's
    own rounds: q = `k2Q q.b q.base d₁ d₂ extq` for some extractor extq.
  THE PAYERS OF THE THREE: the first two, with q.b: `K2.k2_piece`
      (Johnson/Top/H0/Tw/K2C/PieceFacts.lean), at every piece of the first row but the last; the
      third: by the join's owner's post its named rows of pieces bear that cap at every piece by
      definition: NOT OPENED IN LEAN BY US.

Limits. Not joined with either payer. No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Top.H0.K2Ties.Assembly

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes.Maker Iop
open VerifiableInference.Desc.Sound
open _root_.Run (ckP)

variable {F : Frame}

/-- **The piece written out, from three facts on its fields.** -/
theorem k2Q_of_facts {P Cl W : Type} (q : Piece (ckP .two) F (P × First.S) Cl W) (d₁ d₂ : RDT) (h1 :
    q.ds = [d₁, d₂]) (h2 : q.back = []) (h3 : q.err = Err.cap 128 (uLT (ckP .two) q.ds)) :
    ∃ extq, q = k2Q q.b q.base d₁ d₂ extq := by
  obtain ⟨b, base, ds, back, ext, err⟩ := q
  dsimp only at h1 h2 h3
  subst h1
  subst h2
  subst h3
  exact ⟨ext, rfl⟩

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.k2Q_of_facts
