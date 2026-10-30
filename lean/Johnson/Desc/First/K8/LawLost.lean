-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/K8/LawLost.lean: THE SMALLNESS TEST, ITS FIRST HALF: ITS LAW WITH THE ROUND'S
LOST SET WRITTEN OUT.

`piece_good` (Johnson/Desc/First/K8/LawPiece.lean) says that the kind's block at its own stretch has
the library's property `KObj.BK.Good`. Its third part is round-by-round knowledge soundness, a
recursion over the stretch's rounds. The stretch has ONE round: here that recursion is unfolded, so
that the law can be read with no notion of the library's but a count.
  `hear_lost`: at every statement in front of the block that meets the condition there, and whatever
    the prover sends in the round: of the written verifier messages c, AT MOST e are such that the
    following FAILS: whenever the block puts out a statement behind, and that statement breaks the
    promise behind or has the witness w, the statement in front has the witness w.
  `hear_leads`: so outside that lost set: a statement behind that has a witness gives a statement in
    front that has one: the same. `hear_keeps`: and, at EVERY c, lost or not: the promise behind is
    kept.
Statements and proofs. The lost set is of this one round; e is the piece's error: at least the
proved block's count (one part in 2 ^ tau of the typed challenges) times the sampler's own bound on
how many written messages go to one typed challenge. It holds at every transcript, not at an honest
one alone.
Limits: those of LawPiece.lean: the caller and the letters are parameters; no caller is named. That
there is a combination (tau is not 0) is no premise: at tau = 0 the bound e is at least the whole
space and the law says nothing; the kind's own test on the plan shuts that case out of a
description.

-/
import Johnson.Desc.First.K8.LawPiece

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open Iop Prob Cb.Pv.Tail OnBytes.Maker OnBytes.Tie.Pv.Tail KObj VerifiableInference.OnPublicFiles
  VerifiableInference.Desc.Sound

section
variable {S Cl W : Type} {F : Frame} {seat : Seat S} {p : Par} {base e : ℕ} {d : TailCallerOn}

/-- What holds at a written transcript of the round outside the lost set. -/
def Reads.Fine (Q : Reads Cl W F seat p base e d) (a : S × F.E.Str)
    (m : (roundT (Run.ckP .two) (rdt p)).up.Msg) (c : (roundT (Run.ckP .two) (rdt p)).up.Chal) :
    Prop :=
  ∀ (a' : S × F.E.Str) (w : W),
    (piece (Cl := Cl) (W := W) (F := F) seat p base e).ior.red.out a
      ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p])) = some a' →
    (Q.relB a' w ∨ ¬ Q.onB a') → Q.relA a w

/-- **The round's lost set has at most e members.** -/
theorem hear_lost (Q : Reads Cl W F seat p base e d) (hf : Fits p d.c.s) (hOK : d.c.s.OK)
    (he : (Fintype.card (Dr d.c.s) / 2 ^ d.c.s.tau) *
      (Run.bsRound .two (rdt p).entry (rdt p).kind).w ≤ e)
    (a : S × F.E.Str) (ha : Q.onA a) (m : (roundT (Run.ckP .two) (rdt p)).up.Msg) :
    cnt (fun c : (roundT (Run.ckP .two) (rdt p)).up.Chal => ¬ Q.Fine a m c) ≤ e :=
  (piece_good Q hf hOK he).know a ha m

/-- Outside the lost set a true statement behind gives a true statement in front. -/
theorem hear_leads (Q : Reads Cl W F seat p base e d) (a a' : S × F.E.Str)
    (m : (roundT (Run.ckP .two) (rdt p)).up.Msg) (c : (roundT (Run.ckP .two) (rdt p)).up.Chal)
    (hfine : Q.Fine a m c)
    (ho : (piece (Cl := Cl) (W := W) (F := F) seat p base e).ior.red.out a
      ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p])) = some a')
    (h : ∃ w, Q.relB a' w) : ∃ w, Q.relA a w :=
  h.elim fun w hw => ⟨w, hfine a' w ho (Or.inl hw)⟩

/-- At every written transcript the promise behind is kept. -/
theorem hear_keeps (Q : Reads Cl W F seat p base e d) (hf : Fits p d.c.s) (a a' : S × F.E.Str)
    (m : (roundT (Run.ckP .two) (rdt p)).up.Msg) (c : (roundT (Run.ckP .two) (rdt p)).up.Chal)
    (ha : Q.onA a)
    (ho : (piece (Cl := Cl) (W := W) (F := F) seat p base e).ior.red.out a
      ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p])) = some a') : Q.onB a' := by
  obtain ⟨_, hcf, hrd⟩ := Q.of_out hf a a' m c ho
  refine ⟨⟨matrixOf hf c, hcf⟩, fun β _ => ?_⟩
  unfold Reads.behind
  rw [hrd]
  exact ha

end

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.hear_lost
#print axioms VerifiableInference.Desc.First.K8.hear_leads
#print axioms VerifiableInference.Desc.First.K8.hear_keeps
