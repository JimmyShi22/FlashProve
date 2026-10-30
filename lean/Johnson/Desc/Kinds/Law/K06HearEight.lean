-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K06HearEight.lean: THE OUTPUT HEAD'S ONE HEARING, CUT AT EIGHT GIVEN
STRETCHES OF ROUNDS.
WHAT IT IS NOT. CONDITIONAL: THAT THE HEARING RETURNS IS A PREMISE, and so are the stretches'
lengths and that the ledger in front is well laid. Nothing on what the rounds hold, on whether the
verifier accepts, on soundness, on completeness or on what a proof hides.
WHY. Law/Cut.lean's hear_parts and Law/NormHear.lean's norm_parts say that THERE ARE stretches at
which the hearing's seven parts return. Who has the rounds as eight pieces of known lengths (a
prover's eight parts) wants the returns AT THESE PIECES.
  point_spec      what a return of drawPoint on its own round says: one round; the point is what the
                  round sampled; as many elements as asked.
  hear_eight      the pieces q0 .. q7: the point's round; nine hidden scalars; the sumcheck on the
                  squares; the round that ends it; seven hidden scalars; the sumchecks on the
                  products, on "normed", and the head's own. Where hear returns on them in a row,
                  using them up: drawPoint, sendThenBatch, level (on q2 ++ q3), sendThenBatch and
                  three times sumcheck return, each on its own piece with none left, each from a
                  well-laid ledger; each ledger's next number is the one in front plus what the part
                  takes (Law/Takes.lean); the last ledger G is later than each; the point has lt
                  coordinates. Of G's own next number, and of whether G is well laid, nothing is
                  said.
CALLED, OF THE LIBRARY: hear_parts, norm_parts, round_one, batch_one, level_length, sumcheck_spec,
zS_size, takes_send, takes_level, takes_sumcheck, sized_of, keeps_sendThenBatch, keeps_level,
keeps_sumcheck, roundOf_spec, and the small lemmas on a hearing's steps.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K06EveryList

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Fork)
open OnBytes.PscRun (Later)
open Norm (lt ls d lPd T S2)

variable [Sizes] [Policy] [Request] [Token]

/-- What a return of drawPoint that leaves no round says. -/
theorem point_spec {n : Nat} {F G : Fork} {p : List Fmt.RoundView} {z : Point}
    (h : drawPoint n F p = some (z, G, [])) :
    ∃ r, p = [r] ∧ z = (r.drawn.elems.map E.ofTriple).toArray ∧ r.drawn.elems.length = n := by
  unfold drawPoint at h
  obtain ⟨x, Fx, lx, a, b⟩ := bind_some h
  obtain ⟨e, _, rfl⟩ := pure_some b
  obtain ⟨r, rfl, hr⟩ := round_one a
  obtain ⟨_, _, s3, s4⟩ := Part.MaskedSum.roundOf_spec (s := x.1) (d := x.2) hr
  exact ⟨r, rfl, by rw [← e, s4], s3⟩

variable [FinalNorm.In] [In]

/-- **THE ONE HEARING, AT EIGHT GIVEN PIECES.** -/
theorem hear_eight {F G : Fork} {H : HeardAll} {q0 q1 q2 q3 q4 q5 q6 q7 : List Fmt.RoundView}
    (hW : WellLaid F)
    (h : hear F (q0 ++ (q1 ++ (q2 ++ (q3 ++ (q4 ++ (q5 ++ (q6 ++ q7))))))) = some (H, G, []))
    (l0 : q0.length = 1) (l1 : q1.length = 1) (l2 : q2.length = lPd + lt + 3)
    (l3 : q3.length = 1) (l4 : q4.length = 1) (l5 : q5.length = lt + 3)
    (l6 : q6.length = (FinalNorm.zt).size + 3) :
    ∃ Fa Fb Fc Fd Fe : Fork,
      drawPoint lt F q0 = some (H.1.pV, F, []) ∧
      sendThenBatch 9 9 F q1 = some ((H.1.W, H.1.gam), Fa, []) ∧
      level (zS H.1.pV) (Norm.squaresStart H.1.W H.1.gam #[]) Fa (q2 ++ q3) =
        some (H.1.squares, Fb, []) ∧
      sendThenBatch 7 7 Fb q4 = some ((H.1.P, H.1.om), Fc, []) ∧
      sumcheck H.1.pV 4 Fc q5 = some (H.1.products, Fd, []) ∧
      sumcheck FinalNorm.zt 2 Fd q6 = some (H.2.1.normed, Fe, []) ∧
      sumcheck (FinalNorm.zt ++ halves Norm.lPd) 2 Fe q7 = some (H.2.2.logits, G, []) ∧
      (WellLaid Fa ∧ WellLaid Fb ∧ WellLaid Fc ∧ WellLaid Fd ∧ WellLaid Fe) ∧
      (Fa.next = F.next + 9 ∧ Fb.next = Fa.next + (0 + ((2 * (zS H.1.pV).size + 3) + 2)) ∧
        Fc.next = Fb.next + 7 ∧ Fd.next = Fc.next + (1 + ((2 * H.1.pV.size + 3) + 4)) ∧
        Fe.next = Fd.next + (1 + ((2 * (FinalNorm.zt).size + 3) + 2))) ∧
      (Later Fa G ∧ Later Fb G ∧ Later Fc G ∧ Later Fd G ∧ Later Fe G) ∧
      H.1.pV.size = lt := by
  obtain ⟨Fd, Fe, lr, hNorm, wd, we, hN, hLg, hleft⟩ := Came.hear_parts hW h
  obtain ⟨p0, p1, tS, p2, tP, Fa, Fb, Fc, hrs, h0, h1, _, h2, h3, h4, wa, wb, wc⟩ :=
    norm_parts hW hNorm
  obtain ⟨r0, e0, hpv, hn0⟩ := point_spec h0
  have sPV : H.1.pV.size = lt := by rw [hpv, List.size_toArray, List.length_map, hn0]
  obtain ⟨r1, _, e1, _, _, _⟩ := batch_one h1
  obtain ⟨r2, _, e2, _, _, _⟩ := batch_one h3
  have lS : tS.length = lPd + lt + 4 := by rw [level_length h2, zS_size H.1.pV sPV]
  obtain ⟨_, _, _, _, _, _, lP, _⟩ := sumcheck_spec h4
  rw [sPV] at lP
  -- piece by piece
  obtain ⟨a0, t0⟩ := List.append_inj hrs (by rw [l0, e0]; rfl)
  obtain ⟨a1, t1⟩ := List.append_inj t0 (by rw [l1, e1]; rfl)
  rw [← List.append_assoc] at t1
  obtain ⟨a2, t2⟩ := List.append_inj t1 (by rw [List.length_append, l2, l3, lS])
  obtain ⟨a3, t3⟩ := List.append_inj t2 (by rw [l4, e2]; rfl)
  obtain ⟨a4, t4⟩ := List.append_inj t3 (by rw [l5, lP])
  subst a0 a1 a2 a3 a4 t4
  rw [← l6, List.take_left] at hN
  rw [← l6, List.drop_left] at hLg hleft
  have hq7 : q7.take ((FinalNorm.zt ++ halves Norm.lPd).size + 3) = q7 :=
    List.take_of_length_le (List.drop_eq_nil_iff.mp hleft.symm)
  rw [hq7] at hLg
  have k7 : Later Fe G := keeps_sumcheck _ _ _ _ _ _ _ hLg
  have k6 : Later Fd G := (keeps_sumcheck _ _ _ _ _ _ _ hN).trans k7
  have k5 : Later Fc G := (keeps_sumcheck _ _ _ _ _ _ _ h4).trans k6
  have k4 : Later Fb G := (keeps_sendThenBatch _ _ _ _ _ _ _ h3).trans k5
  have k2 : Later Fa G := (keeps_level _ _ _ _ _ _ _ h2).trans k4
  exact ⟨Fa, Fb, Fc, Fd, Fe, h0, h1, h2, h3, h4, hN, hLg, ⟨wa, wb, wc, wd, we⟩,
    ⟨(takes_send (sized_of hW) h1).next, (takes_level (sized_of wa) h2).next,
      (takes_send (sized_of wb) h3).next, (takes_sumcheck (sized_of wc) h4).next,
      (takes_sumcheck (sized_of wd) hN).next⟩, ⟨k2, k4, k5, k6, k7⟩, sPV⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.point_spec
#print axioms VerifiableInference.Desc.Kinds.Head.Law.hear_eight
