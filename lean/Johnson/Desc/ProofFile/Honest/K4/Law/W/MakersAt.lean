-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/MakersAt.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the prover's side: the hypothesis
`MakersNorms` (Law/W/RightNorms.lean) at a state behind the member's step: the two makers return by
the public test k4Fits (K4Seated's field fits), by squares_run and rows_run (Law/SumAtRun.lean);
the two lengths are stand_lens' (Law/SlotsTrue.lean). Statement and proof.

  **`makersNorms_at`**   MakersNorms.

Not shown here. That a state behind the member's step exists: no example is known. The length of
the norms' token point (hPV) and that the layout's number of token bits is the library's (hlt) are
premises. The import closure holds, with Law/W/Halves.lean's own imports, seven modules under
Johnson/RecCompile/. Nothing on soundness, on completeness or on any other property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.RightNorms
import Johnson.Desc.ProofFile.Honest.K4.Law.PtsAtStand
import Johnson.Desc.ProofFile.Honest.K4.Law.SumAtRun
import Johnson.Desc.ProofFile.Honest.K4.Law.OwnFits
import Johnson.Desc.ProofFile.Honest.K4.Law.Starts
import Johnson.Desc.ProofFile.Honest.K4.Law.LookSkel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest
open Inst.Model.FFSeg (Dim)
open VerifiableInference.Desc (Block Claim First.S)
open VerifiableInference.Desc.Sound (MsgQ)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}

/-- **THE NORMS' MAKERS RETURN, AND THE LENGTHS FIT, AT A STATE BEHIND THE MEMBER's STEP.**
CONDITIONAL: on Z, hT, hd, hPV and hlt. -/
theorem makersNorms_at {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {b : Nat} {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Q : K4Pub} {p : Par}
    {blk : Block First.S Claim} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}
    {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn} {A : VerifiableInference.Desc.K9.Part} {o : Own}
    {D : Dim}
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) (hd : drawsFit blk.rounds ds = true) (hPV : o.H.PV.size = D.lT)
    (hlt : Q.P.y.h.lt = D.lT) :
    MakersNorms Q (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds o D := by
  have Se := Z.seat
  have hk : k4Fits Q (look Q m.st.heard) (tokens m.st.input.x) = true :=
    Se.fits m.st.heard m.st.input hT.2.1 hT.2.2.2.2.2.2
  have hr := stand_reach Z
  obtain ⟨_, _, _, _, _, _, e6⟩ := k4StartAt_eq Q
  have l6 : rE Q.P Q.hp Q.g + 1 ≤ ds.length := by rw [← e6]; exact hr
  have l1 : rJ2 Q.P Q.g ≤ ds.length := by
    unfold rE rJ6 rJ5 rJ4 rJ3 at l6
    omega
  have l0 : rJ1 Q.g ≤ ds.length := by
    unfold rJ2 rowsRound at l1
    unfold rJ1
    omega
  have hh := k4_heard_front Se hT
  have tk : ∀ n, (m.st.heard ++ ds.take n).take Q.r0 = m.st.heard := by
    intro n
    rw [← hh]
    exact List.take_left
  have ln : ∀ n, n ≤ ds.length → ((m.st.heard ++ ds.take n).drop Q.r0).length = n := by
    intro n hn
    rw [k4_own_drop Se hT, List.length_take]
    exact Nat.min_eq_left hn
  have s0 : (starts Q).getD 0 0 = rJ1 Q.g := by rw [k4_starts]; rfl
  have s1 : (starts Q).getD 1 0 = rJ2 Q.P Q.g := by rw [k4_starts]; rfl
  obtain ⟨j6, h6, _⟩ := squares_run (k4Wit Q cells weights tokens (look Q) m.st.input) hk
    (m.st.heard ++ ds.take (rJ1 Q.g)) (k4_own_fits Se hT hd _)
    (by rw [ln _ l0, s0]) (by rw [tk]; exact lookSkel_refl _)
  obtain ⟨j8, h8, _⟩ := rows_run (k4Wit Q cells weights tokens (look Q) m.st.input) hk
    (m.st.heard ++ ds.take (rJ2 Q.P Q.g)) (k4_own_fits Se hT hd _)
    (by rw [ln _ l1, s1]) (by rw [tk]; exact lookSkel_refl _)
  obtain ⟨a6, a8, _⟩ := stand_lens Z
  exact
    { sq := by rw [h6]; rfl
      rows := by rw [h8]; rfl
      PV := hPV
      rs6 := a6
      rs8 := by rw [a8]; exact hlt }

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.makersNorms_at
