-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/DrawnFront.lean: CONDITIONAL: at the member of a chain's thread
at which the honest side of an attention segment's own rounds (kind K5) is seated: THE ROUND THAT
DRAWS MANY ELEMENTS HAS BEEN HEARD WHOLE in front of every part behind it. Statements with their
proofs.

  point_size     what the verifier's hearing holds of that round has 2 lgk + 2 lt + 4 elements
  point_front    so has what the prover's side holds of it in front of round n, where the part
                 behind that round begins at or in front of round n
  drawn_front    **the premise Drawn (Johnson/Desc/K5/Honest/Law/Weights.lean) at the challenges in
                 front of part q**, for every part q behind that round: the maxima's round, the
                 score at the index, the key at the index, the index's cells among them

Every statement is CONDITIONAL: the hearing's return; for the last two also: the half's seat, the
thread's clause on the challenges heard, the prover's side of the step; for the last: the two public
premises on the shape's and the planner's numbers. The ties between the witness and the honest side
are not spent.

Limits. Numbers of elements alone. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.AtPoints
import Johnson.Desc.K5.Honest.Law.Weights

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block Claim OpenedColumn First.S noDigest)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Par Heard hear hear_ran close_spec)
open H2K5.Honest (iZero Drawn Planned)

/-- What the hearing holds of the round that draws many elements. CONDITIONAL: its return. -/
theorem point_size {x : OnBytes.Params.AttentionRounds} {s0 s' : P.St} {h : Heard}
    (hh : hear x s0 = some (h, s')) : h.point.size = 2 * x.lgk + 2 * x.lt + 4 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, ⟨F8, rs8, l8⟩, ⟨F9, rs9, l9⟩, _, _, _, _, _, _, pt, _, _, _, _,
    _, _, _, _, _, _, h9, hpt, _⟩ := (hear_ran hh).ran
  obtain ⟨_, _, r, _, _, hn, hd⟩ := close_spec h9
  rw [hpt, List.size_toArray, hd, List.length_map, hn]

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {Z : Seat5} {p : Par} {blk : Block First.S Claim}

section
variable (Hs : K5Seated T b cells Z p blk) {k : Coins Bk} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
  {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
  (hF : T.Fit b m) (hM : T.Moved blk k m E ds y cols) {F : Fork} {hd5 : Heard} {st : P.St}
  (hh : hear p.own (F, (roundsOf y.1).map noDigest, 0) = some (hd5, st))
include Hs hF hM hh

/-- What the prover's side holds of that round in front of round n. CONDITIONAL: see the head. -/
theorem point_front {n : Nat} (hn : H2K5.Honest.firstOf Z.P.x (iZero Z.P.x + 1) ≤ n) :
    ((chalOf Z (m.st.heard ++ ds.take n)).many (H2K5.Honest.firstOf Z.P.x (iZero Z.P.x))).size =
      2 * Z.P.x.lgk + 2 * Z.P.x.lt + 4 := by
  have S := (same_front Hs hF hM hh hn).point (Nat.lt_succ_self _)
  have h1 := point_size hh
  rw [Hs.own, S] at h1
  exact h1

/-- **The premise Drawn at the challenges in front of part q**, q behind the round that draws many
elements. CONDITIONAL: see the head. -/
theorem drawn_front (H : H2K5.Honest.Sized Z.P) (Pl : Planned Z.P) {q : Nat}
    (hq : iZero Z.P.x < q) :
    Drawn Z.P (chalOf Z (m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x q))) :=
  ⟨by
    rw [point_front Hs hF hM hh (H2K5.Honest.HeardIs.firstOf_mono Z.P.x hq), Pl.lgk, Pl.lt, H.lt]
    exact Nat.le_refl _⟩

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.point_size
#print axioms ProofFile.Honest.K5.point_front
#print axioms ProofFile.Honest.K5.drawn_front
