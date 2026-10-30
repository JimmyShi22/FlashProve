-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/AtPoints.lean: at the member of a chain's thread at which the
honest side of an attention segment's own rounds (kind K5) is seated: FROM THE PROVER's FRONTS TO
THE VERIFIER's POINTS. The prover's values are typed at the named points that it makes of the
challenges in front of a part; the verifier's claims are written at the named points that it makes
of all that it heard. Statements with their proofs. EVERY STATEMENT IS CONDITIONAL, and all but the
first hang on the ties (K5Script, Honest/K5/Law/Script.lean), WHICH ARE NOT SHOWN.

  same_front     what the verifier heard holds the challenges of the parts in front of part q that
                 the prover's side holds in front of round n, where part q begins at or in front of
                 round n
  pts_to         the prover's named points in front of round n are the verifier's, as far as the
                 parts in front of part q make them (PtsTo,
                 Johnson/Desc/K5/Honest/Law/PointsIs.lean)
  div_front      what the division's and the value product's summands share returns in front of
                 every round, with its fields written out
  end_at         **under end value number j's slot of the sumcheck that is part q lies the summand's
                 end value number j at the challenges that the verifier heard of that sumcheck**

Limits. Nothing is said on who sees what. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Ends
import Johnson.Desc.ProofFile.Honest.K5.Law.Rows
import Johnson.Desc.ProofFile.Honest.SumLaw.Law
import Johnson.Desc.K5.Honest.Law.PointsMore

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff Fork)
open VerifiableInference.Desc (Block Claim OpenedColumn First.S noDigest)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ worldOwn)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Par Heard Left Pts hear pointsOf chal)
open H2K5.Honest (shapes slotsTo SumPut K5In SameTo PtsTo heardAt ptsOf divIn DivIn)
open ProofFile.Honest.SumLaw

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {Z : Seat5} {p : Par} {blk : Block First.S Claim}
  {A : OnBytes.Attention.Plan} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}

/-- **What the verifier heard holds the challenges that the prover's side holds in front of round
n**, in the parts in front of part q. CONDITIONAL: the half's seat; the thread's clause on the
challenges heard; the prover's side of the step; the hearing's return; part q begins at or in front
of round n. -/
theorem same_front (Hs : K5Seated T b cells Z p blk) {k : Coins Bk}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn} (hF : T.Fit b m)
    (hM : T.Moved blk k m E ds y cols) {F : Fork} {hd5 : Heard} {st : P.St}
    (hh : hear p.own (F, (roundsOf y.1).map noDigest, 0) = some (hd5, st)) {n q : Nat}
    (hq : H2K5.Honest.firstOf Z.P.x q ≤ n) :
    SameTo Z.P.x q hd5 (heardAt Z.P (chalOf Z (m.st.heard ++ ds.take n)) fun _ => none) := by
  have S := heard_at Hs hF hM hh [] q
  rw [List.append_nil] at S
  refine S.trans (H2K5.Honest.heardAt_agree Z.P fun i hi => ?_)
  rw [chalOf_own Hs hF, chalOf_own Hs hF, List.getElem?_take_of_lt (Nat.lt_of_lt_of_le hi hq)]

section
variable (Hs : K5Seated T b cells Z p blk) (Sc : K5Script T b cells Z A blk own rdOf)
  {k : Coins Bk} {s : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
  {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn} (hT : Thr T b k s m E)
  (hd : drawsFit blk.rounds ds = true) (hM : T.Moved blk k m E ds y cols)
  {att : VerifiableInference.Desc.First.AttOwn} (e : s.here = .att att)

include Hs Sc hT hd hM e in
/-- **The prover's named points in front of round n are the verifier's**, as far as the parts in
front of part q make them. pv: the verifier's, made of what it heard, its rows Lf and the key points
that the lookup on the calls left. CONDITIONAL: on the ties; as `same_front`; both calls return. -/
theorem pts_to {F : Fork} {hd5 : Heard} {st : P.St}
    (hh : hear p.own (F, (roundsOf y.1).map noDigest, 0) = some (hd5, st))
    {g : OnBytes.Model.Forest.Heard} (hg : att.g = some g) {Lf : Left} {pv : Pts}
    (hp : pointsOf Z.P.g g.zk hd5 Lf = some pv) {n q : Nat}
    (hq : H2K5.Honest.firstOf Z.P.x q ≤ n) {p₀ : Pts}
    (hp₀ : ptsOf Z.P (chalOf Z (m.st.heard ++ ds.take n)) = some p₀) : PtsTo Z.P.x q p₀ pv := by
  obtain ⟨g', hg', hk, -⟩ := key_at Sc hT e hd
  obtain rfl : g' = g := Option.some.inj (hg'.symm.trans hg)
  rw [← hk n] at hp
  exact H2K5.Honest.points_same Z.P (same_front Hs hT.2.1 hM hh hq) hp₀ hp

include Hs Sc hT hd e in
/-- **What the division's and the value product's summands share returns in front of every round.**
CONDITIONAL: on the ties; the half's seat; the thread in front. -/
theorem div_front (n : Nat) : ∃ (p₀ : Pts) (Dv : DivIn),
    ptsOf Z.P (chalOf Z (m.st.heard ++ ds.take n)) = some p₀ ∧
      divIn Z.P (chalOf Z (m.st.heard ++ ds.take n)) = some Dv ∧ Dv.d = p₀.d ∧
      Dv.ec = P.eqTab p₀.d.zcW := by
  obtain ⟨p₀, hp₀⟩ := pts_front Hs Sc hT hd e n
  obtain ⟨uW, _, hW, _⟩ := P.points_div (show pointsOf Z.P.g _ _ _ = some p₀ from hp₀)
  refine ⟨p₀, ⟨p₀.d, P.weights uW ((chalOf Z (m.st.heard ++ ds.take n)).zk.getD uW.call #[]),
    P.inner uW ((chalOf Z (m.st.heard ++ ds.take n)).zk.getD uW.call #[]),
    heardAt Z.P (chalOf Z (m.st.heard ++ ds.take n)) fun _ => none, P.eqTab p₀.d.zcW⟩, hp₀, ?_,
    rfl, rfl⟩
  unfold divIn
  rw [hp₀]
  show (Z.P.g.single .wl).bind _ = _
  rw [hW]
  rfl

variable {dc : List Fmt.Drawn} {D : Bound GQ} (hD : MaskIs T own rdOf k s att m dc D)

include Hs Sc hT hd hM e hD in
/-- **Under end value number j's slot lies the summand's end value number j, at the challenges that
the verifier heard of that sumcheck.** SP: what lies in the ledger; H: the sumcheck as the kind's
hearing heard it; hn: the summand has as many end values as the call. CONDITIONAL: as sum_slots
(Honest/K5/Law/Slots.lean). -/
theorem end_at {q ld : Nat} {vs : List Var} {en : Ends}
    (hq : (shapes Z.P.x)[q]? = some (.sum ⟨ld, vs, some en⟩)) {G : Fork} {hhq : MaskedSum.Heard}
    (SP : SumPut ⟨ld, vs, some en⟩ (att.F.next + slotsTo Z.P.x q)
      ((roundsOf y.1).drop (H2K5.Honest.firstOf Z.P.x q)) hhq G) {C : Aff}
    (H : SumHeardAt Z.P.x (roundsOf y.1) G q C vs en hhq)
    (hn : ((jobs Z.P).sum q (inOf Z.P.S Z.link (cells m.st.input.trace))
      (chalOf Z (m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x q)))).ends = en.n) :
    (hhq.r.take vs.length).toArray = chal hhq ∧
      ∀ j, j < en.n → (worldOwn (behindPart s att G) [] D).slot (hhq.sEnd + j) =
        Reading.gl.val (((jobs Z.P).sum q (inOf Z.P.S Z.link (cells m.st.input.trace))
          (chalOf Z (m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x q)))).endAt
            (hhq.r.take vs.length) j) := by
  have hM' := hM
  obtain ⟨⟨l, hst, hy⟩, -⟩ := hM'
  obtain ⟨cq, hl, -⟩ := k5_cut T Hs hd hst hy q _ hq
  have ha := (sum_slots Hs Sc hT hd hM e hD hq SP hl).1
  have hE := end_slots Hs Sc hT hd hM e hD hq SP H
  obtain ⟨ld', F', G', hq', hhear, -, -⟩ := H
  obtain rfl : ld' = ld := by
    have h1 := Option.some.inj (hq'.symm.trans hq)
    cases h1
    rfl
  have ec := callAt_jobOf (X := Unit) ⟨ld', vs, some en⟩
    (fun w fr => (jobs Z.P).alone q w (chalOf Z fr.heard))
    (fun w fr => (jobs Z.P).sum q w (chalOf Z fr.heard))
    (inOf Z.P.S Z.link (cells m.st.input.trace))
    (frontOf (⟨inOf Z.P.S Z.link (cells m.st.input.trace),
      m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x q), ()⟩ : State K5In Unit)
      (m.shown.plus ((roundsOf y.1).take (H2K5.Honest.firstOf Z.P.x q))))
  have hr := (sumClaim Unit K5In Unit _ _ _ cq _ _ _ _ C F' G' hhq
    (by rw [ec]; exact k5_drawsOk T Hs hd q _ hq) ha (by rw [ec]; exact hhear)).2.1
  rw [ec] at hr
  refine ⟨take_is_chal hhq vs.length (H2K5.Honest.HeardIs.hear_r hhear).1, fun j hj => ?_⟩
  rw [hE j hj, ← hr]
  unfold H2K5.Honest.Summand.endsAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by rw [hn]; exact hj)]
  rfl

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.same_front
#print axioms ProofFile.Honest.K5.pts_to
#print axioms ProofFile.Honest.K5.div_front
#print axioms ProofFile.Honest.K5.end_at
