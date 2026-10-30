-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/PartsUnits.lean: CONDITIONAL: the honest prover's side of an attention
segment's own rounds: for the masked sumchecks of the softmax-table units and of "the value product
below the diagonal": what a statement on the row that the verifier makes of such a sumcheck asks of
the prover's summand, in the letters of the planner's numbers of these rounds and of what the
verifier has heard. Statements with their proofs. It does for these summands what
Johnson/Desc/K5/Honest/Law/Parts.lean does for four others, in the same forms.

For a summand S, x the planner's numbers, hd or o what the verifier has heard:
  `sVM_vars_x`, `sK_vars_x`   S has the planner's number of variables
  `sVM_tame_x`, `sKM_tame_x`, `sKD_tame_x`   `Summand.Tame` (Law/TermsLaw.lean) at that number of
                variables, 4 coefficients a variable, degree 2 in the further variable
  `sVM_ends_x`, `sK_ends_x`   S has two end values for each pair, for each piece, that the planner
                              counts
  `sVM_good`, `sK_good`   at the challenges that the verifier has heard in this sumcheck, S's terms
                          are
                the weighted products of pairs AT THE VERIFIER'S OWN ARRAY OF WEIGHTS: the prover's
                array and the verifier's are one array, not only read alike; and that array's length
Tool: `wBelow_congr`.

Every statement but the tool and the two on variables is conditional. The premises, and who is meant
to show each: `Sized`, `Planned`, `PairsAre`, `UnitIs`, the planner's numbers of a unit, that the
place's unit has the planner's number of pieces, lM ≤ a 0: public (Law/PublicAtPlan.lean).
`divIn P c = some Dv`, `DivPts`, `KeyPtsAre`, that the verifier's function of the points returns
with the unit's points: as in the files on the readings. hr: the verifier has heard one challenge a
variable and one more. hs: the list's unit has a weight for each pair; hW: the verifier's function
of a unit's weights returns: both are tests of the verifier's own, so a caller on the honest side
has to show that they pass. The key points stand as c.zk, the prover's; a caller whose statement
names the verifier's own key points has to lay that the two are one.
Limits. Nothing here says that a premise holds at any place or run.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.UnitPts
import Johnson.Desc.K5.Honest.Law.ReadVM
import Johnson.Desc.K5.Honest.Law.Parts

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E zeroE)
open OnBytes.Model (Reading)
open VerifiableInference.Desc.First.Att.P (Geo UnitG ScoreP Heard chal weights inner wBelow scoreW
  KeyPtsAre UnitIs)
open Inst.Model.AttSeg (Calls Pub Step)

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## The value product below the diagonal -/

/-- The weights of "the value product below the diagonal" read of what was heard that sumcheck's
challenges alone. -/
theorem wBelow_congr (g : Geo) (pw zW : Array E) {h h' : Heard} (e : chal h.below = chal h'.below) :
    wBelow g pw zW h = wBelow g pw zW h' := by
  unfold wBelow
  rw [e]

theorem sVM_vars_x (P : Pub5) (w : K5In) (c : Chal) : (sVM P w c).vars = P.x.valueM := by
  rw [← cut_iVM]
  unfold sVM
  dsimp only
  split <;> rfl

/-- It has two end values for each pair that the planner counts. -/
theorem sVM_ends_x (P : Pub5) (w : K5In) (c : Chal) (Pl : Planned P) :
    (sVM P w c).ends = 2 * P.x.pairs := by
  rw [Pl.pairs]
  unfold sVM
  dsimp only
  split <;> rfl

/-- It has what the masked sumcheck's prover asks of it, at the planner's number of variables. -/
theorem sVM_tame_x {P : Pub5} (H : Sized P) (w : K5In) (Pl : Planned P) {c : Chal} {Dv : DivIn}
    (h : divIn P c = some Dv) {C : Calls} {p : Pub K} (R : DivPts ρ P C p Dv)
    (pr : PairsAre P.g Dv.d.pwW) : (sVM P w c).Tame ρ (List.replicate P.x.valueM 4) 2 := by
  have T := sVM_tame ρ w H Pl h R pr
  rwa [sVM_vars_x] at T

/-- **At the challenges that the verifier has heard in this sumcheck, its terms are the weighted
products of pairs at the verifier's own array of weights**, which has a weight for each pair. -/
theorem sVM_good (P : Pub5) (w : K5In) (Pl : Planned P) {c : Chal} {Dv : DivIn}
    (h : divIn P c = some Dv) {hd : Heard} (hr : hd.below.r.length = P.x.valueM + 1) {wl : UnitG}
    (hwl : P.g.single .wl = some wl) (hs : (weights wl (c.zk.getD wl.call #[])).size = P.g.NP) :
    (sVM P w c).terms (hd.below.r.take (sVM P w c).vars) = pairsOf P.x.pairs
        (wBelow P.g (weights wl (c.zk.getD wl.call #[])) (inner wl (c.zk.getD wl.call #[])) hd) ∧
      (wBelow P.g (weights wl (c.zk.getD wl.call #[])) (inner wl (c.zk.getD wl.call #[]))
        hd).size = P.x.pairs := by
  obtain ⟨_, wl', _, h2, _, e1, e2, _, _⟩ := divIn_spec h
  obtain rfl : wl' = wl := Option.some.inj (h2.symm.trans hwl)
  refine ⟨?_, ?_⟩
  · rw [sVM_vars_x, sVM_eq P w c h, ofProducts_terms, Pl.pairs, e1, e2]
    refine congrArg _ (wBelow_congr _ _ _ ?_)
    show chal (sumAt _) = _
    rw [chal_sumAt, take_chal _ _ hr]
  · unfold wBelow
    rw [Array.size_map, hs, Pl.pairs]

/-! ## A softmax-table unit -/

/-- The unit number i has the planner's number of variables. u: the planner's two numbers of that
unit: variables, pieces. -/
theorem sK_vars_x (P : Pub5) (w : K5In) (c : Chal) {i : ℕ} {u : ℕ × ℕ}
    (hx : P.x.score[i]? = some u) : (sK P w c i).vars = u.1 := by
  rw [← cut_unit P.x i u hx]
  unfold sK
  dsimp only
  split <;> rfl

/-- It has two end values for each piece that the planner counts. hn: the place's unit has the
planner's number of pieces (public). -/
theorem sK_ends_x (P : Pub5) (w : K5In) (c : Chal) {i : ℕ} {u : ℕ × ℕ} {ug : UnitG}
    (hug : P.g.scores[i]? = some ug) (hn : ug.pcs.length = u.2) : (sK P w c i).ends = 2 * u.2 := by
  rw [← hn]
  unfold sK
  simp only [hug, Option.map_some, Option.getD_some]
  split <;> rfl

/-- Below the diagonal: it has what the masked sumcheck's prover asks of it, at the planner's number
of variables. -/
theorem sKM_tame_x {P : Pub5} (H : Sized P) (w : K5In) {c : Chal} {i : ℕ} {u : ℕ × ℕ}
    (hx : P.x.score[i]? = some u) {ug : UnitG} {k : ScoreP} (hug : P.g.scores[i]? = some ug)
    (hk : (ptsOf P c).bind (·.scores[i]?) = some k) (hbel : ug.below = true)
    (hv : (cut P.x).getD i 3 - 3 = Step.s6b.g P.D) {C : Calls} {p : Pub K}
    (Kp : KeyPtsAre ρ C p.z c.zk) {q : Fin 4} (U : UnitIs P.D C .m1 q ug)
    (pr : PairsAre P.g k.pw) : (sK P w c i).Tame ρ (List.replicate u.1 4) 2 := by
  have T := (sKM_reads_of ρ w H hug hk hbel hv Kp U pr).tame
    fun b ξ => OnBytes.Road.Rows.wbExt6b P.D C p b ξ
  rwa [sK_vars_x P w c hx] at T

/-- On the diagonal: the like. -/
theorem sKD_tame_x {P : Pub5} (H : Sized P) (w : K5In) {c : Chal} {i : ℕ} {u : ℕ × ℕ}
    (hx : P.x.score[i]? = some u) {ug : UnitG} {k : ScoreP} (hug : P.g.scores[i]? = some ug)
    (hk : (ptsOf P c).bind (·.scores[i]?) = some k) (hbel : ug.below = false)
    (hv : (cut P.x).getD i 3 - 3 = Step.s6d.g P.D) {C : Calls} {p : Pub K}
    (Kp : KeyPtsAre ρ C p.z c.zk) {q : Fin 4} (U : UnitIs P.D C .d1 q ug) (hM : P.D.lM ≤ C.a 0)
    (pr : PairsAre P.g k.pw) : (sK P w c i).Tame ρ (List.replicate u.1 4) 2 := by
  have T := (sKD_reads_of ρ w H hug hk hbel hv Kp U hM pr).tame
    fun b ξ => OnBytes.Road.Rows.wbExt6d P.D C p b ξ
  rwa [sK_vars_x P w c hx] at T

/-- **At the challenges that the verifier has heard in this unit's sumcheck, its terms are the
weighted products of pairs at the verifier's own array of weights** Wt, which has a weight for each
piece. o: what the verifier has heard of the unit. hn: as in `sK_ends_x`. -/
theorem sK_good (P : Pub5) (w : K5In) {c : Chal} {i : ℕ} {u : ℕ × ℕ}
    (hx : P.x.score[i]? = some u) {ug : UnitG} {k : ScoreP} (hug : P.g.scores[i]? = some ug)
    (hk : (ptsOf P c).bind (·.scores[i]?) = some k) (hn : ug.pcs.length = u.2)
    {o : ℕ × VerifiableInference.Desc.Part.MaskedSum.Heard} (hr : o.2.r.length = u.1 + 1)
    {Wt : Array E} (hW : scoreW P.g ug (c.zk.getD ug.call #[]) (chal o.2) = some Wt) :
    (sK P w c i).terms (o.2.r.take (sK P w c i).vars) = pairsOf u.2 Wt ∧ Wt.size = u.2 := by
  refine ⟨?_, ?_⟩
  · rw [sK_vars_x P w c hx, sK_eq P w c hug hk, ofProducts_terms, take_chal _ _ hr, hW, hn]
    rfl
  · unfold scoreW at hW
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hW
    obtain ⟨_, _, e⟩ := hW
    rw [← e, Array.size_map, ← hn, VerifiableInference.Desc.First.Att.P.weights_eq]
    simp [VerifiableInference.Desc.First.Att.P.pcsSorted]

end H2K5.Honest

#print axioms H2K5.Honest.wBelow_congr
#print axioms H2K5.Honest.sVM_vars_x
#print axioms H2K5.Honest.sVM_ends_x
#print axioms H2K5.Honest.sVM_tame_x
#print axioms H2K5.Honest.sVM_good
#print axioms H2K5.Honest.sK_vars_x
#print axioms H2K5.Honest.sK_ends_x
#print axioms H2K5.Honest.sKM_tame_x
#print axioms H2K5.Honest.sKD_tame_x
#print axioms H2K5.Honest.sK_good
