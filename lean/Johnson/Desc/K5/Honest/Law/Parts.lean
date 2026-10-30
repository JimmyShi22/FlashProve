-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/Parts.lean: CONDITIONAL: the honest prover's side of an attention
segment's own rounds: for four of its masked sumchecks ("denominator times output", "the value
product on the diagonal", "the score at the index", "the index's cells are bits"): what a statement
on the row that the verifier makes of such a sumcheck asks of the prover's summand, in the letters
of the planner's numbers of these rounds and of what the verifier has heard. Statements with their
proofs.

For each summand S of the four, x the planner's numbers, hd what the verifier has heard:
  `.._vars_x`   S has the planner's number of variables
  `.._tame_x`   `Summand.Tame` (Johnson/Desc/K5/Honest/Law/TermsLaw.lean) at that number of
                variables, 4 coefficients a variable, degree 2 in the further variable
  `.._ends_x`   S has 2 x.pairs end values
  `.._good`     at the challenges that the verifier has heard in this sumcheck, S's terms are the
                weighted products of pairs, x.pairs of them, AT THE VERIFIER'S OWN ARRAY OF WEIGHTS:
                the prover's array and the verifier's are one array, not only read alike
  `atIndex_total`, `start_atIndex_total`, `start_cells_total`   the form from which the verifier
                starts the sumcheck is worth the summand's sum over the cube: for "the score at
                the index" and "the index's cells are bits" alone
Tools: `take_chal`; `wDivision_congr`, `wOn_congr`, `wAtIndex_congr`, `wCells_congr`: a weight
function of the verifier's reads of what was heard only the named fields.

Every statement but `sSE_vars_x` and `sVD_vars_x` is conditional. The premises, and who is meant to
show each: `Sized`, `Planned`, that a token has at most 16 bits, `PairsAre`: public
(Johnson/Desc/K5/Honest/Law/PublicAtPlan.lean). `divIn P c = some Dv`, `DivPts`, `Drawn`,
`IndexPts`, `MaxPts`, `AtIdn`: as in the files on the readings and the starts. hp: the verifier's
function of the points returns at c0: tests on lengths, the caller's. hwl: the shape has a unit for
the list of keys wl (the low 16 bits of the division's two remainders): public. hr: the verifier has
heard one challenge a variable and one more. hs: the list's unit has a weight for each pair: a test
of the verifier's own. ho, hp', ho'': three fields of what the verifier has heard are those that the
prover makes of its challenges: whoever ties the hearing to the challenges. hm: the row maxima that
were sent lie under their slots in the world.
The key points stand as c.zk, the prover's; a caller whose statement names the verifier's own key
points has to lay that the two are one.
Limits. Nothing here says that a premise holds at any place or run.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.ReadSE
import Johnson.Desc.K5.Honest.Law.Starts
import Johnson.Desc.K5.Honest.Law.Named
import Johnson.Desc.First.Att.K05Prem

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E zeroE)
open OnBytes.Model (Reading World Aff)
open OnBytes.Road (pt)
open VerifiableInference.Desc.First.Att.P (Geo UnitG Heard Pts chal weights inner wDivision wOn
  wAtIndex wCells batched)
open Inst.Model.AttSeg (Calls Pub)
open Finset

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## Tools -/

/-- All challenges of a sumcheck but the last, as the verifier cuts them and as the summand is
evaluated at them. -/
theorem take_chal (h : VerifiableInference.Desc.Part.MaskedSum.Heard) (n : ℕ)
    (hl : h.r.length = n + 1) : (h.r.take n).toArray = chal h := by
  unfold chal
  rw [List.dropLast_eq_take, hl, Nat.add_sub_cancel]

/-- The weights of "denominator times output" read of what was heard that sumcheck's challenges
alone. -/
theorem wDivision_congr (g : Geo) (pw zW : Array E) {h h' : Heard}
    (e : chal h.division = chal h'.division) : wDivision g pw zW h = wDivision g pw zW h' := by
  unfold wDivision
  rw [e]

/-- The weights of "the value product on the diagonal": the like. -/
theorem wOn_congr (g : Geo) (pw zW : Array E) {h h' : Heard} (e : chal h.on = chal h'.on) :
    wOn g pw zW h = wOn g pw zW h' := by
  unfold wOn
  rw [e]

/-- The weights of "the score at the index" read of what was heard the powers of its batching
element, the round of many elements, and that sumcheck's challenges. -/
theorem wAtIndex_congr (g : Geo) {h h' : Heard} (e1 : h.om = h'.om) (e2 : h.point = h'.point)
    (e3 : chal h.atIndex = chal h'.atIndex) : wAtIndex g h = wAtIndex g h' := by
  unfold wAtIndex
  rw [e1, e2, e3]

/-- The weights of "the index's cells are bits": the like. -/
theorem wCells_congr (g : Geo) {h h' : Heard} (e1 : h.om'' = h'.om'') (e2 : h.point = h'.point)
    (e3 : chal h.cells = chal h'.cells) : wCells g h = wCells g h' := by
  unfold wCells
  rw [e1, e2, e3]

/-! ## Denominator times output -/

theorem sSE_vars_x (P : Pub5) (w : K5In) (c : Chal) : (sSE P w c).vars = P.x.e := by
  rw [← cut_iSE]
  unfold sSE
  dsimp only
  split <;> rfl

/-- It has two end values for each pair that the planner counts. -/
theorem sSE_ends_x (P : Pub5) (w : K5In) (c : Chal) (Pl : Planned P) :
    (sSE P w c).ends = 2 * P.x.pairs := by
  rw [Pl.pairs]
  unfold sSE
  dsimp only
  split <;> rfl

/-- It has what the masked sumcheck's prover asks of it, at the planner's number of variables. -/
theorem sSE_tame_x {P : Pub5} (H : Sized P) (w : K5In) (Pl : Planned P) {c : Chal} {Dv : DivIn}
    (h : divIn P c = some Dv) {C : Calls} {p : Pub K} (R : DivPts ρ P C p Dv)
    (pr : PairsAre P.g Dv.d.pwW) : (sSE P w c).Tame ρ (List.replicate P.x.e 4) 2 := by
  have T := sSE_tame ρ H w Pl h R pr
  rwa [sSE_vars_x] at T

/-- **At the challenges that the verifier has heard in this sumcheck, its terms are the weighted
products of pairs at the verifier's own array of weights**, which has a weight for each pair. -/
theorem sSE_good (P : Pub5) (w : K5In) (Pl : Planned P) {c : Chal} {Dv : DivIn}
    (h : divIn P c = some Dv) {hd : Heard} (hr : hd.division.r.length = P.x.e + 1) {wl : UnitG}
    (hwl : P.g.single .wl = some wl) (hs : (weights wl (c.zk.getD wl.call #[])).size = P.g.NP) :
    (sSE P w c).terms (hd.division.r.take (sSE P w c).vars) = pairsOf P.x.pairs
        (wDivision P.g (weights wl (c.zk.getD wl.call #[])) (inner wl (c.zk.getD wl.call #[])) hd) ∧
      (wDivision P.g (weights wl (c.zk.getD wl.call #[])) (inner wl (c.zk.getD wl.call #[]))
        hd).size = P.x.pairs := by
  obtain ⟨_, wl', _, h2, _, e1, e2, _, _⟩ := divIn_spec h
  obtain rfl : wl' = wl := Option.some.inj (h2.symm.trans hwl)
  refine ⟨?_, ?_⟩
  · rw [sSE_vars_x, sSE_eq P w c h, ofProducts_terms, Pl.pairs, e1, e2]
    refine congrArg _ (wDivision_congr _ _ _ ?_)
    show chal (sumAt _) = _
    rw [chal_sumAt, take_chal _ _ hr]
  · unfold wDivision
    rw [Array.size_map, hs, Pl.pairs]

/-! ## The value product on the diagonal -/

theorem sVD_vars_x (P : Pub5) (w : K5In) (c : Chal) : (sVD P w c).vars = P.x.valueD := by
  rw [← cut_iVD]
  unfold sVD
  dsimp only
  split <;> rfl

/-- It has two end values for each pair that the planner counts. -/
theorem sVD_ends_x (P : Pub5) (w : K5In) (c : Chal) (Pl : Planned P) :
    (sVD P w c).ends = 2 * P.x.pairs := by
  rw [Pl.pairs]
  unfold sVD
  dsimp only
  split <;> rfl

/-- It has what the masked sumcheck's prover asks of it, at the planner's number of variables. -/
theorem sVD_tame_x {P : Pub5} (H : Sized P) (w : K5In) (Pl : Planned P) {c : Chal} {Dv : DivIn}
    (h : divIn P c = some Dv) {C : Calls} {p : Pub K} (R : DivPts ρ P C p Dv)
    (pr : PairsAre P.g Dv.d.pwW) : (sVD P w c).Tame ρ (List.replicate P.x.valueD 4) 2 := by
  have T := sVD_tame ρ H w Pl h R pr
  rwa [sVD_vars_x] at T

/-- **At the challenges that the verifier has heard in this sumcheck, its terms are the weighted
products of pairs at the verifier's own array of weights**, which has a weight for each pair. -/
theorem sVD_good (P : Pub5) (w : K5In) (Pl : Planned P) {c : Chal} {Dv : DivIn}
    (h : divIn P c = some Dv) {hd : Heard} (hr : hd.on.r.length = P.x.valueD + 1) {wl : UnitG}
    (hwl : P.g.single .wl = some wl) (hs : (weights wl (c.zk.getD wl.call #[])).size = P.g.NP) :
    (sVD P w c).terms (hd.on.r.take (sVD P w c).vars) = pairsOf P.x.pairs
        (wOn P.g (weights wl (c.zk.getD wl.call #[])) (inner wl (c.zk.getD wl.call #[])) hd) ∧
      (wOn P.g (weights wl (c.zk.getD wl.call #[])) (inner wl (c.zk.getD wl.call #[]))
        hd).size = P.x.pairs := by
  obtain ⟨_, wl', _, h2, _, e1, e2, _, _⟩ := divIn_spec h
  obtain rfl : wl' = wl := Option.some.inj (h2.symm.trans hwl)
  refine ⟨?_, ?_⟩
  · rw [sVD_vars_x, sVD_eq P w c h, ofProducts_terms, Pl.pairs, e1, e2]
    refine congrArg _ (wOn_congr _ _ _ ?_)
    show chal (sumAt _) = _
    rw [chal_sumAt, take_chal _ _ hr]
  · unfold wOn
    rw [Array.size_map, hs, Pl.pairs]

/-! ## The score at the index -/

theorem sSF_vars_x {P : Pub5} (H : Sized P) (Pl : Planned P) (w : K5In) (c : Chal) :
    (sSF P w c).vars = P.x.attained := by
  have e := Pl.vSF
  rw [cut_iSF] at e
  rw [e]
  show P.g.lt + P.g.lgk + P.g.ldh = P.D.lT + P.D.lg + P.D.ln
  rw [H.lt]
  rfl

/-- It has two end values for each pair that the planner counts. -/
theorem sSF_ends_x (P : Pub5) (w : K5In) (c : Chal) (Pl : Planned P) :
    (sSF P w c).ends = 2 * P.x.pairs := by
  rw [Pl.pairs]
  rfl

/-- It has what the masked sumcheck's prover asks of it, at the planner's number of variables. -/
theorem sSF_tame_x {P : Pub5} (H : Sized P) (w : K5In) (Pl : Planned P) {c : Chal}
    (Dr : Drawn P c) : (sSF P w c).Tame ρ (List.replicate P.x.attained 4) 2 := by
  have T := sSF_tame ρ H w Pl Dr
  rwa [sSF_vars_x H Pl] at T

/-- **At the challenges that the verifier has heard in this sumcheck, its terms are the weighted
products of pairs at the verifier's own array of weights**, which has a weight for each pair. -/
theorem sSF_good {P : Pub5} (H : Sized P) (w : K5In) (Pl : Planned P) (c : Chal) {hd : Heard}
    (hr : hd.atIndex.r.length = P.x.attained + 1)
    (ho : hd.om = (heardAt P c fun _ => none).om)
    (hp' : hd.point = (heardAt P c fun _ => none).point) :
    (sSF P w c).terms (hd.atIndex.r.take (sSF P w c).vars) =
        pairsOf P.x.pairs (wAtIndex P.g hd) ∧ (wAtIndex P.g hd).size = P.x.pairs := by
  refine ⟨?_, ?_⟩
  · rw [sSF_vars_x H Pl, sSF_terms, Pl.pairs]
    refine congrArg _ (wAtIndex_congr _ ho.symm hp'.symm ?_)
    show chal (sumAt _) = _
    rw [chal_sumAt, take_chal _ _ hr]
  · unfold wAtIndex
    rw [Array.size_map, ho]
    exact size_powers _ _

/-- **The batch of the row maxima that were sent, under the powers that the verifier has heard, is
the summand's sum over the cube.** c: the challenges at which the sum is taken; c0: those at which
the maxima were sent; both read as one p. CONDITIONAL: see the head. -/
theorem atIndex_total {P : Pub5} (H : Sized P) (w : K5In) (Pl : Planned P) {c c0 : Chal}
    (Dr : Drawn P c) (Dr0 : Drawn P c0) {pts : Pts} (hp : ptsOf P c0 = some pts) {p : Pub K}
    (I : IndexPts ρ P c p) (I0 : MaxPts ρ P c0 p) (A : AtIdn P.D (tOf ρ w)) {hd : Heard}
    (ho : hd.om = (heardAt P c fun _ => none).om) :
    ∑ b ∈ range P.x.pairs, ρ.val (hd.om.getD b zeroE) * ρ.val ((m6 P w c0).getD b zeroE) =
      ρ.val (sSF P w c).total := by
  rw [sf_start ρ H w Pl Dr Dr0 hp I I0 A, Pl.pairs, ho]
  exact sum_congr rfl fun b hb => congrArg (· * _) (I.o b (mem_range.mp hb))

/-- **The form from which the verifier starts "the score at the index" is worth the summand's sum
over the cube**, where the maxima that were sent lie under their slots. CONDITIONAL: see the head.
-/
theorem start_atIndex_total {W : World K} {P : Pub5} (H : Sized P) (w : K5In) (Pl : Planned P)
    {c c0 : Chal} (Dr : Drawn P c) (Dr0 : Drawn P c0) {pts : Pts} (hp : ptsOf P c0 = some pts)
    {p : Pub K} (I : IndexPts ρ P c p) (I0 : MaxPts ρ P c0 p) (A : AtIdn P.D (tOf ρ w))
    {hd : Heard} (ho : hd.om = (heardAt P c fun _ => none).om)
    (hm : ∀ b < P.x.pairs, W.slot (hd.maxima + b) = ρ.val ((m6 P w c0).getD b zeroE)) :
    (batched P.x.pairs hd.om hd.maxima 1 0).value ρ W = ρ.val (sSF P w c).total := by
  rw [VerifiableInference.Desc.First.Att.P.batched_value,
    ← atIndex_total ρ H w Pl Dr Dr0 hp I I0 A ho]
  refine sum_congr rfl fun b hb => ?_
  rw [show hd.maxima + (1 * b + 0) = hd.maxima + b by omega, hm b (mem_range.mp hb)]

/-! ## The index's cells are bits -/

theorem sHB_vars_x {P : Pub5} (H : Sized P) (Pl : Planned P) (w : K5In) (c : Chal) :
    (sHB P w c).vars = P.x.bits := by
  have e := Pl.vHB
  rw [cut_iHB] at e
  rw [e]
  show P.g.lt + P.g.lgk + 4 = P.D.lT + P.D.lg + 4
  rw [H.lt]
  rfl

/-- It has two end values for each pair that the planner counts. -/
theorem sHB_ends_x (P : Pub5) (w : K5In) (c : Chal) (Pl : Planned P) :
    (sHB P w c).ends = 2 * P.x.pairs := by
  rw [Pl.pairs]
  rfl

/-- It has what the masked sumcheck's prover asks of it, at the planner's number of variables. -/
theorem sHB_tame_x {P : Pub5} (H : Sized P) (w : K5In) (Pl : Planned P) {c : Chal}
    (Dr : Drawn P c) (hK : P.D.lT ≤ 2 ^ 4) :
    (sHB P w c).Tame ρ (List.replicate P.x.bits 4) 2 := by
  have T := sHB_tame ρ H w Pl Dr hK
  rwa [sHB_vars_x H Pl] at T

/-- **At the challenges that the verifier has heard in this sumcheck, its terms are the weighted
products of pairs at the verifier's own array of weights**, which has a weight for each pair. -/
theorem sHB_good {P : Pub5} (H : Sized P) (w : K5In) (Pl : Planned P) (c : Chal) {hd : Heard}
    (hr : hd.cells.r.length = P.x.bits + 1) (ho'' : hd.om'' = (heardAt P c fun _ => none).om'')
    (hp' : hd.point = (heardAt P c fun _ => none).point) :
    (sHB P w c).terms (hd.cells.r.take (sHB P w c).vars) =
        pairsOf P.x.pairs (wCells P.g hd) ∧ (wCells P.g hd).size = P.x.pairs := by
  refine ⟨?_, ?_⟩
  · rw [sHB_vars_x H Pl, sHB_terms, Pl.pairs]
    refine congrArg _ (wCells_congr _ ho''.symm hp'.symm ?_)
    show chal (sumAt _) = _
    rw [chal_sumAt, take_chal _ _ hr]
  · unfold wCells
    rw [Array.size_map, ho'']
    exact size_powers _ _

/-- **The form from which the verifier starts "the index's cells are bits", the constant 0, is worth
the summand's sum over the cube.** CONDITIONAL: see the head. -/
theorem start_cells_total {W : World K} {P : Pub5} (H : Sized P) (w : K5In) (Pl : Planned P)
    {c : Chal} (Dr : Drawn P c) (hK : P.D.lT ≤ 2 ^ 4) (A : AtIdn P.D (tOf ρ w)) :
    (Aff.ofConst zeroE).value ρ W = ρ.val (sHB P w c).total := by
  rw [hb_zero ρ H w Pl Dr hK A, Aff.value_ofConst, ρ.zero]

end H2K5.Honest

#print axioms H2K5.Honest.take_chal
#print axioms H2K5.Honest.wDivision_congr
#print axioms H2K5.Honest.wOn_congr
#print axioms H2K5.Honest.wAtIndex_congr
#print axioms H2K5.Honest.wCells_congr
#print axioms H2K5.Honest.sSE_vars_x
#print axioms H2K5.Honest.sSE_ends_x
#print axioms H2K5.Honest.sSE_tame_x
#print axioms H2K5.Honest.sSE_good
#print axioms H2K5.Honest.sVD_vars_x
#print axioms H2K5.Honest.sVD_ends_x
#print axioms H2K5.Honest.sVD_tame_x
#print axioms H2K5.Honest.sVD_good
#print axioms H2K5.Honest.sSF_vars_x
#print axioms H2K5.Honest.sSF_ends_x
#print axioms H2K5.Honest.sSF_tame_x
#print axioms H2K5.Honest.sSF_good
#print axioms H2K5.Honest.atIndex_total
#print axioms H2K5.Honest.start_atIndex_total
#print axioms H2K5.Honest.sHB_vars_x
#print axioms H2K5.Honest.sHB_ends_x
#print axioms H2K5.Honest.sHB_tame_x
#print axioms H2K5.Honest.sHB_good
#print axioms H2K5.Honest.start_cells_total
