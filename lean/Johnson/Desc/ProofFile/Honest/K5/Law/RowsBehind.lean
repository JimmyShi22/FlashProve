-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/RowsBehind.lean: CONDITIONAL: at the member of a `Thread` at
which the half of an attention segment's own rounds is seated, in the world of the forms behind the
kind's hearing: EVERY ROW THAT THE VERIFIER MAKES OF THE KIND's MASKED SUMCHECKS IS WORTH 0. One
definition of a proposition, and statements with their proofs.

What is joined: the statement on all rows (`rows_zero_k5`, Honest/K5/Law/RowsK5.lean); the clauses
on values part by part (Honest/K5/Law/AtBehind.lean; here the value product below the diagonal and
the softmax-table units, out of Johnson/Desc/K5/Honest/Law/PartsUnits.lean); what the hearing laid
and heard (`laid_at`, Honest/K5/Law/Starts.lean; `along_at`, Honest/K5/Law/Ends.lean); "the round
that draws many elements has been heard whole" (`drawn_front`, Honest/K5/Law/DrawnFront.lean).

THE MAIN STATEMENT IS CONDITIONAL ON TWO BUNDLES OF PREMISES, NEITHER OF WHICH IS SHOWN TO BE
MEETABLE: the three ties between the witness and the honest side (`K5Script`,
Honest/K5/Law/Script.lean), and
`FrontsOk`, which gathers what is still owed: public numbers; the key points; what the summands'
points are at their parts' fronts; that each softmax-table unit's summand is tame; the ties between
the challenges read there and those that the hearing holds; and one clause on the witness's cells.
Main names:
  `FrontsOk`           what is still owed at the member, beside the three ties
  `partVals_below_at`, `partVals_unit_at`
  `valuesAt_behind`    all clauses on values
  `rows_zero_behind`   **every row is worth 0**

Limits. Nothing on the other claims of the kind. Nothing is claimed on soundness, completeness or
hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.AtBehind
import Johnson.Desc.ProofFile.Honest.K5.Law.DrawnFront
import Johnson.Desc.K5.Honest.Law.PartsUnits

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (zeroE)
open OnBytes.Model (Reading Aff Fork)
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Block Claim OpenedColumn First.S noDigest)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ worldOwn)
open VerifiableInference.Desc.Part (MaskedSum.Heard)
open VerifiableInference.Desc.Part.MaskedSum (Var Ends)
open VerifiableInference.Desc.First.Att.P (Par Heard Left UnitG ScoreP hear leftP chal scoreW
  weights inner wBelow)
open H2K5.Honest (K5In shapes Laid iSE iVM iVD iM6 iSF iSD iHB iZero Planned Drawn DivIn divIn
  DivPts PairsAre heardAt rhoOf om4Of ptsOf IndexPts MaxPts AtIdn tOf sK)

/-- **What is still owed at the member, beside the three ties**, for the statement on the rows. Z:
the seat. w: the segment's cells. heard, ds: the challenges in front of the member, and its own. zk:
the key points at which the verifier lays its weights. hd: what the kind's hearing holds. It is a
definition: a premise's form. NOTHING HERE SHOWS THAT IT CAN BE MET. Its fields, by what they hang
on: public numbers (sized, planned, token, someUnit, somePair, and in `unit` the number of pieces);
the tie on the key points (key); the return of the verifier's function for the points at a part's
front, and what these points read as (div, unit, index); that a unit's summand is tame (in `unit`);
the tie between what the hearing holds and what the honest side has heard (omF, ptF, omH, ptH, rho,
om4); the witness's cells (idn). -/
structure FrontsOk (Z : Seat5) (w : K5In) (heard ds : List Fmt.Drawn)
    (zk : Array (Array OnBytes.E)) (hd : Heard) : Prop where
  /-- public: the shape's and the plan's numbers -/
  sized : H2K5.Honest.Sized Z.P
  planned : Planned Z.P
  token : Z.P.D.lT ≤ 2 ^ 4
  someUnit : Z.P.x.score.isEmpty = false
  somePair : Z.P.x.pairs ≠ 0
  /-- the key points in front of every round of the member are the verifier's -/
  key : ∀ n, (chalOf Z (heard ++ ds.take n)).zk = zk
  /-- in front of the division's three sumchecks its points are there, read as the library's, and
  have a piece for each pair -/
  div : ∀ q, q = iSE Z.P.x ∨ q = iVM Z.P.x ∨ q = iVD Z.P.x →
    ∃ (Dv : DivIn) (C : Inst.Model.AttSeg.Calls) (pb : Inst.Model.AttSeg.Pub GE),
      divIn Z.P (frontQ Z heard ds q) = some Dv ∧ DivPts Reading.gl Z.P C pb Dv ∧
        PairsAre Z.P.g Dv.d.pwW
  /-- in front of a softmax-table unit its points are there; the place's unit has the plan's number
  of pieces; the unit's summand is tame -/
  unit : ∀ (i : Nat) (u : Nat × Nat) (ug : UnitG), Z.P.x.score[i]? = some u →
    Z.P.g.scores[i]? = some ug →
    ∃ kk : ScoreP, (ptsOf Z.P (frontQ Z heard ds i)).bind (·.scores[i]?) = some kk ∧
      ug.pcs.length = u.2 ∧
      (sK Z.P w (frontQ Z heard ds i) i).Tame Reading.gl (List.replicate u.1 4) 2
  /-- what the hearing holds is what the summands read at their fronts -/
  omF : hd.om = (heardAt Z.P (frontQ Z heard ds (iSF Z.P.x)) fun _ => none).om
  ptF : hd.point = (heardAt Z.P (frontQ Z heard ds (iSF Z.P.x)) fun _ => none).point
  omH : hd.om'' = (heardAt Z.P (frontQ Z heard ds (iHB Z.P.x)) fun _ => none).om''
  ptH : hd.point = (heardAt Z.P (frontQ Z heard ds (iHB Z.P.x)) fun _ => none).point
  rho : rhoOf Z.P (frontQ Z heard ds (iSD Z.P.x)) = chal hd.atIndex
  om4 : om4Of Z.P (frontQ Z heard ds (iSD Z.P.x)) = hd.om'
  /-- the powers and the point read as the library's letters, at the two fronts -/
  index : ∃ pb : Inst.Model.AttSeg.Pub GE,
    IndexPts Reading.gl Z.P (frontQ Z heard ds (iSF Z.P.x)) pb ∧
      MaxPts Reading.gl Z.P (frontQ Z heard ds (iM6 Z.P.x)) pb
  /-- THE WITNESS's CELLS MEET THE LIBRARY's THREE FAMILIES OF IDENTITIES -/
  idn : AtIdn Z.P.D (tOf Reading.gl w)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {Z : Seat5} {p : Par} {blk : Block First.S Claim}
  {A : OnBytes.Attention.Plan} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}

section
variable (Hs : K5Seated T b cells Z p blk) (Sc : K5Script T b cells Z A blk own rdOf)
  {k : Coins Bk} {s : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
  {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn} (hT : Thr T b k s m E)
  (hd : drawsFit blk.rounds ds = true) (hM : T.Moved blk k m E ds y cols)
  {att : VerifiableInference.Desc.First.AttOwn} (e : s.here = .att att) {dc : List Fmt.Drawn}
  {D : Bound GQ} (hD : MaskIs T own rdOf k s att m dc D)
  {G : Fork} {hd5 : Heard} (L : Laid Z.P.x att.F.next (roundsOf y.1) hd5 G)
  (Al : Along Z.P.x (roundsOf y.1) G hd5) (H : H2K5.Honest.Sized Z.P) (Pl : Planned Z.P)
include Hs Sc hT hd hM e hD L Al H Pl

/-- **The clauses on values at "the value product below the diagonal", at the member.** CONDITIONAL
as `partVals_on_at` (Honest/K5/Law/AtBehind.lean). -/
theorem partVals_below_at {Dv : DivIn}
    (h : divIn Z.P (frontQ Z m.st.heard ds (iVM Z.P.x)) = some Dv)
    {C : Inst.Model.AttSeg.Calls} {pb : Inst.Model.AttSeg.Pub GE}
    (R : DivPts Reading.gl Z.P C pb Dv) (pr : PairsAre Z.P.g Dv.d.pwW)
    {zk : Array (Array OnBytes.E)} (hzk : (frontQ Z m.st.heard ds (iVM Z.P.x)).zk = zk)
    {wl : UnitG} (hwl : Z.P.g.single .wl = some wl)
    (hsz : (weights wl (zk.getD wl.call #[])).size = Z.P.g.NP) :
    PartVals (Local W₀ Rc Xi Tr) X Bk (Bk.rowsOf T.chain) (k.look T.chain) Z
      (fun t : Local W₀ Rc Xi Tr => inOf Z.P.S Z.link (cells t.trace))
      (inOf Z.P.S Z.link (cells m.st.input.trace)) m.st.heard ds
      (worldOwn (behindPart s att G) [] D) (iVM Z.P.x) (.slot hd5.values)
      (List.replicate Z.P.x.valueM 4) (prodEnds Z.P.x.pairs) hd5.below
      (GoodProducts (prodEnds Z.P.x.pairs) hd5.below
        (wBelow Z.P.g (weights wl (zk.getD wl.call #[])) (inner wl (zk.getD wl.call #[]))
          hd5)) := by
  subst hzk
  have hr : hd5.below.r.length = Z.P.x.valueM + 1 := by
    have := Al.below.r_length
    rwa [prodVs, List.length_replicate] at this
  have Gd := H2K5.Honest.sVM_good Z.P (inOf Z.P.S Z.link (cells m.st.input.trace)) Pl h hr hwl hsz
  refine partVals_products _ _ _ _ _ Z _ _ _ _ _ _ _ _ _ _ _ _ (H2K5.Honest.shape_iVM Z.P.x) ?_ ?_
    (coinsUnder_at Hs Sc hT hd hM e hD fun _ hq => L.below _ hq) ?_ ?_
  · rw [summandAt_iVM]
    exact H2K5.Honest.sVM_tame_x Reading.gl H _ Pl h R pr
  · rw [summandAt_iVM]
    exact H2K5.Honest.sVM_ends_x Z.P _ _ Pl
  · rw [summandAt_iVM]
    exact start_below Hs Sc hT hd hM e hD L
  · rw [summandAt_iVM]
    exact ⟨Z.P.x.pairs, _, rfl, Gd.1, Gd.2, fun _ _ => rfl⟩

omit H Pl in
/-- **The clauses on values at a softmax-table unit's sumcheck, at the member.** CONDITIONAL as
`coinsUnder_at`, and on: L, Al; the unit's numbers u, what the hearing holds of it o, the place's
unit ug; in front of the part the unit's points are there; the place's unit has the plan's number of
pieces; the unit's summand is tame; zk: the key points at the part's front; the verifier's weights
Wt are what its function returns there. -/
theorem partVals_unit_at {i : Nat} {u : Nat × Nat} {o : Nat × MaskedSum.Heard} {ug : UnitG}
    {kk : ScoreP} {Wt : Array OnBytes.E} (hu : Z.P.x.score[i]? = some u)
    (ho : hd5.scores[i]? = some o) (hug : Z.P.g.scores[i]? = some ug)
    (hk : (ptsOf Z.P (frontQ Z m.st.heard ds i)).bind (·.scores[i]?) = some kk)
    (hn : ug.pcs.length = u.2)
    (hTm : (sK Z.P (inOf Z.P.S Z.link (cells m.st.input.trace)) (frontQ Z m.st.heard ds i) i).Tame
      Reading.gl (List.replicate u.1 4) 2)
    {zk : Array (Array OnBytes.E)} (hzk : (frontQ Z m.st.heard ds i).zk = zk)
    (hW : scoreW Z.P.g ug (zk.getD ug.call #[]) (chal o.2) = some Wt) :
    PartVals (Local W₀ Rc Xi Tr) X Bk (Bk.rowsOf T.chain) (k.look T.chain) Z
      (fun t : Local W₀ Rc Xi Tr => inOf Z.P.S Z.link (cells t.trace))
      (inOf Z.P.S Z.link (cells m.st.input.trace)) m.st.heard ds
      (worldOwn (behindPart s att G) [] D) i (.slot (o.1 + 6))
      (List.replicate u.1 4) (prodEnds u.2) o.2
      (GoodProducts (prodEnds u.2) o.2 Wt) := by
  subst hzk
  have hi : i < Z.P.x.score.length := (List.getElem?_eq_some_iff.1 hu).1
  have hr : o.2.r.length = u.1 + 1 := by
    have := (Al.score i u o hu ho).r_length
    rwa [prodVs, List.length_replicate] at this
  have Gd := H2K5.Honest.sK_good Z.P (inOf Z.P.S Z.link (cells m.st.input.trace)) hu hug hk hn hr hW
  refine partVals_products _ _ _ _ _ Z _ _ _ _ _ _ _ _ _ _ _ _ (H2K5.Honest.shape_unit Z.P.x i u hu)
    ?_ ?_ (coinsUnder_at Hs Sc hT hd hM e hD fun _ hq => (L.unit i o _ ho hq).1) ?_ ?_
  · rw [summandAt_unit _ _ _ _ hi]
    exact hTm
  · rw [summandAt_unit _ _ _ _ hi]
    exact H2K5.Honest.sK_ends_x Z.P _ _ hug hn
  · rw [summandAt_unit _ _ _ _ hi]
    exact start_unit_at Hs Sc hT hd e hM hD L hu ho
  · rw [summandAt_unit _ _ _ _ hi]
    exact ⟨u.2, _, rfl, Gd.1, Gd.2, fun _ _ => rfl⟩

end

section
variable (Hs : K5Seated T b cells Z p blk) (Sc : K5Script T b cells Z A blk own rdOf)
  {k : Coins Bk} {s : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
  {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn} (hT : Thr T b k s m E)
  (hd : drawsFit blk.rounds ds = true) (hM : T.Moved blk k m E ds y cols)
  {att : VerifiableInference.Desc.First.AttOwn} (e : s.here = .att att) {dc : List Fmt.Drawn}
  {D : Bound GQ} (hD : MaskIs T own rdOf k s att m dc D)
  {G : Fork} {hd5 : Heard} {rest : List Fmt.RoundView} {lead : Nat}
  (hz : OnBytes.Model.Road.Sized att.F)
  (hh : hear p.own (att.F, (roundsOf y.1).map noDigest, 0) = some (hd5, G, rest, lead))
  {zk : Array (Array OnBytes.E)}
  (Fr : FrontsOk Z (inOf Z.P.S Z.link (cells m.st.input.trace)) m.st.heard ds zk hd5)
include Hs Sc hT hd hM e hD hz hh Fr

/-- **All clauses on values, at the member, in the world of the forms behind the hearing.**
CONDITIONAL on: the three ties (`K5Script`), WHICH ARE NOT SHOWN; the half's seat; the thread in
front; the challenges fit; the prover's side of the step; the world's mask row is the witness's; the
state's ledger is sized and the kind's hearing returns from it on the rounds played; `FrontsOk`. -/
theorem valuesAt_behind :
    ValuesAt (Local W₀ Rc Xi Tr) X Bk (Bk.rowsOf T.chain) (k.look T.chain) Z
      (fun t : Local W₀ Rc Xi Tr => inOf Z.P.S Z.link (cells t.trace))
      (inOf Z.P.S Z.link (cells m.st.input.trace)) m.st.heard ds
      (worldOwn (behindPart s att G) [] D) Z.P.g zk hd5 := by
  have L := laid_at Hs hd hM hz hh
  have Al := along_at Hs hd hM ⟨hz.vp, hz.mf, hz.got⟩ hh
  have H := Fr.sized
  have Pl := Fr.planned
  have Dq : ∀ q, iZero Z.P.x < q → Drawn Z.P (frontQ Z m.st.heard ds q) := fun q hq =>
    drawn_front Hs hT.2.1 hM hh H Pl hq
  have hn : Z.P.x.pairs = Z.P.x.pairs - 1 + 1 := by
    have := Fr.somePair
    omega
  obtain ⟨pb, I, I0⟩ := Fr.index
  refine ⟨fun i u o ug Wt hu ho hug hW => ?_, fun wl hwl hs => ?_, fun wl hwl hs => ?_,
    fun wl hwl hs => ?_, ?_, ?_, ?_⟩
  · obtain ⟨kk, hk, hnn, hTm⟩ := Fr.unit i u ug hu hug
    exact partVals_unit_at Hs Sc hT hd hM e hD L Al hu ho hug hk hnn hTm (Fr.key _) hW
  · obtain ⟨Dv, C, pb', h, R, pr⟩ := Fr.div _ (Or.inl rfl)
    exact partVals_division_at Hs Sc hT hd hM e hD L Al H Pl Fr.someUnit h R pr (Fr.key _) hwl hs
  · obtain ⟨Dv, C, pb', h, R, pr⟩ := Fr.div _ (Or.inr (Or.inl rfl))
    exact partVals_below_at Hs Sc hT hd hM e hD L Al H Pl h R pr (Fr.key _) hwl hs
  · obtain ⟨Dv, C, pb', h, R, pr⟩ := Fr.div _ (Or.inr (Or.inr rfl))
    exact partVals_on_at Hs Sc hT hd hM e hD L Al H Pl h R pr (Fr.key _) hwl hs
  · exact partVals_atIndex_at Hs Sc hT hd hM e hD L Al H Pl hn
      (Dq _ (by unfold iZero iSF; omega)) (Dq _ (by unfold iZero iM6; omega)) Fr.omF Fr.ptF I I0
      Fr.idn
  · exact partVals_key_at Hs Sc hT hd hM e hD L Al H Pl Fr.rho Fr.om4
  · exact partVals_cells_at Hs Sc hT hd hM e hD L Al H Pl (Dq _ (by unfold iZero iHB; omega))
      Fr.token Fr.omH Fr.ptH Fr.idn

/-- **AT THE MEMBER, IN THE WORLD OF THE FORMS BEHIND THE HEARING, EVERY ROW THAT THE VERIFIER MAKES
OF THE KIND's MASKED SUMCHECKS IS WORTH 0.** CONDITIONAL as `valuesAt_behind`, and on: the
verifier's text for the rows has returned them, at the seat's shape and the key points zk. -/
theorem rows_zero_behind {Lf : Left} (hL : leftP Z.P.g zk hd5 G = some Lf) :
    RowsZero (worldOwn (behindPart s att G) [] D) Lf := by
  have Vs := valuesAt_behind Hs Sc hT hd hM e hD hz hh Fr
  obtain ⟨⟨l, hl, hy⟩, -⟩ := hM
  rw [Hs.own] at hh
  exact rows_zero_k5 T Hs hd hl hy hz hh hL Vs

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.partVals_below_at
#print axioms ProofFile.Honest.K5.partVals_unit_at
#print axioms ProofFile.Honest.K5.valuesAt_behind
#print axioms ProofFile.Honest.K5.rows_zero_behind
