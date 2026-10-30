-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/AtBehind.lean: CONDITIONAL: at the member of a `Thread` at
which the half of an attention segment's own rounds is seated, in the world of the forms behind the
kind's hearing: the clauses on values (`PartVals`, Honest/K5/Law/RowsK5.lean), sumcheck by sumcheck,
with the coins under the sumcheck's own slots and the start form's worth laid in. Statements with
their proofs.

What is joined: Honest/K5/Law/FillProducts.lean (the summands' form); Honest/K5/Law/Slots.lean,
Starts.lean and Ends.lean (what lies under a slot in that world); Honest/K5/Law/Along.lean (each
sumcheck's own hearing); Johnson/Desc/K5/Honest/Law/Parts.lean (two of the starts).

EVERY STATEMENT IS CONDITIONAL, FIRST OF ALL ON THE THREE TIES BETWEEN THE WITNESS AND THE HONEST
SIDE (`K5Script`, Honest/K5/Law/Script.lean), WHICH ARE NOT SHOWN. The further premises stand in
each statement's own comment. One of them speaks of the witness's cells: they meet the library's
three families of identities (`AtIdn`, Johnson/Desc/K5/Honest/Law/Idn.lean); nothing in this folder
draws the third of these from what stands in front of the member.
Main names:
  `coinsUnder_at`   the coins under the own slots of the sumcheck that is part q
  `heard_vars`      the challenges that the hearing holds of a sumcheck are the run's own
  `partVals_division_at`, `partVals_on_at`, `partVals_cells_at`, `partVals_atIndex_at`,
  `partVals_key_at`

Limits. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.FillProducts
import Johnson.Desc.ProofFile.Honest.K5.Law.Ends
import Johnson.Desc.ProofFile.Honest.K5.Law.StartUnit

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff Fork)
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Block Claim OpenedColumn First.S)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ worldOwn)
open VerifiableInference.Desc.Part (MaskedSum.Heard)
open VerifiableInference.Desc.Part.MaskedSum (Var Ends)
open VerifiableInference.Desc.First.Att.P (Par Heard UnitG chal batched weights inner wDivision wOn
  wAtIndex wCells)
open H2K5.Honest (shapes slotsTo SumPut Laid iSE iVD iM6 iSF iSD iHB keyVars Planned Drawn DivIn
  divIn DivPts PairsAre heardAt rhoOf om4Of ptsOf IndexPts MaxPts AtIdn tOf)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {Z : Seat5} {p : Par} {blk : Block First.S Claim}
  {A : OnBytes.Attention.Plan} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}

/-- **The challenges that the hearing holds of the sumcheck that is part q are the run's own**, as
the law of the honest part names them. CONDITIONAL on: the half's seat; the challenges fit; the
prover's side of the step; part q is a sumcheck at this call; it was heard as `SumHeardAt` says. -/
theorem heard_vars {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {b : Nat} {cells : Tr → Cells} {Z : Seat5} {p : Par} {blk : Block First.S Claim}
    (Hs : K5Seated T b cells Z p blk) {k : Coins Bk} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hd : drawsFit blk.rounds ds = true) (hM : T.Moved blk k m E ds y cols) {G : Fork} {q : Nat}
    {C : Aff} {ld : Nat} {vs : List Var} {en : Ends} {hhq : MaskedSum.Heard}
    (hq : (shapes Z.P.x)[q]? = some (.sum ⟨ld, vs, some en⟩))
    (Hq : SumHeardAt Z.P.x (roundsOf y.1) G q C vs en hhq) :
    hhq.r = ProofFile.Honest.SumLaw.varsOf ⟨ld, vs, some en⟩
      ((ds.drop (H2K5.Honest.firstOf Z.P.x q)).take (vs.length + 3)) := by
  obtain ⟨⟨l, hl, hy⟩, -⟩ := hM
  obtain ⟨cq, -, ha⟩ := k5_cut T Hs hd hl hy q (.sum ⟨ld, vs, some en⟩) hq
  obtain ⟨ld', F', G', hq', hh', -, -⟩ := Hq
  obtain rfl : ld = ld' := by
    have h0 := Option.some.inj (hq.symm.trans hq')
    injection h0 with h1
    injection h1 with h2
  have ec := callAt_jobOf ⟨ld, vs, some en⟩
    (fun (w : H2K5.Honest.K5In) (fr : Front Unit) => (jobs Z.P).alone q w (chalOf Z fr.heard))
    (fun w fr => (jobs Z.P).sum q w (chalOf Z fr.heard))
  have h3 := (ProofFile.Honest.SumLaw.sumClaim Unit H2K5.Honest.K5In Unit (nameOf Z.place q "sum")
    (nameOf Z.place q "ends") (jobQ Z ⟨ld, vs, some en⟩ q) cq _ _ _ _ C F' G' hhq
    (by rw [ec]; exact k5_drawsOk T Hs hd q _ hq) ha (by rw [ec]; exact hh')).2.1
  rw [ec] at h3
  exact h3

section
variable (Hs : K5Seated T b cells Z p blk) (Sc : K5Script T b cells Z A blk own rdOf)
  {k : Coins Bk} {s : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
  {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn} (hT : Thr T b k s m E)
  (hd : drawsFit blk.rounds ds = true) (hM : T.Moved blk k m E ds y cols)
  {att : VerifiableInference.Desc.First.AttOwn} (e : s.here = .att att) {dc : List Fmt.Drawn}
  {D : Bound GQ} (hD : MaskIs T own rdOf k s att m dc D)
include Hs Sc hT hd hM e hD

/-- **At the member, the world of the forms behind the hearing has the hiding polynomial's coins
under the own slots of the sumcheck that is part q.** CONDITIONAL on: the three ties between the
witness and the honest side, WHICH ARE NOT SHOWN; the half's seat; the thread in front; the
challenges fit; the prover's side of the step; the world's mask row is the witness's; what lies in
the ledger behind the hearing for part q (SP). -/
theorem coinsUnder_at {G : Fork} {q : Nat} {dn : List Nat} {en : Ends} {hhq : MaskedSum.Heard}
    (SP : ∀ ld, (shapes Z.P.x)[q]? = some (.sum ⟨ld, dn.map Var.plain, some en⟩) →
      SumPut ⟨ld, dn.map Var.plain, some en⟩ (att.F.next + slotsTo Z.P.x q)
        ((roundsOf y.1).drop (H2K5.Honest.firstOf Z.P.x q)) hhq G) :
    CoinsUnder (Local W₀ Rc Xi Tr) X Bk (Bk.rowsOf T.chain) (k.look T.chain) Z
      (fun t : Local W₀ Rc Xi Tr => inOf Z.P.S Z.link (cells t.trace))
      (worldOwn (behindPart s att G) [] D) q dn en hhq := fun ld hq _ hl =>
  (sum_slots Hs Sc hT hd hM e hD hq (SP ld hq) hl).2.2.1

variable {G : Fork} {hd5 : Heard} (L : Laid Z.P.x att.F.next (roundsOf y.1) hd5 G)
  (Al : Along Z.P.x (roundsOf y.1) G hd5) (H : H2K5.Honest.Sized Z.P) (Pl : Planned Z.P)
include L Al H Pl

/-- **The clauses on values at "the denominator times the output", at the member.** The coins, the
start and the challenges' number are paid; CONDITIONAL as `coinsUnder_at`, and on: what the hearing
laid and heard (L, Al); the shape's and the plan's numbers; there is a softmax-table unit; at the
part's front the division's points are there, read as the library's, and have a piece for each pair;
zk: the key points at the part's front, kept as a letter of its own because the statement on all
rows has the verifier's key points there; hwl, hsz: the place has its one unit wl, and that unit's
weights at zk are as many as the pairs: the two tests under which `ValuesAt`
(Honest/K5/Law/RowsK5.lean) asks this clause. -/
theorem partVals_division_at (hsc : Z.P.x.score.isEmpty = false) {Dv : DivIn}
    (h : divIn Z.P (frontQ Z m.st.heard ds (iSE Z.P.x)) = some Dv)
    {C : Inst.Model.AttSeg.Calls} {pb : Inst.Model.AttSeg.Pub GE}
    (R : DivPts Reading.gl Z.P C pb Dv) (pr : PairsAre Z.P.g Dv.d.pwW)
    {zk : Array (Array OnBytes.E)} (hzk : (frontQ Z m.st.heard ds (iSE Z.P.x)).zk = zk)
    {wl : UnitG} (hwl : Z.P.g.single .wl = some wl)
    (hsz : (weights wl (zk.getD wl.call #[])).size = Z.P.g.NP) :
    PartVals (Local W₀ Rc Xi Tr) X Bk (Bk.rowsOf T.chain) (k.look T.chain) Z
      (fun t : Local W₀ Rc Xi Tr => inOf Z.P.S Z.link (cells t.trace))
      (inOf Z.P.S Z.link (cells m.st.input.trace)) m.st.heard ds
      (worldOwn (behindPart s att G) [] D) (iSE Z.P.x) (.slot (hd5.five + 1))
      (List.replicate Z.P.x.e 4) (prodEnds Z.P.x.pairs) hd5.division
      (GoodProducts (prodEnds Z.P.x.pairs) hd5.division
        (wDivision Z.P.g (weights wl (zk.getD wl.call #[])) (inner wl (zk.getD wl.call #[]))
          hd5)) := by
  have hr : hd5.division.r.length = Z.P.x.e + 1 := by
    have := Al.division.r_length
    rwa [prodVs, List.length_replicate] at this
  refine partVals_division _ _ _ _ _ Z _ _ _ _ _ hd5 zk H Pl h R pr hr hwl hsz hzk
    (coinsUnder_at Hs Sc hT hd hM e hD fun _ hq => L.division _ hq) ?_
  rw [summandAt_iSE]
  exact start_division Hs Sc hT hd hM e hD L hsc

/-- **The like at "the value product on the diagonal".** CONDITIONAL likewise. -/
theorem partVals_on_at {Dv : DivIn}
    (h : divIn Z.P (frontQ Z m.st.heard ds (iVD Z.P.x)) = some Dv)
    {C : Inst.Model.AttSeg.Calls} {pb : Inst.Model.AttSeg.Pub GE}
    (R : DivPts Reading.gl Z.P C pb Dv) (pr : PairsAre Z.P.g Dv.d.pwW)
    {zk : Array (Array OnBytes.E)} (hzk : (frontQ Z m.st.heard ds (iVD Z.P.x)).zk = zk)
    {wl : UnitG} (hwl : Z.P.g.single .wl = some wl)
    (hsz : (weights wl (zk.getD wl.call #[])).size = Z.P.g.NP) :
    PartVals (Local W₀ Rc Xi Tr) X Bk (Bk.rowsOf T.chain) (k.look T.chain) Z
      (fun t : Local W₀ Rc Xi Tr => inOf Z.P.S Z.link (cells t.trace))
      (inOf Z.P.S Z.link (cells m.st.input.trace)) m.st.heard ds
      (worldOwn (behindPart s att G) [] D) (iVD Z.P.x) (.slot (hd5.values + 1))
      (List.replicate Z.P.x.valueD 4) (prodEnds Z.P.x.pairs) hd5.on
      (GoodProducts (prodEnds Z.P.x.pairs) hd5.on
        (wOn Z.P.g (weights wl (zk.getD wl.call #[])) (inner wl (zk.getD wl.call #[])) hd5)) := by
  have hr : hd5.on.r.length = Z.P.x.valueD + 1 := by
    have := Al.on.r_length
    rwa [prodVs, List.length_replicate] at this
  refine partVals_on _ _ _ _ _ Z _ _ _ _ _ hd5 zk H Pl h R pr hr hwl hsz hzk
    (coinsUnder_at Hs Sc hT hd hM e hD fun _ hq => L.on _ hq) ?_
  rw [summandAt_iVD]
  exact start_on Hs Sc hT hd hM e hD L

/-- **The like at "the index's cells are bits".** CONDITIONAL as `coinsUnder_at`, and on: L, Al; the
numbers; at the part's front the round that draws many elements has been heard whole; a token has at
most 16 bits; the powers and the point that the hearing holds are those that the summand reads at
the part's front; THE WITNESS's CELLS MEET THE LIBRARY's THREE FAMILIES OF IDENTITIES (Ai). -/
theorem partVals_cells_at (Dr : Drawn Z.P (frontQ Z m.st.heard ds (iHB Z.P.x)))
    (hK : Z.P.D.lT ≤ 2 ^ 4)
    (ho : hd5.om'' = (heardAt Z.P (frontQ Z m.st.heard ds (iHB Z.P.x)) fun _ => none).om'')
    (hpt : hd5.point = (heardAt Z.P (frontQ Z m.st.heard ds (iHB Z.P.x)) fun _ => none).point)
    (Ai : AtIdn Z.P.D (tOf Reading.gl (inOf Z.P.S Z.link (cells m.st.input.trace)))) :
    PartVals (Local W₀ Rc Xi Tr) X Bk (Bk.rowsOf T.chain) (k.look T.chain) Z
      (fun t : Local W₀ Rc Xi Tr => inOf Z.P.S Z.link (cells t.trace))
      (inOf Z.P.S Z.link (cells m.st.input.trace)) m.st.heard ds
      (worldOwn (behindPart s att G) [] D) (iHB Z.P.x) (.ofConst zeroE)
      (List.replicate Z.P.x.bits 4) (prodEnds Z.P.x.pairs) hd5.cells
      (GoodProducts (prodEnds Z.P.x.pairs) hd5.cells (wCells Z.P.g hd5)) := by
  have hr : hd5.cells.r.length = Z.P.x.bits + 1 := by
    have := Al.cells.r_length
    rwa [prodVs, List.length_replicate] at this
  refine partVals_cells _ _ _ _ _ Z _ _ _ _ _ hd5 H Pl Dr hK hr ho hpt
    (coinsUnder_at Hs Sc hT hd hM e hD fun _ hq => L.cells _ hq) ?_
  rw [summandAt_iHB]
  exact H2K5.Honest.start_cells_total Reading.gl H _ Pl Dr hK Ai

/-- **The like at "the score at the index".** CONDITIONAL as `coinsUnder_at`, and on: L, Al; the
numbers; there is a pair; in front of this part and of the maxima's the round that draws many
elements has been heard whole; the powers and the point that the hearing holds are those that the
summand reads at the part's front; these read as the library's letters pb, at both fronts; THE
WITNESS's CELLS MEET THE LIBRARY's THREE FAMILIES OF IDENTITIES (Ai). -/
theorem partVals_atIndex_at {n : Nat} (hn : Z.P.x.pairs = n + 1)
    (Dr : Drawn Z.P (frontQ Z m.st.heard ds (iSF Z.P.x)))
    (Dr0 : Drawn Z.P (frontQ Z m.st.heard ds (iM6 Z.P.x)))
    (ho : hd5.om = (heardAt Z.P (frontQ Z m.st.heard ds (iSF Z.P.x)) fun _ => none).om)
    (hpt : hd5.point = (heardAt Z.P (frontQ Z m.st.heard ds (iSF Z.P.x)) fun _ => none).point)
    {pb : Inst.Model.AttSeg.Pub GE}
    (I : IndexPts Reading.gl Z.P (frontQ Z m.st.heard ds (iSF Z.P.x)) pb)
    (I0 : MaxPts Reading.gl Z.P (frontQ Z m.st.heard ds (iM6 Z.P.x)) pb)
    (Ai : AtIdn Z.P.D (tOf Reading.gl (inOf Z.P.S Z.link (cells m.st.input.trace)))) :
    PartVals (Local W₀ Rc Xi Tr) X Bk (Bk.rowsOf T.chain) (k.look T.chain) Z
      (fun t : Local W₀ Rc Xi Tr => inOf Z.P.S Z.link (cells t.trace))
      (inOf Z.P.S Z.link (cells m.st.input.trace)) m.st.heard ds
      (worldOwn (behindPart s att G) [] D) (iSF Z.P.x) (batched Z.P.x.pairs hd5.om hd5.maxima 1 0)
      (List.replicate Z.P.x.attained 4) (prodEnds Z.P.x.pairs) hd5.atIndex
      (GoodProducts (prodEnds Z.P.x.pairs) hd5.atIndex (wAtIndex Z.P.g hd5)) := by
  have hr : hd5.atIndex.r.length = Z.P.x.attained + 1 := by
    have := Al.atIndex.r_length
    rwa [prodVs, List.length_replicate] at this
  obtain ⟨pts, hp0⟩ := pts_front Hs Sc hT hd e (H2K5.Honest.firstOf Z.P.x (iM6 Z.P.x))
  refine partVals_atIndex _ _ _ _ _ Z _ _ _ _ _ hd5 H Pl Dr hr ho hpt
    (coinsUnder_at Hs Sc hT hd hM e hD fun _ hq => L.atIndex _ hq) ?_
  rw [summandAt_iSF]
  refine H2K5.Honest.start_atIndex_total Reading.gl H _ Pl Dr Dr0 hp0 I I0 Ai ho fun i hi => ?_
  have hi' : i < n + 1 := by
    rw [← hn]
    exact hi
  rw [maxima_slots Hs Sc hT hd hM e hD L hn i hi', ProofFile.Honest.SumLaw.padTo_getD, if_pos hi']

/-- **The like at "the key at the index".** CONDITIONAL as `coinsUnder_at`, and on: L, Al; the
numbers; the two arrays that the summand reads at the part's front, the challenges of the score at
the index and the batching element's powers, are those that the hearing holds. -/
theorem partVals_key_at
    (hrho : rhoOf Z.P (frontQ Z m.st.heard ds (iSD Z.P.x)) = chal hd5.atIndex)
    (hom : om4Of Z.P (frontQ Z m.st.heard ds (iSD Z.P.x)) = hd5.om') :
    PartVals (Local W₀ Rc Xi Tr) X Bk (Bk.rowsOf T.chain) (k.look T.chain) Z
      (fun t : Local W₀ Rc Xi Tr => inOf Z.P.S Z.link (cells t.trace))
      (inOf Z.P.S Z.link (cells m.st.input.trace)) m.st.heard ds
      (worldOwn (behindPart s att G) [] D) (iSD Z.P.x)
      (batched Z.P.x.pairs hd5.om' hd5.atIndex.sEnd 2 1)
      (keyDs Z.P.x) (keyEnds Z.P.x) hd5.key
      (GoodKey Z.P.g (keyVars Z.P.x) (keyEnds Z.P.x) (chal hd5.atIndex) hd5.om') := by
  have hr : hd5.atIndex.r.length = Z.P.x.attained + 1 := by
    have := Al.atIndex.r_length
    rwa [prodVs, List.length_replicate] at this
  obtain ⟨pts, hpS⟩ := pts_front Hs Sc hT hd e (H2K5.Honest.firstOf Z.P.x (iSD Z.P.x))
  refine partVals_key _ _ _ _ _ Z _ _ _ _ _ hd5 Pl hrho hom
    (coinsUnder_at Hs Sc hT hd hM e hD fun _ hq => L.key _ hq) ?_
  have hv : hd5.atIndex.r = ProofFile.Honest.SumLaw.varsOf
      ⟨0, prodVs Z.P.x.attained, some (prodEnds Z.P.x.pairs)⟩
      ((ds.drop (H2K5.Honest.firstOf Z.P.x (iSF Z.P.x))).take
        ((prodVs Z.P.x.attained).length + 3)) :=
    heard_vars Hs hd hM (H2K5.Honest.shape_iSF Z.P.x) Al.atIndex
  have hF := summandAt_iSF Z (inOf Z.P.S Z.link (cells m.st.input.trace)) m.st.heard ds
  unfold summandAt at hF
  have hst : H2K5.Honest.sSF Z.P (inOf Z.P.S Z.link (cells m.st.input.trace))
      (frontQ Z m.st.heard ds (iSF Z.P.x)) =
      H2K5.Honest.sSF Z.P (inOf Z.P.S Z.link (cells m.st.input.trace))
        (frontQ Z m.st.heard ds (iSD Z.P.x)) :=
    H2K5.Honest.stable_sSF Z.P _
      (fronts_agree Hs hT.2.1 ds (H2K5.Honest.HeardIs.firstOf_mono Z.P.x
        (show iSF Z.P.x ≤ iSD Z.P.x by unfold iSF iSD; omega)))
      (show iM6 Z.P.x < iSF Z.P.x by unfold iM6 iSF; omega)
  have hpt : hd5.atIndex.r.take (prodVs Z.P.x.attained).length =
      (rhoOf Z.P (frontQ Z m.st.heard ds (iSD Z.P.x))).toList := by
    rw [hrho, prodVs, List.length_replicate, ← take_is_chal hd5.atIndex _ hr]
  rw [summandAt_iSD, start_key Hs Sc hT hd hM e hD L Al,
    H2K5.Honest.sSD_start Reading.gl H _ (by rw [hpS]; rfl) Pl.vSF, ← Pl.pairs]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : 2 * i + 1 < (H2K5.Honest.sSF Z.P (inOf Z.P.S Z.link (cells m.st.input.trace))
      (frontQ Z m.st.heard ds (iSF Z.P.x))).ends := by
    rw [H2K5.Honest.sSF_ends_x Z.P _ _ Pl]
    have := Finset.mem_range.1 hi
    omega
  rw [hom, ← hv, hF, H2K5.Honest.Summand.endsAt_getD _ _ _ hi', hpt, hst]

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.heard_vars
#print axioms ProofFile.Honest.K5.coinsUnder_at
#print axioms ProofFile.Honest.K5.partVals_division_at
#print axioms ProofFile.Honest.K5.partVals_on_at
#print axioms ProofFile.Honest.K5.partVals_cells_at
#print axioms ProofFile.Honest.K5.partVals_atIndex_at
#print axioms ProofFile.Honest.K5.partVals_key_at
