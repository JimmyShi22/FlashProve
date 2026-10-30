-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/SayParts.lean: CONDITIONAL: at the member of a chain's thread
at which the honest side of an attention segment's own rounds (kind K5) is seated, in the world in
which the items "the forms of a run are worth 0" are said behind the member: WHAT THE KIND's CLAIMS
SAY, CLAIM BY CLAIM (Say3, UnitAt, Say5 .. Say8, Johnson/Desc/First/Att/Claims/Say.lean,
Say58.lean), each in the form in which sayAt_of_rows (Honest/K5/Law/Say.lean) takes it. Statements
with their proofs.
EVERY STATEMENT BUT THE FIRST IS CONDITIONAL, and all these hang on the ties (K5Script,
Honest/K5/Law/Script.lean), WHICH ARE NOT SHOWN.

  worldBehind_is   the world of the sentence behind the lay (worldBehind,
                 Johnson/Desc/K5/Honest/Law/Own.lean) is the world of the slots' laws
  cellsAre_at    the matrices read off the witness hold the prover's cells (CellsAre,
                 Johnson/Desc/K5/Honest/Law/AloneMeets.lean)
  cellsAre_behind   the same of the matrices at the state behind the member's lay (matsAt,
                 Johnson/Desc/K5/Honest/Law/Planes.lean), at the witness behind the member
  say3_holds, say4_holds, say5_holds, say6_holds, say7_holds, say8_holds
                 **the claim's sentence**, from: "the written form is worth the slot less the
                 prover's value", or "the reader's form is worth the prover's value" (Meets..,
                 Johnson/Desc/K5/Honest/Law/SayOf.lean), A PREMISE HERE; and the worth 0 of the
                 claim's rows, a premise too. The other half, "the slot is worth the prover's
                 value", is laid in (Honest/K5/Law/UnderUnits.lean, UnderDiv.lean, UnderIndex.lean)

Further premises. say4_holds: each unit has its tables in i.t. say6_holds: the equation of the value
product on the two sums' totals, each at the challenges in front of its own part, the accumulated
output and the denominator at the verifier's points. The rest: see the head of
Honest/K5/Law/UnderDiv.lean.

Limits. Nothing is said on who sees what. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.UnderUnits
import Johnson.Desc.ProofFile.Honest.K5.Law.UnderIndex
import Johnson.Desc.K5.Honest.Law.Own
import Johnson.Desc.K5.Honest.Law.Planes

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff Fork)
open VerifiableInference.Desc (Block Claim OpenedColumn First.S noDigest)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ Stated dataQ worldOwn matsOfData)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Par Heard Left hear pointsOf)
open H2K5.Honest (iVM iVD sVM sVD accAt zcAt MeetsPlanes MeetsUnit Meets5 MeetsV Meets7 Meets8
  CellsAre)
open K5Law (oldOf scoreBack tbBack remBack Say3 UnitAt Say5 Say6 Say7 Say8)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {Z : Seat5} {p : Par} {blk : Block First.S Claim}
  {A : OnBytes.Attention.Plan} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}

/-- The world of the sentence behind the lay is the world of the slots' laws. No premise. -/
theorem worldBehind_is (St : Stated) (own : List (Nat × Nat)) (s : First.S)
    (a : VerifiableInference.Desc.First.AttOwn) (h : Heard) (G : Fork) (rd : Nat × Nat → MsgQ) :
    H2K5.Honest.worldBehind St own s a h G rd =
      worldOwn (behindPart s a G) []
        (St.at1 (P.behind s a h G) (dataQ own (behindPart s a G) rd)) := rfl

/-- **The matrices read off the witness hold the prover's cells.** CONDITIONAL: on the ties; the
library's rule lays every valid name inside a matrix other than the lookup's planes' (AddrIn,
Honest/K5/Law/Script.lean); the thread in front of the member. -/
theorem cellsAre_at (Sc : K5Script T b cells Z A blk own rdOf) (hA : AddrIn Z.P.S A.seam.tl)
    {k : Coins Bk} {s : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    (hT : Thr T b k s m E) {a : VerifiableInference.Desc.K9.Part}
    (ha : VerifiableInference.Desc.K9.segAt? s = some a) (dx : List Fmt.Drawn) :
    CellsAre Reading.gl Z.P.S
      (matsOfData A.seam.tl ((s.link?.map (·.arrayOf)).getD #[])
        (dataQ own a (rdOf (T.wit k m.st.input (m.st.heard ++ dx)))))
      (inOf Z.P.S Z.link (cells m.st.input.trace)) :=
  fun q hq => cells_named Sc hA hT ha dx q hq

/-- **The same of the matrices at the state behind the member's lay**, read off the witness at a
continuation ds' of the challenges heard behind the member. CONDITIONAL: as `cellsAre_at`; an
attention segment is open; the prover's side of the step. -/
theorem cellsAre_behind (Sc : K5Script T b cells Z A blk own rdOf) (hA : AddrIn Z.P.S A.seam.tl)
    {k : Coins Bk} {s : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    (hT : Thr T b k s m E) {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
    {cols : List OpenedColumn} (hM : T.Moved blk k m E ds y cols)
    {att : VerifiableInference.Desc.First.AttOwn} (e : s.here = .att att) (hd5 : Heard) (G : Fork)
    (ds' : List Fmt.Drawn) :
    CellsAre Reading.gl Z.P.S
      (H2K5.Honest.matsAt A (P.behind s att hd5 G) (dataQ own (behindPart s att G)
        (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))))
      (inOf Z.P.S Z.link (cells m.st.input.trace)) := by
  obtain ⟨⟨l, -, hy⟩, -⟩ := hM
  unfold H2K5.Honest.matsAt
  rw [link_behind e, play_heard _ _ _ _ _ hy, (play_mid _ _ _ _ _ hy).1, List.append_assoc]
  exact cellsAre_at Sc hA hT (P.segAt_front e) (ds ++ ds')

section
variable (Hs : K5Seated T b cells Z p blk) (Sc : K5Script T b cells Z A blk own rdOf)
  (hc : Z.P.counted = true)
  {k : Coins Bk} {s : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
  {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn} (hT : Thr T b k s m E)
  (hd : drawsFit blk.rounds ds = true) (hM : T.Moved blk k m E ds y cols)
  {att : VerifiableInference.Desc.First.AttOwn} (e : s.here = .att att) {dc : List Fmt.Drawn}
  {D : Bound GQ} (hD : MaskIs T own rdOf k s att m dc D)
  (hz : OnBytes.Model.Road.Sized att.F) {G : Fork} {hd5 : Heard} {rest : List Fmt.RoundView} {lead : Nat}
  (hh : hear p.own (att.F, (roundsOf y.1).map noDigest, 0) = some (hd5, G, rest, lead))
  {g : OnBytes.Model.Forest.Heard} (hg : att.g = some g) {Lf : Left} {i : P.Runs.In}
  (hi : pointsOf Z.P.g g.zk hd5 Lf = some i.p) {gL : OnBytes.Model.Forest.Heard} {K : Nat}
include Hs Sc hc hT hd hM e hD hz hh hg hi

/-- **Claim 3.** CONDITIONAL: see the head. -/
theorem say3_holds (M : MeetsPlanes (worldOwn (behindPart s att G) [] D) Z.P.S gL i K
      (inOf Z.P.S Z.link (cells m.st.input.trace))) :
    Say3 Reading.gl (worldOwn (behindPart s att G) [] D) (oldOf Z.P.S gL i) K :=
  H2K5.Honest.say3_of M (under_planes Hs Sc hc hT hd hM e hD hz hh hg hi)

/-- **Claim 4, unit by unit.** hv: each unit has its tables. CONDITIONAL: see the head. -/
theorem say4_holds (MP : MeetsPlanes (worldOwn (behindPart s att G) [] D) Z.P.S gL i K
      (inOf Z.P.S Z.link (cells m.st.input.trace)))
    (hv : ∀ x ∈ i.p.scores.toList.zipIdx, ∃ tb, i.t.score[x.2]? = some tb ∧
      MeetsUnit (worldOwn (behindPart s att G) [] D) Z.P.S gL i K
        (inOf Z.P.S Z.link (cells m.st.input.trace)) x.1 tb) :
    ∀ x ∈ i.p.scores.toList.zipIdx,
      x.1.sc.row.value Reading.gl (worldOwn (behindPart s att G) [] D) = 0 →
      ∃ tb pc, i.t.score[x.2]? = some tb ∧ i.p.planes[x.1.claim]? = some pc ∧
        UnitAt Reading.gl (worldOwn (behindPart s att G) [] D) (oldOf Z.P.S gL i) K
          (scoreBack x.1) (tbBack tb) (remBack pc) := by
  intro x hx hr
  obtain ⟨tb, htb, MU⟩ := hv x hx
  have hk : i.p.scores[x.2]? = some x.1 := by
    rw [← Array.getElem?_toList]
    exact List.mem_zipIdx_iff_getElem?.1 hx
  have F := unit_facts Hs Sc hc hT hd hM e hD hz hh hg hi hk
  obtain ⟨pc, hpc, -, -, -⟩ := F.plane
  exact ⟨tb, pc, htb, hpc, H2K5.Honest.unit_of MP
    (under_planes Hs Sc hc hT hd hM e hD hz hh hg hi)
    (Array.mem_toList_iff.2 (Array.mem_of_getElem? hpc)) MU F.under hr⟩

/-- **Claim 5.** CONDITIONAL: see the head. -/
theorem say5_holds (M : Meets5 (worldOwn (behindPart s att G) [] D) Z.P.S gL i K
      (inOf Z.P.S Z.link (cells m.st.input.trace))) :
    i.p.d.scE.row.value Reading.gl (worldOwn (behindPart s att G) [] D) = 0 →
      Say5 Reading.gl (worldOwn (behindPart s att G) [] D) (oldOf Z.P.S gL i) K :=
  H2K5.Honest.say5_of M (under5 Hs Sc hc hT hd hM e hD hz hh hg hi)

/-- **Claim 6.** he: the equation of the value product. CONDITIONAL: see the head. -/
theorem say6_holds (M : MeetsV (worldOwn (behindPart s att G) [] D) Z.P.S gL i K
      (inOf Z.P.S Z.link (cells m.st.input.trace)))
    (he : Reading.gl.val (sVM Z.P (inOf Z.P.S Z.link (cells m.st.input.trace))
        (chalOf Z (m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x (iVM Z.P.x))))).total +
      Reading.gl.val (sVD Z.P (inOf Z.P.S Z.link (cells m.st.input.trace))
        (chalOf Z (m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x (iVD Z.P.x))))).total -
      Reading.gl.val (accAt Z.P.g (inOf Z.P.S Z.link (cells m.st.input.trace)) i.p.d) -
      Reading.gl.val i.p.d.gam *
        Reading.gl.val (zcAt Z.P.g (inOf Z.P.S Z.link (cells m.st.input.trace)) i.p.d) = 0) :
    i.p.d.vpm.row.value Reading.gl (worldOwn (behindPart s att G) [] D) = 0 →
      i.p.d.vpd.row.value Reading.gl (worldOwn (behindPart s att G) [] D) = 0 →
      Say6 Reading.gl (worldOwn (behindPart s att G) [] D) (oldOf Z.P.S gL i) K :=
  H2K5.Honest.say6_of M (underV Hs Sc hc hT hd hM e hD hz hh hg hi) he

/-- **Claim 7.** CONDITIONAL: see the head. -/
theorem say7_holds (M : Meets7 (worldOwn (behindPart s att G) [] D) Z.P.S gL i K
      (inOf Z.P.S Z.link (cells m.st.input.trace))) :
    i.p.x.scF.row.value Reading.gl (worldOwn (behindPart s att G) [] D) = 0 →
      i.p.x.scd.row.value Reading.gl (worldOwn (behindPart s att G) [] D) = 0 →
      Say7 Reading.gl (worldOwn (behindPart s att G) [] D) (oldOf Z.P.S gL i) K :=
  H2K5.Honest.say7_of M (under7 Hs Sc hc hT hd hM e hD hz hh hg hi)

/-- **Claim 8.** CONDITIONAL: see the head. -/
theorem say8_holds (M : Meets8 (worldOwn (behindPart s att G) [] D) Z.P.S gL i K
      (inOf Z.P.S Z.link (cells m.st.input.trace))) :
    i.p.x.scH.row.value Reading.gl (worldOwn (behindPart s att G) [] D) = 0 →
      Say8 Reading.gl (worldOwn (behindPart s att G) [] D) (oldOf Z.P.S gL i) K :=
  H2K5.Honest.say8_of M (under8 Hs Sc hc hT hd hM e hD hz hh hg hi)

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.worldBehind_is
#print axioms ProofFile.Honest.K5.cellsAre_at
#print axioms ProofFile.Honest.K5.cellsAre_behind
#print axioms ProofFile.Honest.K5.say3_holds
#print axioms ProofFile.Honest.K5.say4_holds
#print axioms ProofFile.Honest.K5.say5_holds
#print axioms ProofFile.Honest.K5.say6_holds
#print axioms ProofFile.Honest.K5.say7_holds
#print axioms ProofFile.Honest.K5.say8_holds
