-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/MeetsAt.lean: CONDITIONAL: at the member of a chain's thread at
which the honest side of an attention segment's own rounds (kind K5) is seated, in the world in
which the items "the forms of a run are worth 0" are said behind the member: THE FIRST HALVES OF
WHAT THE KIND's CLAIMS SAY (MeetsPlanes, MeetsUnit, Meets5, MeetsV, Meets7, Meets8,
Johnson/Desc/K5/Honest/Law/SayOf.lean): "the written form is worth the slot less the prover's value,
read", "the reader's form is worth the prover's value, read": each in the form in which say3_holds
.. say8_holds (Honest/K5/Law/SayParts.lean) take it as a premise. Statements with their proofs. A
joining of lemmas; no algebra is in this file.

Main names:
  chalLens_of_hear   the numbers of challenges that the verifier has heard are those that the
                 shape's numbers ask
  meets_at       **all six first halves**

EVERY STATEMENT IS CONDITIONAL. THE PREMISES OF meets_at, and who is meant to show each:
  Hs (K5Seated), Sc (K5Script), hT (the thread in front), hM (the prover's side of the step), e (the
    open segment), hz (the ledger in front is sized), hh (the hearing returns): as in
    Honest/K5/Law/SayParts.lean. THE TIES (K5Script) ARE A PREMISE's FORM THAT IS NOT SHOWN. Of
    them are spent: the witness's cell is the trace's; the state's key points are cut as the lookup
    cuts them.
  hP: the seat's public data are the plan's shape and own numbers. Pu: the public premises in one
    (Johnson/Desc/K5/Honest/Law/PublicAtPlan.lean; at the library's head on the public input:
    Law/PublicAtHead.lean). hA: the library's rule lays every valid name of a cell inside its matrix
    (shown in Honest/K5/Law/AddrInAt.lean: under the library's head; at a planner's plan, with
    hpos). hpos: six numbers of the shape are not 0. All public.
  hin, h1, h2: the claims' reading and the runs "first" and "second" return at the state behind the
    lay. hzk: the claims' key points are those of gL.
  At: EVERY TABLE OF THE VERIFIER's LIST IS TRUE, IN THAT WORLD, OF THE MATRICES READ OFF THE
    WITNESS BEHIND THE MEMBER (AttAt, Johnson/Road/Rows/AttRead.lean): whoever lays the world
    (Johnson/Desc/K5/Honest/Law/AttAtHead.lean has it at the head's letters, for the world that
    reads the array of the tables through the filling's stated function).
Limits. A plan in which the layers of the group have more than one shift is not reached. None of the
premises is shown to be met. Nothing is said on who sees what. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.SayParts
import Johnson.Desc.ProofFile.Honest.K5.Law.Along
import Johnson.Desc.ProofFile.Honest.K5.Law.DrawnFront
import Johnson.Desc.K5.Honest.Law.MeetsBehind
import Johnson.Desc.K5.Honest.Law.PtsPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff Fork)
open OnBytes.Road.Rows (AttAt)
open VerifiableInference.Desc (Block Claim OpenedColumn First.S noDigest)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ dataQ worldOwn)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Par Heard hear)
open H2K5.Honest (MeetsPlanes MeetsUnit Meets5 MeetsV Meets7 Meets8 PublicAll)
open K5Law (oldOf)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {Z : Seat5} {p : Par} {blk : Block First.S Claim}
  {A : OnBytes.Attention.Plan} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}

/-- **The numbers of challenges that the verifier has heard are those that the shape's numbers ask**
(`ChalLens`, Johnson/Desc/K5/Honest/Law/PtsFitOf.lean). CONDITIONAL on: the public premises in one;
the hearing returns, at the plan's own numbers of these rounds, from a sized ledger. -/
theorem chalLens_of_hear (Pu : PublicAll ⟨A.S, A.own⟩ A.fs) {F G : Fork} {rs rest : List Fmt.RoundView}
    {lead : Nat} {hd5 : Heard} (hz : OnBytes.Model.Road.Sized F)
    (hh : hear A.own (F, rs, 0) = some (hd5, G, rest, lead)) :
    H2K5.Honest.ChalLens A.S hd5 := by
  have Al := along_of_hear_road hz hh
  have pv : ∀ n, (prodVs n).length = n := fun n => List.length_replicate
  refine H2K5.Honest.chalLens_of_lengths (P := ⟨A.S, A.own⟩) Pu Al.units
    (fun i u o hu ho => by rw [(Al.score i u o hu ho).r_length, pv])
    (by rw [Al.division.r_length, pv]) (by rw [Al.below.r_length, pv])
    (by rw [Al.on.r_length, pv]) (by rw [Al.atIndex.r_length, pv]) ?_
    (by rw [Al.cells.r_length, pv]) (point_size hh)
  rw [Al.key.r_length]
  unfold H2K5.Honest.keyVars
  rw [List.length_map, List.length_append, List.length_append, List.length_replicate,
    List.length_replicate, List.length_replicate]

section
variable (Hs : K5Seated T b cells Z p blk) (Sc : K5Script T b cells Z A blk own rdOf)
  {k : Coins Bk} {s : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
  {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn} (hT : Thr T b k s m E)
  (hM : T.Moved blk k m E ds y cols)
  {att : VerifiableInference.Desc.First.AttOwn} (e : s.here = .att att)
  (hz : OnBytes.Model.Road.Sized att.F) {G : Fork} {hd5 : Heard} {rest : List Fmt.RoundView} {lead : Nat}
  (hh : hear p.own (att.F, (roundsOf y.1).map noDigest, 0) = some (hd5, G, rest, lead))
  {i : P.Runs.In} {gL : OnBytes.Model.Forest.Heard} {K : Nat}
include Hs Sc hT hM e hz hh

/-- **All the first halves of what the claims say, at the member**, in the world in which the items
"the forms of a run are worth 0" are said behind it, each in the form in which say3_holds ..
say8_holds (Honest/K5/Law/SayParts.lean) take it. CONDITIONAL; the premises are listed in the file's
head. -/
theorem meets_at (hP : Z.P = ⟨A.S, A.own⟩) (Pu : PublicAll ⟨A.S, A.own⟩ A.fs)
    (hA : AddrIn Z.P.S A.seam.tl) (hpos : K5Law.PosG (P.geoOf A.S))
    (hin : P.inOf (P.seatCO (P.parCOf A)) (P.parCOf A) (P.behind s att hd5 G) = some (i, K))
    {l₁ l₂ : List Aff} {j : P.Runs.JoinsP} (h1 : P.Runs.firstRun i K = some (l₁, j))
    (h2 : P.Runs.secondRun i K = some l₂) (hzk : i.zk = gL.zk) {D : Bound GQ}
    {ds' : List Fmt.Drawn} {lid : Nat} {cf : OnBytes.Attention.Cfg}
    {fs : OnBytes.Model.Forest.Shape}
    (At : AttAt Reading.gl (worldOwn (behindPart s att G) [] D) A.seam.tl K
      (H2K5.Honest.matsAt A (P.behind s att hd5 G) (dataQ own (behindPart s att G)
        (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds'))))) (oldOf A.S gL i) lid cf fs) :
    MeetsPlanes (worldOwn (behindPart s att G) [] D) Z.P.S gL i K
        (inOf Z.P.S Z.link (cells m.st.input.trace)) ∧
      (∀ x ∈ i.p.scores.toList.zipIdx, ∃ tb, i.t.score[x.2]? = some tb ∧
        MeetsUnit (worldOwn (behindPart s att G) [] D) Z.P.S gL i K
          (inOf Z.P.S Z.link (cells m.st.input.trace)) x.1 tb) ∧
      Meets5 (worldOwn (behindPart s att G) [] D) Z.P.S gL i K
        (inOf Z.P.S Z.link (cells m.st.input.trace)) ∧
      MeetsV (worldOwn (behindPart s att G) [] D) Z.P.S gL i K
        (inOf Z.P.S Z.link (cells m.st.input.trace)) ∧
      Meets7 (worldOwn (behindPart s att G) [] D) Z.P.S gL i K
        (inOf Z.P.S Z.link (cells m.st.input.trace)) ∧
      Meets8 (worldOwn (behindPart s att G) [] D) Z.P.S gL i K
        (inOf Z.P.S Z.link (cells m.st.input.trace)) := by
  have eS : Z.P.S = A.S := by rw [hP]
  have ex : p.own = A.own := Hs.own.trans (by rw [hP])
  have hc := cellsAre_behind Sc hA hT hM e hd5 G ds'
  rw [ex] at hh
  have Cl := chalLens_of_hear Pu hz hh
  obtain ⟨g, hg, K3, _⟩ := Sc.keyTie k s m E hT att e
  have Kp := P.keyPts_of_k3 Pu.fit K3
  obtain ⟨eg, _, _, g', l, lk, hg', _, hPt, _⟩ := P.inOf_behind hin
  obtain rfl : g = g' := Option.some.inj (hg.symm.trans hg')
  have hPt' : P.pointsOf (P.geoOf A.S) g.zk hd5 l = some i.p := hPt
  have Pp := H2K5.Honest.planes_public (P := ⟨A.S, A.own⟩) Pu
    (OnBytes.Road.Rows.norm_of_hid At.shape) hPt' Kp.size
  obtain ⟨prW, prX, prH⟩ := H2K5.Honest.lists_public (P := ⟨A.S, A.own⟩) Pu hPt'
  rw [eS] at hc ⊢
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := H2K5.Honest.meets_behind A hin h1 h2 hzk hpos At hc Cl
    (fun g₂ hg₂ pc hpc => by
      rw [← Option.some.inj (hg.symm.trans hg₂)]
      exact (Pp pc hpc).1)
    (fun pc hpc => (Pp pc hpc).2) prW prX prH
  refine ⟨m1, fun x hx => ?_, m3, m4, m5, m6⟩
  obtain ⟨tb, _, t1, _⟩ := H2K5.Honest.unit_in (gL := gL) (S := A.S) eg hzk
    (by rw [show i.g = P.geoOf A.S from eg]; exact hPt') h1 h2
    (OnBytes.Road.Rows.shapedG_of_hid At.shape).G (k := x.1) (n := x.2) hx
  exact ⟨tb, t1, m2 x.1 x.2 tb hx t1⟩

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.chalLens_of_hear
#print axioms ProofFile.Honest.K5.meets_at
