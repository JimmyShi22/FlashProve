-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/SayMember.lean: CONDITIONAL: at the member of a `Thread` at
which the half of an attention segment's own rounds is seated: all that the kind's claims say holds
(`SayAt`, Johnson/Desc/First/Att/Claims/SayAt.lean), at whatever the claims' reading behind the lay
returns, at the plan's shape. One statement with its proof: a joining of lemmas.

THE STATEMENT IS CONDITIONAL. Among its premises on values are hD (the world's mask row is the
witness's) and three bundles. The three ties between the witness and the honest side (`K5Script`):
THEY ARE NOT SHOWN. The clause on the witness's cells (`AtIdn`): Honest/K5/Law/IdnAt.lean hands it,
under `IdnOwed`, which is shown of no valid, out of the thread's letter `valid`; it is shown of no
run's input. That each written reader's form meets the honest side's value (six premises):
Honest/K5/Law/MeetsAt.lean draws all six, conditionally, from `K5Script`, public premises, returns
of the verifier's texts behind the lay and one premise on the verifier's tables.
Main name:
  `sayAt_member`

Limits. One member, one world. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.FrontsAt
import Johnson.Desc.ProofFile.Honest.K5.Law.Claim6At
import Johnson.Desc.First.Att.K05FormsMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes.Model (Reading Aff Fork)
open VerifiableInference.Desc (Block Claim OpenedColumn First.S noDigest)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ worldOwn)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Par Heard hear)
open H2K5.Honest (PublicAll AtIdn tOf MeetsPlanes MeetsUnit Meets5 MeetsV Meets7 Meets8)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {Z : Seat5} {p : Par} {blk : Block First.S Claim}
  {A : OnBytes.Attention.Plan} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}

/-- **At the member, all that the kind's claims say holds, at whatever the claims' reading behind
the lay returns.** `sayAt_holds` (Honest/K5/Law/SayHolds.lean) with these of its premises paid: what
is still owed for the rows (`frontsOk_at`, Honest/K5/Law/FrontsAt.lean); the value product's
equation (`claim6_at`, Honest/K5/Law/Claim6At.lean); the seat's numbers are counted (out of Pu); the
returns of the verifier's texts for the rows and the named points, and the shape of the claims'
values, out of the reading's return (`inOf_behind`, Johnson/Desc/First/Att/K05FormsMade.lean).
CONDITIONAL on: the three ties (Sc), WHICH ARE NOT SHOWN; the half's seat; the thread in front;
the challenges fit; the prover's side of the step; an attention segment is open; the world's mask
row is the witness's; the state's ledger is sized and the kind's hearing returns from it on the
rounds played; the seat's public data are the plan's shape and own numbers (hP); the public premises
(Pu); there is a pair; THE WITNESS's CELLS MEET THE LIBRARY's THREE FAMILIES OF IDENTITIES (Id);
what the lookup on the calls handed on (hgL); the reading's return (hin); that each written reader's
form meets the honest side's value (the six premises M). -/
theorem sayAt_member (Hs : K5Seated T b cells Z p blk) (Sc : K5Script T b cells Z A blk own rdOf)
    {k : Coins Bk} {s : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn} (hT : Thr T b k s m E)
    (hd : drawsFit blk.rounds ds = true) (hM : T.Moved blk k m E ds y cols)
    {att : VerifiableInference.Desc.First.AttOwn} (e : s.here = .att att) {dc : List Fmt.Drawn}
    {D : Bound GQ} (hD : MaskIs T own rdOf k s att m dc D)
    (hz : OnBytes.Model.Road.Sized att.F) {G : Fork} {hd5 : Heard} {rest : List Fmt.RoundView}
    {lead : Nat}
    (hh : hear p.own (att.F, (roundsOf y.1).map noDigest, 0) = some (hd5, G, rest, lead))
    (hP : Z.P = ⟨A.S, A.own⟩) (Pu : PublicAll ⟨A.S, A.own⟩ A.fs) (hpairs : A.own.pairs ≠ 0)
    (Id : AtIdn Z.P.D (tOf Reading.gl (inOf Z.P.S Z.link (cells m.st.input.trace))))
    {gL : OnBytes.Model.Forest.Heard} (hgL : att.g = some gL) {i : P.Runs.In} {K : Nat}
    (hin : P.inOf (P.seatCO (P.parCOf A)) (P.parCOf A) (P.behind s att hd5 G) = some (i, K))
    (MP : MeetsPlanes (worldOwn (behindPart s att G) [] D) Z.P.S gL i K
      (inOf Z.P.S Z.link (cells m.st.input.trace)))
    (MU : ∀ x ∈ i.p.scores.toList.zipIdx, ∃ tb, i.t.score[x.2]? = some tb ∧
      MeetsUnit (worldOwn (behindPart s att G) [] D) Z.P.S gL i K
        (inOf Z.P.S Z.link (cells m.st.input.trace)) x.1 tb)
    (M5 : Meets5 (worldOwn (behindPart s att G) [] D) Z.P.S gL i K
      (inOf Z.P.S Z.link (cells m.st.input.trace)))
    (MV : MeetsV (worldOwn (behindPart s att G) [] D) Z.P.S gL i K
      (inOf Z.P.S Z.link (cells m.st.input.trace)))
    (M7 : Meets7 (worldOwn (behindPart s att G) [] D) Z.P.S gL i K
      (inOf Z.P.S Z.link (cells m.st.input.trace)))
    (M8 : Meets8 (worldOwn (behindPart s att G) [] D) Z.P.S gL i K
      (inOf Z.P.S Z.link (cells m.st.input.trace))) :
    K5Law.SayAt Reading.gl (worldOwn (behindPart s att G) [] D) A.S gL i K := by
  obtain ⟨eg, _, _, g, l, lk, hg, hL, hi, _⟩ := P.inOf_behind hin
  obtain rfl : gL = g := Option.some.inj (hgL.symm.trans hg)
  have Pu' : PublicAll Z.P A.fs := by
    rw [hP]
    exact Pu
  have eS : Z.P.S = A.S := by rw [hP]
  have eG : Z.P.g = (P.parCOf A).geo := by
    rw [hP]
    rfl
  rw [← eG] at hL hi eg
  obtain ⟨g0, hg0, K3, -⟩ := Sc.keyTie k s m E hT att e
  obtain rfl : g0 = gL := Option.some.inj (hg0.symm.trans hgL)
  have Kp := H2K5.Honest.keyPts_of_keysFit Pu'.keys K3
  obtain ⟨uW, Cu⟩ := H2K5.Honest.pts_cut hi
  have pr : H2K5.Honest.PairsAre Z.P.g i.p.d.pwW := by
    rw [Cu.pwW]
    exact Pu'.pairsWl uW Cu.single _
  have Fr := frontsOk_at Hs Sc hT hd hM e hh hgL Pu' (by rw [hP]; exact hpairs) Id
  have he := claim6_at Hs Sc hT hd hM e hh hgL hi Pu'.sized Pu'.planned Kp Pu'.wl pr Id
  have hS := sayAt_holds Hs Sc Pu'.counted hT hd hM e hD hz hh hgL hL hi eg Fr MP MU M5 MV he M7 M8
  rw [eS] at hS
  exact hS

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.sayAt_member
