-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Idn12/SayHolds2.lean: CONDITIONAL: A SECOND FORM of one
declaration of Johnson/Desc/ProofFile/Honest/K5/Law/SayHolds.lean: `sayAt_holds`.
The forms there take as a premise that the cells meet all three of the library's families of
identities on an attention segment (`AtIdn`, Johnson/Desc/K5/Honest/Law/Idn.lean). These take the
first two families alone (`Idn12`, Johnson/Desc/K5/Honest/Law/Idn12/Idn2.lean). Here the premise is
the field idn of the bundle Fr (`FrontsOk₂`, Idn12/RowsBehind2.lean).

Why. CONDITIONALLY, `Idn12` follows from two items that the row of the segment's own rounds asks in
front (Johnson/Desc/K5/Honest/Law/IdnOfAsked.lean): among others under the library's head on the
public input as a hypothesis, hH and hc; none of these, nor the items, is shown. The third family on
the whole cube follows from no such item.

How. THE TEXT IS THE ELDER FILE's: each declaration named above with its docstring and its proof,
the premise's name exchanged, and each name of a declaration that has a second form exchanged for
that form's (a subscript 2 at its end). Every other lemma is called from the elder files, which are
imported and stay as they are.

Limits. Those of SayHolds.lean, whose head says what each premise is and who is meant to show it.
Every theorem is conditional.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.SayHolds
import Johnson.Desc.ProofFile.Honest.K5.Law.Idn12.RowsBehind2

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes.Model (Reading Aff Fork)
open VerifiableInference.Desc (Block Claim OpenedColumn First.S noDigest)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ worldOwn)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Par Heard Left hear leftP pointsOf)
open H2K5.Honest (iVM iVD sVM sVD accAt zcAt MeetsPlanes MeetsUnit Meets5 MeetsV Meets7 Meets8)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {Z : Seat5} {p : Par} {blk : Block First.S Claim}
  {A : OnBytes.Attention.Plan} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}

/-- **AT THE MEMBER, IN THE WORLD OF THE FORMS BEHIND THE HEARING, ALL THAT THE KIND's CLAIMS SAY
HOLDS** (`SayAt`, Johnson/Desc/First/Att/Claims/SayAt.lean). CONDITIONAL on: the three ties between
the witness and the honest side (Sc), WHICH ARE NOT SHOWN; the half's seat; the seat's numbers
are counted (hc); the thread in front; the challenges fit; the prover's side of the step; an
attention segment is open; the world's mask row is the witness's; the state's ledger is sized and
the kind's hearing returns from it on the rounds played; what the lookup on the calls heard is there
(hg); the verifier's text for the rows and its function for the named points have returned, and the
claims' values i hold these points at the seat's shape (hL, hi, hig); what is still owed for the
rows (Fr); that each written reader's form meets the honest side's value (the six premises M), and
the value product's equation (he). NONE OF Sc, Fr, THE SIX AND he IS SHOWN HERE. -/
theorem sayAt_holds₂ (Hs : K5Seated T b cells Z p blk) (Sc : K5Script T b cells Z A blk own rdOf)
    (hc : Z.P.counted = true) {k : Coins Bk} {s : First.S} {m : Mid (Local W₀ Rc Xi Tr) X}
    {E : Env} {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
    {cols : List OpenedColumn} (hT : Thr T b k s m E) (hd : drawsFit blk.rounds ds = true)
    (hM : T.Moved blk k m E ds y cols) {att : VerifiableInference.Desc.First.AttOwn}
    (e : s.here = .att att) {dc : List Fmt.Drawn} {D : Bound GQ}
    (hD : MaskIs T own rdOf k s att m dc D) (hz : OnBytes.Model.Road.Sized att.F) {G : Fork}
    {hd5 : Heard} {rest : List Fmt.RoundView} {lead : Nat}
    (hh : hear p.own (att.F, (roundsOf y.1).map noDigest, 0) = some (hd5, G, rest, lead))
    {g : OnBytes.Model.Forest.Heard} (hg : att.g = some g) {Lf : Left} {i : P.Runs.In}
    (hL : leftP Z.P.g g.zk hd5 G = some Lf) (hi : pointsOf Z.P.g g.zk hd5 Lf = some i.p)
    (hig : i.g = Z.P.g) {gL : OnBytes.Model.Forest.Heard} {K : Nat}
    (Fr : FrontsOk₂ Z (inOf Z.P.S Z.link (cells m.st.input.trace)) m.st.heard ds g.zk hd5)
    (MP : MeetsPlanes (worldOwn (behindPart s att G) [] D) Z.P.S gL i K
      (inOf Z.P.S Z.link (cells m.st.input.trace)))
    (MU : ∀ x ∈ i.p.scores.toList.zipIdx, ∃ tb, i.t.score[x.2]? = some tb ∧
      MeetsUnit (worldOwn (behindPart s att G) [] D) Z.P.S gL i K
        (inOf Z.P.S Z.link (cells m.st.input.trace)) x.1 tb)
    (M5 : Meets5 (worldOwn (behindPart s att G) [] D) Z.P.S gL i K
      (inOf Z.P.S Z.link (cells m.st.input.trace)))
    (MV : MeetsV (worldOwn (behindPart s att G) [] D) Z.P.S gL i K
      (inOf Z.P.S Z.link (cells m.st.input.trace)))
    (he : Reading.gl.val (sVM Z.P (inOf Z.P.S Z.link (cells m.st.input.trace))
        (chalOf Z (m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x (iVM Z.P.x))))).total +
      Reading.gl.val (sVD Z.P (inOf Z.P.S Z.link (cells m.st.input.trace))
        (chalOf Z (m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x (iVD Z.P.x))))).total -
      Reading.gl.val (accAt Z.P.g (inOf Z.P.S Z.link (cells m.st.input.trace)) i.p.d) -
      Reading.gl.val i.p.d.gam *
        Reading.gl.val (zcAt Z.P.g (inOf Z.P.S Z.link (cells m.st.input.trace)) i.p.d) = 0)
    (M7 : Meets7 (worldOwn (behindPart s att G) [] D) Z.P.S gL i K
      (inOf Z.P.S Z.link (cells m.st.input.trace)))
    (M8 : Meets8 (worldOwn (behindPart s att G) [] D) Z.P.S gL i K
      (inOf Z.P.S Z.link (cells m.st.input.trace))) :
    K5Law.SayAt Reading.gl (worldOwn (behindPart s att G) [] D) Z.P.S gL i K := by
  have H : K5Law.PointsAre i.g g.zk hd5 Lf i.p := by
    rw [hig]
    exact K5Law.points_are hi
  exact sayAt_of_rows H (rows_zero_behind₂ Hs Sc hT hd hM e hD hz hh Fr hL)
    (say3_holds Hs Sc hc hT hd hM e hD hz hh hg hi MP)
    (say4_holds Hs Sc hc hT hd hM e hD hz hh hg hi MP MU)
    (say5_holds Hs Sc hc hT hd hM e hD hz hh hg hi M5)
    (say6_holds Hs Sc hc hT hd hM e hD hz hh hg hi MV he)
    (say7_holds Hs Sc hc hT hd hM e hD hz hh hg hi M7)
    (say8_holds Hs Sc hc hT hd hM e hD hz hh hg hi M8)

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.sayAt_holds₂
