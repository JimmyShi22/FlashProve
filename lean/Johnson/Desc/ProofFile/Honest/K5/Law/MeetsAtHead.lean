-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/MeetsAtHead.lean: CONDITIONAL, under the library's one head on
the public input (P5J.AtMgA, Johnson/P5J/MgAtAll.lean), at the member of a chain's thread at which
the honest side of an attention segment's own rounds (kind K5) is seated: THE FIRST HALVES OF WHAT
THE KIND's CLAIMS SAY (MeetsPlanes, MeetsUnit, Meets5, MeetsV, Meets7, Meets8,
Johnson/Desc/K5/Honest/Law/SayOf.lean), in the world in which the table's sentence on the forms of
the segment's own runs evaluates them behind the lay, at the witness behind the member. One
statement with its proof: meets_at (Honest/K5/Law/MeetsAt.lean) with five of its premises drawn from
the head. A joining of lemmas.

Main name:
  meets_at_head

What is drawn from the head, and by what: the public premises in one: public_at_head
(Johnson/Desc/K5/Honest/Law/PublicAtHead.lean); six numbers of the shape are not 0: posG_all,
seated_all (Johnson/Desc/First/Att/Door/Law/K5RestPublic.lean, K5RestOpen.lean); the runs "first"
and "second" return behind the lay: runs_at_head (Johnson/Desc/K5/Honest/Law/DoorAtHead.lean); every
table of the verifier's list is true of the matrices read off the witness, in that world:
attAt_behind_at_head (Johnson/Desc/K5/Honest/Law/AttAtHead.lean). That the claims' key points are
those of what the lookup handed on: zk_of (Johnson/Desc/First/Att/Claims/AnySeat.lean).

THE PREMISES THAT ARE LEFT, and who is meant to show each:
  the head h, and what the statements named above take beside it: the group and its plan; the
    table's meaning and lists; the state is reached, bears no mark and meets the promise in front.
  Hs (K5Seated), Sc (K5Script, at the group's plan and the seats that the item's sentence may read),
    hT, hM, e, hz: as in Honest/K5/Law/SayParts.lean. THE TIES (K5Script) ARE A PREMISE's FORM THAT
    IS NOT SHOWN.
  hh: the hearing of the rounds played returns, with no round left over and no scalar waiting.
  hP: the seat's public data are the plan's shape and own numbers. hA: the library's rule lays every
    valid name of a cell inside its matrix. Public; neither is drawn from the head here. hA is drawn
    from it in Honest/K5/Law/AddrInAt.lean.
  hgL: what the lookup on the calls handed on. hin: the claims' reading's return behind the lay.
Limits. The head is a hypothesis. At the function OnBytes.secondHashFunction, of which nothing is asked here; at
the library's full size alone. None of the premises is shown to be met. Nothing is said on who sees
what. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.MeetsAt
import Johnson.Desc.K5.Honest.Law.AttAtHead
import Johnson.Desc.K5.Honest.Law.PublicAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff Fork)
open VerifiableInference.Desc (Block Claim OpenedColumn First.S noDigest)
open VerifiableInference.Desc.Sound (MsgQ dataQ worldOwn)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Par Heard hear)
open H2K5.Honest (MeetsPlanes MeetsUnit Meets5 MeetsV Meets7 Meets8)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {Z : Seat5} {p : Par} {blk : Block First.S Claim}
  {rdOf : T.Wt → Nat × Nat → MsgQ}
  {Dw : OnBytes.Maker.WholeD} {rw₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **All the first halves of what the claims say, at the member and under the library's one head on
the public input.** g: the group of layers; a: its plan; the world: that in which the table's
sentence on the forms of the segment's own runs evaluates them behind the lay, at the witness behind
the member. CONDITIONAL; the premises are listed in the file's head. -/
theorem meets_at_head {Zl : _} (h : P5J.AtMgA OnBytes.secondHashFunction Zl Dw rw₀ Zp Np cF x₀)
    {L : VerifiableInference.Desc.K12.Door.Laid} (hL : P5J.At.laid? Zp = some L) {g : Nat}
    (hg : g < 12) {a : OnBytes.Attention.Plan}
    {x₁ : VerifiableInference.Desc.First.Look.Place} (ea : (P5J.At.X Zp).A[g]? = some a)
    (hx : VerifiableInference.Desc.First.Look.lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁)
    {W' : Type} (Mg : VerifiableInference.Desc.First.Meaning ProofFile.InstPub W')
    (hpub : Mg.pub = (P5J.mgAtAll h).pub) (hpubP : Mg.pubP = (P5J.mgAtAll h).pubP)
    (O : List VerifiableInference.Desc.First.Item)
    (Q : List VerifiableInference.Desc.First.Pub)
    (Oq : H2K5.Honest.Open8 (2 * g + 1) Q) {n : Nat} {π : ProofFile.InstPub} {s : First.S}
    {ys : VerifiableInference.Desc.Strs}
    (hr : Johnson.Desc.First.Walk.Tied.Reach 0 cF.blocksInOrder (ProofFile.startS Zp) n (π, s))
    (hu : s.failed = none)
    (hon : VerifiableInference.Desc.First.onAt (P5J.At.N Zp cF) Mg P5J.At.links
      (some ⟨1, some (2 * g + 1), 3, .K5⟩) O Q (π, s) ys)
    (Hs : K5Seated T b cells Z p blk)
    (Sc : K5Script T b cells Z a blk (h.𝔇.pubD.N.sent (2 * g + 1) 0) rdOf)
    {k : Coins Bk} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn} (hT : Thr T b k s m E)
    (hM : T.Moved blk k m E ds y cols) {att : VerifiableInference.Desc.First.AttOwn}
    (e : s.here = .att att) (hz : OnBytes.Model.Road.Sized att.F) {G : Fork} {hd5 : Heard}
    (hh : hear p.own (att.F, (roundsOf y.1).map noDigest, 0) = some (hd5, G, [], 0))
    (hP : Z.P = ⟨a.S, a.own⟩) (hA : AddrIn Z.P.S a.seam.tl) (ds' : List Fmt.Drawn)
    {gL : OnBytes.Model.Forest.Heard} (hgL : att.g = some gL) {i : P.Runs.In} {K : Nat}
    (hin : P.inOf (P.seatCO (P.parCOf a)) (P.parCOf a) (P.behind s att hd5 G) = some (i, K)) :
    MeetsPlanes (worldOwn (behindPart s att G) [] (h.𝔇.St.at1 (P.behind s att hd5 G)
          (dataQ (h.𝔇.pubD.N.sent (2 * g + 1) 0) (behindPart s att G)
            (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))))) Z.P.S gL i K
        (inOf Z.P.S Z.link (cells m.st.input.trace)) ∧
      (∀ x ∈ i.p.scores.toList.zipIdx, ∃ tb, i.t.score[x.2]? = some tb ∧
        MeetsUnit (worldOwn (behindPart s att G) [] (h.𝔇.St.at1 (P.behind s att hd5 G)
          (dataQ (h.𝔇.pubD.N.sent (2 * g + 1) 0) (behindPart s att G)
            (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))))) Z.P.S gL i K
          (inOf Z.P.S Z.link (cells m.st.input.trace)) x.1 tb) ∧
      Meets5 (worldOwn (behindPart s att G) [] (h.𝔇.St.at1 (P.behind s att hd5 G)
          (dataQ (h.𝔇.pubD.N.sent (2 * g + 1) 0) (behindPart s att G)
            (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))))) Z.P.S gL i K
        (inOf Z.P.S Z.link (cells m.st.input.trace)) ∧
      MeetsV (worldOwn (behindPart s att G) [] (h.𝔇.St.at1 (P.behind s att hd5 G)
          (dataQ (h.𝔇.pubD.N.sent (2 * g + 1) 0) (behindPart s att G)
            (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))))) Z.P.S gL i K
        (inOf Z.P.S Z.link (cells m.st.input.trace)) ∧
      Meets7 (worldOwn (behindPart s att G) [] (h.𝔇.St.at1 (P.behind s att hd5 G)
          (dataQ (h.𝔇.pubD.N.sent (2 * g + 1) 0) (behindPart s att G)
            (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))))) Z.P.S gL i K
        (inOf Z.P.S Z.link (cells m.st.input.trace)) ∧
      Meets8 (worldOwn (behindPart s att G) [] (h.𝔇.St.at1 (P.behind s att hd5 G)
          (dataQ (h.𝔇.pubD.N.sent (2 * g + 1) 0) (behindPart s att G)
            (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))))) Z.P.S gL i K
        (inOf Z.P.S Z.link (cells m.st.input.trace)) := by
  have ex : p.own = a.own := Hs.own.trans (by rw [hP])
  have hh' : hear a.own (att.F, (roundsOf y.1).map noDigest, 0) = some (hd5, G, [], 0) := by
    rw [← ex]
    exact hh
  obtain ⟨blk₀, hb⟩ := H2K5.Door.seated_all h hg
  have hpos : K5Law.PosG (P.geoOf a.S) := H2K5.Door.posG_all h hg ea hb
  have Pu := H2K5.Honest.public_at_head h hg ea
  obtain ⟨i₁, K₁, l₁, l₂, j, _, _, _, hin₁, h1, h2, _⟩ :=
    H2K5.Honest.runs_at_head h hL hg ea hx Mg hpub hpubP O Q Oq hr hu hon e hh'
  obtain ⟨rfl, rfl⟩ : i₁ = i ∧ K₁ = K := Prod.mk.inj (Option.some.inj (hin₁.symm.trans hin))
  obtain ⟨lid, cf, fs, _, _, HA⟩ := H2K5.Honest.attAt_behind_at_head h hL hg ea hx Mg hpub hpubP O
    Q Oq hr hu hon e hh' (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))
  have hzk : i₁.zk = gL.zk := K5Law.zk_of hin (by
    show att.g.map (·.zk) = _
    rw [hgL]
    rfl)
  exact meets_at Hs Sc hT hM e hz hh hP Pu hA hpos hin h1 h2 hzk (ds' := ds')
    ((HA i₁ K₁ hin).2 gL)

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.meets_at_head
