-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/AddrInAt.lean: CONDITIONAL: the public premise AddrIn
(Honest/K5/Law/Script.lean: the library's rule of addresses lays every valid name of a cell inside
its matrix, which is not the matrix of the lookup's planes), SHOWN: at a plan that the planner
returns, where six numbers of its shape are not 0 (PosG: public), and under the library's one head
on the public input (P5J.AtMgA, Johnson/P5J/MgAtAll.lean). Statements with their proofs: each is
Johnson/Desc/K5/Honest/Law/AddrIn.lean's addr_inside_ofPlan in AddrIn's name. And with it the first
halves of what the kind's claims say, at the member and under the head, with that premise gone and
all their other premises as they were.

Main names:
  addrIn_ofPlan, addrIn_of_plan   at a plan that is the planner's but for one field of the smallness
                 test's numbers; at a plan that the planner returns
  addrIn_at_head   under the head, at the plan of a group of layers
  meets_head     meets_at_head (Honest/K5/Law/MeetsAtHead.lean) without the premise AddrIn

Conditional on: addrIn_ofPlan, addrIn_of_plan: six numbers of the shape are not 0 (PosG,
Johnson/Desc/First/Att/Claims/TablesSpec.lean): public. addrIn_at_head: the head alone, by
ofPlan_all, posG_all (Johnson/Desc/First/Att/Door/Law/K5RestPublic.lean) and seated_all
(K5RestOpen.lean). meets_head: as the head of Honest/K5/Law/MeetsAtHead.lean lists, but for hA.
Limits. The head is a hypothesis. That the rule of addresses is the program's is shown by no
theorem. THE TIES (K5Script) ARE A PREMISE's FORM THAT IS NOT SHOWN. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.MeetsAtHead
import Johnson.Desc.K5.Honest.Law.AddrIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open VerifiableInference.Desc.First.Att

/-- **`AddrIn` (Honest/K5/Law/Script.lean) at a plan that is the planner's but for one field of the
smallness test's numbers.** CONDITIONAL on that, and on: six numbers of the shape are not 0. Public.
-/
theorem addrIn_ofPlan {A : OnBytes.Attention.Plan} (hA : K5Law.OfPlan A)
    (hpos : K5Law.PosG (P.geoOf A.S)) : AddrIn A.S A.seam.tl := by
  exact H2K5.Honest.addr_inside_ofPlan hA hpos

/-- **`AddrIn` at a plan that the planner returns.** CONDITIONAL as `addrIn_ofPlan`. -/
theorem addrIn_of_plan {settings : OnBytes.Model.Settings} {j : OnBytes.Attention.In}
    {cf : OnBytes.Attention.Cfg} {A : OnBytes.Attention.Plan}
    (h : OnBytes.Attention.plan settings j cf = Except.ok A) (hpos : K5Law.PosG (P.geoOf A.S)) :
    AddrIn A.S A.seam.tl := by
  exact addrIn_ofPlan (K5Law.ofPlan_self h) hpos

/-- **`AddrIn` under the library's one head on the public input**, at the plan a of the group g of
layers. CONDITIONAL on the head. -/
theorem addrIn_at_head {Zl : _} {Dw : OnBytes.Maker.WholeD} {rw₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Zl Dw rw₀ Zp Np cF x₀) {g : Nat} (hg : g < 12)
    {a : OnBytes.Attention.Plan} (ea : (P5J.At.X Zp).A[g]? = some a) :
    AddrIn a.S a.seam.tl := by
  obtain ⟨blk₀, hb⟩ := H2K5.Door.seated_all h hg
  exact addrIn_ofPlan (H2K5.Door.ofPlan_all h ea) (H2K5.Door.posG_all h hg ea hb)

section
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block Claim OpenedColumn First.S noDigest)
open VerifiableInference.Desc.Sound (MsgQ dataQ worldOwn)
open VerifiableInference.Desc.First.Att.P (Par Heard hear)
open H2K5.Honest (MeetsPlanes MeetsUnit Meets5 MeetsV Meets7 Meets8)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {Z : Seat5} {p : Par} {blk : Block First.S Claim}
  {rdOf : T.Wt → Nat × Nat → MsgQ}
  {Dw : OnBytes.Maker.WholeD} {rw₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **All the first halves of what the claims say, at the member and under the head: of the four
public premises of meets_at (hP, Pu, hA, hpos) hP alone is left.** It is meets_at_head
(Honest/K5/Law/MeetsAtHead.lean) with `AddrIn` drawn from the head. CONDITIONAL; the premises are
those of meets_at_head but for hA. -/
theorem meets_head {Zl : _} (h : P5J.AtMgA OnBytes.secondHashFunction Zl Dw rw₀ Zp Np cF x₀)
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
    (hP : Z.P = ⟨a.S, a.own⟩) (ds' : List Fmt.Drawn)
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
  have hA : AddrIn Z.P.S a.seam.tl := by
    rw [show Z.P.S = a.S by rw [hP]]
    exact addrIn_at_head h hg ea
  exact meets_at_head h hL hg ea hx Mg hpub hpubP O Q Oq hr hu hon Hs Sc hT hM e hz hh hP hA ds' hgL
    hin

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.addrIn_ofPlan
#print axioms ProofFile.Honest.K5.addrIn_of_plan
#print axioms ProofFile.Honest.K5.addrIn_at_head
#print axioms ProofFile.Honest.K5.meets_head
