-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K10Debt.lean: K10's DEBT AT THE CLOSED CONSTANT, AT THE CONCRETE SECOND HASH FUNCTION:
SIX FIELDS. A definition, statements and proofs: calls; no more.
It names the debt in fewer fields than `AtMgA.K10Left` (Johnson/P5J/K10Left.lean: nine fields),
which stands beneath it.

What is said, at h : AtMgA OnBytes.secondHashFunction ..:
  `AtMgA.K10Debt h L`: `K10Left`'s fields reads, clear, fenFit (no kind's), kept, fence, law, to the
    letter. GONE: low and ride.
  `k10_left_of_debt`: under the three flat lists' heads: it gives `h.K10Left L`: low by `k10_low_at`
    (Johnson/P5J/K10Low.lean); ride by `k10_ride_closed`
    (Johnson/LPFE1R/K10HeadOpenAt.lean), from fenFit, low and fence. `k10_kind_at_debt`: so `h.Kind
    L .K10`.
Limits. BOOK-KEEPING. `K10Debt` IS THE DEBT: no member is known. law still names a part of the
conclusion (`GoodIn`), with the first tie beside it. AT OnBytes.secondHashFunction ALONE. The three flat lists'
heads are premises. Nothing on soundness.

-/
import Johnson.P5J.K10Low
import Johnson.LPFE1R.K10HeadOpenAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start fenceFit)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.First.Close (OutF)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
/-- The first chain's frame at the seated term. -/
local notation "FR" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

set_option quotPrecheck false in
/-- The first chain's pieces' type. -/
local notation "PC" => Piece (ckP .two) FR (ProofFile.InstPub × TS) ProofFile.Cl
  (Wit (CellsM numsFull) At.Tok MsgT)

set_option quotPrecheck false in
/-- Its statements' type. -/
local notation "ST" => (ProofFile.InstPub × TS) × (Frame.E FR).Str

/-- **K10's DEBT AT THE CLOSED CONSTANT.** -/
structure AtMgA.K10Debt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok) : Prop where
  /-- a rider reads of the witness only what the table says: no kind's -/
  reads : ∀ (i : ℕ) (a : Place), At.ps[i]? = some a → a.kind = KindName.K10 →
    ReadsOkAtQR (Fr := FR) (At.arr Zp) (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a)
      h.toAtMg.rch i
  /-- what riders read is clear of what rows lay: the table's -/
  clear : RidersClearQ (At.arr Zp) (At.N Zp cF) fullLinks At.ps
  /-- the table's test on its numbers: every sampled tenant's tree is sent in front -/
  fenFit : fenceFit (At.N Zp cF) fullLinks At.ps = true
  /-- what is kept lies in its group -/
  kept : ∀ (i : ℕ) (a : Place), At.ps[i]? = some a → a.kind = KindName.K10 →
    ∀ t ∈ (At.N Zp cF).keptOf (a.link.getD 0), t ∈ (At.N Zp cF).group (a.link.getD 0)
  /-- at a reached state the index masks' message is a member of no group -/
  fence : ∀ (i : ℕ) (a : Place), At.ps[i]? = some a → a.kind = KindName.K10 →
    ∀ s : ST, h.toAtMg.rch i s → OutF s.1.2
  /-- the piece's law at the pick, and the first tie, at one condition in front -/
  law : ∀ (i : ℕ) (q : PC) (a : Place), (h.toAtMg.row L)[i]? = some q → At.ps[i]? = some a →
    a.kind = KindName.K10 →
    ∃ o : ST → Prop, (q.withMap (h.toAtMg.ex L i)).GoodIn o (fun _ => True)
        (relAt (meansQ (Fr := FR) (At.N Zp cF) (mgAtAll h) fun a => a) (insQ fullLinks At.ps i))
        (relAt (meansQ (Fr := FR) (At.N Zp cF) (mgAtAll h) fun a => a)
          (outsQ fullLinks At.ps i)) ∧
      ∀ s : ST, onQ (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) i s →
        h.toAtMg.rch i s → ¬ s.1.2.failed ≠ none → o s

/-- **The debt gives what was left.** -/
theorem k10_left_of_debt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q1 : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q2 : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q3 : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) (W : h.K10Debt L) :
    h.K10Left L :=
  have low : ∀ (i : ℕ) (q : PC) (a : Place), (h.toAtMg.row L)[i]? = some q → At.ps[i]? = some a →
      a.kind = KindName.K10 → (At.N Zp cF).treesAt At.ps[i]? ≤ q.base :=
    fun i q a hq ha hk => k10_low_at h L q1 q2 q3 i a ha hk q hq
  ⟨W.reads, W.clear, W.fenFit, low, W.kept, W.fence, W.law,
    k10_ride_closed h L q1 q2 q3 W.fenFit low W.fence⟩

/-- **THE FIELD, FROM THE DEBT.** -/
theorem k10_kind_at_debt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q1 : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q2 : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q3 : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) (W : h.K10Debt L) :
    h.Kind L .K10 :=
  k10_kind_at_left h L q1 q2 q3 (k10_left_of_debt h L q1 q2 q3 W)

end P5J

#print axioms P5J.k10_left_of_debt
#print axioms P5J.k10_kind_at_debt
