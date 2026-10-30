-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K10Left.lean: WHAT IS LEFT OF K10's NAMED CONDITION AT THE CLOSED CONSTANT, AT THE
CONCRETE SECOND HASH FUNCTION, ONCE WHAT LIES IS CALLED. A definition, statements and proofs:
calls; no more. Beside Johnson/P5J/K10Owes.lean, K10Asks.lean, K10Seat.lean.

What is said, at h : AtMgA OnBytes.secondHashFunction ..:
  `AtMgA.K10Left h L`: THE DEBT: three sentences that are no kind's: reads (`ReadsOkAtQR` at K10's
    places), clear (`RidersClearQ`), fenFit (`fenceFit`'s yes at the constant's numbers); and at
    each place i of the kind K10, at the piece q of the seated term's first row: low (the plan's
    count of trees at the place is at most q.base); kept (what is kept lies in its group); fence
    ("reached" gives: the index masks' message is a member of no group); law and front at one
    condition in front o (the piece's law at the pick; the first tie); ride (what rides past holds
    in front if it holds behind, of one witness).
  `k10_owes_of_left`: under the three flat lists' heads: it gives `h.K10Owes L`: the fields asks,
    dec, trees, msgs, step of `K10OwesAt` are PAID: `k10_asks_at`, `k10_dec_at` (K10Asks.lean),
    `k10_counts_at`, `k10_step_at` (K10Seat.lean). `k10_kind_at_left`: so `h.Kind L .K10`.
Limits. BOOK-KEEPING. `K10Left` IS THE DEBT: no member is known. law still names a part of the
conclusion (`GoodIn`). AT OnBytes.secondHashFunction ALONE. The three flat lists' heads are premises, as in the
tower's own rows. Nothing on soundness.

-/
import Johnson.P5J.K10Asks
import Johnson.P5J.K10Seat

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

/-- **WHAT IS LEFT OF K10's CONDITION AT THE CLOSED CONSTANT.** -/
structure AtMgA.K10Left (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok) : Prop where
  /-- a rider reads of the witness only what the table says: no kind's -/
  reads : ∀ (i : ℕ) (a : Place), At.ps[i]? = some a → a.kind = KindName.K10 →
    ReadsOkAtQR (Fr := FR) (At.arr Zp) (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a)
      h.toAtMg.rch i
  /-- what riders read is clear of what rows lay: the table's -/
  clear : RidersClearQ (At.arr Zp) (At.N Zp cF) fullLinks At.ps
  /-- the table's test on its numbers: every sampled tenant's tree is sent in front -/
  fenFit : fenceFit (At.N Zp cF) fullLinks At.ps = true
  /-- the plan's count of trees at the place is at most the piece's first tree -/
  low : ∀ (i : ℕ) (q : PC) (a : Place), (h.toAtMg.row L)[i]? = some q → At.ps[i]? = some a →
    a.kind = KindName.K10 → (At.N Zp cF).treesAt At.ps[i]? ≤ q.base
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
  /-- what rides past holds in front if it holds behind, of one witness -/
  ride : ∀ (i : ℕ) (q : PC) (a : Place), (h.toAtMg.row L)[i]? = some q → At.ps[i]? = some a →
    a.kind = KindName.K10 →
    ∀ (s : ST) τ (b : ST) w j, onQ (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) i s →
      h.toAtMg.rch i s → s.1.2.failed = none → q.ior.red.out s τ = some b →
      onQ (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) (i + 1) b →
      openAfter (insQ fullLinks At.ps) (outsQ fullLinks At.ps) (· ∈ start fullLinks) i j →
      ¬ insQ fullLinks At.ps i j →
      meansQ (At.N Zp cF) (mgAtAll h) (fun a => a) j b w →
      meansQ (At.N Zp cF) (mgAtAll h) (fun a => a) j s w

/-- **What is left gives the condition's second form.** -/
theorem k10_owes_of_left (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q1 : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q2 : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q3 : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) (W : h.K10Left L) :
    h.K10Owes L := by
  refine ⟨W.reads, W.clear, fun i q a hq ha hk => ?_⟩
  obtain ⟨o, hlaw, hfront⟩ := W.law i q a hq ha hk
  obtain ⟨ht, hm⟩ := k10_counts_at h i a ha hk
  exact ⟨o, OutF, q.base, hlaw, hfront, W.fence i a ha hk,
    k10_asks_at h W.fenFit i q.base a ha hk (W.low i q a hq ha hk),
    fun z s s' y y' _ hB => k10_dec_at h q.base z s s' y y' hB,
    fun p hp => by
      obtain rfl : a = p := Option.some.inj (ha.symm.trans hp)
      exact W.kept i a ha hk,
    ht, hm, W.ride i q a hq ha hk, k10_step_at h L q1 q2 q3 i a ha hk q hq⟩

/-- **THE FIELD, FROM WHAT IS LEFT.** -/
theorem k10_kind_at_left (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q1 : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q2 : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q3 : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) (W : h.K10Left L) :
    h.Kind L .K10 :=
  k10_kind_at_owes h L (k10_owes_of_left h L q1 q2 q3 W)

end P5J

#print axioms P5J.k10_owes_of_left
#print axioms P5J.k10_kind_at_left
