-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/K10HeadOpenAt.lean: HeadOpen AT K10's ACCEPTING STEP, AT THE CLOSED
CONSTANT; AND SO THE FIELD "ride" OF AtMgA.K10Left FROM THREE OTHER FIELDS OF THAT STRUCTURE ALONE.
Theorems with their proofs.

  out_k10          K10's accepting step leaves s.out
  tokHOf_of_out    the meant reader of the heard token (P5J.tokHOf) reads s.out alone
  P5J.k10_headOpen_at   HeadOpen h.𝔇 Op (R10 ‹a frame› base), at every Op, frame and base: by
                   headPartK6_goesBack (Johnson/Desc/Kinds/Law/HeadPartsGoBack.lean): over R10
                   the public part stays, so the request's reader answers alike (by definition at
                   h.𝔇); s.out stays, so the heard token does
  P5J.k10_ride_closed   **K10Left's field ride, to the letter, from fenFit · low · fence**

Limits. fenFit, low and fence stay fields of the debt. At OnBytes.secondHashFunction. The full size alone. No
soundness statement.

-/
import Johnson.LPFE1R.K10RideAt
import Johnson.Desc.Kinds.Law.HeadPartsGoBack
import Johnson.P5J.TokTerms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (K10Step)

theorem out_k10 {s t : S} (h : K10Step s t) : t.out = s.out := by
  obtain ⟨es, rs, x, _, rfl⟩ := h
  exact (First.Close.putRec_keeps s _).2.2.2.1

/-- The meant reader of the heard token reads s.out alone. -/
theorem tokHOf_of_out {P : Type} {a b : P × S} (h : b.2.out = a.2.out) :
    P5J.tokHOf a = P5J.tokHOf b := by
  unfold P5J.tokHOf P5J.tokOfHeard First.S.heardTok? First.S.heard
  rw [h]

end VerifiableInference.Desc.LinkJoin

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers Item start fenceFit)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.First.Close (OutF)
open VerifiableInference.Desc.LinkJoin (R10 tokHOf_of_out out_k10)
open VerifiableInference.Desc.Kinds.Head.Law (headPartK6_goesBack)
open Johnson.Desc.First.Walk.Tied (HeadOpen)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **HeadOpen at K10's accepting step, at the closed constant.** -/
theorem k10_headOpen_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Op : Item → Prop)
    (F : Frame) (base : ℕ) : HeadOpen h.𝔇 Op (R10 F base) := by
  intro p _ i
  refine headPartK6_goesBack _ _ _ _ _ _ _ _ _ _ _ _ (R10 F base) (fun a y b y' hr => ?_) p
    (fun _ a y b y' hr => tokHOf_of_out (out_k10 hr.2.1)) i
  obtain ⟨za, sa⟩ := a
  obtain ⟨zb, sb⟩ := b
  obtain rfl : zb = za := hr.1
  rfl

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

/-- **K10Left's FIELD ride, FROM THREE OTHER FIELDS OF THAT STRUCTURE ALONE.** -/
theorem k10_ride_closed (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q1 : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q2 : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q3 : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (fenFit : fenceFit (At.N Zp cF) fullLinks At.ps = true)
    (low : ∀ (i : ℕ) (q : PC) (a : Place), (h.toAtMg.row L)[i]? = some q → At.ps[i]? = some a →
      a.kind = KindName.K10 → (At.N Zp cF).treesAt At.ps[i]? ≤ q.base)
    (fence : ∀ (i : ℕ) (a : Place), At.ps[i]? = some a → a.kind = KindName.K10 →
      ∀ s : ST, h.toAtMg.rch i s → OutF s.1.2) :
    ∀ (i : ℕ) (q : PC) (a : Place), (h.toAtMg.row L)[i]? = some q → At.ps[i]? = some a →
    a.kind = KindName.K10 →
    ∀ (s : ST) τ (b : ST) w j, onQ (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) i s →
      h.toAtMg.rch i s → s.1.2.failed = none → q.ior.red.out s τ = some b →
      onQ (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) (i + 1) b →
      openAfter (insQ fullLinks At.ps) (outsQ fullLinks At.ps) (· ∈ start fullLinks) i j →
      ¬ insQ fullLinks At.ps i j →
      meansQ (At.N Zp cF) (mgAtAll h) (fun a => a) j b w →
      meansQ (At.N Zp cF) (mgAtAll h) (fun a => a) j s w :=
  k10_ride_at h L q1 q2 q3 fenFit low fence fun _ q _ _ _ _ => k10_headOpen_at h _ FR q.base

end P5J

#print axioms VerifiableInference.Desc.LinkJoin.out_k10
#print axioms P5J.k10_headOpen_at
#print axioms P5J.k10_ride_closed
