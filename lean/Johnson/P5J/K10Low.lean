-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K10Low.lean: TWO MORE DEBTS OF K10's CONDITION AT THE CLOSED CONSTANT FALL BY CALLS OF
OTHER FILES' KIND-FREE LEMMAS: the field low of `AtMgA.K10Left` (Johnson/P5J/K10Left.lean), and the
premise hcap of `k10_law_withMap` (Johnson/Desc/First/Close/Law/KindK10Law.lean). Statements and
proofs; one evaluation by the kernel.

What is said, at h : AtMgA OnBytes.secondHashFunction .., under the three flat lists' heads:
  `k10_not_last`: no place of the kind K10 in `At.ps` has a number above 356: by the kernel.
  `k10_base_at`: at a place i of the kind K10 the seated term's piece's first tree IS the constant's
    numbers' count of trees at that place: q.base = (At.N Zp cF).treesAt At.ps[i]?. By `atRow_more`,
    `atRow_blocks`, `atRow_told`, `atRow_in` (Johnson/Desc/Kinds/Law/RowAtConst.lean,
    RowLenAtConst.lean), `base_treesAt` (Johnson/Desc/Sound/PieceFence.lean) and `bookFit_withTold`
    (Johnson/Desc/First/BookFitTold.lean). `k10_low_at`: so the field low.
  `k10_cap_at`: that piece's error is the cap of 128 bits a round at its own rounds' data.
Limits. AT OnBytes.secondHashFunction ALONE. The three flat lists' heads are premises. Calls; nothing on the
laws. Nothing on soundness.

-/
import Johnson.P5J.K10Left
import Johnson.Desc.Kinds.Law.RowAtConst
import Johnson.Desc.Kinds.Law.RowLenAtConst
import Johnson.Desc.Sound.PieceFence
import Johnson.Desc.First.BookFitTold

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start bookFit bookFit_withTold)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ
open _root_.Iop (Err)
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.Kinds.Head.Law (atRow_more atRow_blocks atRow_told atRow_in
  ps_length)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

theorem k10_not_last_all : ((List.range 358).all fun i => (At.ps[i]?).all fun a =>
    a.kind != KindName.K10 || decide (i < 357)) = true := by decide +kernel

/-- No place of the kind K10 is the last. -/
theorem k10_not_last (i : ℕ) (a : Place) (ha : At.ps[i]? = some a)
    (hk : a.kind = KindName.K10) : i < 357 := by
  have hi : i < 358 := ps_length ▸ (List.getElem?_eq_some_iff.1 ha).1
  have h := List.all_eq_true.1 k10_not_last_all i (List.mem_range.2 hi)
  rw [ha] at h
  simpa [hk] using h

/-- **The seated piece's first tree is the table's own count at the place.** -/
theorem k10_base_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q1 : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q2 : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q3 : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) (i : ℕ) (a : Place)
    (ha : At.ps[i]? = some a) (hk : a.kind = KindName.K10) :
    ∀ q, (h.toAtMg.row L)[i]? = some q → q.base = (At.N Zp cF).treesAt At.ps[i]? := by
  intro q hq
  have hM := (atRow_more h.toAtMg L q1 q2 q3 i q hq
    (atRow_in h.toAtMg i (k10_not_last i a ha hk))).1
  have hfit : bookFit (At.N Zp cF) At.ps (VerifiableInference.Desc.Sound.toldOf
      (cF.blocksInOrder.map (held (P := ProofFile.InstPub)))) =
      true := by
    rw [atRow_told]
    exact bookFit_withTold _ At.ps (VerifiableInference.Desc.Sound.toldOf cF.blocksInOrder)
      (ProofFile.Law.flatPlaces_nodup fullLinks true)
  exact base_treesAt hM (atRow_blocks h.toAtMg) (At.N Zp cF) At.ps hfit
    (Nat.le_of_lt (List.getElem?_eq_some_iff.1 ha).1)

/-- **The field low.** -/
theorem k10_low_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q1 : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q2 : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q3 : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) (i : ℕ) (a : Place)
    (ha : At.ps[i]? = some a) (hk : a.kind = KindName.K10) :
    ∀ q, (h.toAtMg.row L)[i]? = some q → (At.N Zp cF).treesAt At.ps[i]? ≤ q.base :=
  fun q hq => Nat.le_of_eq (k10_base_at h L q1 q2 q3 i a ha hk q hq).symm

/-- **The seated piece's error is the cap of 128 bits a round.** -/
theorem k10_cap_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q1 : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q2 : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q3 : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) (i : ℕ) (a : Place)
    (ha : At.ps[i]? = some a) (hk : a.kind = KindName.K10) :
    ∀ q, (h.toAtMg.row L)[i]? = some q → q.err = Err.cap 128 (uLT (ckP .two) q.ds) :=
  fun q hq => (atRow_more h.toAtMg L q1 q2 q3 i q hq
    (atRow_in h.toAtMg i (k10_not_last i a ha hk))).2

end P5J

#print axioms P5J.k10_not_last
#print axioms P5J.k10_base_at
#print axioms P5J.k10_low_at
#print axioms P5J.k10_cap_at
