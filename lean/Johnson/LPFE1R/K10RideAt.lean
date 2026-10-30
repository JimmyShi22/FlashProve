-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/K10RideAt.lean: AT THE CLOSED CONSTANT (mgAtAll h): THE
FIELD "ride" OF AtMgA.K10Left (Johnson/P5J/K10Left.lean), TO THE LETTER, FROM THREE OTHER FIELDS OF
THAT STRUCTURE (fenFit · low · fence) AND ONE NAMED PREMISE (HeadOpen). Theorems with their proofs;
one test on the written list, by the kernel.

  lowItem_of_sampled  an open item's pins' trees lie below base where every sampled tenant's does
  k10Only_full, k10At_of_kind   BY THE KERNEL: a place of the kind K10 in the written full list
                   stands at one of K10's 25 numbers
  low_at_k10       lowItem at every rider at these numbers, from fenceFit and "the plan's count of
                   trees at the place is at most base" (fence_of_fit)
  links_are, places_are   fullLinks | At.ps are linksFull | plF
  P5J.k10_ride_at  **THE FIELD ride**: by k10_ride_full (Link/Law/RidersAtK10.lean) at 𝔇 := h.𝔇,
                   Mg := mgBase: hstep by k10_step_at · hidx is the field fence · the
                   three "meant" premises BY DEFINITION at h.𝔇 (rfl, held by Lean here) · lowItem by
                   low_at_k10

Limits. HeadOpen h.𝔇 ‹the riders at i› (R10 ‹the frame› q.base) STAYS: the output head's parts of
"constr" ride at K10's places of the 24 earlier segments; that h.𝔇.headPart goes back over K10's
step is shown in Johnson/LPFE1R/K10HeadOpenAt.lean (P5J.k10_headOpen_at), from the standing
hypotheses (P5J.AtMgA) at OnBytes.secondHashFunction. fenFit, low and fence stay
fields of the debt. At OnBytes.secondHashFunction. The full size alone. No soundness statement.

-/
import Johnson.P5J.K10Left
import Johnson.Desc.First.Link.Law.RidersAtK10

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Numbers start openSets sampledIn fenceFit)
open Johnson.Desc.First.Walk.Tied

theorem lowItem_of_sampled (N : Numbers) (O : List Item) (base : ℕ)
    (h : ∀ x ∈ sampledIn N O, x.1 < base) {j : Item} (hj : j ∈ O) :
    lowItem N (· < base) j := by
  cases j with
  | pin m t => exact fun x hx => h x (List.mem_flatMap.2 ⟨_, hj, hx⟩)
  | pinKept m => exact fun x hx => h x (List.mem_flatMap.2 ⟨_, hj, hx⟩)
  | pinI => exact h _ (List.mem_flatMap.2 ⟨_, hj, List.mem_singleton.2 rfl⟩)
  | pinV => exact h _ (List.mem_flatMap.2 ⟨_, hj, List.mem_singleton.2 rfl⟩)
  | _ => trivial

/-- A test with code: K10's places stand at K10's numbers alone. -/
def k10OnlyB : Bool :=
  (List.range 358).all fun i => (plF[i]?).all fun a => a.kind != KindName.K10 || k10At.contains i

set_option maxRecDepth 1000000 in
theorem k10Only_full : k10OnlyB = true := by decide +kernel

theorem k10At_of_kind {i : ℕ} {a : Place} (ha : plF[i]? = some a) (hk : a.kind = KindName.K10) :
    i ∈ k10At := by
  have hi : i < 358 := by
    have := (List.getElem?_eq_some_iff.1 ha).1
    rwa [length9] at this
  have h := List.all_eq_true.1 k10Only_full i (List.mem_range.2 hi)
  rw [ha] at h
  simpa [hk] using h

/-- **lowItem at every rider at K10's numbers.** -/
theorem low_at_k10 (N : Numbers) (hfen : fenceFit N linksFull plF = true) {k : ℕ}
    (hk : k ∈ k10At) {base : ℕ} (hb : N.treesAt plF[k]? ≤ base) (i : Item)
    (ho : openAfter (insQ linksFull plF) (outsQ linksFull plF) (· ∈ start linksFull) k i) :
    lowItem N (· < base) i :=
  lowItem_of_sampled N _ base (fence_of_fit N linksFull plF hfen k base (k10At_le hk) hb)
    (open_mem9 (k10At_le hk) ho)

theorem links_are : P5J.fullLinks = linksFull := rfl

theorem places_are : P5J.At.ps = plF := rfl

end VerifiableInference.Desc.LinkJoin

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
open VerifiableInference.Desc.LinkJoin (R10 k10_ride_full k10At_of_kind low_at_k10)
open Johnson.Desc.First.Walk.Tied (HeadOpen)

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

/-- **K10Left's FIELD ride, TO THE LETTER.** -/
theorem k10_ride_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q1 : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q2 : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q3 : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (fenFit : fenceFit (At.N Zp cF) fullLinks At.ps = true)
    (low : ∀ (i : ℕ) (q : PC) (a : Place), (h.toAtMg.row L)[i]? = some q → At.ps[i]? = some a →
      a.kind = KindName.K10 → (At.N Zp cF).treesAt At.ps[i]? ≤ q.base)
    (fence : ∀ (i : ℕ) (a : Place), At.ps[i]? = some a → a.kind = KindName.K10 →
      ∀ s : ST, h.toAtMg.rch i s → OutF s.1.2)
    (hH : ∀ (i : ℕ) (q : PC) (a : Place), (h.toAtMg.row L)[i]? = some q → At.ps[i]? = some a →
      a.kind = KindName.K10 →
      HeadOpen h.𝔇 (fun j => openAfter (insQ fullLinks At.ps) (outsQ fullLinks At.ps)
        (· ∈ start fullLinks) i j ∧ ¬ insQ fullLinks At.ps i j) (R10 FR q.base)) :
    ∀ (i : ℕ) (q : PC) (a : Place), (h.toAtMg.row L)[i]? = some q → At.ps[i]? = some a →
    a.kind = KindName.K10 →
    ∀ (s : ST) τ (b : ST) w j, onQ (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) i s →
      h.toAtMg.rch i s → s.1.2.failed = none → q.ior.red.out s τ = some b →
      onQ (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) (i + 1) b →
      openAfter (insQ fullLinks At.ps) (outsQ fullLinks At.ps) (· ∈ start fullLinks) i j →
      ¬ insQ fullLinks At.ps i j →
      meansQ (At.N Zp cF) (mgAtAll h) (fun a => a) j b w →
      meansQ (At.N Zp cF) (mgAtAll h) (fun a => a) j s w := by
  intro i q a hq ha hk
  have hik := k10At_of_kind ha hk
  exact k10_ride_full (F := FR) (Cl := ProofFile.Cl) h.𝔇 mgBase (At.N Zp cF) h.toAtMg.rch hik q.base q
    (k10_step_at h L q1 q2 q3 i a ha hk q hq) (fun s _ hr => fence i a ha hk s hr)
    (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (seats := At.seats Zp) rfl (hH i q a hq ha hk)
    (fun j ho _ => low_at_k10 (At.N Zp cF) fenFit hik (low i q a hq ha hk) j ho)

end P5J

#print axioms VerifiableInference.Desc.LinkJoin.lowItem_of_sampled
#print axioms VerifiableInference.Desc.LinkJoin.k10Only_full
#print axioms VerifiableInference.Desc.LinkJoin.low_at_k10
#print axioms P5J.k10_ride_at
