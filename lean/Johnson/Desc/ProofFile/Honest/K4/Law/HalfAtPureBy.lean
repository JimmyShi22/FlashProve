-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/HalfAtPureBy.lean: CONDITIONAL.

What is here. `half_atPure` (Law/HalfAtPure.lean) WITH A WEAKER HYPOTHESIS ON THE FILLING's LIST OF
LOTS. What it finds: the first entry of A.H.first at the place `IM.k4Place g` is `k4Half …`, K4's
own half: A the honest prover that the frame's maker `onlineProverFromPublicFiles` returns at the public files of h, the
place that of the member of the feed-forward layers' own rounds (sub-protocol K4). That equation is
the hypothesis named half of `k4_accepted_dear` (Law/DearTop.lean). There hL asks that K4's lot
`k4HLot cells weights look` itself is a member of the list. Here it is enough that SOME lot of the
list has, at the maker's own public part and ground, the halves that K4's lot has there. It is meant
for a filling that wraps K4's lot, for instance to hand it a reader of the index that is made of the
public part. The frame's `atPure_first_find_kind` (Honest/FirstFindKind.lean) is general in the lot
and reads its halves at that public part and ground alone.

  `half_atPure_at`   **half, at the maker's prover, from a lot M of the list (hM) and its halves at
     the maker's own public part (hE)**
  `half_atPure_by`   the same from ∃ M ∈ P.lots, …; called by `half_widerOwn` (Law/AtWiderLots.lean)
  `half_atPure_mem`   `half_atPure`'s own hypothesis gives the weaker one; no statement calls it yet

Limits. HYPOTHESES, ALL: h · `LaidK4` · hA (the maker returns) · hM, hE · ho (no other lot has a
half at a place of the kind K4); no example of them together is known. THAT ANY FILLING HAS SUCH AN
M: no filling is imported here; that hE holds at a wrapper by unfolding is not held by this file.
THE FULL SIZE ALONE, and the format's second hash function alone. Beneath it stand comparisons by Lean's own
kernel that no independent checker has replayed (Law/FitsMember.lean's head counts them). A LAW, NOT
A PART: it rests on modules under Johnson/Goal/: no file that defines a part of the proof file's
description may import this one.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.HalfAtPure

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Block)
open P5J (AtMgA TS)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Tr X₀ X' : Type}

/-- **half, AT THE MAKER's PROVER, FROM THE HALVES AT THE MAKER's OWN PUBLIC PART.** hM, hE: a lot M
of the filling has there the halves of K4's lot. CONDITIONAL: on h, `LaidK4`, hA, hM, hE and ho. THE
FULL SIZE ALONE (h). -/
theorem half_atPure_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) {P : OnlineProverParts W₀ Rc Tr X₀ X'}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'} (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → Forest.Heard)
    {M : HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X'} (hM : M ∈ P.lots)
    (hE : M.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G)
    (ho : ∀ M' ∈ P.lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G) :
    A.H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half cells weights k4Tokens (look Zp A.G) (k4PubAt cF k x)) := by
  obtain ⟨hZ, hG, -⟩ := atPure_ok hA
  have eZ : A.Z = Zp := Except.ok.inj (hZ.symm.trans h.laid.pub)
  obtain ⟨G₀, hG₀, hx⟩ := Lh.lot
  have eG : G₀ = A.G := Option.some.inj (hG₀.symm.trans (eZ ▸ hG))
  subst eG
  refine atPure_first_find_kind hA hM (fun M' hM' => ?_) ?_
  · rw [hE]
    exact ho M' hM'
  · rw [hE, eZ]
    exact lot_half_head h Lh cells weights look hx

/-- The same from ∃ M ∈ P.lots, …. CONDITIONAL: as `half_atPure_at`. -/
theorem half_atPure_by (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) {P : OnlineProverParts W₀ Rc Tr X₀ X'}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'} (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → Forest.Heard)
    (hL : ∃ M ∈ P.lots, M.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G)
    (ho : ∀ M' ∈ P.lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G) :
    A.H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half cells weights k4Tokens (look Zp A.G) (k4PubAt cF k x)) := by
  obtain ⟨M, hM, hE⟩ := hL
  exact half_atPure_at h Lh hA cells weights look hM hE ho

/-- `half_atPure`'s own hypothesis gives the weaker one. -/
theorem half_atPure_mem {P : OnlineProverParts W₀ Rc Tr X₀ X'} (A : OnlineProverWithDescription W₀ Rc Tr X₀ X')
    {cells : Tr → Cells} {weights : W₀ → Weights}
    {look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → Forest.Heard}
    (hL : k4HLot cells weights look ∈ P.lots) :
    ∃ M ∈ P.lots, M.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G :=
  ⟨_, hL, rfl⟩

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.half_atPure_at
#print axioms ProofFile.Honest.K4.half_atPure_by
#print axioms ProofFile.Honest.K4.half_atPure_mem
