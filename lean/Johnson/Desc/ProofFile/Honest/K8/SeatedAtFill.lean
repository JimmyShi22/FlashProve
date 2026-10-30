-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/SeatedAtFill.lean: the smallness test (K8): THE RECORD `K8Seated`
(Johnson/Desc/ProofFile/Honest/K8/Seated.lean) AT THE FIRST CHAIN's THREAD AT THE HEAD, AT THE
PROVER THAT THE MAKER `onlineProverFromPublicFiles` BUILDS, AT ALL 25 OF THE KIND's DRAWS. Four theorems; no definition;
none of the library's goals.

  `k8Seated_at_fill.outHead`, `.layers`, `.att`   THERE ARE the ground, the planned link and the
                   thread's member, each tied, with K8Seated ‹the thread at H := A.H› ‹the border›
                   ‹the member› cells ‹the place's numbers, mats at them›
  **`k8Seated_at_fill`**   l < 25 ⊢ the same at (14 * l + (if l = 24 then 5 else 4) + 2): one
                   sentence for the 25
THE PREMISES, ALL FOUR ON THE MAKER AND ITS FILLING, as in
Johnson/Desc/ProofFile/Honest/K8/PlaysAtFill.lean: hA, hex, ho, hlen.
HOW. `k8Seated_at_head.…` (Johnson/Desc/ProofFile/Honest/K8/PlaysAtHead.lean) and
`halfAt_at_fill.…` (Johnson/Desc/ProofFile/Honest/K8/HalfAtFill.lean) name the same ground, planned
link and member: each is tied by an equation: the lines of `playsS_at_fill.…`, WRITTEN A FURTHER
TIME.
One instance is taken away, as in the files beneath. Tactics that search: `omega`, on numbers of
segments alone.
Limits. THE PREMISES ON THE LIST OF LOTS ARE PROVED HERE OF NO FILLING. THAT `onlineProverFromPublicFiles` RETURNS IS A
PREMISE. cells and mats are letters; so are the thread's other letters. No Script, input or coin is
read: the record speaks of the thread's lists and the place's numbers. THE FULL SIZE ALONE, under
the library's head.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.PlaysAtFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Strs Place Claim Block KindName)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First (S)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead WtF Script)

variable {W₀ Rc Tr X₀ X : Type} (cells : Tr → Cells)
  (mats : Pub → Ground → LinkH → Nat → List (Nat × String × Nat))
  {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
  {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
  (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
  (hex : ∃ M ∈ P.lots, M.halves A.Z A.G = (smallLot cells mats).halves A.Z A.G)
  (ho : ∀ M ∈ P.lots, (∀ x ∈ M.halves A.Z A.G, x.place.kind ≠ KindName.K8) ∨
    M.halves A.Z A.G = (smallLot cells mats).halves A.Z A.G)
  (hlen : ∀ (l : ℕ) (Xl : LinkH), A.G.built[l]? = some Xl →
    (mats A.Z A.G Xl l).length = (ProofFile.k8Par A.Z A.G Xl l).ks.length)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
include h hA hex ho hlen

/-- At the output head's draw (border 343). -/
theorem k8Seated_at_fill.outHead :
    ∃ (G₀ : ProofFile.Ground) (Xl : LinkH) (blk : Block S ProofFile.Cl),
      ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ ∧ G₀.built[24]? = some Xl ∧
      K8Seated (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (343) blk cells (ProofFile.k8Par Zp G₀ Xl (24), mats Zp G₀ Xl (24)) := by
  obtain ⟨G₀, Xl, blk, hG, hX, hb, hP⟩ :=
    k8Seated_at_head.outHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
  obtain ⟨G₁, Xl₁, blk₁, hG₁, hX₁, hb₁, hH⟩ :=
    halfAt_at_fill.outHead cells mats h hA hex ho Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
  obtain rfl : G₁ = G₀ := Option.some.inj (hG₁.symm.trans hG)
  obtain rfl : Xl₁ = Xl := Option.some.inj (hX₁.symm.trans hX)
  obtain rfl : blk₁ = blk := Option.some.inj (hb₁.symm.trans hb)
  obtain ⟨hZ, hGA, -⟩ := atPure_ok hA
  have eZ : A.Z = Zp := Except.ok.inj (hZ.symm.trans h.laid.pub)
  rw [eZ] at hGA
  have eG : A.G = G₁ := Option.some.inj (hGA.symm.trans hG)
  have q := hlen _ Xl₁ (by rw [eG]; exact hX)
  rw [eZ, eG] at q
  exact ⟨G₁, Xl₁, blk₁, hG, hX, hP cells _ hH q⟩

/-- At the draw of the layers' segment of group g (border 28 g + 6). -/
theorem k8Seated_at_fill.layers {g : Nat} (hg : g < 12) :
    ∃ (G₀ : ProofFile.Ground) (Xl : LinkH) (blk : Block S ProofFile.Cl),
      ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ ∧ G₀.built[2 * g]? = some Xl ∧
      K8Seated (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (28 * g + 6) blk cells (ProofFile.k8Par Zp G₀ Xl (2 * g), mats Zp G₀ Xl (2 * g)) := by
  obtain ⟨G₀, Xl, blk, hG, hX, hb, hP⟩ :=
    k8Seated_at_head.layers h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hg
  obtain ⟨G₁, Xl₁, blk₁, hG₁, hX₁, hb₁, hH⟩ :=
    halfAt_at_fill.layers cells mats h hA hex ho Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hg
  obtain rfl : G₁ = G₀ := Option.some.inj (hG₁.symm.trans hG)
  obtain rfl : Xl₁ = Xl := Option.some.inj (hX₁.symm.trans hX)
  obtain rfl : blk₁ = blk := Option.some.inj (hb₁.symm.trans hb)
  obtain ⟨hZ, hGA, -⟩ := atPure_ok hA
  have eZ : A.Z = Zp := Except.ok.inj (hZ.symm.trans h.laid.pub)
  rw [eZ] at hGA
  have eG : A.G = G₁ := Option.some.inj (hGA.symm.trans hG)
  have q := hlen _ Xl₁ (by rw [eG]; exact hX)
  rw [eZ, eG] at q
  exact ⟨G₁, Xl₁, blk₁, hG, hX, hP cells _ hH q⟩

/-- At the draw of the attention segment of group g (border 14 (2 g + 1) + 6). -/
theorem k8Seated_at_fill.att {g : Nat} (hg : g < 12) :
    ∃ (G₀ : ProofFile.Ground) (Xl : LinkH) (blk : Block S ProofFile.Cl),
      ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ ∧ G₀.built[2 * g + 1]? = some Xl ∧
      K8Seated (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (14 * (2 * g + 1) + 6) blk cells
        (ProofFile.k8Par Zp G₀ Xl (2 * g + 1), mats Zp G₀ Xl (2 * g + 1)) := by
  obtain ⟨G₀, Xl, blk, hG, hX, hb, hP⟩ :=
    k8Seated_at_head.att h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hg
  obtain ⟨G₁, Xl₁, blk₁, hG₁, hX₁, hb₁, hH⟩ :=
    halfAt_at_fill.att cells mats h hA hex ho Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hg
  obtain rfl : G₁ = G₀ := Option.some.inj (hG₁.symm.trans hG)
  obtain rfl : Xl₁ = Xl := Option.some.inj (hX₁.symm.trans hX)
  obtain rfl : blk₁ = blk := Option.some.inj (hb₁.symm.trans hb)
  obtain ⟨hZ, hGA, -⟩ := atPure_ok hA
  have eZ : A.Z = Zp := Except.ok.inj (hZ.symm.trans h.laid.pub)
  rw [eZ] at hGA
  have eG : A.G = G₁ := Option.some.inj (hGA.symm.trans hG)
  have q := hlen _ Xl₁ (by rw [eG]; exact hX)
  rw [eZ, eG] at q
  exact ⟨G₁, Xl₁, blk₁, hG, hX, hP cells _ hH q⟩

/-- **The record `K8Seated` at the maker's prover, at each of the 25 draws.** No Script, input or
coin is read. -/
theorem k8Seated_at_fill {l : ℕ} (hl : l < 25) :
    ∃ (G₀ : ProofFile.Ground) (Xl : LinkH) (blk : Block S ProofFile.Cl),
      ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ ∧ G₀.built[l]? = some Xl ∧
      K8Seated (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (14 * l + (if l = 24 then 5 else 4) + 2) blk cells
        (ProofFile.k8Par Zp G₀ Xl l, mats Zp G₀ Xl l) := by
  by_cases h24 : l = 24
  · subst h24
    exact k8Seated_at_fill.outHead cells mats h hA hex ho hlen Q test carryX item n₁ n₂ b₀ Vd Rd Kp
      w
  · rw [if_neg h24]
    rcases Nat.even_or_odd' l with ⟨g, rfl | rfl⟩
    · have e : 14 * (2 * g) + 4 + 2 = 28 * g + 6 := by omega
      rw [e]
      exact k8Seated_at_fill.layers cells mats h hA hex ho hlen Q test carryX item n₁ n₂ b₀ Vd Rd
        Kp w (by omega)
    · have e : 14 * (2 * g + 1) + 4 + 2 = 14 * (2 * g + 1) + 6 := by omega
      rw [e]
      exact k8Seated_at_fill.att cells mats h hA hex ho hlen Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
        (by omega)

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.k8Seated_at_fill.outHead
#print axioms ProofFile.Honest.K8.k8Seated_at_fill.layers
#print axioms ProofFile.Honest.K8.k8Seated_at_fill.att
#print axioms ProofFile.Honest.K8.k8Seated_at_fill
