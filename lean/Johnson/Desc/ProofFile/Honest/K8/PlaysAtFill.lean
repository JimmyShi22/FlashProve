-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/PlaysAtFill.lean: THE SMALLNESS TEST: THE DEBT "IT PLAYS"
(`PlaysS`, Johnson/Desc/ProofFile/Honest/Thread/PaysS.lean) AT THE FIRST CHAIN's THREAD AT THE HEAD,
AT THE PROVER THAT THE MAKER `onlineProverFromPublicFiles` BUILDS, AT ALL 25 OF THE KIND's DRAWS, AT WHATEVER IS SAID:
THE DEBT STANDS BARE, under no "there are". Four theorems; no definition; none of the library's
goals.

  `playsS_at_fill.outHead`, `.layers`, `.att`   PlaysS ‹the thread at H := A.H› Said ‹the border›:
                   343 · 28 g + 6 · 14 (2 g + 1) + 6
  **`playsS_at_fill`**   l < 25 ⊢ PlaysS ‹the thread at H := A.H› Said
                   (14 * l + (if l = 24 then 5 else 4) + 2): one sentence for the 25
THE PREMISES, ALL FOUR ON THE MAKER AND ITS FILLING: the maker returns A at a filling P, at the
head's own three files · some lot of P.lots has, at A.Z and A.G, the halves of `smallLot cells
mats` · every lot of P.lots has there halves at places of other kinds than K8 alone, or these halves
· at each planned link of A.G mats yields a list with one entry for each matrix of the link (as
long as the place's list `ks`).
HOW. `playsS_at_head.…` (Honest/K8/PlaysAtHead.lean) and `halfAt_at_fill.…`
(Honest/K8/HalfAtFill.lean) name the same ground, planned link and member: each is tied by an
equation.
ONE LINE TAKES AN INSTANCE AWAY (attribute [-instance] Inst.Model.Scl.ref), as the files beneath do.
TACTICS THAT SEARCH: `omega`, on numbers of segments alone.
Limits. THE PREMISES ON THE LIST OF LOTS ARE PROVED HERE OF NO FILLING: the filling `widerFill`
(Johnson/Desc/ProofFile/Honest/AtPureWider.lean) lays `smallLot id (fun _ G _ l => K3.matsOwn G.W
l)` as a lot, so the first holds there by membership; the second is not proved here; the lists'
lengths follow there where the lookup's own list of matrices at l is the planned link's
(`matsOwn_meets`, Johnson/Desc/ProofFile/Honest/K8/MatsMeet.lean): not called here. THAT `onlineProverFromPublicFiles`
RETURNS IS A PREMISE. cells and mats are letters; so are the thread's other letters. THE FULL SIZE
ALONE, under the library's head (h : `P5J.AtMgA`). The files under Johnson/Desc/ProofFile/Honest/
that this head names are files that the library may not hold.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.PlaysAtHead
import Johnson.Desc.ProofFile.Honest.K8.HalfAtFill

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
include hA hex ho hlen

/-- **It plays, at the output head's draw, at the maker's prover.** -/
theorem playsS_at_fill.outHead
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    PlaysS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (343) := by
  obtain ⟨G₀, Xl, blk, hG, hX, hb, hP⟩ :=
    playsS_at_head.outHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
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
  exact hP cells _ hH q

/-- **It plays, at a layers' segment's draw, at the maker's prover.** -/
theorem playsS_at_fill.layers
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {g : Nat} (hg : g < 12) :
    PlaysS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (28 * g + 6) := by
  obtain ⟨G₀, Xl, blk, hG, hX, hb, hP⟩ :=
    playsS_at_head.layers h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hg
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
  exact hP cells _ hH q

/-- **It plays, at an attention segment's draw, at the maker's prover.** -/
theorem playsS_at_fill.att
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {g : Nat} (hg : g < 12) :
    PlaysS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * (2 * g + 1) + 6) := by
  obtain ⟨G₀, Xl, blk, hG, hX, hb, hP⟩ :=
    playsS_at_head.att h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hg
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
  exact hP cells _ hH q

/-- **IT PLAYS AT ALL 25 DRAWS.** -/
theorem playsS_at_fill (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {l : ℕ}
    (hl : l < 25) :
    PlaysS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + (if l = 24 then 5 else 4) + 2) := by
  by_cases h24 : l = 24
  · subst h24
    exact playsS_at_fill.outHead cells mats h hA hex ho hlen Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
      Said
  · rw [if_neg h24]
    rcases Nat.even_or_odd' l with ⟨g, rfl | rfl⟩
    · have e : 14 * (2 * g) + 4 + 2 = 28 * g + 6 := by omega
      rw [e]
      exact playsS_at_fill.layers cells mats h hA hex ho hlen Q test carryX item n₁ n₂ b₀ Vd Rd Kp
        w Said (by omega)
    · have e : 14 * (2 * g + 1) + 4 + 2 = 14 * (2 * g + 1) + 6 := by omega
      rw [e]
      exact playsS_at_fill.att cells mats h hA hex ho hlen Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
        Said (by omega)

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.playsS_at_fill.outHead
#print axioms ProofFile.Honest.K8.playsS_at_fill.layers
#print axioms ProofFile.Honest.K8.playsS_at_fill.att
#print axioms ProofFile.Honest.K8.playsS_at_fill
