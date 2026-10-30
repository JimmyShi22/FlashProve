-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/HalfAtFill.lean: THE SMALLNESS TEST: "THE PROVER's HALF AT THE
DRAW's PLACE IS THE KIND's" (`HalfAt`, Johnson/Desc/ProofFile/Honest/K8/AcceptedAtHead.lean), AT THE
PROVER THAT THE MAKER `onlineProverFromPublicFiles` BUILDS AT ANY FILLING, AT EACH OF THE KIND's 25 DRAWS: FROM "THE
MAKER RETURNS" AND TWO PREMISES ON THE FILLING's LIST OF LOTS. Five theorems; no definition; none
of the library's goals.

  `find_zip`   on a list alone: the search by the place of segment n + l among the halves that the
                   lot's honest side makes of a list of planned links, counted from n, finds the
                   half of the link at l
  **`k8_half_any_fill`**   general in the size: the maker returns A at a filling P · some lot of
                   P.lots has, at A.Z and A.G, the halves of `smallLot cells mats` · every lot of
                   P.lots has there halves at places of other kinds than K8 alone, or these halves ·
                   A.G has the planned link Xl at l ⊢ the search by the draw's place in A.H.first
                   finds `smallHalf cells (k8Par A.Z A.G Xl l, mats A.Z A.G Xl l)`
  **`halfAt_at_fill.outHead`**, **`.layers`**, **`.att`**   under the library's head, at the head's
                   own three files: THERE ARE the ground, the planned link and the thread's member,
                   each tied, with HalfAt ‹the thread at H := A.H› ‹the member› cells ‹the place's
                   numbers, mats at them›
HOW. `atPure_ok` (Johnson/Desc/ProofFile/Honest/AtPureLaw.lean), `atPure_first_find_kind`
(Johnson/Desc/ProofFile/Honest/FirstFindKind.lean). KIN, NOT CALLED: the like for the merge
(Johnson/Desc/ProofFile/Honest/K11/Plays/HalfAtAnyFill.lean) and for the code switch
(Johnson/Desc/ProofFile/Honest/K2/Law/HalfAtPure.lean) · the member's place:
it is laid alone at its written address (`IM.k8_of_head`, `IM.k8_of_layers`, `IM.k8_of_attention`,
Johnson/IMR/K8Seat.lean).
ONE LINE TAKES AN INSTANCE AWAY (attribute [-instance] Inst.Model.Scl.ref), as the files beneath do.
TACTICS THAT SEARCH: `omega` and `simp`, on numbers of segments and on lists' first members alone.
Limits. THE TWO PREMISES ON THE LIST ARE PROVED HERE OF NO FILLING: the filling `widerFill`
(Johnson/Desc/ProofFile/Honest/AtPureWider.lean) lays `smallLot id (fun _ G _ l => K3.matsOwn G.W
l)` as a lot, so the first holds there by membership; the second is not proved here. THAT `onlineProverFromPublicFiles`
RETURNS IS A PREMISE. cells and mats are letters. THE FULL SIZE ALONE in the last three, under the
library's head (h : `P5J.AtMgA`). The files under Johnson/Desc/ProofFile/Honest/ that this head
names are files that the library may not hold.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.AcceptedAtHead
import Johnson.Desc.ProofFile.Honest.FirstFindKind

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

section
variable {W₀ Rc Xi Tr X : Type} (cells : Tr → Cells)
  (mats : Pub → Ground → LinkH → Nat → List (Nat × String × Nat)) (Z : Pub) (G : Ground)

/-- The search by a segment's place among the lot's halves. -/
theorem find_zip : ∀ (xs : List LinkH) (n l : ℕ) (Xl : LinkH), xs[l]? = some Xl →
    (((xs.zipIdx n).map fun y =>
      (smallHalf cells (k8Par Z G y.1 y.2, mats Z G y.1 y.2) :
        Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)).find? fun g =>
      g.place == ⟨1, some (n + l), (k8Par Z G Xl (n + l)).piece, .K8⟩) =
      some (smallHalf cells (k8Par Z G Xl (n + l), mats Z G Xl (n + l)))
  | [], _, _, _, h => by simp at h
  | x :: xs, n, 0, Xl, h => by
    obtain rfl : x = Xl := by simpa using h
    rw [List.zipIdx_cons, List.map_cons]
    exact List.find?_cons_of_pos (by exact beq_self_eq_true _)
  | x :: xs, n, l + 1, Xl, h => by
    have h' : xs[l]? = some Xl := by simpa using h
    rw [List.zipIdx_cons, List.map_cons, List.find?_cons_of_neg]
    · have e : n + (l + 1) = n + 1 + l := by omega
      rw [e]
      exact find_zip xs (n + 1) l Xl h'
    · intro hb
      have e := congrArg Place.link (eq_of_beq hb)
      have e' : n = n + (l + 1) := Option.some.inj e
      omega

end

section
variable {W₀ Rc Tr X₀ X : Type} (cells : Tr → Cells)
  (mats : Pub → Ground → LinkH → Nat → List (Nat × String × Nat))

/-- **At the prover that the maker builds, at any filling.** -/
theorem k8_half_any_fill {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {P : OnlineProverParts W₀ Rc Tr X₀ X}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A)
    (hex : ∃ M ∈ P.lots, M.halves A.Z A.G = (smallLot cells mats).halves A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ x ∈ M.halves A.Z A.G, x.place.kind ≠ KindName.K8) ∨
      M.halves A.Z A.G = (smallLot cells mats).halves A.Z A.G)
    {l : ℕ} {Xl : LinkH} (hX : A.G.built[l]? = some Xl) :
    (A.H.first.find? fun g => g.place == ⟨1, some l, (k8Par A.Z A.G Xl l).piece, .K8⟩) =
      some (smallHalf cells (k8Par A.Z A.G Xl l, mats A.Z A.G Xl l)) := by
  obtain ⟨M, hM, eM⟩ := hex
  refine atPure_first_find_kind hA hM (fun N hN => by rw [eM]; exact ho N hN) ?_
  rw [eM]
  have q := find_zip (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) cells mats A.Z A.G
    A.G.built.toList 0 l Xl (by rw [Array.getElem?_toList]; exact hX)
  rw [Nat.zero_add] at q
  exact q

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
  {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
  (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
  (hex : ∃ M ∈ P.lots, M.halves A.Z A.G = (smallLot cells mats).halves A.Z A.G)
  (ho : ∀ M ∈ P.lots, (∀ x ∈ M.halves A.Z A.G, x.place.kind ≠ KindName.K8) ∨
    M.halves A.Z A.G = (smallLot cells mats).halves A.Z A.G)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
include hA hex ho

/-- **The half at the output head's draw.** -/
theorem halfAt_at_fill.outHead :
    ∃ (G₀ : ProofFile.Ground) (Xl : LinkH) (blk : Block S ProofFile.Cl),
      ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ ∧ G₀.built[24]? = some Xl ∧
      (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[343]? =
        some blk ∧
      HalfAt (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread blk cells
        (ProofFile.k8Par Zp G₀ Xl (24), mats Zp G₀ Xl (24)) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨G₀, Xl, blk, hG, hX, -, hb, -, -⟩ :=
    reached_head h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
  obtain rfl : Bs.G₀ = G₀ := Option.some.inj (O.blank.symm.trans hG)
  obtain ⟨hZ, hGA, -⟩ := atPure_ok hA
  obtain rfl : A.Z = Zp := Except.ok.inj (hZ.symm.trans h.laid.pub)
  have eG : A.G = Bs.G₀ := Option.some.inj (hGA.symm.trans O.blank)
  have hp : blk.place = ⟨1, some (24), (ProofFile.k8Par A.Z Bs.G₀ Xl (24)).piece, .K8⟩ := by
    obtain ⟨Lk, b, Xb, e1, e2, eX, la, ep, -⟩ := IM.k8_of_head h.scope h.reads O
    have h0 := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope h.scope h.reads O (l := 24) (by omega) 5] at h0
    have hb' : cF.blocksInOrder[14 * (24) + 5 + 2]? = some blk := by
      have e : 14 * (24) + 5 + 2 = 343 := by omega
      rw [e]
      exact hb
    obtain rfl : b = blk := Option.some.inj (h0.symm.trans hb')
    obtain rfl : Xb = Xl := Option.some.inj (eX.symm.trans hX)
    rw [ep]
    exact (congrArg (·.place) la).trans rfl
  refine ⟨Bs.G₀, Xl, blk, hG, hX, hb, ?_⟩
  show (A.H.first.find? fun g => g.place == blk.place) = _
  rw [hp]
  have q := k8_half_any_fill cells mats hA hex ho (Xl := Xl) (by rw [eG]; exact hX)
  rw [eG] at q
  exact q

/-- **The half at a layers' segment's draw.** -/
theorem halfAt_at_fill.layers {g : Nat} (hg : g < 12) :
    ∃ (G₀ : ProofFile.Ground) (Xl : LinkH) (blk : Block S ProofFile.Cl),
      ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ ∧ G₀.built[2 * g]? = some Xl ∧
      (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[28 * g + 6]? =
        some blk ∧
      HalfAt (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread blk cells
        (ProofFile.k8Par Zp G₀ Xl (2 * g), mats Zp G₀ Xl (2 * g)) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨G₀, Xl, blk, hG, hX, -, hb, -, -⟩ :=
    reached_layers h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hg
  obtain rfl : Bs.G₀ = G₀ := Option.some.inj (O.blank.symm.trans hG)
  obtain ⟨hZ, hGA, -⟩ := atPure_ok hA
  obtain rfl : A.Z = Zp := Except.ok.inj (hZ.symm.trans h.laid.pub)
  have eG : A.G = Bs.G₀ := Option.some.inj (hGA.symm.trans O.blank)
  have hp : blk.place = ⟨1, some (2 * g), (ProofFile.k8Par A.Z Bs.G₀ Xl (2 * g)).piece, .K8⟩ := by
    obtain ⟨Lk, b, Xb, hpl, e1, e2, eX, la, -, ep, -⟩ := IM.k8_of_layers h.scope h.reads O g hg
    have h0 := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope h.scope h.reads O (l := 2 * g) (by omega) 4] at h0
    have hb' : cF.blocksInOrder[14 * (2 * g) + 4 + 2]? = some blk := by
      have e : 14 * (2 * g) + 4 + 2 = 28 * g + 6 := by omega
      rw [e]
      exact hb
    obtain rfl : b = blk := Option.some.inj (h0.symm.trans hb')
    obtain rfl : Xb = Xl := Option.some.inj (eX.symm.trans hX)
    rw [ep]
    exact (congrArg (·.place) la).trans rfl
  refine ⟨Bs.G₀, Xl, blk, hG, hX, hb, ?_⟩
  show (A.H.first.find? fun g => g.place == blk.place) = _
  rw [hp]
  have q := k8_half_any_fill cells mats hA hex ho (Xl := Xl) (by rw [eG]; exact hX)
  rw [eG] at q
  exact q

/-- **The half at an attention segment's draw.** -/
theorem halfAt_at_fill.att {g : Nat} (hg : g < 12) :
    ∃ (G₀ : ProofFile.Ground) (Xl : LinkH) (blk : Block S ProofFile.Cl),
      ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ ∧ G₀.built[2 * g + 1]? = some Xl ∧
      (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[14 * (2 * g + 1) + 6]? =
        some blk ∧
      HalfAt (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread blk cells
        (ProofFile.k8Par Zp G₀ Xl (2 * g + 1), mats Zp G₀ Xl (2 * g + 1)) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨G₀, Xl, blk, hG, hX, -, hb, -, -⟩ :=
    reached_att h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hg
  obtain rfl : Bs.G₀ = G₀ := Option.some.inj (O.blank.symm.trans hG)
  obtain ⟨hZ, hGA, -⟩ := atPure_ok hA
  obtain rfl : A.Z = Zp := Except.ok.inj (hZ.symm.trans h.laid.pub)
  have eG : A.G = Bs.G₀ := Option.some.inj (hGA.symm.trans O.blank)
  have hp : blk.place = ⟨1, some (2 * g + 1), (ProofFile.k8Par A.Z Bs.G₀ Xl (2 * g + 1)).piece, .K8⟩ := by
    obtain ⟨Lk, b, Xb, a, e1, e2, eX, la, -, ep, -⟩ := IM.k8_of_attention h.scope h.reads O g hg
    have h0 := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope h.scope h.reads O (l := 2 * g + 1) (by omega) 4] at h0
    have hb' : cF.blocksInOrder[14 * (2 * g + 1) + 4 + 2]? = some blk := by
      have e : 14 * (2 * g + 1) + 4 + 2 = 14 * (2 * g + 1) + 6 := by omega
      rw [e]
      exact hb
    obtain rfl : b = blk := Option.some.inj (h0.symm.trans hb')
    obtain rfl : Xb = Xl := Option.some.inj (eX.symm.trans hX)
    rw [ep]
    exact (congrArg (·.place) la).trans rfl
  refine ⟨Bs.G₀, Xl, blk, hG, hX, hb, ?_⟩
  show (A.H.first.find? fun g => g.place == blk.place) = _
  rw [hp]
  have q := k8_half_any_fill cells mats hA hex ho (Xl := Xl) (by rw [eG]; exact hX)
  rw [eG] at q
  exact q

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.find_zip
#print axioms ProofFile.Honest.K8.k8_half_any_fill
#print axioms ProofFile.Honest.K8.halfAt_at_fill.outHead
#print axioms ProofFile.Honest.K8.halfAt_at_fill.layers
#print axioms ProofFile.Honest.K8.halfAt_at_fill.att
