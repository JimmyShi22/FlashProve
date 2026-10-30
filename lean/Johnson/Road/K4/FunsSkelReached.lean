-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/FunsSkelReached.lean: BEHIND K4's SUB-PROTOCOL, AT EVERY STATE THAT THE FIRST
CHAIN's RUN REACHES THERE, THE LIST OF TABLES THAT THE STATE BEARS (S.funs?) HAS A SKELETON THAT IS
A TERM OF THE PUBLIC PARAMETERS: of each table the matrix, the length and the first entry are the
library's `layShapes` (OnBytes/Tie/Pv/Tail/ShapesLay.lean) at the layers' public parameters and the
group; the vector's number is 2. NOTHING ON THE WEIGHTS phi. Statements with their proofs: calls.

  `funsSkel_kept`: at two states with an accept of K4's sub-protocol between them (`KeptAtS`): by
    the library's `funs_shapes` and `hear_public`.
  `funsSkel_step`: at an accept of the seated sub-protocol at K4's place.
  **`funsSkel_reached`**: hS · hR · an opening · g < 12 · Reach 0 c.blocksInOrder start (28 * g + 5) (z, s')
  ⟹ ∃ funs, s'.funs? = some funs ∧ shapesOf funs = layShapes Bs.G₀.W.layers g ∧ ∀ Fn ∈ funs.toList,
  Fn.tree = 2. **`funsSkel_rchAt`**: the same at the relation "reached" of the IOP as written in
  Lean.

Limits. AT THE BORDER JUST BEHIND K4 ALONE: that the list is left by the sub-protocols between K4
and the batching is not said here. That there is an opening is shown by no theorem here. K04_law,
the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.
-/
import Johnson.Road.K4.FunsThirdReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par hear_public)
open OnBytes.Tie.Pv.Tail.Closed (shapesOf layShapes funs_shapes)
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied (Reach RchAt rchAt_raw stepYes_decide)

/-- Behind an accept of K4's sub-protocol: the skeleton of the list of tables. -/
theorem funsSkel_kept {p : Par} {s s' : S} (K : KeptAtS p s s') :
    ∃ funs, s'.funs? = some funs ∧ shapesOf funs = layShapes p.P p.g ∧
      ∀ Fn ∈ funs.toList, Fn.tree = 2 := by
  obtain ⟨a, fo, o, G, _, _, _, _, _, hf, _, _, _, _, _, t, u, hh⟩ := K
  obtain ⟨_, _, iU3, tab, laid, nU3, TS, claimsP, pts, hd2, _, _, e3, _, _, _, _, _, _, e10⟩ :=
    hear_public hh
  obtain ⟨k1, k2⟩ := funs_shapes e10
  refine ⟨o.funs, hf, ?_, k2⟩
  have e3' : Layer.layTables ((p.P.tails.getD p.g {}).mats.map fun M => (M.m, M.k))
      (Layer.tableAsks p.P.y p.P.rd p.g) 0 = some (tab, laid, nU3) := e3
  rw [k1]
  unfold layShapes
  rw [e3']

/-- At an accept of the seated sub-protocol at K4's place. -/
theorem funsSkel_step {b : Block S ProofFile.Cl} {x : Bool × Par} {name : String} {g : ℕ}
    (h : IM.LaidAlone ProofFile.sameReply b (ProofFile.k4Block x) name (k4PlaceAt g)) {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} (hd : b.decide s rs gs = .ok s') :
    ∃ funs, s'.funs? = some funs ∧ shapesOf funs = layShapes x.2.P x.2.g ∧
      ∀ Fn ∈ funs.toList, Fn.tree = 2 := by
  have K : KeptAtS { x.2 with k3Runs := true } s s' :=
    kept_atS ((IM.k4_yes h s s' rs gs).1 hd).1
  exact funsSkel_kept K

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
  {g : ℕ}

/-- **Behind K4's sub-protocol, at every reached state: the skeleton of the list of tables is a term
of the public parameters.** -/
theorem funsSkel_reached (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hg : g < 12) {Q : Type}
    {start : Q → S} {z : Q} {s' : S} (h : Reach 0 c.blocksInOrder start (28 * g + 5) (z, s')) :
    ∃ funs, s'.funs? = some funs ∧ shapesOf funs = layShapes Bs.G₀.W.layers g ∧
      ∀ Fn ∈ funs.toList, Fn.tree = 2 := by
  obtain ⟨z', s, s'', b, e, _, hb, hy⟩ := reach_pred (k := 28 * g + 4) h
  obtain ⟨_, rfl⟩ := Prod.mk.inj e
  obtain ⟨Lk, b₀, x, e1, e2, _, e4, _, e6, e7, _⟩ := IM.k4_of hS hR O g hg
  have hi : IM.flatIx c (2 * g) 2 = 28 * g + 4 := by
    rw [IM.flatIx_scope hS hR O (by omega) 2]
    omega
  have hf : c.blocksInOrder[28 * g + 4]? = some b₀ := by
    rw [← hi]
    exact IM.hear_at_flat e1 e2
  obtain rfl : b₀ = b := Option.some.inj (hf.symm.trans hb)
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  have k := funsSkel_step e4 hd
  rw [e6, e7] at k
  exact k

/-- **The same at the relation "reached" of the IOP as written in Lean.** -/
theorem funsSkel_rchAt (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hg : g < 12) {Str : Type}
    {a : ((descAt Z A B c).XiPub × (descAt Z A B c).S₁) × Str}
    (h : RchAt (descAt Z A B c) (28 * g + 5) a) :
    ∃ funs, S.funs? a.1.2 = some funs ∧ shapesOf funs = layShapes Bs.G₀.W.layers g ∧
      ∀ Fn ∈ funs.toList, Fn.tree = 2 :=
  funsSkel_reached hS hR O hg (z := a.1.1) (s' := a.1.2) (rchAt_raw h)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.funsSkel_kept
#print axioms OnBytes.Road.K4.funsSkel_step
#print axioms OnBytes.Road.K4.funsSkel_reached
#print axioms OnBytes.Road.K4.funsSkel_rchAt
