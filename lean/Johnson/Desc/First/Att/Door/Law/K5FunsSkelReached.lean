-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5FunsSkelReached.lean: kind K5: AT EVERY STATE THAT THE FIRST CHAIN's RUN REACHES JUST BEHIND THE SENDING OF THE READS WITH ITS QUIET STEP, AT AN ATTENTION SEGMENT 2 g + 1: THE LIST OF TABLES THAT THE STATE BEARS (S.funs?) HAS A SKELETON THAT IS A TERM OF THE PLAN's SHAPE ALONE: the library's
attShapes a.S (nScores a.S) (OnBytes/Tie/Pv/Tail/ShapesAtt.lean), a := the public parameters' plan of group g; the vector's number is 2. NOTHING ON THE WEIGHTS phi.

Compiled with the whole library.

(Where this and lean/THEOREM.md differ, the page holds.)

After the file for the layers' segments (Johnson/Road/K4/FunsSkelReached.lean: funsSkel_reached, behind K4's sub-protocol): the walk is that file's; the seat, the quiet step's arm and the skeleton are this segment's.

Main names:
  `funsSkel_k1Reads`: at an accept of the reads' place's block (IM.k1Reads: K1's own with the quiet step joined) at a link of kind 1: by quiet_arms (Johnson/Desc/First/K8/LawCondK1.lean) and funsSkel_reads (K5FunsSkel.lean).
  **`funsSkel_att_reached`**: hS · hR · an opening · g < 12 · Reach 0 c.blocksInOrder start (14 * (2 * g + 1) + 6) (z, s') ⟹ ∃ a funs, Bs.G₀.W.A[g]? = some a ∧ s'.funs? = some funs ∧ shapesOf funs = attShapes a.S (nScores a.S) ∧ ∀ Fn ∈ funs.toList, Fn.tree = 2.
  **`funsSkel_att_rchAt`**: the same at the relation "reached" of the IOP as written in Lean.
Limits. AT THAT BORDER ALONE: that the list is left by the sub-protocols between it and the batching is not said here. That there is an opening is shown by no theorem here.
Is it empty here? Where no state is reached nothing is said. No premise beyond that other file's.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5FunsSkel
import Johnson.Desc.First.K8.LawCondK1
import Johnson.IMR.K1Scope
import Johnson.IMR.PureJoin
import Johnson.IMR.FlatScope
import Johnson.Road.K4.FunsThirdReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open OnBytes OnBytes.Model
open OnBytes.Tie.Pv.Tail.Closed (shapesOf attShapes nScores)
open OnBytes.Road.K4 (reach_pred descAt)
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8.Ready (quiet_arms)
open Johnson.Desc.First.Walk.Tied (Reach RchAt rchAt_raw stepYes_decide)

/-- At an accept of the reads' place's block at a link of kind 1. -/
theorem funsSkel_k1Reads {Z : ProofFile.Pub} {G : ProofFile.Ground} {l : ℕ} {X : Stages.LinkH} {pr : ℕ} {reads : Option (List ℕ)}
    (h1 : X.kind = 1) {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (h : (IM.k1Reads Z G l X pr reads).decide s rs gs = .ok s') :
    ∃ a funs, G.W.A[X.g]? = some a ∧ s'.funs? = some funs ∧ shapesOf funs = attShapes a.S (nScores a.S) ∧
      ∀ Fn ∈ funs.toList, Fn.tree = 2 := by
  obtain ⟨m, _, H⟩ := K5Law.except_bind_ok h
  rcases quiet_arms G l X _ _ _ _ H with ⟨_, a, ha, hd⟩ | ⟨hn, _⟩
  · obtain ⟨funs, e1, e2, e3⟩ := funsSkel_reads a hd
    exact ⟨a, funs, ha, e1, e2, e3⟩
  · exact absurd h1 hn

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
  {g : ℕ}

/-- **Behind the sending of the reads with its quiet step, at an attention segment, at every reached state: the skeleton of the list of tables is a term of the plan's shape.** -/
theorem funsSkel_att_reached (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hg : g < 12) {Q : Type}
    {start : Q → S} {z : Q} {s' : S} (h : Reach 0 c.blocksInOrder start (14 * (2 * g + 1) + 6) (z, s')) :
    ∃ a funs, Bs.G₀.W.A[g]? = some a ∧ s'.funs? = some funs ∧ shapesOf funs = attShapes a.S (nScores a.S) ∧
      ∀ Fn ∈ funs.toList, Fn.tree = 2 := by
  obtain ⟨z', s, s'', b, e, _, hb, hy⟩ := reach_pred (k := 14 * (2 * g + 1) + 5) h
  obtain ⟨_, rfl⟩ := Prod.mk.inj e
  obtain ⟨Lk, b₀, Xl, pd, reads, digits, e1, e2, hX, _, hA⟩ := IM.k1_reads_of hS hR O (2 * g + 1) (by omega)
  have hix : IM.k1Ix (2 * g + 1) false = 3 := by
    show 3 + (if 2 * g + 1 = 24 then 1 else 0) = 3
    rw [if_neg (by omega)]
  have hi : IM.flatIx c (2 * g + 1) 3 = 14 * (2 * g + 1) + 5 := by
    rw [IM.flatIx_scope hS hR O (by omega) 3]
  have hf : c.blocksInOrder[14 * (2 * g + 1) + 5]? = some b₀ := by
    rw [← hi, ← hix]
    exact IM.hear_at_flat e1 e2
  obtain rfl : b₀ = b := Option.some.inj (hf.symm.trans hb)
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  have hq := ((IM.yes_alone hA (fun e => nomatch e) s s' rs gs).1 hd).1
  obtain ⟨_, l', _, _, _, _, hX', hk1, hg1, _⟩ := (IM.ground_named hS hR O.pub O.blank).1 g hg
  obtain rfl : l' = Xl := Option.some.inj (hX'.symm.trans hX)
  obtain ⟨a, funs, ea, r⟩ := funsSkel_k1Reads hk1 hq
  rw [hg1] at ea
  exact ⟨a, funs, ea, r⟩

/-- **The same at the relation "reached" of the IOP as written in Lean.** -/
theorem funsSkel_att_rchAt (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hg : g < 12) {Str : Type}
    {a₀ : ((descAt Z A B c).XiPub × (descAt Z A B c).S₁) × Str}
    (h : RchAt (descAt Z A B c) (14 * (2 * g + 1) + 6) a₀) :
    ∃ a funs, Bs.G₀.W.A[g]? = some a ∧ S.funs? a₀.1.2 = some funs ∧ shapesOf funs = attShapes a.S (nScores a.S) ∧
      ∀ Fn ∈ funs.toList, Fn.tree = 2 :=
  funsSkel_att_reached hS hR O hg (z := a₀.1.1) (s' := a₀.1.2) (rchAt_raw h)

end H2K5.Door

#print axioms H2K5.Door.funsSkel_k1Reads
#print axioms H2K5.Door.funsSkel_att_reached
#print axioms H2K5.Door.funsSkel_att_rchAt
