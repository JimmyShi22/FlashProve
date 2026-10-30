-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K1/Twin.lean: THE LOT OF THE COMMITMENTS (`ProofFile.k1Pure`,
Johnson/Desc/ProofFile/Lots/PureLots.lean) LESS ITS FUNCTIONS (`ProofFile.Sk.lotSk`,
Johnson/Desc/ProofFile/Law/Skel/SkelFaults.lean) IS A FUNCTION OF A FEW PLAIN
VALUES: a law at every public part Z and every ground G: no scope, no premise. Definitions, and
statements with their proofs by unfolding; nothing is evaluated.

What the lot is. 51 blocks: the first segment's opening; and at each of the 25 built segments the
sending of the reads, with a quiet step laid behind it by Block.andThen, and the sending of the
digits (Johnson/Desc/ProofFile/Lot/K1.lean).
What a skeleton of it reads. Of the first chain's parameters: the codes and the request's shape
(`parLater_congr`, `firstPar_congr`, Johnson/Desc/K1/Law/QFull.lean), and at the first block the
layout too (`firstPlanOk`). Of the plan's two numbers: the answers to a sample, at the first block
alone. Of a segment: its two pieces; WHETHER the plan names arrays at the reads and at the digits
(which arrays, no skeleton reads: `commitOwn`'s test on the plan asks `arrays.isSome`); and whether
the quiet step passes its own test on the plan.

  `laterSk`, `firstSk`; `skel_laterAt`, `skel_firstAtS` (by rfl); `retype_later`, `retype_first`
  `quietOf`   the block that k1Pure's own text lays behind the reads' sending
  `Bare`, `blockAt_bare`, `readsQuietAt_bare`, `quietOf_bare`   **whatever stands there, the block
      that refuses too, has no round, no oracle message, nothing fixed before and no run**
  `later_andThen`   so of the quiet step only its test on the plan is left in the joined skeleton
  `View`, `segView`   a segment's view: five plain values
  `segSk`, `k1Sk`   THE TWIN
  `seg_skel`, `blocks_skel`   **MAIN: the lot's blocks' skeletons are the twin's**
  `k1Sk_congr`, `k1Sk_gp`   what the twin reads of the parameters and of the plan's two numbers
  `k1LotSk`, `lotSk_k1`   **the lot's row at every Z and G**
  `k1_steady`   the lot supplies no batching

What is not claimed. That a view is any particular value. Nothing on what a block decides.
Nothing on soundness. No example of the head is shown in this file; two, at storedPublicFiles and at zGap alone,
are AtFullSide.Top.headMember_zFull and headMember_zGap, whose own Limits say what they are worth.

-/
import Johnson.Desc.ProofFile.Law.Skel.SkelEnd
import Johnson.Desc.ProofFile.Lots.PureLots
import Johnson.Desc.K1.Law.QFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Desc.K1Lot

open OnBytes OnBytes.Params OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First (S)
open _root_.Desc.Plain (GPar)
open VerifiableInference.Desc.K1 (parLater firstPar laterAt firstSegmentOpening planOkOwn firstPlanOk
  linkNumbers gpOf parLater_congr firstPar_congr)
open ProofFile (Ground Pub Lot Cl)
open ProofFile.Sk

/-! ## 1 The kind's own blocks, less their functions -/

/-- A segment's later sending. ok: the plan names arrays. -/
def laterSk (q : Params.First) (gp : GPar) (l piece m : ℕ) (ok : Bool) : Skel :=
  { name := "K1: a commitment", place := ⟨1, some l, piece, .K1⟩, nRounds := 2, nOracles := 2
    told := toldFrom 0 (VerifiableInference.Desc.K1.oracles (parLater q gp l piece m))
    before := [], planOk := planOkOwn (parLater q gp l piece m) && ok, claims := [], after := [] }

theorem skel_laterAt (q : Params.First) (gp : GPar) (l piece m : ℕ) (arrays : Option (List ℕ)) :
    skel (laterAt q gp l piece m arrays : Block S Unit) = laterSk q gp l piece m arrays.isSome :=
  rfl

/-- The first segment's opening. -/
def firstSk (q : Params.First) (gp : GPar) : Skel :=
  { name := "K1: the first segment's opening", place := ⟨1, some 0, 1, .K1⟩, nRounds := 2
    nOracles := 2, told := toldFrom 0 (VerifiableInference.Desc.K1.oracles (firstPar q gp))
    before := [], planOk := planOkOwn (firstPar q gp) && firstPlanOk q gp.samples, claims := []
    after := [] }

theorem skel_firstAtS (q : Params.First) (gp : GPar) :
    skel (firstSegmentOpening q gp : Block S Unit) = firstSk q gp := rfl

theorem retype_later (q : Params.First) (gp : GPar) (l piece m : ℕ) (ok : Bool) :
    (laterSk q gp l piece m ok).retype = laterSk q gp l piece m ok := by
  simp [Skel.retype, laterSk]

theorem retype_first (q : Params.First) (gp : GPar) : (firstSk q gp).retype = firstSk q gp := by
  simp [Skel.retype, firstSk]

/-! ## 2 The quiet step behind the reads' sending -/

/-- The quiet step that `ProofFile.k1Pure` lays behind the reads' sending at segment l. -/
def quietOf (G : Ground) (l : ℕ) (X : LinkH) : Block S Unit :=
  let piece : ℕ := if X.kind == 0 || X.kind == 1 then 4 else 5
  ProofFile.orLoud s!"link {l}: the step after the commitment before the smallness test"
    ⟨1, some l, piece, .K1⟩
    "the step after the commitment that comes before the smallness test"
    (ProofFile.readsQuietAt G l X piece)

/-- A block with no round, no oracle message, nothing fixed before and no run. -/
def Bare (b : Block S Unit) : Prop :=
  b.rounds = [] ∧ b.oracles = [] ∧ b.before = [] ∧ b.claims = [] ∧ b.after = []

theorem blockAt_bare {Gs : Array Layer.HPlan2} {hS : Head.Shape} {HLy : Head.HL}
    {H : Head.HPlanH2} {kinds : List (ℕ × ℕ)} {l : ℕ} {b : Block S Unit}
    (h : VerifiableInference.Desc.K8.ReadsQuiet.blockAt Gs hS HLy H kinds l = some b) :
    Bare b := by
  unfold VerifiableInference.Desc.K8.ReadsQuiet.blockAt at h
  obtain ⟨k, _, h⟩ := Option.bind_eq_some_iff.1 h
  by_cases h0 : (k.1 == 0) = true
  · rw [if_pos h0] at h
    obtain ⟨hp, _, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · rw [if_neg h0] at h
    by_cases h2 : (k.1 == 2) = true
    · rw [if_pos h2] at h
      obtain rfl := Option.some.inj h
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · rw [if_neg h2] at h
      cases h

theorem readsQuietAt_bare {G : Ground} {l piece : ℕ} {X : LinkH} {b : Block S Unit}
    (h : ProofFile.readsQuietAt G l X piece = some b) : Bare b := by
  unfold ProofFile.readsQuietAt at h
  by_cases h1 : (X.kind == 1) = true
  · rw [if_pos h1] at h
    by_cases h4 : (piece == 4) = true
    · rw [if_pos h4] at h
      unfold VerifiableInference.Desc.First.Att.readsAtO at h
      obtain ⟨A, _, rfl⟩ := Option.map_eq_some_iff.1 h
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · rw [if_neg h4] at h
      cases h
  · rw [if_neg h1] at h
    by_cases hp : (piece == (if X.kind == 0 then 4 else 5)) = true
    · rw [if_pos hp] at h
      exact blockAt_bare h
    · rw [if_neg hp] at h
      cases h

/-- **Whatever stands there, the refuser too, has no round and names no run.** -/
theorem quietOf_bare (G : Ground) (l : ℕ) (X : LinkH) : Bare (quietOf G l X) := by
  unfold quietOf
  dsimp only
  cases h : ProofFile.readsQuietAt G l X (if X.kind == 0 || X.kind == 1 then 4 else 5) with
  | none => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | some b => exact readsQuietAt_bare h

/-- K1's sending with such a step laid behind it: only the step's test on the plan is left. -/
theorem later_andThen (q : Params.First) (gp : GPar) (l piece m : ℕ) (ok : Bool)
    {z : Block S Unit} (hz : Bare z) :
    (laterSk q gp l piece m ok).andThen "K1: a commitment" (skel z) =
      laterSk q gp l piece m (ok && z.planOk) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hz
  simp [Skel.andThen, laterSk, skel, h1, h2, h3, h4, h5, toldFrom, Bool.and_assoc]

/-! ## 3 The twin -/

/-- A segment's view: its two pieces; whether the plan names arrays at the reads and at the
digits; whether the quiet step passes its test on the plan. Plain data. -/
abbrev View : Type := ℕ × ℕ × Bool × Bool × Bool

def segView (G : Ground) (x : LinkH × ℕ) : Option View :=
  (linkNumbers G x.1).map fun n =>
    (n.1, n.2.1, n.2.2.1.isSome, n.2.2.2.isSome, (quietOf G x.2 x.1).planOk)

/-- A segment's two skeletons. -/
def segSk (q : Params.First) (gp : GPar) (l : ℕ) : Option View → List Skel
  | none => []
  | some v => [laterSk q gp l v.1 1 (v.2.2.1 && v.2.2.2.2), laterSk q gp l v.2.1 2 v.2.2.2.1]

/-- **The lot's skeletons, of what it reads.** -/
def k1Sk (q : Params.First) (gp : GPar) (vs : List (ℕ × Option View)) : List Skel :=
  firstSk q gp :: vs.flatMap fun y => segSk q gp y.1 y.2

/-- One segment. -/
theorem seg_skel (Z : Pub) (G : Ground) (X : LinkH) (l : ℕ) :
    ((match linkNumbers G X with
      | none => ([] : List (Block S Unit))
      | some (pr, pd, reads, digits) =>
        [(laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).andThen
            (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).name (quietOf G l X),
         laterAt G.first (gpOf Z) l pd 2 digits]).map
      fun (b : Block S Unit) => skel (b.retype : Block S Cl)) =
      segSk G.first (gpOf Z) l (segView G (X, l)) := by
  unfold segView
  cases h : linkNumbers G X with
  | none => rfl
  | some n =>
    obtain ⟨pr, pd, reads, digits⟩ := n
    have e : (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).name = "K1: a commitment" :=
      rfl
    simp only [List.map_cons, List.map_nil, skel_retype, skel_andThen, skel_laterAt, e,
      later_andThen _ _ _ _ _ _ (quietOf_bare G l X), retype_later, Option.map_some]
    rfl

/-- **AT EVERY PUBLIC PART AND EVERY GROUND: the lot's blocks' skeletons are the twin's.** -/
theorem blocks_skel (Z : Pub) (G : Ground) :
    ((ProofFile.k1Pure Z).blocks G).map skel =
      k1Sk G.first (gpOf Z) (G.built.toList.zipIdx.map fun x => (x.2, segView G x)) := by
  show (((VerifiableInference.Desc.K1.blocks (gpOf Z) (fun G l X => some (quietOf G l X)) G).map
    fun (b : Block S Unit) => (b.retype : Block S Cl)) ++ []).map skel = _
  rw [List.append_nil, List.map_map]
  unfold VerifiableInference.Desc.K1.blocks k1Sk
  simp only [List.map_append, List.map_cons, List.map_nil, List.singleton_append,
    List.map_flatMap, List.flatMap_map, Function.comp_apply, skel_retype, skel_firstAtS,
    retype_first]
  congr 1
  refine List.flatMap_congr fun x _ => ?_
  obtain ⟨X, l⟩ := x
  exact seg_skel Z G X l

/-! ## 4 What the twin reads of the chain's parameters -/

theorem k1Sk_congr {q q' : Params.First} (hc : q.codes = q'.codes) (hs : q.shape = q'.shape)
    (hl : q.layout = q'.layout) (gp : GPar) (vs : List (ℕ × Option View)) :
    k1Sk q gp vs = k1Sk q' gp vs := by
  have e1 : firstSk q gp = firstSk q' gp := by
    unfold firstSk firstPlanOk
    rw [firstPar_congr hc hs, hc, hs, hl]
  have e2 : ∀ l piece m ok, laterSk q gp l piece m ok = laterSk q' gp l piece m ok := by
    intro l piece m ok
    unfold laterSk
    rw [parLater_congr hc hs]
  have e3 : ∀ l v, segSk q gp l v = segSk q' gp l v := by
    intro l v
    cases v with
    | none => rfl
    | some v => simp only [segSk, e2]
  unfold k1Sk
  simp only [e1, e3]

/-- Of the plan's two numbers the twin reads the answers to a sample alone. -/
theorem k1Sk_gp (q : Params.First) {gp gp' : GPar} (h : gp.samples = gp'.samples)
    (vs : List (ℕ × Option View)) : k1Sk q gp vs = k1Sk q gp' vs := by
  have e1 : firstSk q gp = firstSk q gp' := by
    show ({ name := _, place := _, nRounds := _, nOracles := _, told := _, before := _
            planOk := planOkOwn (firstPar q gp) && firstPlanOk q gp.samples, claims := _
            after := _ } : Skel) = _
    rw [h]
    rfl
  have e2 : ∀ l piece m ok, laterSk q gp l piece m ok = laterSk q gp' l piece m ok :=
    fun _ _ _ _ => rfl
  have e3 : ∀ l v, segSk q gp l v = segSk q gp' l v := by
    intro l v
    cases v with
    | none => rfl
    | some v => simp only [segSk, e2]
  unfold k1Sk
  simp only [e1, e3]

/-! ## 5 The lot's row -/

/-- The lot less its functions, of what it reads. -/
def k1LotSk (q : Params.First) (gp : GPar) (vs : List (ℕ × Option View)) : LotSk :=
  { name := "the commitments (K1)", letters := false, still := [], blocks := k1Sk q gp vs
    batch := fun _ => none, each := fun _ => false, tests := fun _ => false }

/-- **AT EVERY PUBLIC PART AND EVERY GROUND.** -/
theorem lotSk_k1 (Z : Pub) (G : Ground) :
    lotSk G (ProofFile.k1Pure Z) =
      k1LotSk G.first (gpOf Z) (G.built.toList.zipIdx.map fun x => (x.2, segView G x)) := by
  unfold lotSk k1LotSk
  rw [blocks_skel]
  rfl

/-- The lot supplies no batching: so it is steady. -/
theorem k1_steady (Z : Pub) (G : Ground) : Steady G (ProofFile.k1Pure Z) :=
  steady_none G _ fun _ => rfl

end Johnson.AtFull.Desc.K1Lot

#print axioms Johnson.AtFull.Desc.K1Lot.skel_laterAt
#print axioms Johnson.AtFull.Desc.K1Lot.skel_firstAtS
#print axioms Johnson.AtFull.Desc.K1Lot.retype_later
#print axioms Johnson.AtFull.Desc.K1Lot.retype_first
#print axioms Johnson.AtFull.Desc.K1Lot.blockAt_bare
#print axioms Johnson.AtFull.Desc.K1Lot.readsQuietAt_bare
#print axioms Johnson.AtFull.Desc.K1Lot.quietOf_bare
#print axioms Johnson.AtFull.Desc.K1Lot.later_andThen
#print axioms Johnson.AtFull.Desc.K1Lot.seg_skel
#print axioms Johnson.AtFull.Desc.K1Lot.blocks_skel
#print axioms Johnson.AtFull.Desc.K1Lot.k1Sk_congr
#print axioms Johnson.AtFull.Desc.K1Lot.k1Sk_gp
#print axioms Johnson.AtFull.Desc.K1Lot.lotSk_k1
#print axioms Johnson.AtFull.Desc.K1Lot.k1_steady
