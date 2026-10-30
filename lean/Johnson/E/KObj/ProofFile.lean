-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/E/KObj/ProofFile.lean: the hypothesis on the proof file's protocol from the blocks of two
typed lists.

Statements and proofs. The proof file's protocol of an object is "a request's own part in every
slot, in local rounds; then the test at N instances" (`online S.req S.linOn`, Hiop/RecBuild.lean).
Here `req` is a typed list of plain blocks and `linOn` a typed list of batch blocks (`KObj.ObjB`,
Johnson/E/KObj/BatchObj.lean).

Main names:
  `KObj.ObjB.ProofBlocks`: every block of the two lists has its property, and the request's blocks
    hand the record and the encoded index on.
  `KObj.ObjB.proof_sndB`: then for each record the session has round-by-round knowledge soundness
    in the form for batches, for the relaxed relation at the decoded index, at the two lists'
    errors in a row. By `rec_online_know_ofK` (Cb/Thin/Cond/TargetSoundOnly.lean).
  `KObj.ObjB.proofSound_lhr`: the hypothesis `proofSound` (Johnson/Top/OnFilesAt.lean), word for
    word, at the object `(O.obj.S H).lhr`, if every error of both lists is at most εs.
  `KObj.ObjB.proofSound_lhrW`: the same at the passed object `(O.obj.S H).lhrW Nn σT σL σB g`
    (verifier messages made by samplers from digests; proof-of-work bits), at εs := κs · κ, by
    `sndBKT_pull` and `sndBKT_grind` on the session alone.
  `KObj.by_family`: "for every place" is "for every family, for every place of it".
Limits: `proofSound_lhr` speaks of the object before the two passes, whose rounds' messages are the
blocks' own: there the hypothesis `wires` (exact uniformity from digests) cannot hold, so it alone
feeds no description; `proofSound_lhrW` is the form that a written description can use. Both
objects have early := id and late := none. Of the other three lists and of every honest side
nothing is asked. It is not said that any object is the protocol that the programs run, that any
block has its property, or which rounds are shared.
-/
import Johnson.E.KObj.BatchObj
import Cb.Thin.Cond.TargetSoundOnly
import Johnson.RecCompile.Join

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj
open Iop Prob Hiop IOR Cb Compile Compile.Batch Compile.Batch.Cms
open scoped ENNReal

/-- the proof file's named hypotheses -/
structure ObjB.ProofBlocks (O : ObjB) : Prop where
  /-- the first proof chain: every plain block has its property -/
  req   : O.req.Each PG
  /-- … and hands the record and the encoded index on -/
  hands : O.req.HandsL (T := O.C.Rec) (U := O.C.E0.Str) ⟨Prod.snd, id⟩ ⟨Prod.snd, Prod.fst⟩
  /-- the shared and the second proof chain: every batch block has its property -/
  linOn : O.linOn.Each

/-- (P1) -/
theorem ObjB.proof_sndB (O : ObjB) (H : O.obj.Hon) (h : O.ProofBlocks) :
    ∀ rec : O.C.Rec, ((O.obj.S H).session.toBatch.comap fun x => (x, rec)).SndBKT O.N id none
      (fun x y w => O.C.D y rec = none ∨ ∃ i, O.C.D y rec = some i ∧ O.C.Rno i x w)
      (fun x y τ => (O.obj.S H).wit (x, rec) y τ)
      (Err.app (O.req.blk O.C.cells0).err O.linOn.blk.b.err) :=
  rec_online_know_ofK O.C (O.obj.S H) (O.obj.P H) (O.req.good O.C.cells0 h.req).know
    (linB_of_list O.C O.on O.linOn O.dOn h.linOn) (O.req.hands O.C.cells0 _ _ h.hands).passes
    (O.req.hands O.C.cells0 _ _ h.hands).copy

/-- The hypothesis `proofSound`, in its own words, at the object before the two passes. -/
theorem ObjB.proofSound_lhr (O : ObjB) (H : O.obj.Hon) (h : O.ProofBlocks) (εs : ℝ≥0∞)
    (b1 : Err.Below (O.req.blk O.C.cells0).err εs) (b2 : Err.Below O.linOn.blk.b.err εs) :
    ∃ (wit : O.C.X × (O.obj.S H).lhr.Rec → (oneExternalString (O.obj.S H).lhr.wordLength (O.obj.S H).lhr.Symbol).Str →
        Tr (O.obj.S H).lhr.onlineBatch.loc.shape → O.C.Cells) (ε : _),
      Err.Below ε εs ∧ ∀ rec, ((O.obj.S H).lhr.batAt rec).SndBKT (O.obj.S H).lhr.maxBatchSize
        (O.obj.S H).lhr.early (O.obj.S H).lhr.late ((O.obj.S H).lhr.relB O.C.Rno rec)
        (fun x y τ => wit (x, rec) y τ) ε :=
  ⟨(O.obj.S H).wit, Err.app (O.req.blk O.C.cells0).err O.linOn.blk.b.err, Err.Below.app b1 b2,
    O.proof_sndB H h⟩

/-- The hypothesis `proofSound`, in its own words, at the passed object, by the proof file alone. -/
theorem ObjB.proofSound_lhrW (O : ObjB) (H : O.obj.Hon) (h : O.ProofBlocks) (Nn : Type) [Inhabited
    Nn]
    (σT : Samplers (O.obj.S H).lhr.offline.shape) (σL : Samplers (O.obj.S H).lhr.link.shape)
    (σB : Samplers (O.obj.S H).lhr.onlineBatch.loc.shape) (g : (O.obj.S H).Bits) (κs K κ : ℝ≥0∞)
    (gdB : σB.Good κs K) (b1 : Err.BelowG g.req (O.req.blk O.C.cells0).err κ)
    (b2 : Err.BelowG g.linOn O.linOn.blk.b.err κ) :
    ∃ (wit : O.C.X × ((O.obj.S H).lhrW Nn σT σL σB g).Rec →
        (oneExternalString ((O.obj.S H).lhrW Nn σT σL σB g).wordLength ((O.obj.S H).lhrW Nn σT σL σB g).Symbol).Str →
        Tr ((O.obj.S H).lhrW Nn σT σL σB g).onlineBatch.loc.shape → O.C.Cells) (ε : _),
      Err.Below ε (κs * κ) ∧ ∀ rec, (((O.obj.S H).lhrW Nn σT σL σB g).batAt rec).SndBKT
        ((O.obj.S H).lhrW Nn σT σL σB g).maxBatchSize ((O.obj.S H).lhrW Nn σT σL σB g).early
        ((O.obj.S H).lhrW Nn σT σL σB g).late (((O.obj.S H).lhrW Nn σT σL σB g).relB O.C.Rno rec)
        (fun x y τ => wit (x, rec) y τ) ε :=
  ⟨fun b y τ => (O.obj.S H).wit b y (Tr.push σB (Tr.strip (g.BR.pull σB) τ)), _,
    (Err.below_grind_iff _ _ _).2 (Err.BelowG.pull gdB
      ((belowG_app _ _ g.req g.linOn (O.req.blk O.C.cells0).err O.linOn.blk.b.err κ).2 ⟨b1, b2⟩)),
    fun rec =>
      sndBKT_grind Nn O.C.X O.C.Cells _ (((O.obj.S H).lhr.pull σT σL σB).batAt rec) (g.BR.pull σB)
        (O.obj.S H).lhr.maxBatchSize (O.obj.S H).lhr.early (O.obj.S H).lhr.late
        ((O.obj.S H).lhr.relB O.C.Rno rec) _ _
        (sndBKT_pull O.C.X O.C.Cells _ ((O.obj.S H).lhr.batAt rec) σB gdB.fib (O.obj.S H).lhr.maxBatchSize
          (O.obj.S H).lhr.early (O.obj.S H).lhr.late ((O.obj.S H).lhr.relB O.C.Rno rec)
          (fun x y τ => (O.obj.S H).wit (x, rec) y τ) _ (O.proof_sndB H h rec))⟩

/-! ### (P3) by family -/

/-- "for every place up to n" is "for every family, for every place of that family" -/
theorem by_family {F : Type} (κ : ℕ → F) (n : ℕ) (Pr : ℕ → Prop) :
    (∀ i ≤ n, Pr i) ↔ ∀ f : F, ∀ i ≤ n, κ i = f → Pr i :=
  ⟨fun h _ i hi _ => h i hi, fun h i hi => h (κ i) i hi rfl⟩

#print axioms KObj.ObjB.proof_sndB
#print axioms KObj.ObjB.proofSound_lhr
#print axioms KObj.ObjB.proofSound_lhrW

end KObj
