-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/WalksFile.lean: the walks of the forests of the three chains' rounds say yes at a
value of the typing of a whole file, under named premises.

OnBytes/TypedOracleCompiler/Joined/K/Left.lean asks, among what is left for a yes of a file's verifier, that the
walk of each forest of each chain's rounds ends, under the oracle functions g, in its trees' roots
(the fields `walk₁`, `walk₂`, `walk₃` of `AfterRuns`). OnBytes/Maker/WalksTree.lean has this for a
stretch of written rounds. Here it is said at a value π of `typeFile`
(OnBytes/Maker/TypeFile.lean), in the words of these three fields.

  `walks_typeFile`   **the three fields.**

The premises, none shown here. `WalkOwes`, and for each of the three stretches `RootsRead` and
`LeavesRead` (OnBytes/Maker/WalksTree.lean), the last at the tables that `tabsWFull` returns. The
test `shapesFit` on the data. No premise on the verifier's messages is taken: which positions are
read enters through `LeavesRead` alone.

The digest cfg' in `WalkOwes` (it stands in the vertices' hashes) and the letter cfg of `typeFile`
are two letters here; at a real file they are one digest. OnBytes/Maker/WalksOf.lean has the law
with one letter, with `RootsRead` paid and `LeavesRead` cut in two (`walks_of`): that is the one to
quote.

Not claimed. The stored table's walk (the field `walkE`). That the typing returns a value. Nothing
on soundness (index binding included), what a root fixes, opening-form binding, no two openings of
a commitment, correctness of extraction or whatever else names a committer or a prover.

-/
import OnBytes.Maker.WalksTree

set_option autoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile (Opening)
open _root_.Run _root_.Run.PQ

section File
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (a : ℕ) (W : Three.Whole)
  {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3) (silent : Xi → TF → TJ → T3 → Bool)
  (run : Xi → View → View → View → Bool) {I X : Type} {L : BatchProtocolWithLeafBody I X}
  (g : Fam (typedOracleFamily 256 (K + 1) L)) (hh : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray)
  (cfg' : ByteArray)
  (embS : (p : OPos (chainsOf C (WholeD.of a W) tF tJ t3).sh) →
    OSym (chainsOf C (WholeD.of a W) tF tJ t3).sh p → Body L)

/-- **The walks of the forests of the three chains' rounds, at a value of `typeFile`.** a', b', e':
what the three chains have yielded. -/
theorem walks_typeFile (sb : ℕ) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3) (salt : ByteArray)
    (path : List ByteArray) (r : Proof.TailRead)
    (π : OneProtocolProof 256 (wholeDesc C (WholeD.of a W) tF tJ t3 silent run).batch)
    (h : typeFile C a W tF tJ t3 silent run sb cfg pF pJ p3 salt path r = some π) (x : Xi)
    (a' : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₁)
    (b' : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₂)
    (e' : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₃)
    (hshape : shapesFit a W = true) (O : WalkOwes g hh cfg' W r)
    (hr₁ : RootsRead W r C (WholeD.of a W).ds₁ 0 (wiresLo C K chal (WholeD.of a W).ds₁) a'.2.1.2)
    (hr₂ : RootsRead W r C (WholeD.of a W).ds₂ (WholeD.of a W).t₁
      (wiresSh C K chal (WholeD.of a W).ds₂) b'.2.1.2)
    (hr₃ : RootsRead W r C (WholeD.of a W).ds₃ ((WholeD.of a W).t₁ + (WholeD.of a W).t₂)
      (wiresLo C K chal (WholeD.of a W).ds₃) e'.2.1.2)
    (hf₁ : ∀ tabs, tabsWFull W sb r = some tabs →
      LeavesRead g W r C (WholeD.of a W).ds₁ 0 tabs (fun p => symb₁ embS (.inr p))
        fun p => rd₁ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
          (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) x π a' b' e' (.inr p))
    (hf₂ : ∀ tabs, tabsWFull W sb r = some tabs →
      LeavesRead g W r C (WholeD.of a W).ds₂ (WholeD.of a W).t₁ tabs
        (fun p => symb₂ embS (.inr p))
        fun p => rd₂ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
          (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) x π a' b' e' (.inr p))
    (hf₃ : ∀ tabs, tabsWFull W sb r = some tabs →
      LeavesRead g W r C (WholeD.of a W).ds₃ ((WholeD.of a W).t₁ + (WholeD.of a W).t₂) tabs
        (fun p => symb₃ embS (.inr p))
        fun p => rd₃ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
          (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) x π a' b' e' (.inr p)) :
      (∀ Fs, forestsB _ (chainsOf C (WholeD.of a W) tF tJ t3).A₁
          (wire₁ (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run)) (symb₁ embS) a'.2.1
          (rd₁ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
            (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) x π a' b' e')
          (op₁ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run) π) = some Fs →
        ∀ T ∈ Fs, walkP g T T.reads = true) ∧
      (∀ Fs, forestsB _ (chainsOf C (WholeD.of a W) tF tJ t3).A₂
          (wire₂ (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run)) (symb₂ embS) b'.2.1
          (rd₂ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
            (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) x π a' b' e')
          (op₂ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run) π) = some Fs →
        ∀ T ∈ Fs, walkP g T T.reads = true) ∧
      (∀ Fs, forestsB _ (chainsOf C (WholeD.of a W) tF tJ t3).A₃
          (wire₃ (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run)) (symb₃ embS) e'.2.1
          (rd₃ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
            (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) x π a' b' e')
          (op₃ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run) π) = some Fs →
        ∀ T ∈ Fs, walkP g T T.reads = true) := by
  obtain ⟨tabs, etab, ht, -, -, o1, o2, o3⟩ :=
    typeFile_opens C a W tF tJ t3 silent run sb cfg pF pJ p3 salt path r π h
  have htabs := tabsWFull_holds ht
  have hrow := tabsWFull_row ht
  have w1 : wire₁ (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) = _ :=
    wire₁_qb (wiresOf C K chal (WholeD.of a W) tF tJ t3) _ _ _ _ _
  have w2 : wire₂ (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) = _ :=
    wire₂_qb (wiresOf C K chal (WholeD.of a W) tF tJ t3) _ _ _ _ _
  have w3 : wire₃ (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) = _ :=
    wire₃_qb (wiresOf C K chal (WholeD.of a W) tF tJ t3) _ _ _ _ _
  refine ⟨fun Fs hF => ?_, fun Fs hF => ?_, fun Fs hF => ?_⟩
  · rw [w1, o1] at hF
    exact walks_lo C K chal _ 0 g hh cfg' hrow htabs hshape (shape₁ C (WholeD.of a W)) O _ _ _ hr₁
      (hf₁ tabs ht) Fs (forests_behind K tF _ _ _ _ _ _ Fs hF)
  · rw [w2, o2] at hF
    exact walks_sh C K chal _ _ g hh cfg' hrow htabs hshape (shape₂ C (WholeD.of a W)) O _ _ _ hr₂
      (hf₂ tabs ht) Fs (forests_behind K tJ _ _ _ _ _ _ Fs hF)
  · rw [w3, o3] at hF
    exact walks_lo C K chal _ _ g hh cfg' hrow htabs hshape (shape₃ C (WholeD.of a W)) O _ _ _ hr₃
      (hf₃ tabs ht) Fs (forests_behind K t3 _ _ _ _ _ _ Fs hF)

end File

end OnBytes.Maker
