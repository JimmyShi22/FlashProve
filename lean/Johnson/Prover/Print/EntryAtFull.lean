-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Print/EntryAtFull.lean: the public premises of Johnson/Prover/Print/Entry.lean at the
written rounds' data of the entry's file, at the full size (`dsFull`, OnBytes/Flat/LinkSibAt.lean)
and at the small example (`dsSmall`): by evaluation in Lean's kernel. And: at most two trees in a
round gives what the compiled prover's theorem asks of the file's wire record.

Main names (namespace `Johnson.Prover.Print`).
  `PublicL ds a`   the public premises as one record: `RootsFitL`, `TreesApart`, the five public
                   clauses of `SizesL`, and: at most two trees in a round
  `publicL_full`, `publicL_small`   they hold at (dsFull, frS.P.T.a) and at (dsSmall, srS.P.T.a)
  `fewJ_wqW`, `few0_wqW`   at most two trees in a round: `FewJ` and `Few0`
                   (OnBytes/TypedOracleCompiler/Joined/K/RunSome.lean) at the wire record `wqW`
                   (Johnson/RunOne/StrictLinkW.lean)

Limits. Facts on two written lists and two numbers. Nothing on a proof string, a prover or a file.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Print.Entry
import OnBytes.Flat.LinkSibAt
import OnBytes.TypedOracleCompiler.Joined.K.RunSome

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Print
open TypedOracleCompiler.Run TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (View CK XO)
open OnBytes.Flat (linkSkeletonOfRoundData dsFull dsSmall)
open OnBytes.Slice (frS srS)
open Johnson.RunOne.StrictW (wqW)

/-- The public premises on the rounds' data ds and the stored tables' depth a. -/
structure PublicL (ds : List PQ.RD) (a : ℕ) : Prop where
  rootsFit : RootsFitL ds
  apart : TreesApart ds
  rounds : ds.length < 2 ^ 64
  items : ∀ d ∈ ds, d.items.length < 2 ^ 64 ∧ ∀ i ∈ d.items, i ≠ .f ∧ i ≠ .word
  trees : (ds.map (·.trees.length)).sum < 2 ^ 64
  shapes : ∀ d ∈ ds, ∀ s ∈ d.trees, s.tree < 2 ^ 64 ∧ s.a < 64 ∧ s.W < 2 ^ 64
  depth : a < 64
  few : ∀ d ∈ ds, d.trees.length ≤ 2

theorem publicL_full : PublicL dsFull frS.P.T.a where
  rootsFit := by
    unfold RootsFitL
    decide +kernel
  apart := by
    unfold TreesApart
    decide +kernel
  rounds := by decide +kernel
  items := by decide +kernel
  trees := by decide +kernel
  shapes := by decide +kernel
  depth := by decide +kernel
  few := by decide +kernel

theorem publicL_small : PublicL dsSmall srS.P.T.a where
  rootsFit := by
    unfold RootsFitL
    decide +kernel
  apart := by
    unfold TreesApart
    decide +kernel
  rounds := by decide +kernel
  items := by decide +kernel
  trees := by decide +kernel
  shapes := by decide +kernel
  depth := by decide +kernel
  few := by decide +kernel

/-! ## At most two trees in a round -/

theorem fewJ_wiresSL (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) :
    ∀ ds : List PQ.RD, (∀ d ∈ ds, d.trees.length ≤ 2) →
      FewJ (PQ.uL C ds) (_root_.Run.Twin.allLo (PQ.SL C ds)) (PQ.wiresSL C K chal ds)
  | [], _ => trivial
  | d :: ds, h =>
    ⟨by
      show (d.trees.map (·.a)).length ≤ 2
      rw [List.length_map]
      exact h d List.mem_cons_self,
      fewJ_wiresSL C K chal ds fun e he => h e (List.mem_cons_of_mem _ he)⟩

theorem few0_wiresSL (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) :
    ∀ ds : List PQ.RD,
      Few0 (PQ.uL C ds) (_root_.Run.Twin.allLo (PQ.SL C ds)) (PQ.wiresSL C K chal ds)
  | [] => trivial
  | _ :: ds => ⟨Nat.zero_le _, few0_wiresSL C K chal ds⟩

section
variable (C : CK) (ds : List PQ.RD) (a : ℕ) (xs : List XO) {X : Type} (dec : X → View → Bool)
  (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

theorem fewJ_wqW (h : ∀ d ∈ ds, d.trees.length ≤ 2) :
    FewJ (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape (linkSkeletonOfRoundData C ds a xs dec).up.ann
      (wqW C ds a xs dec K chal).sh :=
  ⟨Nat.zero_le _, fewJ_wiresSL C K chal ds h⟩

theorem few0_wqW :
    Few0 (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape (linkSkeletonOfRoundData C ds a xs dec).up.ann
      (wqW C ds a xs dec K chal).sh :=
  ⟨Nat.zero_le _, few0_wiresSL C K chal ds⟩

end

end Johnson.Prover.Print
