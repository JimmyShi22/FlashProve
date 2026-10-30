-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/TreesLine.lean: the typed rounds of OnBytes/Maker/Trees.lean, the stretches of a whole
file (OnBytes/Maker/Whole.lean) and the wire records of OnBytes/Maker/Wire.lean ARE those of
OnBytes/TypedOracleCompiler/Run/PlanQS.lean and OnBytes/TypedOracleCompiler/Slice/Batch3Wire.lean, by definition. Every statement is
proved by unfolding, but for three: `toRDs_ofLine` (an induction), `heq_cons` and `wiresLo_line`.

Why it is stated. Whatever is shown in OnBytes/TypedOracleCompiler/Run/ of a chain's typed rounds and of their wire
records is shown of these terms. Here a reader, and Lean, can see that they are the same terms.

  `uLT_line`, `SOfT_line`: a chain's typed rounds, at the data without the stored tables (`toRDs`).
  `stretch₁_line`, `stretch₂_line`, `stretch₃_line`: the three stretches of a whole file's shape.
  `drawnT_line`, `passT_line`, `rhoT_line`, `rvT_line`, `treeShT_line`, `posAtST_line`,
    `colAtST_line`: what a view is made of.
  `wireLo_line`, `wireSh_line`: a local and a shared written round's wire record.
  `ofLine`, `toRDs_ofLine`: a chain's data of that text as data of Trees.lean, and back.
  `heq_cons`: a tool: one round's record in front of two lists of records that are one across types.
  `wiresLo_line`: a local chain's wire records are that text's `wiresSL`. The two stand over two
    terms for one annotation ("local rounds only": `RoundSplits.allLocal` here, `Twin.allLo` there), which
    are equal by a theorem (`Twin.allLo_eq`) and not by unfolding: so the statement is an equality
    across types.

What is not claimed. Nothing on a stored table: that text has none in a round's data. Nothing on the
three silent rounds. Nothing on the whole file's wire record against that text's.


-/
import OnBytes.Maker.Wire

set_option autoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

section
variable (C : CK) (ds : List RDT)

theorem uLT_line : uLT C ds = TypedOracleCompiler.Run.PQ.uL C (toRDs ds) := rfl

theorem SOfT_line : SOfT C ds = TypedOracleCompiler.Run.PQ.SOf C (toRDs ds) := rfl

theorem drawnT_line : drawnT C ds = TypedOracleCompiler.Run.PQ.drawnSL C (toRDs ds) := rfl

theorem passT_line : passT C ds = TypedOracleCompiler.Run.PQ.passSL C (toRDs ds) := rfl

theorem rhoT_line : rhoT C ds = TypedOracleCompiler.Run.PQ.rhoSL C (toRDs ds) := rfl

theorem rvT_line : rvT C ds = TypedOracleCompiler.Run.PQ.rvSL C (toRDs ds) := rfl

theorem treeShT_line : treeShT ds = TypedOracleCompiler.Run.PQ.treeSh (toRDs ds) := rfl

theorem posAtST_line : posAtST C ds = TypedOracleCompiler.Run.PQ.posAtS C (toRDs ds) := rfl

theorem colAtST_line : colAtST C ds = TypedOracleCompiler.Run.PQ.colAtS C (toRDs ds) := rfl

end

section
variable (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)

theorem stretch₁_line : (chainsOf C D tF tJ t3).s₁ = TypedOracleCompiler.Run.PQ.uL C (toRDs D.ds₁) := rfl

theorem stretch₂_line : (chainsOf C D tF tJ t3).s₂ = TypedOracleCompiler.Run.PQ.uL C (toRDs D.ds₂) := rfl

theorem stretch₃_line : (chainsOf C D tF tJ t3).s₃ = TypedOracleCompiler.Run.PQ.uL C (toRDs D.ds₃) := rfl

end

/-- A round's data of OnBytes/TypedOracleCompiler/Run/PlanQTypes.lean, as data of Trees.lean: no stored table. -/
def ofLine (d : TypedOracleCompiler.Run.PQ.RD) : RDT := ⟨d, []⟩

theorem toRDs_ofLine : ∀ ds : List TypedOracleCompiler.Run.PQ.RD, toRDs (ds.map ofLine) = ds
  | [] => rfl
  | d :: ds => congrArg (d :: ·) (toRDs_ofLine ds)

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

theorem wireLo_line (d : RDT) : wireLo C K chal d = TypedOracleCompiler.Run.PQ.wireS C K chal d.toRD := rfl

theorem wireSh_line (d : RDT) : wireSh C K chal d = TypedOracleCompiler.Slice.wireSh C K chal d.toRD := rfl

/-- One round's record in front of two lists of records that are one across their types. -/
theorem heq_cons {r : Round} {s : Shape} (a : RAnn r) (w : WireRB 256 (K + 1) r a) {A B : RoundSplits s}
    (h : A = B) (W : RoundsQueryLayout 256 (K + 1) s A) (V : RoundsQueryLayout 256 (K + 1) s B) (hw : HEq W V) :
    HEq ((w, W) : RoundsQueryLayout 256 (K + 1) (r :: s) (a, A))
      ((w, V) : RoundsQueryLayout 256 (K + 1) (r :: s) (a, B)) := by
  subst h
  rw [eq_of_heq hw]

/-- **A local chain's wire records are that text's.** -/
theorem wiresLo_line : ∀ ds : List RDT,
    HEq (wiresLo C K chal ds) (TypedOracleCompiler.Run.PQ.wiresSL C K chal (toRDs ds))
  | [] => HEq.rfl
  | d :: ds =>
    heq_cons K (RAnn.allLocal (roundT C d).up) (wireLo C K chal d) (Twin.allLo_eq (SLT C ds)).symm
      (wiresLo C K chal ds) (TypedOracleCompiler.Run.PQ.wiresSL C K chal (toRDs ds)) (wiresLo_line ds)

end

end OnBytes.Maker
