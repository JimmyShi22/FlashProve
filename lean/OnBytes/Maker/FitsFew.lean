-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/FitsFew.lean: at the wire record of a file's protocol (`wqWhole`,
OnBytes/Maker/Wire.lean) each component of each round has at most `maxRt` trees, if each round of
the data sends at most so many.

The run of a file's three chains (`FileW.runs_at`, OnBytes/TypedOracleCompiler/Joined/K/RunsAt.lean) asks `Fits`.
Five of its eight fields bound the number of trees of a round's components (`FewJ`, `Few0`,
OnBytes/TypedOracleCompiler/Joined/K/RunSome.lean). Here they are brought down to the rounds' data: a written round
has one tree for each entry of its list `trees`; the three rounds in front of the chains have none.
The other three fields: OnBytes/Maker/FitsLen.lean.

Main names:
  `fewJ_wiresLo`, `few0_wiresSh`   for a list of written rounds, local or shared.
  `few₁_whole`, `fewJ_whole`, `fewJ0_whole`, `few₂_whole`, `few₃_whole`   the five fields at
                  `wqWhole`.
Limits: on the wire records alone. That any data's rounds send at most `maxRt` trees is not shown
here.


-/
import OnBytes.Maker.LineAt
import OnBytes.TypedOracleCompiler.Joined.K.RunsAt

set_option autoImplicit false

namespace OnBytes.Maker
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Iop TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

theorem fewJ_wiresLo : ∀ ds : List RDT, (∀ d ∈ ds, d.trees.length ≤ TypedOracleCompiler.Iop.maxRt) →
    FewJ (uLT C ds) (RoundSplits.allLocal (uLT C ds)) (wiresLo C K chal ds)
  | [], _ => trivial
  | d :: ds, h =>
    ⟨by
      show (d.trees.map (·.a)).length ≤ TypedOracleCompiler.Iop.maxRt
      rw [List.length_map]
      exact h d (List.mem_cons_self ..),
    fewJ_wiresLo ds fun e he => h e (List.mem_cons_of_mem _ he)⟩

theorem few0_wiresSh : ∀ ds : List RDT, (∀ d ∈ ds, d.trees.length ≤ TypedOracleCompiler.Iop.maxRt) →
    Few0 (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) (wiresSh C K chal ds)
  | [], _ => trivial
  | d :: ds, h =>
    ⟨by
      show (d.trees.map (·.a)).length ≤ TypedOracleCompiler.Iop.maxRt
      rw [List.length_map]
      exact h d (List.mem_cons_self ..),
    few0_wiresSh ds fun e he => h e (List.mem_cons_of_mem _ he)⟩

end

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (D : WholeD)
  {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3) (silent : Xi → TF → TJ → T3 → Bool)
  (run : Xi → View → View → View → Bool)

local notation "𝒞" => chainsOf C D tF tJ t3
local notation "𝒮" => wqWhole C K chal D tF tJ t3 silent run

theorem few₁_whole (h : ∀ d ∈ D.ds₁, d.trees.length ≤ TypedOracleCompiler.Iop.maxRt) :
    FewJ (𝒞).c₁ (𝒞).A₁ (wire₁ 𝒮) := by
  rw [wire₁_whole]
  exact ⟨Nat.zero_le _, fewJ_wiresLo C K chal D.ds₁ h⟩

theorem fewJ_whole : (wire₂ 𝒮).1.depthJ.length ≤ TypedOracleCompiler.Iop.maxRt := by
  rw [wire₂_whole]
  exact Nat.zero_le _

theorem fewJ0_whole : (wire₂ 𝒮).1.depth0.length ≤ TypedOracleCompiler.Iop.maxRt := by
  rw [wire₂_whole]
  exact Nat.zero_le _

theorem few₂_whole (h : ∀ d ∈ D.ds₂, d.trees.length ≤ TypedOracleCompiler.Iop.maxRt) :
    Few0 (𝒞).s₂ (RoundSplits.const (RAnn.ofShared .sh) (𝒞).s₂) (wire₂ 𝒮).2 := by
  rw [wire₂_whole]
  exact few0_wiresSh C K chal D.ds₂ h

theorem few₃_whole (h : ∀ d ∈ D.ds₃, d.trees.length ≤ TypedOracleCompiler.Iop.maxRt) :
    FewJ (𝒞).c₃ (𝒞).A₃ (wire₃ 𝒮) := by
  rw [wire₃_whole]
  exact ⟨Nat.zero_le _, fewJ_wiresLo C K chal D.ds₃ h⟩

end

end OnBytes.Maker
