-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Runnable/AtModelSizes.lean: the array program at the sizes ArrayProgram.modelShape
(Maverick's, with a window of 1,024) and the tables ArrayProgram.lookupTables compared with the
library's program at `{ ppref with T := n }` (n the context's length), a table of scales s : ScalesAndPolicy and
the tables tbRef.
  lookupTables_eq      the program's accessors to the packed numbers (Inst/Model/TablesData.lean)
                         are the library's refSILU, refSIGM, refExp, refC 0, refS 0
  tabRel_ref, good_ref   the hypotheses of IntegerModel/Runnable/Main.lean on tables and sizes hold
                         here
  next_atModelSizes          ArrayProgram.next on a context of tokens = the library's first choice
                         (argTo of lgK: the least token of largest logit) at the last position; none
                         exactly where the context is empty, longer than 1,024, or a range condition
                         (RunsK) fails.
                         Hypothesis: the program's settings and weights agree with the library's
                         inside the shapes
-/
import IntegerModel.Runnable.Main
import IntegerModel.Runnable.ArrayTables
import Inst.Model.ProgTests
import Inst.Model.TablesRef

set_option autoImplicit false

namespace IntegerModel.Runnable

open Inst.Model

/-- The library's reference tables as the program's record. refC and refS take the layer first and
give 2^12 and 0 in a layer without rotary step; layer 0 has the step, so refC 0 and refS 0 are the
entries of Data.cos and Data.sin less 4,096, clamped to ±4,096. -/
def tablesRef : ArrayProgram.Tables :=
  { silu := refSILU, sigmoid := refSIGM, exp := refExp, expRows := 2307,
    cos := refC 0, sin := refS 0 }

/-- the program's own accessors (core Lean, over the library's packed numbers) are the library's -/
theorem lookupTables_eq : ArrayProgram.lookupTables = tablesRef := by
  have hc' : refC 0 = fun i j => clamp 4096 ((dec Data.cos 14 (64 * i + j) : ℤ) - 4096) := by
    funext i j; exact if_neg (by decide)
  have hs' : refS 0 = fun i j => clamp 4096 ((dec Data.sin 14 (64 * i + j) : ℤ) - 4096) := by
    funext i j; exact if_neg (by decide)
  unfold tablesRef
  rw [hc', hs']
  rfl

theorem good_ref (n : ℕ) : Good { ppref with T := n } :=
  ⟨⟨64, rfl⟩, ⟨(by decide : 0 < 8), ⟨5, rfl⟩⟩, (by decide : 0 < 128)⟩

theorem hasRotary_iff (L : ℕ) : ArrayProgram.hasRotary L = true ↔ ¬ rotaryOff L := by
  unfold ArrayProgram.hasRotary rotaryOff
  simp

theorem tabRel_ref (s : ScalesAndPolicy) (L : ℕ) : TabRel tablesRef tbRef L (s.kap L).expRows where
  silu := rfl
  sigm := rfl
  exp := rfl
  rows := by
    unfold ScalesAndPolicy.kap
    split <;> rfl
  cos i j := by
    show _ = refC L i j
    by_cases h : rotaryOff L
    · rw [if_neg fun a => (hasRotary_iff L).1 a h]
      unfold refC
      rw [if_pos h]
    · rw [if_pos ((hasRotary_iff L).2 h)]
      show refC 0 i j = refC L i j
      unfold refC
      rw [if_neg h, if_neg (by decide)]
  sin i j := by
    show _ = refS L i j
    by_cases h : rotaryOff L
    · rw [if_neg fun a => (hasRotary_iff L).1 a h]
      unfold refS
      rw [if_pos h]
    · rw [if_pos ((hasRotary_iff L).2 h)]
      show refS 0 i j = refS L i j
      unfold refS
      rw [if_neg h, if_neg (by decide)]

theorem toks_eq {V : ℕ} (ctx : List (Fin V)) :
    (ctx.map fun y => y.val).toArray = Array.ofFn fun i : Fin ctx.length => (ctx.get i).val := by
  apply Array.ext
  · simp
  · intro i h1 h2
    simp

section Next
variable (s : ScalesAndPolicy) (w : Weights) (st : ArrayProgram.Settings)
  (hst : SameSettings ppref st s.kap s.nf) (W : ArrayProgram.Weights)
  (hW : SameWeights ppref W w) (ctx : List (Fin ppref.V))
include hst hW

/-- the form for use under any Decidable instance -/
theorem next_atModelSizes_is :
    Is (ArrayProgram.next ArrayProgram.modelShape ArrayProgram.lookupTables st
        W (ctx.map fun y => y.val).toArray)
      (0 < ctx.length ∧
        ctx.length ≤ ppref.T ∧
        RunsK { ppref with T := ctx.length } s.kap s.nf (fun _ => tbRef) w (fun i => ctx.get i))
      (argTo (lgK { ppref with T := ctx.length } s.kap s.nf (fun _ => tbRef) w
          (fun i => ctx.get i) (ctx.length - 1))
        (ppref.V - 1)) := by
  have h := next_is { ppref with T := ctx.length } s.kap s.nf (fun _ => tbRef) w
    (fun i => ctx.get i) (good_ref _) ppref.T tablesRef (fun L _ => tabRel_ref s L) st
    ⟨hst.layer, hst.final⟩ W ⟨fun L hL =>
      ⟨(hW.layer L hL).Wq, (hW.layer L hL).Wk, (hW.layer L hL).Wv, (hW.layer L hL).Wo,
        (hW.layer L hL).Wg, (hW.layer L hL).Wu, (hW.layer L hL).Wd, (hW.layer L hL).Wr,
        (hW.layer L hL).Eg, (hW.layer L hL).Eu, (hW.layer L hL).Ed⟩,
    hW.emb, hW.head⟩
  have hS : ArrayProgram.modelShape = shapeOf { ppref with T := ctx.length } ppref.T := rfl
  rw [lookupTables_eq, toks_eq, hS]
  exact h

/-- ArrayProgram.next, at modelShape and lookupTables, on a context of tokens is the library's first
choice at the last position; it is none exactly where the context is empty, longer than 1,024, or a
range condition fails. For any table of scales s, Lawful (Inst/Model/Scales.lean) or not; any
integer weights w, well formed (Weights.WF) or not; any list of tokens below 202,048. The program's
settings st and weights W agree with s and w inside the shapes (48 layers; each matrix's rows and
columns) and are arbitrary outside. -/
theorem next_atModelSizes
    [Decidable
        (RunsK { ppref with T := ctx.length } s.kap s.nf (fun _ => tbRef) w (fun i => ctx.get i))] :
    ArrayProgram.next ArrayProgram.modelShape ArrayProgram.lookupTables st
        W (ctx.map fun y => y.val).toArray =
      if 0 < ctx.length ∧
    ctx.length ≤ ppref.T ∧
    RunsK { ppref with T := ctx.length } s.kap s.nf (fun _ => tbRef) w (fun i => ctx.get i) then
          some (argTo
            (lgK { ppref with T := ctx.length } s.kap s.nf (fun _ => tbRef) w
              (fun i => ctx.get i) (ctx.length - 1)) (ppref.V - 1))
        else none :=
  (next_atModelSizes_is s w st hst W hW ctx).eq_ite

end Next

end IntegerModel.Runnable
