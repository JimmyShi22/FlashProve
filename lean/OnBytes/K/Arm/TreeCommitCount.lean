-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/TreeCommitCount.lean: the written committer `commitM` (OnBytes/K/Arm/TreeCommit.lean)
asks at most twice as many queries as it has rows.

States.
  `Rom.OComp.QueryBound.bindOut`: `OComp.QueryBound.bind` (Rom/Prefix.lean) where the second
    algorithm's count is known at the values that the first can return alone (`AllOut`,
    Compile/GenPub.lean).
  `queryBound_pairUp`, `queryBound_levelsM`, `queryBound_leavesM`, `queryBound_commitM`.

Limits. An upper bound: at 2 ^ a rows the true count is 2 ^ (a + 1) - 1. Of this library's term
alone; no program is counted. For proofs only; no program imports this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Arm.TreeCommit
import Compile.GenPub

set_option autoImplicit false

namespace Rom
open Compile.GenPub (AllOut)

variable {S : OSpec} {α β : Type}

/-- `OComp.QueryBound.bind` where the second algorithm's count is known at the values that the first
can return alone. -/
theorem OComp.QueryBound.bindOut {P : α → Prop} {c : OComp S α} {g : α → OComp S β} {s t : ℕ}
    (h : c.QueryBound s) (hP : AllOut P c) (hg : ∀ a, P a → (g a).QueryBound t) :
    (c.bind g).QueryBound (s + t) := by
  induction c generalizing s with
  | pure a => exact (hg a hP).mono (by omega)
  | query o q k ih =>
    cases s with
    | zero => exact h.elim
    | succ s =>
      have : s + 1 + t = (s + t) + 1 := by omega
      rw [this]
      exact fun r => ih r (h r) (hP r)
  | sample n k ih => exact fun r => ih r (h r) (hP r)

end Rom

namespace OnBytes.K.Arm
open Rom _root_.Compile
open _root_.Compile.GenPub (AllOut)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

theorem queryBound_pairUp (cfg : ByteArray) :
    ∀ l : List (Dig 256), (pairUp (vertexQ cfg) l).QueryBound (l.length / 2)
  | [] => trivial
  | [_] => trivial
  | a :: b :: t => by
      show ((vertexQ cfg a b).bind fun c =>
        (pairUp (vertexQ cfg) t).bind fun r => OComp.pure (c :: r)).QueryBound
          ((t.length + 1 + 1) / 2)
      have e : (t.length + 1 + 1) / 2 = 1 + (t.length / 2 + 0) := by omega
      rw [e]
      exact OComp.QueryBound.bind (s := 1) (fun _ => trivial) fun _ =>
        OComp.QueryBound.bind (queryBound_pairUp cfg t) fun _ => trivial

theorem allOut_pairUp (cfg : ByteArray) :
    ∀ l : List (Dig 256),
      AllOut (fun u => u.length + l.length / 2 = l.length) (pairUp (vertexQ cfg) l)
  | [] => by
      show ([] : List (Dig 256)).length + ([] : List (Dig 256)).length / 2 = _
      rfl
  | [x] => by
      show [x].length + [x].length / 2 = [x].length
      simp
  | a :: b :: t => by
      show AllOut _ ((vertexQ cfg a b).bind fun c =>
        (pairUp (vertexQ cfg) t).bind fun r => OComp.pure (c :: r))
      refine AllOut.bind (Q' := fun _ => True) (fun _ => trivial) fun c _ =>
        AllOut.bind (allOut_pairUp cfg t) fun r hr => ?_
      have hr' : r.length + t.length / 2 = t.length := hr
      show (c :: r).length + (a :: b :: t).length / 2 = (a :: b :: t).length
      simp only [List.length_cons]
      omega

/-- The building of the levels asks at most as many queries as the first level has entries. -/
theorem queryBound_levelsM (cfg : ByteArray) :
    ∀ (d : ℕ) (l : List (Dig 256)), (levelsM (vertexQ cfg) d l).QueryBound l.length
  | 0, _ => trivial
  | d + 1, l => by
      show ((pairUp (vertexQ cfg) l).bind fun u =>
        (levelsM (vertexQ cfg) d u).bind fun r => OComp.pure (l :: r)).QueryBound l.length
      have h := OComp.QueryBound.bindOut (t := l.length - l.length / 2)
        (g := fun u => (levelsM (vertexQ cfg) d u).bind fun r => OComp.pure (l :: r))
        (queryBound_pairUp cfg l) (allOut_pairUp cfg l) fun u hu => by
          have hu' : u.length + l.length / 2 = l.length := hu
          have e : l.length - l.length / 2 = u.length + 0 := by omega
          rw [e]
          exact OComp.QueryBound.bind (queryBound_levelsM cfg d u) fun _ => trivial
      exact h.mono (by omega)

theorem queryBound_leavesM : ∀ strs : List (List Bool), (leavesM strs).QueryBound strs.length
  | [] => trivial
  | s :: ss => by
      show ((OComp.ask () s).bind fun u =>
        (leavesM ss).bind fun us => OComp.pure (u :: us)).QueryBound (ss.length + 1)
      have e : ss.length + 1 = 1 + (ss.length + 0) := by omega
      rw [e]
      exact OComp.QueryBound.bind (s := 1) (fun _ => trivial) fun _ =>
        OComp.QueryBound.bind (queryBound_leavesM ss) fun _ => trivial

theorem allOut_leavesM : ∀ strs : List (List Bool),
    AllOut (fun us => us.length = strs.length) (leavesM strs)
  | [] => rfl
  | s :: ss => by
      show AllOut _ ((OComp.ask () s).bind fun u =>
        (leavesM ss).bind fun us => OComp.pure (u :: us))
      refine AllOut.bind (Q' := fun _ => True) (fun _ => trivial) fun u _ =>
        AllOut.bind (allOut_leavesM ss) fun us hus => ?_
      have hus' : us.length = ss.length := hus
      show (u :: us).length = (s :: ss).length
      simp only [List.length_cons]
      exact congrArg (· + 1) hus'

/-- **The written committer asks at most twice as many queries as it has rows.** -/
theorem queryBound_commitM (cfg : ByteArray) (k a : ℕ) (rows : List (List UInt64 × ByteArray)) :
    (commitM cfg k a rows).QueryBound (2 * rows.length) := by
  show ((leavesM (strsFrom cfg k a 0 rows)).bind fun l =>
    (levelsM (vertexQ cfg) a l).bind fun lv => OComp.pure (rootOf lv)).QueryBound (2 * rows.length)
  have h := OComp.QueryBound.bindOut (t := rows.length)
    (g := fun l => (levelsM (vertexQ cfg) a l).bind fun lv => OComp.pure (rootOf lv))
    (queryBound_leavesM (strsFrom cfg k a 0 rows)) (allOut_leavesM _) fun l hl => by
      have hl' : l.length = (strsFrom cfg k a 0 rows).length := hl
      rw [strsFrom_length] at hl'
      have e : rows.length = l.length + 0 := by omega
      rw [e]
      exact OComp.QueryBound.bind (queryBound_levelsM cfg a l) fun _ => trivial
  rw [strsFrom_length] at h
  exact h.mono (by omega)

end OnBytes.K.Arm

#print axioms OnBytes.K.Arm.queryBound_commitM
