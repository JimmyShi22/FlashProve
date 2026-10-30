-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/ViewK.lean: the written view of the proximity test (the kind K12): columns made
of the declared groups and of written columns, opening by opening; that they follow (Follows,
Johnson/Desc/K12/Law/Written.lean); and when Block.step's test "the columns" is met on them.

Definitions, statements and proofs, over Follows, Follows.drop and srcFirst
(Johnson/Desc/K12/Law/Written.lean) and Want and kpw (Johnson/Desc/K12/Law/StepGroups.lean).
Main names:
  `colsFrom`, `colsOf`: the columns: for group number i, at each of its wants (key, position,
    width): the key, the position, and src i at the position.
  `colsFrom_length`: they are as many as the wants.
  `follows_from`, `follows_colsOf`: laid into groups by the groups' lengths (regroup), they follow
    src.
  `kpw_from`, `kpw_colsOf`: their key, position and width are the wants just where the written
    columns have the declared widths; then the second line of Block.step is met.
  `srcK`, `follows_view`: at the place: in front of the batching's openings nothing, behind them
    srcFirst; what the frame deals to the stages (grpsS) follows srcFirst.
Limits: No soundness is claimed, and nothing is said on hiding.
It does not say that a prover's view is colsOf of anything.
Every theorem of this file is proved outright; what each rests on is printed at the file's end.

-/
import Johnson.Desc.K12.Law.Written
import Johnson.Desc.K12.Law.StepGroups

set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw (Want kpw)

/-- The columns of the groups, the first of which has the number n. -/
def colsFrom (n : ℕ) (groups : List (List Want)) (src : ℕ → ℕ → List UInt64) :
    List VerifiableInference.Desc.OpenedColumn :=
  (groups.zipIdx n).flatMap fun x => x.1.map fun w => (w.1, w.2.1, src x.2 w.2.1)

/-- The written view's columns. src i x: the written column behind opening number i, at x. -/
def colsOf (groups : List (List Want)) (src : ℕ → ℕ → List UInt64) :
    List VerifiableInference.Desc.OpenedColumn :=
  groups.zipIdx.flatMap fun x => x.1.map fun w => (w.1, w.2.1, src x.2 w.2.1)

theorem colsOf_eq (groups : List (List Want)) (src : ℕ → ℕ → List UInt64) :
    colsOf groups src = colsFrom 0 groups src := rfl

theorem colsFrom_cons (n : ℕ) (g : List Want) (gs : List (List Want))
    (src : ℕ → ℕ → List UInt64) :
    colsFrom n (g :: gs) src =
      g.map (fun w => (w.1, w.2.1, src n w.2.1)) ++ colsFrom (n + 1) gs src := by
  unfold colsFrom
  rw [List.zipIdx_cons, List.flatMap_cons]

theorem colsFrom_length (src : ℕ → ℕ → List UInt64) : ∀ (groups : List (List Want)) (n : ℕ),
    (colsFrom n groups src).length = (groups.flatMap id).length
  | [], _ => rfl
  | g :: gs, n => by
    rw [colsFrom_cons, List.flatMap_cons, List.length_append, List.length_append, List.length_map,
      colsFrom_length src gs (n + 1)]
    rfl

theorem follows_from (src : ℕ → ℕ → List UInt64) : ∀ (groups : List (List Want)) (n i : ℕ)
    (grp : List (ℕ × List UInt64)),
    (regroup (groups.map (·.length)) (colsFrom n groups src))[i]? = some grp →
    ∀ x ∈ grp, x.2 = src (n + i) x.1
  | [], _, _, _, h => by cases h
  | g :: gs, n, i, grp, h => by
    rw [colsFrom_cons] at h
    have hl : (g.map fun w : Want => ((w.1, w.2.1, src n w.2.1) :
        VerifiableInference.Desc.OpenedColumn)).length
        = g.length := List.length_map _
    have h' : ((((g.map fun w : Want => ((w.1, w.2.1, src n w.2.1) : VerifiableInference.Desc.OpenedColumn))
        ++
        colsFrom (n + 1) gs src).take g.length).map fun c => (c.2.1, c.2.2)) ::
        regroup (gs.map (·.length))
          (((g.map fun w : Want => ((w.1, w.2.1, src n w.2.1) : VerifiableInference.Desc.OpenedColumn)) ++
            colsFrom (n + 1) gs src).drop g.length) = regroup ((g :: gs).map (·.length))
          ((g.map fun w : Want => ((w.1, w.2.1, src n w.2.1) : VerifiableInference.Desc.OpenedColumn)) ++
            colsFrom (n + 1) gs src) := rfl
    rw [← h', List.take_left' hl, List.drop_left' hl] at h
    cases i with
    | zero =>
      obtain rfl := Option.some.inj h
      intro x hx
      rw [List.map_map] at hx
      obtain ⟨w, _, rfl⟩ := List.mem_map.1 hx
      rfl
    | succ i =>
      intro x hx
      have := follows_from src gs (n + 1) i grp h x hx
      rw [this]
      congr 1
      omega

/-- The written view's columns, laid into groups as Block.step lays them, follow src. -/
theorem follows_colsOf (groups : List (List Want)) (src : ℕ → ℕ → List UInt64) :
    Follows (regroup (groups.map (·.length))
      ((colsOf groups src).take (groups.flatMap id).length)) src := by
  intro i grp hi x hx
  rw [colsOf_eq, List.take_of_length_le (by rw [colsFrom_length])] at hi
  have := follows_from src groups 0 i grp hi x hx
  rwa [Nat.zero_add] at this

theorem kpw_from (src : ℕ → ℕ → List UInt64) : ∀ (groups : List (List Want)) (n : ℕ),
    (∀ (i : ℕ) (grp : List Want) (w : Want), groups[i]? = some grp → w ∈ grp →
      (src (n + i) w.2.1).length = w.2.2) →
    (colsFrom n groups src).map kpw = groups.flatMap id
  | [], _, _ => rfl
  | g :: gs, n, h => by
    rw [colsFrom_cons, List.map_append, List.flatMap_cons, List.map_map,
      kpw_from src gs (n + 1) fun i grp w hi hw => by
        have := h (i + 1) grp w hi hw
        rwa [show n + (i + 1) = n + 1 + i by omega] at this]
    congr 1
    refine (List.map_congr_left fun w hw => ?_).trans (List.map_id' g)
    have e : (src n w.2.1).length = w.2.2 := h 0 g w rfl hw
    show (w.1, w.2.1, (src n w.2.1).length) = w
    rw [e]

/-- Their key, position and width are the wants, where the written columns have the declared widths.
-/
theorem kpw_colsOf (groups : List (List Want)) (src : ℕ → ℕ → List UInt64)
    (h : ∀ (i : ℕ) (grp : List Want) (w : Want), groups[i]? = some grp → w ∈ grp →
      (src i w.2.1).length = w.2.2) :
    (colsOf groups src).map kpw = groups.flatMap id :=
  kpw_from src groups 0 fun i grp w hi hw => by rw [Nat.zero_add]; exact h i grp w hi hw

/-- The written columns behind the openings of the whole test: nothing behind the batching's own (it
opens none at the four places); behind them srcFirst. -/
def srcK (p : P12) {s : Sg} (c : OnBytes.Slice.Chain s) (b : c.Bl) (ts : List ℕ) (gT : ℕ → ℕ → List
    UInt64)
    (i : ℕ) : ℕ → List UInt64 :=
  if i < nOpen (((laidOf p).take 1).map (·.1)) then fun _ => []
  else srcFirst c b (laidS p) ts gT (i - nOpen (((laidOf p).take 1).map (·.1)))

/-- At the place: what the frame deals to the stages, of the written view, follows srcFirst. -/
theorem follows_view (p : P12) {s : Sg} (c : OnBytes.Slice.Chain s) (b : c.Bl) (ts : List ℕ)
    (gT : ℕ → ℕ → List UInt64) (groups : List (List Want)) :
    Follows (grpsS p (regroup (groups.map (·.length))
      ((colsOf groups (srcK p c b ts gT)).take (groups.flatMap id).length)))
      (srcFirst c b (laidS p) ts gT) := by
  unfold grpsS
  refine (follows_colsOf groups (srcK p c b ts gT)).drop _ _ fun i x => ?_
  unfold srcK
  rw [if_neg (by omega), Nat.add_sub_cancel_left]

end H2K.JointK
