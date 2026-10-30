-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/HomFmtProofs.lean: the proofs of the statements of Run/HomFmt.lean.

The statements: for every morphism of monads `φ : Hom m n` (Run/Hom.lean) and each function F of
the format named there, φ.app (F h ..) = F (φ.on h) .. (for `HM` and the three walks: with ask,
comb in the place of h). What is not said: Run/HomFmt.lean, the head, Limits.

One lemma for each function (`Run.Hom.HM` to `Run.Hom.wholeChain`: for use by name).

Terms: lean/GLOSSARY.md.
-/
import Run.HomFmt

set_option autoImplicit false

namespace Run

namespace Hom
variable {m n : Type → Type} [Monad m] [Monad n] (φ : Hom m n)
open _root_.Fmt

theorem HM (ask : ByteArray → m ByteArray) (number tree index : Nat) (start bytes : ByteArray) :
    φ.app (Fmt.HM ask number tree index start bytes) =
      Fmt.HM (fun s => φ.app (ask s)) number tree index start bytes := by
  unfold Fmt.HM
  split
  · simp only [φ.app_bind, φ.app_pure]
  · rfl

variable (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray)

/-! ### The first query -/

theorem startChainW (lab : Nat) (pd statement : ByteArray) (rnd : Option ByteArray) :
    φ.app (Fmt.startChainW h lab pd statement rnd) =
      Fmt.startChainW (φ.on h) lab pd statement rnd := by
  unfold Fmt.startChainW
  split
  · split
    · simp only [φ.app_bind, φ.app_pure]
      rfl
    · split
      · simp only [φ.app_bind]
        refine congrArg _ (funext fun run => ?_)
        split
        · simp only [φ.app_bind, φ.app_pure]
          rfl
        · exact φ.app_pure _
      · exact φ.app_pure _
  · exact φ.app_pure _

/-! ### A round's query -/

theorem fetchFrom (lab : Nat) (rho : ByteArray) (i : Nat) (msg : ByteArray)
    (kind : Kind) (w nonce : Nat) :
    ∀ (k j : Nat) (acc : Array ByteArray),
      φ.app (Fmt.fetchFrom h lab rho i msg kind w nonce k j acc) =
        Fmt.fetchFrom (φ.on h) lab rho i msg kind w nonce k j acc
  | 0, _, _ => φ.app_pure _
  | k + 1, j, acc => by
    simp only [Fmt.fetchFrom, φ.app_bind, fetchFrom lab rho i msg kind w nonce k]
    rfl

theorem fetchW (lab : Nat) (rho : ByteArray) (i : Nat) (msg : ByteArray)
    (kind : Kind) (w nonce k : Nat) :
    φ.app (Fmt.fetchW h lab rho i msg kind w nonce k) =
      Fmt.fetchW (φ.on h) lab rho i msg kind w nonce k := by
  simp only [Fmt.fetchW, φ.app_bind, φ.app_pure, fetchFrom]

theorem queryW (c : Chain) (msg : ByteArray) (kind : Kind) (work nonce K : Nat) :
    φ.app (c.queryW h msg kind work nonce K) = c.queryW (φ.on h) msg kind work nonce K := by
  unfold Chain.queryW
  split
  · simp only [φ.app_bind, φ.app_pure, fetchW]
  · exact φ.app_pure _

/-! ### A tree and its opening -/

section
variable {α σ : Type} (comb : Nat → Nat → α → α → m α) (give : Nat → Nat → σ → Option (α × σ))

theorem walkLoneW (d i : Nat) (x : α) (s : σ) :
    φ.app (Fmt.walkLoneW comb give d i x s) =
      Fmt.walkLoneW (fun a b c e => φ.app (comb a b c e)) give d i x s := by
  unfold Fmt.walkLoneW
  split
  · exact φ.app_pure _
  · split <;> simp only [φ.app_bind, φ.app_pure]

theorem walkLevelW (d : Nat) :
    ∀ (l : List (Nat × α)) (s : σ), φ.app (Fmt.walkLevelW comb give d l s) =
      Fmt.walkLevelW (fun a b c e => φ.app (comb a b c e)) give d l s
  | [], s => φ.app_pure _
  | [(i, x)], s => by simp only [Fmt.walkLevelW, φ.app_bind, φ.app_pure, walkLoneW]
  | (i, x) :: (i', x') :: rest, s => by
    unfold Fmt.walkLevelW
    split
    · simp only [φ.app_bind, φ.app_pure, walkLevelW d rest]
    · simp only [φ.app_bind, walkLoneW]
      refine congrArg _ (funext fun r => ?_)
      cases r with
      | none => exact φ.app_pure _
      | some p => simp only [φ.app_bind, φ.app_pure, walkLevelW d ((i', x') :: rest)]

theorem walkW :
    ∀ (d : Nat) (now : List (Nat × α)) (s : σ) (met : List (Nat × Nat × α)),
      φ.app (Fmt.walkW comb give d now s met) =
        Fmt.walkW (fun a b c e => φ.app (comb a b c e)) give d now s met
  | 0, now, s, met => by
    unfold Fmt.walkW
    split <;> first | exact φ.app_pure _ | simp_all
  | d + 1, now, s, met => by
    simp only [Fmt.walkW, φ.app_bind, walkLevelW]
    refine congrArg _ (funext fun r => ?_)
    cases r with
    | none => exact φ.app_pure _
    | some p => exact walkW d _ _ _

end

theorem leavesW (sh : Shape) (start : ByteArray) :
    ∀ (xs : List Nat) (cs : List (List UInt64 × ByteArray)),
      φ.app (Fmt.leavesW h sh start xs cs) = Fmt.leavesW (φ.on h) sh start xs cs
  | x :: xs, (col, salt) :: cs => by
    simp only [Fmt.leavesW, φ.app_bind, φ.app_pure, leavesW sh start xs cs]
    rfl
  | [], _ => by simp only [Fmt.leavesW, φ.app_pure]
  | _ :: _, [] => by simp only [Fmt.leavesW, φ.app_pure]

theorem readOpeningW (cfg : ByteArray) (f : Fld) (salt : Nat) (sh : Shape) (start : ByteArray)
    (xs : List Nat) (b : ByteArray) (i : Nat) :
    φ.app (Fmt.readOpeningW h cfg f salt sh start xs b i) =
      Fmt.readOpeningW (φ.on h) cfg f salt sh start xs b i := by
  unfold Fmt.readOpeningW
  split
  · split
    · exact φ.app_pure _
    · simp only [φ.app_bind, φ.app_pure, leavesW, walkW]
      rfl
  · exact φ.app_pure _

theorem checkOpeningW (cfg : ByteArray) (f : Fld) (salt : Nat) (sh : Shape) (start root : ByteArray)
    (xs : List Nat) (opening : ByteArray) :
    φ.app (Fmt.checkOpeningW h cfg f salt sh start root xs opening) =
      Fmt.checkOpeningW (φ.on h) cfg f salt sh start root xs opening := by
  simp only [Fmt.checkOpeningW, φ.app_bind, readOpeningW]
  refine congrArg _ (funext fun r => ?_)
  cases r <;> exact φ.app_pure _

/-! ### A chain in a file -/

theorem readOpens (cfg : ByteArray) (P : Plan) (run : Option ByteArray) (roots : Array ByteArray)
    (poss : List Nat) (b : ByteArray) :
    ∀ (os : List (Shape × Src)) (sn : Seen) (i : Nat),
      φ.app (Fmt.readOpens h cfg P run roots poss b os sn i) =
        Fmt.readOpens (φ.on h) cfg P run roots poss b os sn i
  | [], _, _ => φ.app_pure _
  | (sh, src) :: os, sn, i => by
    unfold Fmt.readOpens
    simp only []
    split
    · exact φ.app_pure _
    · simp only [φ.app_bind, readOpeningW]
      refine congrArg _ (funext fun r => ?_)
      cases r with
      | none => exact φ.app_pure _
      | some o =>
        simp only []
        split
        · split
          · exact φ.app_pure _
          · simp only [φ.app_bind, readOpens cfg P run roots poss b os]
            refine congrArg _ (funext fun r => ?_)
            cases r <;> exact φ.app_pure _
        · exact φ.app_pure _

theorem step (cfg : ByteArray) (P : Plan) (run : Option ByteArray)
    (b : ByteArray) (s : St) (r : Round) :
    φ.app (Fmt.step h cfg P run b s r) = Fmt.step (φ.on h) cfg P run b s r := by
  unfold Fmt.step
  split
  · exact φ.app_pure _
  · split
    · exact φ.app_pure _
    · split
      · exact φ.app_pure _
      · simp only [φ.app_bind, queryW]
        refine congrArg _ (funext fun q => ?_)
        cases q with
        | none => exact φ.app_pure _
        | some cv =>
          simp only []
          split
          · exact φ.app_pure _
          · simp only [φ.app_bind, readOpens]
            refine congrArg _ (funext fun q => ?_)
            cases q <;> exact φ.app_pure _

theorem foldRounds (cfg : ByteArray) (P : Plan) (run : Option ByteArray) (b : ByteArray) :
    ∀ (rs : List Round) (s : St),
      φ.app (Fmt.foldRounds h cfg P run b rs s) = Fmt.foldRounds (φ.on h) cfg P run b rs s
  | [], _ => φ.app_pure _
  | r :: rs, s => by
    simp only [Fmt.foldRounds, φ.app_bind, step]
    refine congrArg _ (funext fun q => ?_)
    cases q with
    | none => exact φ.app_pure _
    | some s' => exact foldRounds cfg P run b rs s'

theorem readChain (S : Fmt.Spec) (seen : Seen) (b : ByteArray) (i : Nat) :
    φ.app (Fmt.readChain h S seen b i) = Fmt.readChain (φ.on h) S seen b i := by
  unfold Fmt.readChain
  split
  · exact φ.app_pure _
  · simp only []
    split
    · exact φ.app_pure _
    · simp only [φ.app_bind, startChainW]
      refine congrArg _ (funext fun pd => ?_)
      refine congrArg _ (funext fun q => ?_)
      cases q with
      | none => exact φ.app_pure _
      | some hd =>
        simp only [φ.app_bind, foldRounds]
        refine congrArg _ (funext fun q => ?_)
        cases q <;> exact φ.app_pure _

theorem wholeChain (S : Fmt.Spec) (b : ByteArray) :
    φ.app (Fmt.wholeChain h S b) = Fmt.wholeChain (φ.on h) S b := by
  simp only [Fmt.wholeChain, φ.app_bind, readChain]
  refine congrArg _ (funext fun q => ?_)
  cases q <;> exact φ.app_pure _

end Hom

theorem hom_HM : Spec.hom_HM := fun _ _ _ _ φ => φ.HM

theorem hom_first : Spec.hom_first := fun _ _ _ _ φ h => φ.startChainW h

theorem hom_round : Spec.hom_round := fun _ _ _ _ φ h => ⟨φ.fetchFrom h, φ.fetchW h, φ.queryW h⟩

theorem hom_tree : Spec.hom_tree := fun _ _ _ _ φ =>
  ⟨fun _ _ comb give => ⟨φ.walkLoneW comb give, φ.walkLevelW comb give, φ.walkW comb give⟩,
    fun h => ⟨φ.leavesW h, φ.readOpeningW h, φ.checkOpeningW h⟩⟩

theorem hom_file : Spec.hom_file := fun _ _ _ _ φ h =>
  ⟨φ.readOpens h, φ.step h, φ.foldRounds h, φ.readChain h, φ.wholeChain h⟩

end Run
