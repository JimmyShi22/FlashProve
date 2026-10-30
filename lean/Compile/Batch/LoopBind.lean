-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/LoopBind.lean: what follows the search over nonces may be moved into its continuation,
for programs of `LStep` (Rom/DeferLate.lean): `tryL`, `fbWL`, `fbTGL`, `fbGL`, `fbSlotGL` of
Compile/Batch/Mirror.lean.
  `fbGL_bind`, `fbSlotGL_bind`
      (search .. k).bind f = search .. fun nc dd bl tl => (k nc dd bl tl).bind f

Notation: `k nc dd bl tl`, the continuation of a search; in `fbW` (Compile/Batch/Prover.lean), whose
late form is `fbWL`: k is given the number of the final attempt, the chaining values of those before
it, and the blocks and the chaining value of the final one; in `fbG`, `fbGL`: nc is an `Option ℕ`:
the number of the final attempt, if there is a record; `g`: a `GrW C P` (Iop/BatchWire.lean), a
proof-of-work record; `gr`: an `Option` of one; `h`: an `Option r.Chal`: the challenge, if it is
given; `last`: a `Bool`: is this the last attempt (`tryL`, Compile/Batch/Mirror.lean);
`Lp lam K L α` (Compile/Batch/Mirror.lean): `LStep (spec lam K L) (split lam K L) α`.
-/
import Compile.Batch.Mirror

namespace Compile.Batch
open Iop Rom

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {β γ : Type} {r : Round} {a : RAnn r}
  {P : Type} (w : WireRB lam K r a) (ab : Option r.Chal → ASet lam K) (t : Tag) (tk : Tok)
  (us : List Tok) (h : Option r.Chal)

theorem tryL_bind (g : GrW r.Chal P) (last : Bool)
    (mk : ASet lam K → Lp lam K L β) (f : β → Lp lam K L γ) :
    (tryL w g ab h last mk).bind f = tryL w g ab h last fun A => (mk A).bind f := by
  cases h <;> rfl

theorem fbWL_bind (g : GrW r.Chal P)
    (k : ℕ → List Tok → Blk lam K → Tok → Lp lam K L β) (f : β → Lp lam K L γ) :
    ∀ (n j : ℕ) (dd : List Tok), (fbWL w g ab t tk us h k n j dd).bind f =
      fbWL w g ab t tk us h (fun m d bl tl => (k m d bl tl).bind f) n j dd
  | 0, j, dd => by
      rw [fbWL, fbWL, tryL_bind]
      rfl
  | n + 1, j, dd => by
      rw [fbWL, fbWL, tryL_bind]
      refine congrArg _ (funext fun A => ?_)
      show fbLw t j tk us A (fun bl tl =>
          (if g.ok (w.chal bl) then k (j + 1) dd bl tl
            else fbWL w g ab t tk us h k n (j + 1) (tl :: dd)).bind f) = _
      refine congrArg _ (funext fun bl => funext fun tl => ?_)
      rw [apply_ite (fun z : Lp lam K L β => z.bind f), fbWL_bind g k f n (j + 1) (tl :: dd)]

theorem fbTGL_bind (g : GrW r.Chal P)
    (k : ℕ → List Tok → Blk lam K → Tok → Lp lam K L β) (f : β → Lp lam K L γ) :
    (fbTGL w g ab t tk us h k).bind f =
      fbTGL w g ab t tk us h fun m d bl tl => (k m d bl tl).bind f := by
  unfold fbTGL
  cases g.more with
  | zero =>
      show (tryL w g ab h true _).bind f = _
      rw [tryL_bind]
      rfl
  | succ n =>
      show (tryL w g ab h false _).bind f = _
      rw [tryL_bind]
      refine congrArg _ (funext fun A => ?_)
      show fbL t tk us A (fun bl tl =>
          (if g.ok (w.chal bl) then k 0 [] bl tl else fbWL w g ab t tk us h k n 0 [tl]).bind f) = _
      refine congrArg _ (funext fun bl => funext fun tl => ?_)
      rw [apply_ite (fun z : Lp lam K L β => z.bind f), fbWL_bind w ab t tk us h g k f n 0 [tl]]

/-- What follows the search may be moved into its continuation. -/
theorem fbGL_bind (gr : Option (GrW r.Chal P))
    (k : Option ℕ → List Tok → Blk lam K → Tok → Lp lam K L β) (f : β → Lp lam K L γ) :
    (fbGL w gr ab t tk us h k).bind f =
      fbGL w gr ab t tk us h fun nc dd bl tl => (k nc dd bl tl).bind f := by
  cases gr with
  | none => rfl
  | some g => exact fbTGL_bind w ab t tk us h g (fun m => k (some m)) f

theorem fbSlotGL_bind (gr : Option (GrW r.Chal P)) (ph : PhT) (c : Tok) (root : Option Tok)
    (k : Option ℕ → List Tok → Blk lam K → Tok → Lp lam K L β) (f : β → Lp lam K L γ) :
    (fbSlotGL w gr ab t ph tk c root h k).bind f =
      fbSlotGL w gr ab t ph tk c root h fun nc dd bl tl => (k nc dd bl tl).bind f := by
  cases ph <;> exact fbGL_bind w ab t _ _ h gr k f

end Compile.Batch
