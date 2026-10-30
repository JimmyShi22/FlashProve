-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeySide3.lean: THE STATE's SIDE OF THE LIBRARY's PROMISE ON THE KEY FILE's LAST CHAIN (its
`Tests₃`, Johnson/RunOne/KeyOn3Parts.lean, at its own letters, with "the codes' lengths are in
order": `T₃L`, Johnson/Top/Fire/Code/KeyASide3AtFk.lean): ITS START AND ITS FOUR STEPS, in scope, in
the form that a thread can spend: from an accepting step of the sub-protocol as it is. By calls. On
the verifier's states alone. No thread is in it. NOTHING IS SHOWN OF ANY PROVER.

THE LIBRARY HAS IT ALONG ITS OWN HISTORY (`aSide₃_at_all`, KeyASide3All.lean). Its four steps
(`step₃_01`, `step₃_12`, `step₃_23`, `step₃_34`) are proved of the sub-protocols as they are, at
every handed half; its start (`tests₃_start`, Johnson/RunOne/KeyTests3Steps.lean) takes the shared
chain's side at its last border and the yes of the last chain's start, and no oracle.

  (`Side₃ X P k z`, E2E/KeySideDef.lean: `T₃L` at the library's seats and numbers)
  **`steps₃`**: THE FOUR, GATHERED, in scope: a list of calls, as they stand inside the proof of
      `aSide₃_of_hist`; what they ask is paid by the calls of the proof of `aSide₃_at_all`
  **`side₃_step`**: ONE STEP, from an accepting step (`StepYes`), at what the description is made of
  **`side₃_start`**: THE START: the shared chain's side at border 12 at (x, e₁, e₂), and the start's
      yes, give `Side₃` at border 0

Limits.

- The oracles' side of the promise is not in it.
- At the library's own seats and numbers: the full size's.
- Implications: they say nothing where no step accepts.

-/
import E2E.KeyStateSide2
import Johnson.Top.Fire.Code.KeyASide3All

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyThread

section
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key (FirstState Claim Xi)
open Johnson.RunOne.KeyRows1 (plan₁)
open Johnson.RunOne.KeyRows23
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.Desc.First.Walk.Tied (StepYes)
open LPFD

variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
variable {Zp : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public} {cfg : ByteArray}
  {m : Johnson.G.OfPlan.Made}

/-- **The four steps, gathered.** -/
theorem steps₃ (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀)
    (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hp : (Fk X N P).planOk = true) :
    ∀ j, j < 4 → ∀ b, (Fk X N P).second.blocksInOrder[j]? = some b →
      StepInvP (P := P₃) b (Side₃ X P j) (Side₃ X P (j + 1)) := by
  have hst : (oneAt X).ranges.stages.length = 4 := by
    rw [(one_full hZ hP hm hX hp).1]
    exact Johnson.RunOne.KeyLetters.stages_full
  have hat : AtOk atSix off₂N off₃N ((oneAt X).ranges.stages.length + 2) := by
    rw [hst]
    exact atOk_six
  intro j hj b hb
  match j, hj with
  | 0, _ => exact step₃_01 X N P atSix off₂N off₃N hat b hb
  | 1, _ => exact step₃_12 X N P atSix off₂N off₃N b hb
  | 2, _ =>
    exact step₃_23 X N P atSix off₂N off₃N (fileOk_of_planOk' _ hp)
      (Johnson.RunOne.KeySendGood.samples_in_scope hZ hP hm hX hp) b hb
  | 3, _ => exact step₃_34 X N P atSix off₂N off₃N b hb
  | n + 4, h4 => exact absurd h4 (by omega)

/-- **ONE STEP**, from an accepting step. -/
theorem side₃_step {Z : VerifierAndGoals.PublicFiles} (hs : AtPublicFiles.AtFiles.KeySourced Z X N P)
    (scope : VerifierAndGoals.InScope Z = true) {b : Nat} (hb : b < 4)
    {blk : Block St₃ VerifiableInference.Desc.Key.Claim}
    (hblk : (Fk X N P).second.blocksInOrder[b]? = some blk) {ft : Nat} {s s' : St₃}
    (hy : StepYes ft blk s s') {p : P₃} (h : Side₃ X P b (p, s)) : Side₃ X P (b + 1) (p, s') := by
  obtain ⟨X₀, m, h0, hm, hX, -, -⟩ := hs.source
  obtain ⟨R, c, -, e⟩ := hy
  have q := (step_ok_iff ft blk s s' R c c.length).1 e
  exact steps₃ X N P scope (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO h0) hm hX hs.named.plan b hb
    blk hblk p s s' R _ q.1 q.2.2.2 h

/-- **THE START.** -/
theorem side₃_start (x : Xi) (e₁ : FirstState) (e₂ : St₂) (s₃ : St₃)
    (hst : (Fk X N P).start₃ x e₁ e₂ = .ok s₃) (T : T₂ X atSix off₂N 12 ((x, e₁), e₂)) :
    Side₃ X P 0 ((x, e₁, e₂), s₃) :=
  tests₃_start atSix (shapeAt X) (plan₁ (oneAt X)) (oneAt X).given.plan.samples [0]
    (last₁At (oneAt X)) (srcOk (ownTest P)) off₂N off₃N ((oneAt X).ranges.stages.length + 2)
    (codesAt X) (fun x s₁ s₂ => (Fk X N P).start₃ x s₁ s₂) (starts_fkD X N P)
    (last₁_gives (oneAt X)) off_six x e₁ e₂ s₃ hst T

end

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.steps₃
#print axioms AtPublicFiles.KeyThread.side₃_step
#print axioms AtPublicFiles.KeyThread.side₃_start
