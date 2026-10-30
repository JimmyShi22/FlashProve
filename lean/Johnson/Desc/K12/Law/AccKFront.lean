-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.GpOfPass
import Johnson.Desc.K12.Law.TopH
import Johnson.Desc.K12.Law.BatOk
/-
Johnson/Desc/K12/Law/AccKFront.lean: A YES OF accK PAYS WHAT STANDS IN FRONT OF THE GAME: FrontK at its own first round. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING. OF proximityTestKind guardedProximityTestParts p (whose batching's part asks gpOk).
  accK_front        accK p F t0 r0 c ts W τ = true ⇒ ∃ e row Ly S' D x, gpL's yes ∧ FrontK p t0 a r0 e row Ly S' D ∧ r0 as shown draws just the one element x
  front_of_notDoomed  ¬ Doomed … (accK … r0 … = false) ⇒ the same: by the library's Doomed.of_forall: where no transcript is accepted every prover is doomed
EVERY THEOREM OF THIS FILE IS PROVED OUTRIGHT: nothing is left open and nothing is laid down by decree; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.First (gpOk gpOf gpL Plain gpOk_inv)
open H2K.ClaimSays (bat_ok)


theorem accK_front (p : P12) (F : ℕ) (t0 : T12) (r0 : Fmt.RoundView) {s : Sg} (c : Chain s)
    (ts : List ℕ) (W : c.Bl → ℕ → WO) (τ : Tr (PQ.uL (ckP .two) c.rds)) (he : p.early = true)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hs : p.nums.stages = a :: rest) (h : accK p F t0 r0 c ts W τ = true) :
    ∃ (e : Fmt.Entry) (row : GroupRow) (Ly : GroupLayout) (S' : Statement) (D : Plain) (x : E),
      H2K.First.ok (gpL p a row D) = true ∧ FrontK p t0 a r0 e row Ly S' D ∧
      (noDigest r0).drawn.elems.map E.ofTriple = [x] := by
  unfold accK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, _⟩ := h
  split at h1
  · rename_i v heq
    obtain ⟨_, _, hdec⟩ := Prox.step_ok F _ t0 v.1 _ _ v.2 heq
    obtain ⟨_, _, e, r, row, L, S', hr, hb, hg⟩ := k12_guards p he t0 v.1 _ _ hp hdec
    obtain rfl : noDigest r0 = r := (List.cons.inj hr).1
    obtain ⟨D, hD, hok⟩ := gpOk_inv p _ a rest row L hs rfl hg
    obtain ⟨_, x, _, _, _, hx, _⟩ := bat_ok _ _ _ _ _ _ _ hb
    exact ⟨e, row, L, S', D, x, hok, ⟨hb, hg, hD⟩, hx⟩
  · cases h1


theorem front_of_notDoomed (p : P12) (F : ℕ) (t0 : T12) (r0 : Fmt.RoundView) {s : Sg} (c : Chain s)
    (ts : List ℕ) (W : c.Bl → ℕ → WO) (he : p.early = true)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hs : p.nums.stages = a :: rest)
    (h : ¬ Doomed (PQ.uL (ckP .two) c.rds) c.errL fun τ => accK p F t0 r0 c ts W τ = false) :
    ∃ (e : Fmt.Entry) (row : GroupRow) (Ly : GroupLayout) (S' : Statement) (D : Plain) (x : E),
      H2K.First.ok (gpL p a row D) = true ∧ FrontK p t0 a r0 e row Ly S' D ∧
      (noDigest r0).drawn.elems.map E.ofTriple = [x] := by
  by_contra hn
  apply h
  refine Doomed.of_forall _ _ fun τ => ?_
  cases hacc : accK p F t0 r0 c ts W τ with
  | false => rfl
  | true => exact absurd (accK_front p F t0 r0 c ts W τ he hp a rest hs hacc) hn

end H2K.JointK

#print axioms H2K.JointK.accK_front
#print axioms H2K.JointK.front_of_notDoomed
