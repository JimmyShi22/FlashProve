-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Slots/FillsMore.lean: WHAT THE BATCHED SUMCHECK's HEARING FILLS, THAT ITS TWO END
FORMS NAME NO SLOT, AND WHICH SLOTS THE MERGE's START FORM NAMES. Statements and proofs, read off
laws (`hearStack_tape`, OnBytes/Desc/First/K4/StackTape.lean; `hearStack_public`,
StackPublic.lean; `endP_spec`, `filledA_of_publicPart`, OnBytes/Desc/First/P1/; the rules on what a
plain function returns, Johnson/Road/K4/Reads/HearStarts.lean) and off Panels.lean.

  `stretch`: from "at a + i, i < n" to "at j, a ≤ j < a + n".
  `stack_fills`: where `hearStack` returns K, from a ledger F with arrays of the right sizes to G: G
    is `Sized`; what is filled in F is filled in G; the 2 + (1 + LamM) + NCLp slots from K.sA0 on
    are filled in G; where K.sH1, K.sB0, K.sV lie among them; and EVERY SLOT THAT THE BATCHED
    SUMCHECK's OWN CLAIM K.rowS NAMES IS FILLED IN G: it lays its own window itself, and it begins
    only where the public part of its start form is there, which is so only where every slot of that
    form is filled (the lookup's form `fo.cEnd` is a part of it).
  `stack_fin`: K.fin.Alin and K.fin.Blin are `SlotsIn S` at every S: they name no slot.
  `slotsIn_wsForkStart`, `merge_start`: the merge's start form is `wsForkStart sv rho` at some rho:
    it names slots of the list sv alone.

Limits. One direction, from a return. Nothing on what lies under a slot. Nothing on soundness.

-/
import Johnson.Road.K4.Slots.Fills
import Johnson.Road.K4.Slots.Panels
import Johnson.Road.K4.Reads.HearStarts
import OnBytes.Desc.First.K4.StackTape
import OnBytes.Desc.First.K4.StackPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Slots

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub Env Heard HeardStack)
open OnBytes.PscRun (Sized Filled)
open OnBytes.Desc.First.P1 (endP_spec filledA_of_publicPart)
open OnBytes.Desc.First.K4.Reads (Ret ret_pscBegin ret_wsForkRounds ret_pscEnds)

theorem stretch {a n : ℕ} {Φ : ℕ → Prop} (h : ∀ i, i < n → Φ (a + i)) :
    ∀ j, a ≤ j → j < a + n → Φ j := fun j h1 h2 => by
  have e := h (j - a) (by omega)
  rwa [Nat.add_sub_cancel' h1] at e

/-- **The batched sumcheck.** -/
theorem stack_fills {P : Pub} {v : Env} {H : Heard} {lamS NCLp : ℕ} {F G : Fork} {t u : Tape}
    {K : HeardStack} (hF : Sized F) (h : hearStack engFl P v H lamS NCLp F t = some (K, G, u)) :
    Sized G ∧ (∀ j, Filled F j → Filled G j) ∧
      (∀ i, i < 2 + (1 + P.y.LamM) + NCLp → Filled G (K.sA0 + i)) ∧
      K.sH1 = K.sA0 + 1 ∧ K.sB0 = K.sA0 + 1 + (1 + P.y.LamM) ∧
      K.sV = K.sA0 + (2 + (1 + P.y.LamM)) ∧ SlotsIn (Filled G) K.rowS := by
  obtain ⟨x, mu0, eps, beta, T, rs, sentY, vals, w1, wY, wV, C, G1, ms, y, p, _, _, _, _, hpub, _,
    _, hp, _, _, _, _, _, h1, h2, h3, hv, r1, hrow, r2⟩ := hearStack_tape h
  obtain ⟨s1, k1, f1⟩ := run_fills (show Sized ({ F with
    next := F.next + 1 + 2 * lamS + 2 + (2 + (1 + P.y.LamM) + NCLp) } : Fork) from hF) r1
  obtain ⟨s2, k2, f2⟩ := run_fills s1 r2
  have hst : p.start = C := by
    rw [hp]
    exact (endP_spec _ _ _).2.2.2.1
  refine ⟨s2, fun j hj => k2 j (k1 j hj), fun i hi => k2 _ (f1 i (by omega)), h1, by omega,
    by omega, ?_⟩
  rw [hrow]
  refine slotsIn_rowForm _ _ (fun i hi => f2 i (by simpa using hi)) ?_ slotsIn_empty
  rw [hst]
  exact fun x hx => k2 _ (k1 _ (filledA_of_publicPart hpub x hx).2)

variable {S : ℕ → Prop}

/-- **The two forms that the end of the batched sumcheck leaves name no slot.** -/
theorem stack_fin {P : Pub} {v : Env} {H : Heard} {lamS NCLp : ℕ} {F G : Fork} {t u : Tape}
    {K : HeardStack} (h : hearStack engFl P v H lamS NCLp F t = some (K, G, u)) :
    SlotsIn S K.fin.Alin ∧ SlotsIn S K.fin.Blin := by
  obtain ⟨_, shownT, TS, pans, _, H1, V, shA, shB, _, _, _, _, _, _, _, hpans, _, _, _, _, _, _, _,
    _, _, _, _, hfin⟩ := hearStack_public h
  exact stackEnd_slots (placePanels_ok (panelsT_ok _ _ (panelsA_ok _ panOk_empty) pans hpans)) hfin

/-- The merge's start form names slots of the list alone. -/
theorem slotsIn_wsForkStart (sv : Array ℕ) (rho : Array E) (h : ∀ j ∈ sv.toList, S j) :
    SlotsIn S (wsForkStart sv rho) := by
  unfold wsForkStart
  rw [← Array.foldl_toList]
  refine slotsIn_foldl_mem _ _ (fun f y hy hf => slotsIn_addMul _ hf (slotsIn_slot (h y.1 ?_))) _
    slotsIn_empty
  rw [Array.toList_zip] at hy
  obtain ⟨a, b⟩ := y
  exact (List.of_mem_zip hy).1

/-- **The merge begins with a sum of the listed slots.** -/
theorem merge_start (lay : WsLay) (cl : Array WsClaim) (sv : Array ℕ) :
    Ret (flatForkEnd lay cl sv) fun o => ∃ rho, o.toWsMerged.p.start = wsForkStart sv rho := by
  unfold flatForkEnd Fl.wsForkMerge
  refine Ret.skip fun _ => Ret.skip fun _ => Ret.skip fun _ => ?_
  refine Ret.bind (Φ := fun x : WsMerged × Array E =>
    ∃ rho, x.1.p.start = wsForkStart sv rho) ?_ fun x hx => ?_
  · refine Ret.skip fun rho => Ret.bind (ret_pscBegin _) fun p hp => ?_
    refine Ret.bind (ret_wsForkRounds _ _ p) fun x hx => ?_
    obtain ⟨rm, p1⟩ := x
    refine Ret.bind (ret_pscEnds p1 1 1) fun x hx2 => ?_
    obtain ⟨sFv, p2⟩ := x
    exact Ret.skip fun _ => Ret.pure ⟨rho, (hx2.trans hx).trans hp⟩
  · obtain ⟨o, rho⟩ := x
    exact Ret.pure hx

end OnBytes.Desc.First.K4.Slots

#print axioms OnBytes.Desc.First.K4.Slots.stack_fills
#print axioms OnBytes.Desc.First.K4.Slots.stack_fin
#print axioms OnBytes.Desc.First.K4.Slots.slotsIn_wsForkStart
#print axioms OnBytes.Desc.First.K4.Slots.merge_start
