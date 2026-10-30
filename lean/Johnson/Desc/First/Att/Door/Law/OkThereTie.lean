-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/OkThereTie.lean: WHAT THE Bool OF THE PUBLIC ITEM «K5.okAt» MEANS, AND ITS THREE LAWS.
  okThereB_iff   okThereB g s = true ↔ ∃ U h, s.fork? = some U ∧ s.heard5? = some h ∧ PscRun.Sized U ∧ HeardSlots (PscRun.Filled U) g h
                 (HeardSlots: Johnson/Desc/First/Att/Claims/HeardSlots.lean). AN IFF.
  MADE   ok_made : a yes of the kind's decision at seatSO from t to t₁, the ledger at t sized, GeoFits g p.own ⇒ okThereB g t₁ = true.
  KEPT   ok_kept : okThereB g s = true → CarK5 s s' → okThereB g s' = true (CarK5: Claims/WalkK5.lean: what each block between K5's and the
                 batching owes as Block.Steps).
  SPENT  ok_spent : okThereB c.geo s = true → ∃ U h, s.fork? = some U ∧ s.heard5? = some h ∧ ∀ zk, K5OkAt c zk h U (the named premise on Ok:
                 Claims/InAt.lean; its spender: Claims/K5Still.lean's hQ).
IS IT EMPTY HERE? That the Bool is true at any real record is not shown here: a walk's sheet prints it. NO MEMBER, AT NO SIZE.
-/
import Johnson.Desc.First.Att.Door.OkThereB
import Johnson.Desc.First.Att.Claims.HeardSlots
import Johnson.Desc.First.Att.Claims.WalkK5

set_option autoImplicit false

namespace H2K5.Door
open OnBytes OnBytes.Model
open OnBytes.PscRun (Filled)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo Heard ParC)
open K5Law

theorem stretchB_iff (U : Fork) (a n : ℕ) : stretchB U a n = true ↔ ∀ i, i < n → Filled U (a + i) := by
  unfold stretchB
  simp only [List.all_eq_true, List.mem_range]
  exact Iff.rfl

theorem formB_iff (U : Fork) (f : Aff) : formB U f = true ↔ SlotsIn (Filled U) f := by
  unfold formB
  simp only [List.all_eq_true]
  exact Iff.rfl

theorem sumB_iff (U : Fork) (hh : MaskedSum.Heard) (n : ℕ) : sumB U hh n = true ↔ SumSlots (Filled U) hh n := by
  unfold sumB
  simp only [Bool.and_eq_true, formB_iff, stretchB_iff]
  exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.start, h.coefs⟩, h.ends⟩⟩

theorem heardSlotsB_iff (U : Fork) (g : Geo) (h : Heard) :
    heardSlotsB U g h = true ↔ HeardSlots (Filled U) g h := by
  unfold heardSlotsB
  simp only [Bool.and_eq_true, List.all_eq_true, sumB_iff, stretchB_iff, beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩, a12⟩, a13⟩, a14⟩, a15⟩, a16⟩
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩
  · intro a
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a.rem, a.seven⟩, a.units⟩, a.five⟩, a.bits⟩, a.two⟩, a.values⟩, a.maxima⟩, a.division⟩, a.below⟩,
      a.on⟩, a.atIndex⟩, a.key⟩, a.cells⟩, a.om⟩, a.om''⟩

theorem sizedB_iff (U : Fork) : sizedB U = true ↔ PscRun.Sized U := by
  unfold sizedB PscRun.Sized
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

/-- **What the item says.** -/
theorem okThereB_iff (g : Geo) (s : S) : okThereB g s = true ↔
    ∃ U h, s.fork? = some U ∧ s.heard5? = some h ∧ PscRun.Sized U ∧ HeardSlots (Filled U) g h := by
  unfold okThereB
  cases hF : s.fork? with
  | none => simp
  | some U =>
    cases h5 : s.heard5? with
    | none => simp
    | some h =>
      simp only [Bool.and_eq_true, sizedB_iff, heardSlotsB_iff, Option.some.injEq]
      exact ⟨fun a => ⟨U, h, rfl, rfl, a.1, a.2⟩, fun ⟨_, _, e1, e2, a1, a2⟩ => by subst e1; subst e2; exact ⟨a1, a2⟩⟩

/-- **MADE, behind the kind's own block.** -/
theorem ok_made {g : Geo} {p : P.Par} {t t₁ : S} {rs : List Fmt.RoundView} (hd : P.decide P.seatSO p t rs = .ok t₁)
    (hz : ∀ F, P.seatSO.ledger t = some F → Road.Sized F) (gf : P.GeoFits g p.own) : okThereB g t₁ = true := by
  obtain ⟨_, F, h, G, l1, hh, l2⟩ := (P.decide_lays P.seatSO p _ _ _).1 hd
  obtain ⟨a, _, rfl⟩ := P.seatSO_lay l2
  obtain ⟨b, zG⟩ := heardSlots_of_hear hh (hz F l1) gf
  exact (okThereB_iff g _).2 ⟨G, h, rfl, rfl, ⟨zG.vp, zG.mf, zG.got⟩, b⟩

/-- **KEPT, by every step that carries.** -/
theorem ok_kept {g : Geo} {s s' : S} (h : okThereB g s = true) (hc : CarK5 s s') : okThereB g s' = true := by
  obtain ⟨U, hh, e1, e2, sU, a⟩ := (okThereB_iff g s).1 h
  obtain ⟨U', e1', lU, sU'⟩ := hc.2 U e1 sU
  exact (okThereB_iff g s').2 ⟨U', hh, e1', hc.1 hh e2, sU', heardSlots_mono (fun j hj => (lU.keep j hj).1) a⟩

/-- **SPENT: the named premise on Ok.** -/
theorem ok_spent {c : ParC} {s : S} (h : okThereB c.geo s = true) :
    ∃ U hh, s.fork? = some U ∧ s.heard5? = some hh ∧ ∀ zk, K5OkAt c zk hh U := by
  obtain ⟨U, hh, e1, e2, sU, a⟩ := (okThereB_iff c.geo s).1 h
  exact ⟨U, hh, e1, e2, k5OkAt_of_heardSlots sU a⟩

end H2K5.Door

#print axioms H2K5.Door.okThereB_iff
#print axioms H2K5.Door.ok_made
#print axioms H2K5.Door.ok_kept
#print axioms H2K5.Door.ok_spent
