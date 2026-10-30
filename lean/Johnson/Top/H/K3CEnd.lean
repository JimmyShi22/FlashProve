-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3CEnd.lean: the kind "lookup" (K3): THE FORM THAT THE HEARING LEAVES FOR THE JOIN
NAMES NO ENTRY OF A VIRTUAL ROW, AND EVERY SLOT THAT IT NAMES IS FILLED IN THE LEDGER LEFT AND LIES
BELOW THE NUMBER OF SLOTS: LkPadCEnd (Johnson/Top/H/K3LeftProof.lean), proved; so K3LeavesAtCalls
and what stands on it hold with no premise left. Theorems with their proofs.

How. The form is what the last level of the key side's walk hands down: (1 - tau) (slot sL) + tau
(slot sR) (level_ok, Johnson/Top/H/FlPort/FoLevelRun.lean): no entry, by its make. The level has
SHOWN both slots (levelIn_ran): so they are filled and below the number of slots there; every later
step of the hearing fills free slots alone (hideRun_later), so they stay so. That the ledgers have
their sizes goes along the walk from the tie's end (tie_nums).

Main names: `two_slots` · `level_form` · `walk_keep` · `walk_form` · `lkPadCEnd` ·
`k3LeavesAtCalls`.

Limits. Ties: no error term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3LeftProof
import Johnson.Top.H.FlPort.FoPadFlat
import Johnson.Top.H.FlPort.FoPadShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open TwV FoNums OnBytes OnBytes.Model OnBytes.PscRun OnBytes.PscTie Cb.Fo.Walk

/-- The form that a level hands down names its two end slots alone. -/
theorem two_slots (a b : ℕ) (x y : E) :
    ∀ z ∈ (Aff.scale (Aff.slot a) x + Aff.scale (Aff.slot b) y).slots.toList,
      z.1 = a ∨ z.1 = b := by
  intro z hz
  have e : (Aff.scale (Aff.slot a) x + Aff.scale (Aff.slot b) y) =
      Aff.addMul (Aff.addMul {} (Aff.slot a) x) (Aff.addMul {} (Aff.slot b) y) oneE := rfl
  rw [e] at hz
  simp [Aff.addMul, Aff.slot] at hz
  rcases hz with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- A form whose slots are filled and below the number of slots stays so at a later ledger. -/
theorem FilledA.later' {F G : Fork} {a : Aff} (h : Later F G) (ha : FilledA F a) : FilledA G a :=
  fun x hx => ⟨by rw [h.ns]; exact (ha x hx).1, (h.keep x.1 (ha x hx).2).1⟩

/-- **One level.** -/
theorem level_form (s s' : Forest.Descent) (mu : ℕ) (order : List ℕ) (F G : Fork) (c c' : Tape)
    (h : lkLevel s mu order F c = .ok ((s', G), c')) (hS : Sized F) :
    Sized G ∧ Later F G ∧ s'.form.ents = #[] ∧ FilledA G s'.form := by
  obtain ⟨o, hl, -, -, hf⟩ := level_ok s mu order F G c c' s' h
  obtain ⟨p, m0, eps, rs, sentY, beta, vals, vL, vR, F3, p', -, -, -, -, -, -, -, -, -, -, -, hsR,
    hH3, hvL, hvR, hH7, -⟩ := levelIn_ran mu s.rho s.form order F G c c' o hl
  have hS1 : Sized (took F (1 + 2 * order.length + (2 + 2))) := took_sized _ hS
  have hS3 : Sized F3 := (hideRun_ok _ _ _ _ _ hS1 hH3).2.1
  have hSG : Sized G := (hideRun_ok _ _ _ _ _ hS3 hH7).2.1
  have l3 : Later F3 G := hideRun_later hS3 hH7
  have lFG : Later F G := (took_later F _).trans ((hideRun_later hS1 hH3).trans l3)
  obtain ⟨a1, a2, -⟩ := (shown_iff F3 o.sL vL).1 hvL
  obtain ⟨b1, b2, -⟩ := (shown_iff F3 (o.sL + 1) vR).1 hvR
  refine ⟨hSG, lFG, by rw [hf]; rfl, fun z hz => ?_⟩
  rw [hf] at hz
  rcases two_slots _ _ _ _ z hz with e | e
  · rw [e, l3.ns]
    exact ⟨a1, (l3.keep _ a2).1⟩
  · rw [e, hsR, l3.ns]
    exact ⟨b1, (l3.keep _ b2).1⟩

/-- **A walk over levels keeps the three facts.** -/
theorem walk_keep (f : Forest.Descent → ℕ → Fl Forest.Descent)
    (hf : ∀ s i, ∃ mu order, f s i = lkLevel s mu order) :
    ∀ (l : List ℕ) (s s' : Forest.Descent) (F G : Fork) (c c' : Tape),
      (l.foldlM f s) F c = .ok ((s', G), c') → Sized F → s.form.ents = #[] → FilledA F s.form →
      Sized G ∧ Later F G ∧ s'.form.ents = #[] ∧ FilledA G s'.form
  | [], s, s', Fa, Ga, c, c', h, hS, he, hA => by
    have e := (foldlM_nil_ok f s Fa c ((s', Ga), c')).1 h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (s' = s ∧ Ga = Fa) ∧ c' = c := by simpa [Prod.ext_iff] using e
    exact ⟨hS, Later.refl _, he, hA⟩
  | i :: l, s, s', Fa, Ga, c, c', h, hS, _, _ => by
    obtain ⟨s₁, F₁, c₁, h1, h2⟩ := (foldlM_cons_ok f s i l Fa c ((s', Ga), c')).1 h
    obtain ⟨mu, order, e⟩ := hf s i
    rw [e] at h1
    obtain ⟨a1, a2, a3, a4⟩ := level_form s s₁ mu order Fa F₁ c c₁ h1 hS
    obtain ⟨b1, b2, b3, b4⟩ := walk_keep f hf l s₁ s' F₁ Ga c₁ c' h2 a1 a3 a4
    exact ⟨b1, a2.trans b2, b3, b4⟩

/-- **A walk over at least one level makes them**, from a ledger with its sizes alone. -/
theorem walk_form (f : Forest.Descent → ℕ → Fl Forest.Descent)
    (hf : ∀ s i, ∃ mu order, f s i = lkLevel s mu order) (i : ℕ) (l : List ℕ)
    (s s' : Forest.Descent) (F G : Fork) (c c' : Tape)
    (h : ((i :: l).foldlM f s) F c = .ok ((s', G), c')) (hS : Sized F) :
    Sized G ∧ Later F G ∧ s'.form.ents = #[] ∧ FilledA G s'.form := by
  obtain ⟨s₁, F₁, c₁, h1, h2⟩ := (foldlM_cons_ok f s i l F c ((s', G), c')).1 h
  obtain ⟨mu, order, e⟩ := hf s i
  rw [e] at h1
  obtain ⟨a1, a2, a3, a4⟩ := level_form s s₁ mu order F F₁ c c₁ h1 hS
  obtain ⟨b1, b2, b3, b4⟩ := walk_keep f hf l s₁ s' F₁ G c₁ c' h2 a1 a3 a4
  exact ⟨b1, a2.trans b2, b3, b4⟩

/-- A walk over levels, of the ledger alone. -/
theorem walk_later (f : Forest.Descent → ℕ → Fl Forest.Descent)
    (hf : ∀ s i, ∃ mu order, f s i = lkLevel s mu order) :
    ∀ (l : List ℕ) (s s' : Forest.Descent) (F G : Fork) (c c' : Tape),
      (l.foldlM f s) F c = .ok ((s', G), c') → Sized F → Sized G ∧ Later F G
  | [], s, s', Fa, Ga, c, c', h, hS => by
    have e := (foldlM_nil_ok f s Fa c ((s', Ga), c')).1 h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (s' = s ∧ Ga = Fa) ∧ c' = c := by simpa [Prod.ext_iff] using e
    exact ⟨hS, Later.refl _⟩
  | i :: l, s, s', Fa, Ga, c, c', h, hS => by
    obtain ⟨a1, a2, -, -⟩ := walk_form f hf i l s s' Fa Ga c c' h hS
    exact ⟨a1, a2⟩

/-- **THE FORM LEFT FOR THE JOIN.** -/
theorem lkPadCEnd : LkPadCEnd := by
  intro calls pub lid F F' t u g h hF
  obtain ⟨M, P⟩ := pad_cut calls pub lid F F' t u g h
  have H : FoNums.ok (M.h pub) = true := by
    rw [← pad_shape P]
    exact _root_.Fo.Pay.shapeOf_ok (pad_shapeOf P)
  -- the ledger at the tie's end has its sizes
  obtain ⟨e4, -, -, ha⟩ := head_cut P
  have hS4 : Sized M.F4 := e4 ▸ owed3_sized hF
  have hfac : Reading.gl.val M.a =
      fac (numsF (M.h pub) 5 M.F4.next (Reading.gl.val M.theta)) (Reading.gl.val M.alpha) := by
    rw [ha]
    exact head_fac Reading.gl (M.h pub) H 5 M.F4.next _ _
  obtain ⟨-, -, -, -, -, -, -, -, -, hS5, -⟩ :=
    tie_nums Reading.gl (M.h pub) 5 (Reading.gl.val M.theta) (Reading.gl.val M.alpha) M.a M.F4 M.F5
      M.c4 M.c5 hfac hS4 M.t P.tie
  -- the key side's walk has at least one level
  have hv : (M.h pub).v = FoNums.v' (M.h pub) + 1 := Cb.Fo.ok_v H
  have hk := P.keys
  rw [hv, List.range_succ_eq_map] at hk
  obtain ⟨hS6, -, e6, f6⟩ := walk_form
    (fun (s : Forest.Descent) mu =>
      lkLevel s mu
        (if mu + 1 = FoNums.v' (M.h pub) + 1 then Forest.orderForestRange mu (M.h pub).rK
          else orderDefault mu))
    (fun s i => ⟨_, _, rfl⟩) _ _ _ _ _ _ _ _ hk hS5
  -- the table's walk, and the last eight lines
  obtain ⟨hS7, l67⟩ := walk_later
    (fun (s : Forest.Descent) l => lkLevel s (5 + l) (orderDefault (5 + l)))
    (fun s i => ⟨_, _, rfl⟩) _ _ _ _ _ _ _ P.table hS6
  obtain ⟨D, -, -, -, -, -, -, -, -, -, -, -, -, a13, -, a15, -⟩ :=
    leavesBits_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P.l1 P.l2
      P.l3 P.l4 P.l5 P.l6 P.l7 P.l8
  have hT : Sized (took M.F7 (D.sBit (5 + (M.h pub).d) (M.h pub).d M.table.rho M.F7.next + 1 -
      M.F7.next)) := took_sized _ hS7
  have z1 : Sized M.G6 := (hideRun_ok _ _ _ _ _ hT a13).2.1
  have l78 : Later M.F7 M.G8 :=
    (took_later M.F7 _).trans ((hideRun_later hT a13).trans (hideRun_later z1 a15))
  rw [P.heard, P.fork]
  exact ⟨e6, FilledA.later' (l67.trans l78) f6⟩

end Fo.Tp

namespace VerifiableInference.OnPublicFiles

/-- **K3.block's decide at the calls' seat leaves the record**: no premise left. -/
theorem k3LeavesAtCalls : K3LeavesAtCalls := k3LeavesAtCalls_of Fo.Tp.lkPadCEnd

end VerifiableInference.OnPublicFiles

#print axioms Fo.Tp.level_form
#print axioms Fo.Tp.lkPadCEnd
#print axioms VerifiableInference.OnPublicFiles.k3LeavesAtCalls
