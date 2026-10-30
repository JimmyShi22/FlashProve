--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/Keep/CEndSlots.lean: THE LOOKUP: THE KEY SIDE's END FORM, AS A TEXT: behind a hearing
whose key side has a level, g.cEnd names just two slots, sL and sL + 1, and no entry; both slots are
there and filled in the ledger behind the hearing; the ledger's factor under both is one element
beta; the two coefficients read 1 - tau and tau, so one of them is not 0; and,
at rounds whose words are below the prime, beta reads as an element that is not 0. Definitions,
statements and proofs: the sister, on the form's text, of Johnson/Top/H/Keep/CEndWorth.lean and
CEndTurns.lean.

Main names:
  EndAt F f sL a b beta: the sentence, of a form f at a ledger F.
  endForm_slots: the text of "scale (slot sL) k + scale (slot sR) k'".
  level_at, fold_at, pad_at, lkPad_at: behind a level; a walk of at least one level; a hearing.
  decide_at: of K3.block's decide.
  EndAt.later: it passes to every later ledger.

Limits. As CEndTurns.lean's: okRoundsE, "the ledger has its sizes" and "the key side has a level"
are premises. The coefficients are the words that the routine's own arithmetic leaves (a product
with the word 1 is not reduced away); what is said of them is what they READ as. Not tried for
emptiness: no yes of decide is shown here with these premises.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.CEndTurns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open TwV FoNums OnBytes OnBytes.Model OnBytes.PscRun OnBytes.PscTie OnBytes.Psc

/-- The end form as a text, at a ledger. -/
structure EndAt (F : Fork) (f : Aff) (sL : ℕ) (a b beta : E) : Prop where
  slots : f.slots.toList = [(sL, a), (sL + 1, b)]
  ents : f.ents = #[]
  inL : sL < F.ns ∧ Filled F sL
  inR : sL + 1 < F.ns ∧ Filled F (sL + 1)
  mfL : F.mf.getD sL zeroE = beta
  mfR : F.mf.getD (sL + 1) zeroE = beta
  one : Reading.gl.val a ≠ 0 ∨ Reading.gl.val b ≠ 0
  live : Live beta

theorem EndAt.later {F G : Fork} {f : Aff} {sL : ℕ} {a b beta : E} (h : EndAt F f sL a b beta)
    (hL : Later F G) : EndAt G f sL a b beta :=
  ⟨h.slots, h.ents, ⟨by rw [hL.ns]; exact h.inL.1, (hL.keep _ h.inL.2).1⟩,
    ⟨by rw [hL.ns]; exact h.inR.1, (hL.keep _ h.inR.2).1⟩,
    (hL.keep _ h.inL.2).2.2.trans h.mfL, (hL.keep _ h.inR.2).2.2.trans h.mfR, h.one, h.live⟩

/-- The text of the form that a level hands down. -/
theorem endForm_slots (sL sR : ℕ) (k k' : E) :
    (Aff.scale (Aff.slot sL) k + Aff.scale (Aff.slot sR) k').slots.toList =
      [(sL, mulE oneE k), (sR, mulE (mulE oneE k') oneE)] := by
  show (Aff.addMul (Aff.addMul {} (Aff.slot sL) k) (Aff.addMul {} (Aff.slot sR) k')
    oneE).slots.toList = _
  simp [Aff.addMul, Aff.slot]

theorem level_at (s s' : Forest.Descent) (mu : ℕ) (order : List ℕ) (F G : Fork) (c c' : Tape)
    (h : lkLevel s mu order F c = .ok ((s', G), c')) (hF : Sized F) (hc : Inv c) :
    Later F G ∧ Sized G ∧ Inv c' ∧ ∃ sL a b beta, EndAt G s'.form sL a b beta := by
  obtain ⟨o, ho, _, _, e3⟩ := level_ok s mu order F G c c' s' h
  obtain ⟨p, m0, eps, rs, sentY, beta, vals, vL, vR, F3, p', _, _, _, _, _, _, _, hv2, hEv, _, _,
    hsR, hH3, _, _, hHG, _, _, _⟩ := levelIn_ran mu s.rho s.form order F G c c' o ho
  obtain ⟨i1, i2⟩ := evs_inv hEv hc
  have hT := took_sized (1 + 2 * order.length + (2 + 2)) hF
  obtain ⟨hS3, s3, hnew, _⟩ := hideRun_ok _ F3 o.sL vals beta hT hH3
  obtain ⟨lG, sG, _⟩ := hide_new s3 hHG
  have L : Later F G := ((took_later F _).trans (hideRun_later hT hH3)).trans lG
  obtain ⟨a1, _, a3, _, a5⟩ := hnew 0 (by rw [hv2]; exact Nat.two_pos)
  obtain ⟨b1, _, b3, _, b5⟩ := hnew 1 (by rw [hv2]; exact Nat.one_lt_two)
  rw [Nat.add_zero] at a1 a3 a5
  have n3 : F3.ns = (took F (1 + 2 * order.length + (2 + 2))).ns := hS3.ns
  refine ⟨L, sG, i1, o.sL, mulE oneE (subE oneE o.tau), mulE (mulE oneE o.tau) oneE, beta,
    ⟨by rw [e3, hsR]; exact endForm_slots _ _ _ _, ?_,
      ⟨by rw [lG.ns, n3]; exact a1, (lG.keep _ a3).1⟩,
      ⟨by rw [lG.ns, n3]; exact b1, (lG.keep _ b3).1⟩,
      (lG.keep _ a3).2.2.trans a5, (lG.keep _ b3).2.2.trans b5, ?_,
      i2 .pscY beta (by simp [levelEv])⟩⟩
  · rw [e3]
    exact bare_ents (OnBytes.Road.Rows.bare_add
      (OnBytes.Road.Rows.bare_scale _ (OnBytes.Road.Rows.bare_slot _))
      (OnBytes.Road.Rows.bare_scale _ (OnBytes.Road.Rows.bare_slot _)))
  · by_contra hn
    have h1 : Reading.gl.val (mulE oneE (subE oneE o.tau)) = 0 := by
      by_contra e
      exact hn (Or.inl e)
    have h2 : Reading.gl.val (mulE (mulE oneE o.tau) oneE) = 0 := by
      by_contra e
      exact hn (Or.inr e)
    rw [Reading.gl.mul, Reading.gl.one, Reading.gl.sub, Reading.gl.one, one_mul] at h1
    rw [Reading.gl.mul, Reading.gl.mul, Reading.gl.one, one_mul, mul_one] at h2
    rw [h2, sub_zero] at h1
    exact one_ne_zero h1

theorem fold_at {α : Type} (f : Forest.Descent → α → Fl Forest.Descent)
    (hf : ∀ s a, ∃ mu order, f s a = lkLevel s mu order) :
    ∀ (l : List α) (s s' : Forest.Descent) (A B : Fork) (c c' : Tape), l ≠ [] →
      (l.foldlM f s) A c = .ok ((s', B), c') → Sized A → Inv c →
      ∃ sL a b beta, EndAt B s'.form sL a b beta
  | [], _, _, _, _, _, _, hne, _, _, _ => absurd rfl hne
  | x :: l, s, s', A, B, c, c', _, h, hA, hc => by
    obtain ⟨s₁, F₁, c₁, h1, h2⟩ := (foldlM_cons_ok f s x l A c ((s', B), c')).1 h
    obtain ⟨mu, order, e⟩ := hf s x
    rw [e] at h1
    obtain ⟨_, z1, i1, x1⟩ := level_at s s₁ mu order A F₁ c c₁ h1 hA hc
    cases l with
    | nil =>
      have e2 := (foldlM_nil_ok f s₁ F₁ c₁ ((s', B), c')).1 h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (s' = s₁ ∧ B = F₁) ∧ c' = c₁ := by simpa [Prod.ext_iff] using e2
      exact x1
    | cons y l' => exact fold_at f hf (y :: l') s₁ s' F₁ B c₁ c' (by simp) h2 z1 i1

theorem pad_at {calls : Array Call} {pub : Array Nat} {lid : ℕ} {F F' : Fork} {c c' : Tape}
    {g : Forest.Heard} {M : PadMid} (P : PadCut calls pub lid F c g F' c' M) (hF : Sized F)
    (hv : (M.h pub).v ≠ 0) (hL : Later M.F6 F') (hc : Inv c) :
    ∃ sL a b beta, EndAt F' g.cEnd sL a b beta := by
  obtain ⟨h4, hE4, _⟩ := head_cut P
  have z4 : Sized M.F4 := h4 ▸ owed3_sized hF
  obtain ⟨_, z5, _⟩ := tie_named M.a M.F4 M.F5 M.c4 M.c5 M.t P.tie z4
  have i5 : Inv M.c5 := tie_inv M.a M.F4 M.F5 M.c4 M.c5 M.t P.tie (evs_inv hE4 hc).1
  obtain ⟨sL, a, b, beta, x⟩ := fold_at _ (fun s mu => ⟨_, _, rfl⟩) _ _ _ _ _ _ _
    (by
      intro e
      exact hv (by simpa using congrArg List.length e)) P.keys z5 i5
  refine ⟨sL, a, b, beta, ?_⟩
  rw [P.heard]
  exact x.later hL

theorem lkPad_at (calls : Array Call) (pub : Array Nat) (lid : ℕ) (F F' : Fork) (t u : Tape)
    (g : Forest.Heard) (h : lkPad calls pub lid F t = some (g, F', u)) (hF : Sized F)
    (hv : g.shape.v ≠ 0) (ht : Inv t) : ∃ sL a b beta, EndAt F' g.cEnd sL a b beta := by
  have h' : lkPad calls pub lid F t = .ok ((g, F'), u) := h
  obtain ⟨M, P⟩ := pad_cut calls pub lid F F' t u g h'
  have hg : g.shape = M.h pub := pad_shape P
  have H : FoNums.ok (M.h pub) = true := Cb.Fo.shape_ok P.shape (_root_.Fo.ask_ok P.ask)
  obtain ⟨l, scs, ptT, lvK, lvT, rowsK, rowsT, evK, evT, D, R⟩ :=
    pad_read Reading.gl P hF trivial 5 H
  exact pad_at P hF (hg ▸ hv) (P.fork ▸ R.table.later.trans R.r5.later) ht

end Fo.Tp

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.K.Kc OnBytes.PscRun
open VerifiableInference.Desc.First.Tape (flRun flRun_holds)

/-- **Of K3.block's decide**, at rounds whose words are below the prime. -/
theorem decide_at {S Cl : Type} (seat : Desc.K3.Seat S Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (s s' : S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block seat piece laid before p guests).decide s rs cols = .ok s')
    (ho : okRoundsE rs = true) :
    ∃ (F : Fork) (x : Forest.Heard × Fork), seat.fork s = some F ∧ s' = seat.put s x.1 x.2 ∧
      (Sized F → x.1.shape.v ≠ 0 →
        ∃ sL a b beta, _root_.Fo.Tp.EndAt x.2 x.1.cEnd sL a b beta) := by
  obtain ⟨F, x, hF, hn, hx, rfl⟩ := decide_ok seat piece laid before p guests s s' rs cols hd
  refine ⟨F, x, hF, rfl, fun hS hv => ?_⟩
  unfold Desc.K3.hear at hx
  cases hsh : p.shape with
  | none => simp [hsh] at hx
  | some h =>
    simp only [hsh] at hx
    split at hx
    · rename_i hNC
      obtain ⟨t, ht, hm⟩ := (flRun_holds _ _ _ _ _ _ _ _).1
        (show flRun {} (Desc.K3.messages h) (p.entries.getD []) F rs = some (x.1, x.2) from hx)
      have hl := messagesCut p.calls p.pub p.lid h F t _ (shape_some p h hsh) hNC hm
      exact _root_.Fo.Tp.lkPad_at p.calls p.pub p.lid F x.2 t [] x.1 hl hS hv
        ⟨_root_.Fo.Tp.tapeT_nz _ _ _ _ ht, _root_.Fo.Tp.tapeT_ok _ _ _ _ ht ho⟩
    · exact absurd hx (by simp)

end VerifiableInference.OnPublicFiles

#print axioms Fo.Tp.endForm_slots
#print axioms Fo.Tp.level_at
#print axioms Fo.Tp.lkPad_at
#print axioms VerifiableInference.OnPublicFiles.decide_at
