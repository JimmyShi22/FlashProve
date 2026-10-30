--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
NOT TRIED FOR EMPTINESS AT ANY REAL PLACE.
Johnson/Top/H/Keep/CEndSteer.lean: THE LOOKUP: WHAT LIES UNDER THE TWO SLOTS OF THE KEY SIDE's END
FORM IS WHAT THE TAPE SENDS: at a tape whose every round named "pscValues" that sends two elements
sends the pair (yL, yR), and whose every drawn element has a property Q: behind a return of the flat
lkPad from a ledger that has its sizes, at a shape whose key side has a level: g.cEnd names just the
slots sL and sL + 1; sL + 2 is the ledger's next slot in front plus a number that hangs on the shape
alone; under sL lies yL, under sL + 1 lies yR; the factor under both is one element beta; beta and
g.alpha have Q. Definitions, statements and proofs.

OBJECT: the flat lkPad (OnBytes/K/Kc/FlatHear.lean): the record g and the ledger F' that it returns.
USER: Johnson/Top/H/Ret/RetSteer.lean. Typed for a member of another kind's row: "for every mask
  row there is a view at which the lookup's decide says yes and the hidden values under the end
  form's two slots are any two given values".
LETTERS: calls, pub, lid, F, t, yL, yR, Q free.
  No statement here names Block's, State's or K3's text; its imports' closure holds all
  three (through Johnson/Top/H/Keep/CEndSlots.lean's decide_at).

Main names:
  pv: the round's name. Steered yL yR Q t: the two invariants at the tape's front.
  SteerAt F f sL yL yR beta: the sentence on a form f at a ledger F. SteerAt.later.
  level_steer, fold_steer, tie_steer, pad_steer, lkPad_steer.

Limits. EVERY round of that name with two elements sends the same pair: only the last key level's
pair is left under the end form's slots; the other levels' rows are then worth what they are worth:
NOTHING HERE SAYS THAT THE LOOKUP's OWN ROWS ARE WORTH 0: no honest prover's tape. That such a tape
exists, and that lkPad returns at it, is not said here. Not tried for emptiness.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.CEndSlots
import Johnson.Top.H.Keep.TapeSteer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open TwV FoNums OnBytes OnBytes.Model OnBytes.PscRun OnBytes.PscTie OnBytes.Psc

/-- The name of the round in which a level's two end values are sent. -/
def pv : String := RoundName.pscValues.name

/-- What rides along the walk. -/
def Rides (yL yR : E) (Q : E → Prop) (t : Tape) : Prop := TailH pv [yL, yR] t ∧ AllD Q t

/-- The two invariants at the tape's front. -/
def Steered (yL yR : E) (Q : E → Prop) (t : Tape) : Prop := AllH pv [yL, yR] t ∧ AllD Q t

variable {yL yR : E} {Q : E → Prop}

theorem Steered.rides {t : Tape} (h : Steered yL yR Q t) : Rides yL yR Q t := ⟨h.1.tailH, h.2⟩

theorem evs_rides {l : List Ev} {c c' : Tape} (h : Evs l c c') (hc : Rides yL yR Q c) :
    Rides yL yR Q c' := ⟨evs_tailH l c c' h hc.1, (evs_d l c c' h hc.2).1⟩

/-- The end form at a ledger: its two slots, and what lies under them. -/
structure SteerAt (F : Fork) (f : Aff) (sL : ℕ) (yL yR beta : E) : Prop where
  slots : ∃ a b, f.slots.toList = [(sL, a), (sL + 1, b)]
  inL : Filled F sL
  inR : Filled F (sL + 1)
  vpL : F.vp.getD sL zeroE = yL
  vpR : F.vp.getD (sL + 1) zeroE = yR
  mfL : F.mf.getD sL zeroE = beta
  mfR : F.mf.getD (sL + 1) zeroE = beta

theorem SteerAt.later {F G : Fork} {f : Aff} {sL : ℕ} {yL yR beta : E}
    (h : SteerAt F f sL yL yR beta) (hL : Later F G) : SteerAt G f sL yL yR beta :=
  ⟨h.slots, (hL.keep _ h.inL).1, (hL.keep _ h.inR).1, (hL.keep _ h.inL).2.1.trans h.vpL,
    (hL.keep _ h.inR).2.1.trans h.vpR, (hL.keep _ h.inL).2.2.trans h.mfL,
    (hL.keep _ h.inR).2.2.trans h.mfR⟩

/-- **Behind every level.** -/
theorem level_steer (s s' : Forest.Descent) (mu : ℕ) (order : List ℕ) (F G : Fork) (c c' : Tape)
    (h : lkLevel s mu order F c = .ok ((s', G), c')) (hF : Sized F) (hc : Rides yL yR Q c) :
    Sized G ∧ Rides yL yR Q c' ∧
      ∃ sL beta, SteerAt G s'.form sL yL yR beta ∧ sL + 2 = G.next ∧ Q beta := by
  obtain ⟨o, ho, _, _, e3⟩ := level_ok s mu order F G c c' s' h
  obtain ⟨p, m0, eps, rs, sentY, beta, vals, vL, vR, F3, p', _, _, _, _, _, _, _, hv2, hEv, _, hsL,
    hsR, hH3, _, _, hHG, _, _, _⟩ := levelIn_ran mu s.rho s.form order F G c c' o ho
  have hT := took_sized (1 + 2 * order.length + (2 + 2)) hF
  obtain ⟨hS3, s3, hnew, _⟩ := hideRun_ok _ F3 o.sL vals beta hT hH3
  obtain ⟨hS4, sG, _, _⟩ := hideRun_ok F3 G _ _ _ s3 hHG
  have lG : Later F3 G := hideRun_later s3 hHG
  -- what was read in the round of the two end values
  have hvals : vals.toList = [yL, yR] := by
    have hE := hEv
    unfold levelEv at hE
    obtain ⟨ca, hA, h2⟩ := (evs_append _ _ _ _).1 hE
    obtain ⟨cb, hB, h3⟩ := (evs_append _ _ _ _).1 h2
    obtain ⟨cc, h4, _⟩ := (evs_append _ _ _ _).1 h3
    obtain ⟨d1, a1, d2, a2, d3, a3, d4, a4, _⟩ := h4
    have t1 : TailH pv [yL, yR] d1 :=
      at_tailH a1 (evs_tailH _ _ _ hB (evs_tailH _ _ _ hA hc.1))
    exact read_all (closeOne_allH a2 t1) rfl a3 a4
  have hv : vals = #[yL, yR] := Array.toList_inj.1 hvals
  obtain ⟨_, _, a3, a4, a5⟩ := hnew 0 (by rw [hv2]; exact Nat.two_pos)
  obtain ⟨_, _, b3, b4, b5⟩ := hnew 1 (by rw [hv2]; exact Nat.one_lt_two)
  rw [Nat.add_zero] at a3 a4 a5
  rw [hv] at a4 b4
  refine ⟨sG, evs_rides hEv hc, o.sL, beta,
    ⟨⟨_, _, by rw [e3, hsR]; exact endForm_slots _ _ _ _⟩, (lG.keep _ a3).1, (lG.keep _ b3).1,
      (lG.keep _ a3).2.1.trans a4, (lG.keep _ b3).2.1.trans b4, (lG.keep _ a3).2.2.trans a5,
      (lG.keep _ b3).2.2.trans b5⟩, ?_, (evs_d _ _ _ hEv hc.2).2.2.1 .pscY beta (by simp [levelEv])⟩
  rw [hS4.next, hS3.next, hsL]
  show _ = F.next + (1 + 2 * order.length + (2 + 2))
  omega

/-- **Behind every walk of at least one level.** -/
theorem fold_steer {α : Type} (f : Forest.Descent → α → Fl Forest.Descent)
    (hf : ∀ s a, ∃ mu order, f s a = lkLevel s mu order) :
    ∀ (l : List α) (s s' : Forest.Descent) (A B : Fork) (c c' : Tape), l ≠ [] →
      (l.foldlM f s) A c = .ok ((s', B), c') → Sized A → Rides yL yR Q c →
      ∃ sL beta, SteerAt B s'.form sL yL yR beta ∧ sL + 2 = B.next ∧ Q beta
  | [], _, _, _, _, _, _, hne, _, _, _ => absurd rfl hne
  | x :: l, s, s', A, B, c, c', _, h, hA, hc => by
    obtain ⟨s₁, F₁, c₁, h1, h2⟩ := (foldlM_cons_ok f s x l A c ((s', B), c')).1 h
    obtain ⟨mu, order, e⟩ := hf s x
    rw [e] at h1
    obtain ⟨z1, i1, x1⟩ := level_steer s s₁ mu order A F₁ c c₁ h1 hA hc
    cases l with
    | nil =>
      have e2 := (foldlM_nil_ok f s₁ F₁ c₁ ((s', B), c')).1 h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (s' = s₁ ∧ B = F₁) ∧ c' = c₁ := by simpa [Prod.ext_iff] using e2
      exact x1
    | cons y l' => exact fold_steer f hf (y :: l') s₁ s' F₁ B c₁ c' (by simp) h2 z1 i1

/-! ## The tie lets both ride -/

theorem tieFold_steer (a : E) : ∀ (l : List ℕ) (s s' : Forest.TieStep) (A B : Fork) (c c' : Tape),
    (l.foldlM (lkTieStep a) s) A c = .ok ((s', B), c') → Rides yL yR Q c → Rides yL yR Q c'
  | [], s, s', A, B, c, c', h, hc => by
    have e := (foldlM_nil_ok (lkTieStep a) s A c ((s', B), c')).1 h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (s' = s ∧ B = A) ∧ c' = c := by simpa [Prod.ext_iff] using e
    exact hc
  | j :: l, s, s', A, B, c, c', h, hc => by
    obtain ⟨s₁, F₁, c₁, h1, h2⟩ := (foldlM_cons_ok (lkTieStep a) s j l A c ((s', B), c')).1 h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hE, _⟩ := tieStep_ok a s j A F₁ c c₁ s₁ h1
    exact tieFold_steer a l s₁ s' F₁ B c₁ c' h2 (evs_rides hE hc)

theorem tie_steer (a : E) (F G : Fork) (c c' : Tape) (T : Forest.Tie)
    (h : lkTie a F c = .ok ((T, G), c')) (hc : Rides yL yR Q c) : Rides yL yR Q c' := by
  obtain ⟨s, c1, pt, h1, hE, _⟩ := tie_ok a F G c c' T h
  exact evs_rides hE (tieFold_steer a _ _ _ _ _ _ _ h1 hc)

/-- From the chain of the runs of the routines that lkPad calls. -/
theorem pad_steer {calls : Array Call} {pub : Array Nat} {lid : ℕ} {F F' : Fork} {c c' : Tape}
    {g : Forest.Heard} {M : PadMid} (P : PadCut calls pub lid F c g F' c' M) (hF : Sized F)
    (hv : (M.h pub).v ≠ 0) (hL : Later M.F6 F') (hc : Rides yL yR Q c) :
    ∃ sL beta, SteerAt F' g.cEnd sL yL yR beta ∧ sL + 2 = M.F6.next ∧ Q beta ∧ Q g.alpha := by
  obtain ⟨h4, hE4, _⟩ := head_cut P
  have z4 : Sized M.F4 := h4 ▸ owed3_sized hF
  obtain ⟨_, z5, _⟩ := tie_named M.a M.F4 M.F5 M.c4 M.c5 M.t P.tie z4
  have i5 : Rides yL yR Q M.c5 := tie_steer M.a M.F4 M.F5 M.c4 M.c5 M.t P.tie (evs_rides hE4 hc)
  obtain ⟨sL, beta, x, hn, hb⟩ := fold_steer _ (fun s mu => ⟨_, _, rfl⟩) _ _ _ _ _ _ _
    (by
      intro e
      exact hv (by simpa using congrArg List.length e)) P.keys z5 i5
  refine ⟨sL, beta, ?_, hn, hb, ?_⟩
  · rw [P.heard]
    exact x.later hL
  · rw [P.heard]
    exact (evs_d _ _ _ hE4 hc.2).2.1 .lkp M.alpha (by simp [drawsEv])

/-- **Of the library's flat copy.** -/
theorem lkPad_steer (calls : Array Call) (pub : Array Nat) (lid : ℕ) (F F' : Fork) (t u : Tape)
    (g : Forest.Heard) (h : lkPad calls pub lid F t = some (g, F', u)) (hF : Sized F)
    (hv : g.shape.v ≠ 0) (ht : Steered yL yR Q t) :
    ∃ sL beta, SteerAt F' g.cEnd sL yL yR beta ∧
      sL + 2 = F.next + (tieOff 31 + walkSlots 0 g.shape.v 0) ∧ Q beta ∧ Q g.alpha := by
  have h' : lkPad calls pub lid F t = .ok ((g, F'), u) := h
  obtain ⟨M, P⟩ := pad_cut calls pub lid F F' t u g h'
  have hg : g.shape = M.h pub := pad_shape P
  have H : FoNums.ok (M.h pub) = true := Cb.Fo.shape_ok P.shape (_root_.Fo.ask_ok P.ask)
  obtain ⟨l, scs, ptT, lvK, lvT, rowsK, rowsT, evK, evT, D, R⟩ :=
    pad_read Reading.gl P hF trivial 5 H
  obtain ⟨sL, beta, x, hn, hb, ha⟩ :=
    pad_steer P hF (hg ▸ hv) (P.fork ▸ R.table.later.trans R.r5.later) ht.rides
  have h6 : M.F6.next = F.next + (tieOff 31 + walkSlots 0 (M.h pub).v 0) :=
    ((R.f4 ▸ R.tieSt).trans (⟨R.keys.same, R.keys.filled, R.keys.out⟩ :
      Stretch M.F5 M.F6 _)).next
  exact ⟨sL, beta, x, by rw [hn, h6, hg], hb, ha⟩

end Fo.Tp

#print axioms Fo.Tp.level_steer
#print axioms Fo.Tp.fold_steer
#print axioms Fo.Tp.pad_steer
#print axioms Fo.Tp.lkPad_steer
