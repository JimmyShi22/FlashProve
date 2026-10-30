--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/Keep/CEndTurns.lean: THE LOOKUP: THE KEY SIDE's END FORM HANGS ON THE MASK ROW: behind
every yes of K3.block's decide at rounds whose words are below the prime, from a ledger that has its
sizes, at a shape whose key side has a level: the factor beta of Johnson/Top/H/Keep/CEndWorth.lean's
sentence reads as an element that is not 0; so one entry of the mask row alone turns g.cEnd's worth,
and there is a mask row at which the flat record's sparse form cEndInc is not worth 0. Definitions,
statements and proofs.

Main names:
  OkD, AllOk: every drawn element of every round of a tape has its words below the prime. The twin
    of Johnson/Top/H/Keep/TapeNZ.lean's AllNZ: recv_ok .. evs_ok, roundT_ok, tapeT_ok (from
    okRoundsE, Johnson/Top/H/K3LawKind.lean).
  Inv t := AllNZ t and AllOk t. evs_inv: calls in a row keep it, and every element that a call
    ansNZ of the row returns is Live: not zero as words, and its words below the prime.
  live_ne: a Live element reads as an element of the field that is not 0.
  tie_inv: the tie keeps Inv. level_end2, fold_end2, pad_end2, lkPad_end2: CEndWorth.lean's four,
    with Inv carried and beta Live.
  decide_end: of K3.block's decide.
  EndIs.inc_ne: where a form with EndIs is also FormIs tg inc (the library's record of what was
    heard has g.cEnd so, at cEndC and cEndInc): there is a mask row at which inc is not worth 0.

Limits. okRoundsE is a premise: AT A BARE decide IT CANNOT BE DROPPED: the maker of tapes tests a
draw's three words against 0, not the element: a view in which that level's draw spells the prime
itself passes, and beta then reads as 0 (thought through on the texts; no such view is written out
here). "The ledger has its sizes" and "the key side has a level" are premises. The five letters of
the sentence stand under "there are": that tau is a coordinate of the key side's point, and which
scalars of the rounds vL and vR are, is not said. Not tried for emptiness: no yes of decide is shown
here with these premises.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.CEndWorth
import Johnson.Top.H.Keep.TapeNZ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open TwV FoNums OnBytes OnBytes.Model OnBytes.PscRun OnBytes.PscTie OnBytes.Psc
open VerifiableInference.Desc.First.Tape (roundT tapeT TapeRule)
open VerifiableInference.OnPublicFiles (okRoundsE)

/-! ## The words of a tape's draws are below the prime -/

def OkD (x : FlatRound) : Prop := ∀ d ∈ x.drawn, okE d = true

def AllOk (t : Tape) : Prop := ∀ x ∈ t, OkD x

theorem AllOk.tail {x : FlatRound} {t : Tape} (h : AllOk (x :: t)) : AllOk t :=
  fun y hy => h y (List.mem_cons_of_mem _ hy)

theorem recv_ok {c c' : Tape} {x : E} (h : recv c = some (x, c')) (hc : AllOk c) : AllOk c' := by
  unfold recv at h
  split at h
  · rename_i nm z w y s d t
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · exact hc ⟨nm, z, w, y :: s, d⟩ List.mem_cons_self
    · exact hc r (List.mem_cons_of_mem _ hr)
  · cases h

theorem recvLoop_ok : ∀ (n : Nat) (a v : Array E) (c c' : Tape), recvLoop n a c = some (v, c') →
    AllOk c → AllOk c'
  | 0, a, v, c, c', h, hc => by
    unfold recvLoop at h
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact hc
  | n + 1, a, v, c, c', h, hc => by
    unfold recvLoop at h
    split at h
    · rename_i x u hx
      exact recvLoop_ok n _ v u c' h (recv_ok hx hc)
    · cases h

theorem closeN_ok {name : String} {nz n : Nat} {c c' : Tape} {d : List E}
    (h : closeN name nz n c = some (d, c')) (hc : AllOk c) : AllOk c' := by
  obtain ⟨_, nm, z, w, rfl⟩ := closeN_some h
  exact hc.tail

theorem closeOne_ok {name : String} {nz : Nat} {c c' : Tape} {x : E}
    (h : closeOne name nz c = some (x, c')) (hc : AllOk c) : AllOk c' ∧ okE x = true := by
  obtain ⟨nm, z, w, rfl⟩ := closeOne_some h
  exact ⟨hc.tail, hc _ List.mem_cons_self x (by simp)⟩

theorem at_ok {e : Ev} {c c' : Tape} (h : At e c c') (hc : AllOk c) : AllOk c' := by
  cases e with
  | sum x => exact recv_ok h hc
  | ans r x => exact (closeOne_ok h hc).1
  | ansNZ r x => exact (closeOne_ok h hc).1
  | read n v => exact recvLoop_ok n _ v c c' h hc
  | empty r =>
    have h' : (closeN r.name 0 0 c).map (fun x => ((), x.2)) = some ((), c') := h
    obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 h'
    obtain ⟨-, rfl⟩ := Prod.mk.inj e
    exact closeN_ok (d := y.1) (c' := y.2) hy hc
  | point r n v =>
    have h' : (closeN r.name 0 n c).map (fun x => (x.1.toArray, x.2)) = some (v, c') := h
    obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 h'
    obtain ⟨-, rfl⟩ := Prod.mk.inj e
    exact closeN_ok (d := y.1) (c' := y.2) hy hc

theorem evs_ok : ∀ (l : List Ev) (c c' : Tape), Evs l c c' → AllOk c →
    AllOk c' ∧ ∀ r x, Ev.ansNZ r x ∈ l → okE x = true
  | [], c, c', h, hc => by
    obtain rfl : c' = c := h
    exact ⟨hc, fun _ _ hm => nomatch hm⟩
  | e :: l, c, c', h, hc => by
    obtain ⟨c1, h1, h2⟩ := h
    obtain ⟨a, b⟩ := evs_ok l c1 c' h2 (at_ok h1 hc)
    refine ⟨a, fun r x hm => ?_⟩
    rcases List.mem_cons.1 hm with rfl | hm
    · exact (closeOne_ok (nz := 1) h1 hc).2
    · exact b r x hm

theorem roundT_ok {rule : TapeRule} {r : Fmt.RoundView} {e : Fmt.Entry} {x : FlatRound}
    (h : roundT rule r e = some x) (hr : (r.drawn.elems.all fun y => okE (E.ofTriple y)) = true) :
    OkD x := by
  unfold roundT at h
  split at h
  · cases h
  · split at h
    · obtain rfl := Option.some.inj h
      intro d hd
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (show d ∈ r.drawn.elems.map E.ofTriple from hd)
      exact List.all_eq_true.1 hr y hy
    · cases h

theorem tapeT_ok (rule : TapeRule) : ∀ (rs : List Fmt.RoundView) (es : List Fmt.Entry) (t : Tape),
    tapeT rule rs es = some t → okRoundsE rs = true → AllOk t
  | [], [], t, h, _ => by
    obtain rfl : [] = t := Option.some.inj h
    exact fun _ hx => nomatch hx
  | r :: rs, e :: es, t, h, ho => by
    unfold tapeT at h
    have ho' : (r.vals.all OnBytes.Maker.okGot && r.drawn.elems.all fun x => okE (E.ofTriple x)) =
        true ∧ okRoundsE rs = true := by
      unfold okRoundsE at ho ⊢
      simpa [List.all_cons, Bool.and_eq_true] using ho
    split at h
    · rename_i x u hx hu
      obtain rfl := Option.some.inj h
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact roundT_ok hx (Bool.and_eq_true _ _ ▸ ho'.1).2
      · exact tapeT_ok rule rs es u hu ho'.2 y hy
    · cases h
  | [], _ :: _, _, h, _ => by cases h
  | _ :: _, [], _, h, _ => by cases h

/-! ## Both invariants -/

def Inv (t : Tape) : Prop := AllNZ t ∧ AllOk t

/-- Not zero as words, and the words below the prime. -/
def Live (x : E) : Prop := isZeroE x = false ∧ okE x = true

theorem evs_inv {l : List Ev} {c c' : Tape} (h : Evs l c c') (hc : Inv c) :
    Inv c' ∧ ∀ r x, Ev.ansNZ r x ∈ l → Live x :=
  ⟨⟨(evs_nz l c c' h hc.1).1, (evs_ok l c c' h hc.2).1⟩,
    fun r x hm => ⟨(evs_nz l c c' h hc.1).2 r x hm, (evs_ok l c c' h hc.2).2 r x hm⟩⟩

/-- A Live element reads as an element that is not 0. -/
theorem live_ne {x : E} (h : Live x) : Reading.gl.val x ≠ 0 := fun e => by
  have : isZeroE x = true := (OnBytes.Slice.isZeroE_iff x h.2).2 e
  rw [h.1] at this
  cases this

/-! ## The tie keeps both -/

theorem tieFold_inv (a : E) : ∀ (l : List ℕ) (s s' : Forest.TieStep) (A B : Fork) (c c' : Tape),
    (l.foldlM (lkTieStep a) s) A c = .ok ((s', B), c') → Inv c → Inv c'
  | [], s, s', A, B, c, c', h, hc => by
    have e := (foldlM_nil_ok (lkTieStep a) s A c ((s', B), c')).1 h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (s' = s ∧ B = A) ∧ c' = c := by simpa [Prod.ext_iff] using e
    exact hc
  | j :: l, s, s', A, B, c, c', h, hc => by
    obtain ⟨s₁, F₁, c₁, h1, h2⟩ := (foldlM_cons_ok (lkTieStep a) s j l A c ((s', B), c')).1 h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hE, _⟩ := tieStep_ok a s j A F₁ c c₁ s₁ h1
    exact tieFold_inv a l s₁ s' F₁ B c₁ c' h2 (evs_inv hE hc).1

theorem tie_inv (a : E) (F G : Fork) (c c' : Tape) (T : Forest.Tie)
    (h : lkTie a F c = .ok ((T, G), c')) (hc : Inv c) : Inv c' := by
  obtain ⟨s, c1, pt, h1, hE, _⟩ := tie_ok a F G c c' T h
  exact (evs_inv hE (tieFold_inv a _ _ _ _ _ _ _ h1 hc)).1

/-! ## CEndWorth.lean's four, with Inv carried and beta Live -/

section
variable {K : Type} [CommRing K] (ρ : Reading K)

theorem level_end2 (s s' : Forest.Descent) (mu : ℕ) (order : List ℕ) (F G : Fork) (c c' : Tape)
    (h : lkLevel s mu order F c = .ok ((s', G), c')) (hF : Sized F) (hc : Inv c) :
    Later F G ∧ Sized G ∧ Inv c' ∧
      ∃ sL tau beta vL vR, EndIs ρ G s'.form sL tau beta vL vR ∧ Live beta := by
  obtain ⟨o, ho, _, _, e3⟩ := level_ok s mu order F G c c' s' h
  obtain ⟨p, m0, eps, rs, sentY, beta, vals, vL, vR, F3, p', _, _, _, _, _, _, _, hv2, hEv, _, _,
    hsR, hH3, _, _, hHG, _, _, _⟩ := levelIn_ran mu s.rho s.form order F G c c' o ho
  obtain ⟨i1, i2⟩ := evs_inv hEv hc
  have hT := took_sized (1 + 2 * order.length + (2 + 2)) hF
  obtain ⟨_, s3, hnew, _⟩ := hideRun_ok _ F3 o.sL vals beta hT hH3
  obtain ⟨lG, sG, _⟩ := hide_new s3 hHG
  have L : Later F G := ((took_later F _).trans (hideRun_later hT hH3)).trans lG
  refine ⟨L, sG, i1, o.sL, o.tau, beta, vals.getD 0 zeroE, vals.getD 1 zeroE,
    fun H hH mask entry => ?_, i2 .pscY beta (by simp [levelEv])⟩
  obtain ⟨_, _, a3, a4, a5⟩ := hnew 0 (by rw [hv2]; exact Nat.two_pos)
  obtain ⟨_, _, b3, b4, b5⟩ := hnew 1 (by rw [hv2]; exact Nat.one_lt_two)
  obtain ⟨_, a6, a7⟩ := (lG.trans hH).keep _ a3
  obtain ⟨_, b6, b7⟩ := (lG.trans hH).keep _ b3
  rw [Nat.add_zero] at a4 a5 a6 a7
  have wL : (H.worldOf ρ mask entry).slot o.sL =
      ρ.val (vals.getD 0 zeroE) - ρ.val beta * mask o.sL := by
    show ρ.val (H.vp.getD o.sL zeroE) - ρ.val (H.mf.getD o.sL zeroE) * mask o.sL = _
    rw [a6, a7, a4, a5]
  have wR : (H.worldOf ρ mask entry).slot (o.sL + 1) =
      ρ.val (vals.getD 1 zeroE) - ρ.val beta * mask (o.sL + 1) := by
    show ρ.val (H.vp.getD (o.sL + 1) zeroE) - ρ.val (H.mf.getD (o.sL + 1) zeroE) *
      mask (o.sL + 1) = _
    rw [b6, b7, b4, b5]
  rw [e3, hsR, Aff.value_add, Aff.value_scale, Aff.value_scale, Aff.value_slot, Aff.value_slot,
    wL, wR, ρ.sub, ρ.one]

theorem fold_end2 {α : Type} (f : Forest.Descent → α → Fl Forest.Descent)
    (hf : ∀ s a, ∃ mu order, f s a = lkLevel s mu order) :
    ∀ (l : List α) (s s' : Forest.Descent) (A B : Fork) (c c' : Tape), l ≠ [] →
      (l.foldlM f s) A c = .ok ((s', B), c') → Sized A → Inv c →
      ∃ sL tau beta vL vR, EndIs ρ B s'.form sL tau beta vL vR ∧ Live beta
  | [], _, _, _, _, _, _, hne, _, _, _ => absurd rfl hne
  | a :: l, s, s', A, B, c, c', _, h, hA, hc => by
    obtain ⟨s₁, F₁, c₁, h1, h2⟩ := (foldlM_cons_ok f s a l A c ((s', B), c')).1 h
    obtain ⟨mu, order, e⟩ := hf s a
    rw [e] at h1
    obtain ⟨_, z1, i1, x1⟩ := level_end2 ρ s s₁ mu order A F₁ c c₁ h1 hA hc
    cases l with
    | nil =>
      have e2 := (foldlM_nil_ok f s₁ F₁ c₁ ((s', B), c')).1 h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (s' = s₁ ∧ B = F₁) ∧ c' = c₁ := by simpa [Prod.ext_iff] using e2
      exact x1
    | cons b l' => exact fold_end2 f hf (b :: l') s₁ s' F₁ B c₁ c' (by simp) h2 z1 i1

theorem pad_end2 {calls : Array Call} {pub : Array Nat} {lid : ℕ} {F F' : Fork} {c c' : Tape}
    {g : Forest.Heard} {M : PadMid} (P : PadCut calls pub lid F c g F' c' M) (hF : Sized F)
    (hv : (M.h pub).v ≠ 0) (hL : Later M.F6 F') (hc : Inv c) :
    ∃ sL tau beta vL vR, EndIs ρ F' g.cEnd sL tau beta vL vR ∧ Live beta := by
  obtain ⟨h4, hE4, _⟩ := head_cut P
  have z4 : Sized M.F4 := h4 ▸ owed3_sized hF
  obtain ⟨_, z5, _⟩ := tie_named M.a M.F4 M.F5 M.c4 M.c5 M.t P.tie z4
  have i5 : Inv M.c5 := tie_inv M.a M.F4 M.F5 M.c4 M.c5 M.t P.tie (evs_inv hE4 hc).1
  obtain ⟨sL, tau, beta, vL, vR, x, hb⟩ := fold_end2 ρ _ (fun s mu => ⟨_, _, rfl⟩) _ _ _ _ _ _ _
    (by
      intro e
      exact hv (by simpa using congrArg List.length e)) P.keys z5 i5
  refine ⟨sL, tau, beta, vL, vR, ?_, hb⟩
  rw [P.heard]
  exact x.later ρ hL

end

theorem lkPad_end2 (calls : Array Call) (pub : Array Nat) (lid : ℕ) (F F' : Fork) (t u : Tape)
    (g : Forest.Heard) (h : lkPad calls pub lid F t = some (g, F', u)) (hF : Sized F)
    (hv : g.shape.v ≠ 0) (ht : Inv t) :
    ∃ sL tau beta vL vR, EndIs Reading.gl F' g.cEnd sL tau beta vL vR ∧ Live beta := by
  have h' : lkPad calls pub lid F t = .ok ((g, F'), u) := h
  obtain ⟨M, P⟩ := pad_cut calls pub lid F F' t u g h'
  have hg : g.shape = M.h pub := pad_shape P
  have H : FoNums.ok (M.h pub) = true := Cb.Fo.shape_ok P.shape (_root_.Fo.ask_ok P.ask)
  obtain ⟨l, scs, ptT, lvK, lvT, rowsK, rowsT, evK, evT, D, R⟩ :=
    pad_read Reading.gl P hF trivial 5 H
  exact pad_end2 Reading.gl P hF (hg ▸ hv) (P.fork ▸ R.table.later.trans R.r5.later) ht

/-- **The flat record's sparse form is not 0 at every mask row.** -/
theorem EndIs.inc_ne {K : Type} [Field K] {ρ : Reading K} {F : Fork} {f : Aff} {sL : ℕ}
    {tau beta vL vR : E} (h : EndIs ρ F f sL tau beta vL vR) (hb : ρ.val beta ≠ 0) {tg : K}
    {inc : List (Pl × K)} (hF : FormIs ρ F f tg inc) : ∃ m : ℕ → K, evalL (muOf m) inc ≠ 0 := by
  obtain ⟨j, _, ht⟩ := h.turns hb
  by_contra hn
  have hz : ∀ m : ℕ → K, evalL (muOf m) inc = 0 := fun m => by
    by_contra e
    exact hn ⟨m, e⟩
  refine ht F (Later.refl F) (fun _ => 0) (fun i => if i = j then 1 else 0) (fun _ _ _ => 0)
    (fun i hi => by simp [hi]) (by simp) ?_
  rw [(hF F (Later.refl F)).2, (hF F (Later.refl F)).2, hz, hz]

end Fo.Tp

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.K.Kc OnBytes.PscRun
open VerifiableInference.Desc.First.Tape (flRun flRun_holds)

/-- **Of K3.block's decide**, at rounds whose words are below the prime. -/
theorem decide_end {S Cl : Type} (seat : Desc.K3.Seat S Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (s s' : S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block seat piece laid before p guests).decide s rs cols = .ok s')
    (ho : okRoundsE rs = true) :
    ∃ (F : Fork) (x : Forest.Heard × Fork), seat.fork s = some F ∧ s' = seat.put s x.1 x.2 ∧
      (Sized F → x.1.shape.v ≠ 0 → ∃ sL tau beta vL vR,
        _root_.Fo.Tp.EndIs Reading.gl x.2 x.1.cEnd sL tau beta vL vR ∧
          Reading.gl.val beta ≠ 0) := by
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
      obtain ⟨sL, tau, beta, vL, vR, a, b⟩ :=
        _root_.Fo.Tp.lkPad_end2 p.calls p.pub p.lid F x.2 t [] x.1 hl hS hv
          ⟨_root_.Fo.Tp.tapeT_nz _ _ _ _ ht, _root_.Fo.Tp.tapeT_ok _ _ _ _ ht ho⟩
      exact ⟨sL, tau, beta, vL, vR, a, _root_.Fo.Tp.live_ne b⟩
    · exact absurd hx (by simp)

end VerifiableInference.OnPublicFiles

#print axioms Fo.Tp.evs_inv
#print axioms Fo.Tp.live_ne
#print axioms Fo.Tp.lkPad_end2
#print axioms Fo.Tp.EndIs.inc_ne
#print axioms VerifiableInference.OnPublicFiles.decide_end
