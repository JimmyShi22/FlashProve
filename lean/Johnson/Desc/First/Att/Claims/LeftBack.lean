-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/LeftBack.lean: kind K5: Claims/LeftLater.lean's one-sided laws TURNED
ROUND: what the kind's runs return at a LATER record of the segment they return at an EARLIER one, IF
the earlier ledger shows, under the slots that the kind's road looks under, what the later one shows.

Why. leftP (Att/LeftP.lean) looks at the ledger through "what is shown under a slot" alone, and only
under the end values' slots of the segment's sumchecks; its other refusals are tests that do not take
the ledger. A law on a run of claims that fixes the forms at a snapshot wants the return AT THE
SNAPSHOT from a return at the live record.

Main names:
  ShownBack Ps F G': under every slot that meets Ps, what G' shows F shows.
    shownBack_of_filled: ShownLe F G' and Sized F give ShownBack (Filled F) F G'.
  EndsInP Ps g zk h: in leftP's own letters, a stretch a sumcheck: every slot of it meets Ps.
  left_back, leftKey_back, leftP_back, ptsFrom_back. left_looks: a control: where left returns, every
    slot of its stretch shows something.
  inOf_back, firstK_back, secondK_back, keysOfK_back: at the claims' seat on the kind's own road
    (seatCH), under LeftLater's own premises on the two records.
IS IT EMPTY HERE?
  · At Ps := fun _ => True ShownBack says "F shows all that G' shows": the laws are then LeftLater's
    with the two ledgers' names changed.
  · At Ps := fun _ => False ShownBack holds of every pair and EndsInP fails wherever a stretch is not
    empty.
  · From a refusal at the later record nothing follows.
  · The premise is not idle: left_looks: at a ledger that shows nothing under a slot of the stretch left
    refuses, whatever a later ledger shows.
  · NEITHER ShownBack NOR EndsInP IS SHOWN OF ANY RECORD HERE but through shownBack_of_filled.
Limits. No size is argued but what leftP's own tests give (the pieces' number is NP; scoreW's weights are
  as many as the unit's). That h.om and h.om'' have NP members is not used and not shown: EndsInP speaks
  of their sizes as they are. Nothing of the run "join".
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.LeftLater
import Johnson.Desc.First.Att.K05LeftRet

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open OnBytes.PscRun (Filled)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo Heard Left Pts)
open VerifiableInference.Desc.Part (MaskedSum.Heard)

/-- Under every slot that meets Ps, what G' shows F shows. -/
def ShownBack (Ps : ℕ → Prop) (F G' : Fork) : Prop := ∀ j y, Ps j → G'.shown j = some y → F.shown j = some y

/-- A filled slot of a sized ledger shows something; a ledger that shows what it shows, shows that. -/
theorem shownBack_of_filled {F G' : Fork} (H : ShownLe F G') (hz : Road.Sized F) :
    ShownBack (Filled F) F G' := by
  intro j y hj hy
  have h0 : F.shown j = some (F.vp.getD j zeroE) := P.shown_of_put hz (f := F.mf.getD j zeroE) ⟨hj, rfl, rfl⟩
  have h1 := H _ _ h0
  rw [hy] at h1
  rw [h0, Option.some.inj h1]

/-- The same in the letters of OnBytes/Tie/Pv/Psc/PscLater.lean. -/
theorem shownBack_of_later {F G' : Fork} (H : PscRun.Later F G') (hz : PscRun.Sized F) :
    ShownBack (Filled F) F G' :=
  shownBack_of_filled (shownLe_of_later H) ⟨hz.1, hz.2.1, hz.2.2⟩

theorem foldlM_mono_mem {α β : Type} {f f' : β → α → Option β} :
    ∀ (l : List α), (∀ b a c, a ∈ l → f b a = some c → f' b a = some c) →
      ∀ (b c : β), l.foldlM f b = some c → l.foldlM f' b = some c
  | [], _, b, c, h => h
  | a :: l, hf, b, c, h => by
    rw [List.foldlM_cons] at h ⊢
    obtain ⟨x, hx, hr⟩ := Option.bind_eq_some_iff.1 h
    exact Option.bind_eq_some_iff.2 ⟨x, hf b a x List.mem_cons_self hx,
      foldlM_mono_mem l (fun b a c ha => hf b a c (List.mem_cons_of_mem _ ha)) x c hr⟩

theorem mapM_mono_mem {α β : Type} {f f' : α → Option β} :
    ∀ (l : List α), (∀ a c, a ∈ l → f a = some c → f' a = some c) →
      ∀ (c : List β), l.mapM f = some c → l.mapM f' = some c
  | [], _, c, h => h
  | a :: l, hf, c, h => by
    rw [List.mapM_cons] at h ⊢
    obtain ⟨x, hx, hr⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y, hy, hr⟩ := Option.bind_eq_some_iff.1 hr
    exact Option.bind_eq_some_iff.2 ⟨x, hf a x List.mem_cons_self hx, Option.bind_eq_some_iff.2
      ⟨y, mapM_mono_mem l (fun a c ha => hf a c (List.mem_cons_of_mem _ ha)) y hy, hr⟩⟩

theorem mapM_mono_memA {α β : Type} {f f' : α → Option β} (l : Array α)
    (hf : ∀ a c, a ∈ l.toList → f a = some c → f' a = some c) (c : Array β) (h : l.mapM f = some c) :
    l.mapM f' = some c := by
  rw [Array.mapM_eq_mapM_toList] at h ⊢
  obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 h
  exact Option.map_eq_some_iff.2 ⟨x, mapM_mono_mem _ hf _ hx, e⟩

variable {Ps : ℕ → Prop} {F G' : Fork}

theorem left_back (B : ShownBack Ps F G') {h : MaskedSum.Heard} {W : Array E} {a : Aff}
    (hp : ∀ i, i < 2 * W.size → Ps (h.sEnd + i)) (e : P.left G' h W = some a) :
    P.left F h W = some a := by
  unfold P.left at e ⊢
  obtain ⟨s0, h0, r⟩ := Option.bind_eq_some_iff.1 e
  refine Option.bind_eq_some_iff.2 ⟨s0, foldlM_mono_mem _ (fun b x c hx hc => ?_) _ _ h0, r⟩
  have hx' := List.mem_range.1 hx
  obtain ⟨u, hu, hc⟩ := Option.bind_eq_some_iff.1 hc
  obtain ⟨v, hv, hc⟩ := Option.bind_eq_some_iff.1 hc
  exact Option.bind_eq_some_iff.2 ⟨u, B _ _ (hp _ (by omega)) hu,
    Option.bind_eq_some_iff.2 ⟨v, B _ _ (hp _ (by omega)) hv, hc⟩⟩

theorem foldlM_steps {α β : Type} {f : β → α → Option β} :
    ∀ (l : List α) (b c : β), l.foldlM f b = some c → ∀ a ∈ l, ∃ b' c', f b' a = some c'
  | [], _, _, _, _, ha => nomatch ha
  | x :: l, b, c, h, a, ha => by
    rw [List.foldlM_cons] at h
    obtain ⟨y, hy, hr⟩ := Option.bind_eq_some_iff.1 h
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨b, y, hy⟩
    · exact foldlM_steps l y c hr a ha

/-- A control: **left does look under every slot of its stretch**: where it returns, each shows something.
So at a ledger that shows nothing under one of them left refuses: ShownBack is not an idle premise. -/
theorem left_looks {h : MaskedSum.Heard} {W : Array E} {a : Aff} (e : P.left F h W = some a) :
    ∀ i, i < 2 * W.size → (F.shown (h.sEnd + i)).isSome = true := by
  unfold P.left at e
  obtain ⟨s0, h0, _⟩ := Option.bind_eq_some_iff.1 e
  intro i hi
  obtain ⟨b', c', hc⟩ := foldlM_steps _ _ _ h0 (i / 2) (List.mem_range.2 (by omega))
  obtain ⟨u, hu, hc⟩ := Option.bind_eq_some_iff.1 hc
  obtain ⟨v, hv, _⟩ := Option.bind_eq_some_iff.1 hc
  rcases Nat.mod_two_eq_zero_or_one i with hm | hm
  · have : i = 2 * (i / 2) := by omega
    rw [this, hu]; rfl
  · have : i = 2 * (i / 2) + 1 := by omega
    rw [this, hv]; rfl

theorem leftKey_back (B : ShownBack Ps F G') {g : Geo} {h : MaskedSum.Heard} {rho om' : Array E} {a : Aff}
    (hp : ∀ i, i < g.Lam + g.NP * g.lt → Ps (h.sEnd + i)) (e : P.leftKey g G' h rho om' = some a) :
    P.leftKey g F h rho om' = some a := by
  unfold P.leftKey at e ⊢
  obtain ⟨s0, h0, r⟩ := Option.bind_eq_some_iff.1 e
  refine Option.bind_eq_some_iff.2 ⟨s0, foldlM_mono_mem _ (fun b x c hx hc => ?_) _ _ h0, r⟩
  have hx' : x < g.Lam * g.HA := List.mem_range.1 hx
  have hd : x / g.HA < g.Lam := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hx')
  obtain ⟨kc, hk, hc⟩ := Option.bind_eq_some_iff.1 hc
  obtain ⟨t, ht, hc⟩ := Option.bind_eq_some_iff.1 hc
  refine Option.bind_eq_some_iff.2 ⟨kc, B _ _ (hp _ (by omega)) hk, Option.bind_eq_some_iff.2
    ⟨t, foldlM_mono_mem _ (fun b' k c' hk' hc' => ?_) _ _ ht, hc⟩⟩
  have hc2 : x * g.lt + k < g.NP * g.lt :=
    calc x * g.lt + k < x * g.lt + g.lt := Nat.add_lt_add_left (List.mem_range.1 hk') _
      _ = (x + 1) * g.lt := (Nat.succ_mul x g.lt).symm
      _ ≤ g.NP * g.lt := Nat.mul_le_mul_right g.lt hx'
  obtain ⟨v, hv, hc'⟩ := Option.bind_eq_some_iff.1 hc'
  exact Option.bind_eq_some_iff.2 ⟨v, B _ _ (hp _ (by omega)) hv, hc'⟩

/-- **The slots that leftP looks under, in its own letters: a stretch a sumcheck.** -/
structure EndsInP (Ps : ℕ → Prop) (g : Geo) (zk : Array (Array E)) (h : Heard) : Prop where
  units : ∀ x ∈ (g.scores.toArray.zip h.scores).toList,
    ∀ i, i < 2 * (P.weights x.1 (zk.getD x.1.call #[])).size → Ps (x.2.2.sEnd + i)
  division : ∀ i, i < 2 * g.NP → Ps (h.division.sEnd + i)
  below : ∀ i, i < 2 * g.NP → Ps (h.below.sEnd + i)
  on : ∀ i, i < 2 * g.NP → Ps (h.on.sEnd + i)
  atIndex : ∀ i, i < 2 * h.om.size → Ps (h.atIndex.sEnd + i)
  key : ∀ i, i < g.Lam + g.NP * g.lt → Ps (h.key.sEnd + i)
  cells : ∀ i, i < 2 * h.om''.size → Ps (h.cells.sEnd + i)

theorem scoreW_size {g : Geo} {u : P.UnitG} {zk r w : Array E} (e : P.scoreW g u zk r = some w) :
    w.size = (P.weights u zk).size := by
  unfold P.scoreW at e
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at e
  obtain ⟨_, _, e⟩ := e
  rw [← Option.some.inj e, Array.size_map]

/-- **What leftP returns at the later ledger it returns at the earlier.** -/
theorem leftP_back (B : ShownBack Ps F G') {g : Geo} {zk : Array (Array E)} {h : Heard} {L : Left}
    (E : EndsInP Ps g zk h) (e : P.leftP g zk h G' = some L) : P.leftP g zk h F = some L := by
  unfold P.leftP at e ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at e ⊢
  obtain ⟨u0, g0, scores, hs, wl, hwl, u1, g1, division, hd, below, hb, on, ho, atIndex, ha, keyRow, hk, cells,
    hc, r⟩ := e
  have hsz : (P.weights wl (zk.getD wl.call #[])).size = g.NP := by
    have := P.guard_some g1
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this.1
  refine ⟨u0, g0, scores, mapM_mono_memA _ (fun x c hm hx => ?_) _ hs, wl, hwl, u1, g1, division,
    left_back B (fun i hi => E.division i (by rw [Array.size_map, hsz] at hi; exact hi)) hd, below,
    left_back B (fun i hi => E.below i (by rw [Array.size_map, hsz] at hi; exact hi)) hb, on,
    left_back B (fun i hi => E.on i (by rw [Array.size_map, hsz] at hi; exact hi)) ho, atIndex,
    left_back B (fun i hi => E.atIndex i (by rw [Array.size_map] at hi; exact hi)) ha, keyRow,
    leftKey_back B E.key hk, cells,
    left_back B (fun i hi => E.cells i (by rw [Array.size_map] at hi; exact hi)) hc, r⟩
  obtain ⟨w, hw, hl⟩ := Option.bind_eq_some_iff.1 hx
  exact Option.bind_eq_some_iff.2 ⟨w, hw,
    left_back B (fun i hi => E.units x hm i (by rw [scoreW_size hw] at hi; exact hi)) hl⟩

/-- So does the kind's own road from what was heard to what the claims read. -/
theorem ptsFrom_back (B : ShownBack Ps F G') {g : Geo} {zk : Array (Array E)} {h : Heard} {p : Pts}
    (E : EndsInP Ps g zk h) (e : P.ptsFrom g zk h G' = some p) : P.ptsFrom g zk h F = some p := by
  unfold P.ptsFrom at e ⊢
  obtain ⟨L, hL, r⟩ := Option.bind_eq_some_iff.1 e
  exact Option.bind_eq_some_iff.2 ⟨L, leftP_back B E hL, r⟩

/-! ### at the claims' seat on the kind's own road -/

section Seat
open VerifiableInference.Desc (First.S First.AttOwn)
variable (c : P.ParC) {s s' : First.S} {a a' : First.AttOwn}
  (hs : s.here = .att a) (hs' : s'.here = .att a') (hg : a'.g = a.g) (h5 : a'.heard5 = a.heard5)
  (B : ShownBack Ps a.F a'.F) (hw : widths a'.F = widths a.F)
  (E : ∀ gL h, a.g = some gL → a.heard5 = some h → EndsInP Ps c.geo gL.zk h)
include hs hs' hg h5 B hw E

/-- **What inOf returns at the later record s' it returns at the earlier s.** -/
theorem inOf_back {x : P.Runs.In × ℕ} (e : P.inOf (P.seatCH c) c s' = some x) :
    P.inOf (P.seatCH c) c s = some x := by
  unfold P.inOf at e ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at e ⊢
  obtain ⟨p, hp, lk, hl, t, ht, zk, hz, K, hK, r⟩ := e
  refine ⟨p, ?_, lk, ?_, t, ht, zk, ?_, K, ?_, r⟩
  · have hp1 : (a'.g.bind fun g => s'.heard5?.bind fun h => P.ptsFrom c.geo g.zk h a'.F) = some p := by
      have : (P.seatCH c).pts s' = some p := hp
      unfold P.seatCH at this
      simp only [hs'] at this
      exact this
    show (P.seatCH c).pts s = some p
    unfold P.seatCH
    simp only [hs]
    obtain ⟨g, e1, hp2⟩ := Option.bind_eq_some_iff.1 hp1
    obtain ⟨h, e2, hp3⟩ := Option.bind_eq_some_iff.1 hp2
    have e2a : a.heard5 = some h := by
      unfold First.S.heard5? at e2
      rw [hs'] at e2
      exact h5.symm.trans e2
    have e2' : s.heard5? = some h := by
      unfold First.S.heard5?
      rw [hs]
      exact e2a
    have e1' : a.g = some g := hg.symm.trans e1
    exact Option.bind_eq_some_iff.2 ⟨g, e1', Option.bind_eq_some_iff.2
      ⟨h, e2', ptsFrom_back B (E g h e1' e2a) hp3⟩⟩
  · have : (P.seatCS c).look s' = some lk := hl
    show (P.seatCS c).look s = some lk
    unfold P.seatCS at this ⊢
    simp only [hs', hg] at this
    simp only [hs]
    exact this
  · have : (P.seatCS c).zk s' = some zk := hz
    show (P.seatCS c).zk s = some zk
    unfold P.seatCS at this ⊢
    simp only [hs', hg] at this
    simp only [hs]
    exact this
  · have : (P.seatCS c).cols s' = some K := hK
    show (P.seatCS c).cols s = some K
    unfold P.seatCS at this ⊢
    simp only [hs', cols_of_widths hw] at this
    simp only [hs]
    exact this

/-- **"first" gathers at s the very forms that it gathers at s'.** -/
theorem firstK_back {y : List Aff × First.S} (e : P.firstK (P.seatCH c) c s' = some y) :
    P.firstK (P.seatCH c) c s = some (y.1, s) := by
  unfold P.firstK at e ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at e ⊢
  obtain ⟨x, hx, f, hf, r⟩ := e
  refine ⟨x, inOf_back c hs hs' hg h5 B hw E hx, f, hf, ?_⟩
  rw [← Option.some.inj r]
  rfl

/-- **So does "second".** -/
theorem secondK_back {y : List Aff × First.S} (e : P.secondK (P.seatCH c) c s' = some y) :
    P.secondK (P.seatCH c) c s = some (y.1, s) := by
  unfold P.secondK at e ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at e ⊢
  obtain ⟨x, hx, f, hf, r⟩ := e
  refine ⟨x, inOf_back c hs hs' hg h5 B hw E hx, f, hf, ?_⟩
  rw [← Option.some.inj r]
  rfl

/-- **The key forms at s are those at s'.** -/
theorem keysOfK_back {kf : Array Aff} (e : P.keysOfK (P.seatCH c) c s' = some kf) :
    P.keysOfK (P.seatCH c) c s = some kf := by
  unfold P.keysOfK at e ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at e ⊢
  obtain ⟨x, hx, k3, hk, f, hf, r⟩ := e
  refine ⟨x, inOf_back c hs hs' hg h5 B hw E hx, k3, ?_, f, hf, r⟩
  have : (P.seatCS c).pad s' = some k3 := hk
  show (P.seatCS c).pad s = some k3
  unfold P.seatCS at this ⊢
  simp only [hs', hg] at this
  simp only [hs]
  exact this

end Seat

end K5Law

#print axioms K5Law.left_looks
#print axioms K5Law.shownBack_of_later
#print axioms K5Law.inOf_back
#print axioms K5Law.firstK_back
#print axioms K5Law.secondK_back
#print axioms K5Law.keysOfK_back
#print axioms K5Law.shownBack_of_filled
#print axioms K5Law.leftP_back
#print axioms K5Law.ptsFrom_back
