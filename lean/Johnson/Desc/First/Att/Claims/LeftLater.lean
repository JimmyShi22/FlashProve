-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/LeftLater.lean: kind K5: what the kind's runs read of the first
chain's record, and that they gather the same forms at every later record.

Main names:
  `ShownLe F G`: what is shown under a slot in the ledger F is shown under it in G.
    `shownLe_of_later`: PscRun.Later F G (OnBytes/Tie/Pv/Psc/PscLater.lean) gives it.
  `foldlM_mono`, `mapM_mono`, `mapM_monoA`; `left_mono`, `leftKey_mono`, `leftP_mono`: what leftP
    (Johnson/Desc/First/Att/LeftP.lean) returns at F it returns at G. `ptsFrom_mono`,
    `ptsFrom_later`.
  `inOf_mono`: at the claims' seat on the kind's own road (seatCH,
    Johnson/Desc/First/Att/SeatH.lean): where inOf returns at s it returns the same at every s' in
    which heard5 and g are those of s, the ledger shows what that of s shows, and the arrays'
    numbers of columns (widths, Johnson/Desc/First/Att/Claims/Widths.lean) are those of s.
  `firstK_mono`, `secondK_mono`, `keysOfK_mono`: so the lists of "first" and "second" and the key
    forms are the same at s'.
Limits: one-sided: from a return at s. PscRun.Later has no clause on the arrays: that widths stays
is a premise of its own. Nothing is said of the run "join" (the lookup's kind's text).

Nothing is claimed on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Psc.PscLater
import Johnson.Desc.First.Att.RunsK
import Johnson.Desc.First.Att.SeatH
import Johnson.Desc.First.Att.Claims.Widths

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo Heard Left Pts)
open VerifiableInference.Desc.Part (MaskedSum.Heard)

/-- What is shown under a slot in F is shown under it in G. -/
def ShownLe (F G : Fork) : Prop := ∀ j y, F.shown j = some y → G.shown j = some y

theorem ShownLe.refl (F : Fork) : ShownLe F F := fun _ _ h => h

/-- A later state of the ledger shows what was shown. -/
theorem shownLe_of_later {F G : Fork} (h : PscRun.Later F G) : ShownLe F G := by
  intro j y hy
  unfold Fork.shown at hy ⊢
  split at hy
  · rename_i hc
    rw [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨k1, k2, _⟩ := h.keep j hc.2
    have k1' : G.gotF.getD j false = true := k1
    rw [if_pos (by rw [Bool.and_eq_true, decide_eq_true_eq, h.ns]; exact ⟨hc.1, k1'⟩), k2]
    exact hy
  · cases hy

theorem foldlM_mono {α β : Type} {f f' : β → α → Option β} (hf : ∀ b a c, f b a = some c → f' b a = some c) :
    ∀ (l : List α) (b c : β), l.foldlM f b = some c → l.foldlM f' b = some c
  | [], b, c, h => h
  | a :: l, b, c, h => by
    rw [List.foldlM_cons] at h ⊢
    obtain ⟨x, hx, hr⟩ := Option.bind_eq_some_iff.1 h
    exact Option.bind_eq_some_iff.2 ⟨x, hf _ _ _ hx, foldlM_mono hf l x c hr⟩

theorem mapM_mono {α β : Type} {f f' : α → Option β} (hf : ∀ a c, f a = some c → f' a = some c) :
    ∀ (l : List α) (c : List β), l.mapM f = some c → l.mapM f' = some c
  | [], c, h => h
  | a :: l, c, h => by
    rw [List.mapM_cons] at h ⊢
    obtain ⟨x, hx, hr⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨xs, hxs, e⟩ := Option.bind_eq_some_iff.1 hr
    exact Option.bind_eq_some_iff.2 ⟨x, hf _ _ hx, Option.bind_eq_some_iff.2 ⟨xs, mapM_mono hf l xs hxs, e⟩⟩

theorem mapM_monoA {α β : Type} {f f' : α → Option β} (hf : ∀ a c, f a = some c → f' a = some c)
    (l : Array α) (c : Array β) (h : l.mapM f = some c) : l.mapM f' = some c := by
  rw [Array.mapM_eq_mapM_toList] at h ⊢
  obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 h
  exact Option.map_eq_some_iff.2 ⟨x, mapM_mono hf _ _ hx, e⟩

variable {F G : Fork}

theorem left_mono (H : ShownLe F G) {h : MaskedSum.Heard} {W : Array E} {a : Aff}
    (e : P.left F h W = some a) : P.left G h W = some a := by
  unfold P.left at e ⊢
  obtain ⟨s0, h0, r⟩ := Option.bind_eq_some_iff.1 e
  refine Option.bind_eq_some_iff.2 ⟨s0, foldlM_mono (fun b x c hc => ?_) _ _ _ h0, r⟩
  obtain ⟨u, hu, hc⟩ := Option.bind_eq_some_iff.1 hc
  obtain ⟨v, hv, hc⟩ := Option.bind_eq_some_iff.1 hc
  exact Option.bind_eq_some_iff.2 ⟨u, H _ _ hu, Option.bind_eq_some_iff.2 ⟨v, H _ _ hv, hc⟩⟩

theorem leftKey_mono (H : ShownLe F G) {g : Geo} {h : MaskedSum.Heard} {rho om' : Array E} {a : Aff}
    (e : P.leftKey g F h rho om' = some a) : P.leftKey g G h rho om' = some a := by
  unfold P.leftKey at e ⊢
  obtain ⟨s0, h0, r⟩ := Option.bind_eq_some_iff.1 e
  refine Option.bind_eq_some_iff.2 ⟨s0, foldlM_mono (fun b x c hc => ?_) _ _ _ h0, r⟩
  obtain ⟨kc, hk, hc⟩ := Option.bind_eq_some_iff.1 hc
  obtain ⟨t, ht, hc⟩ := Option.bind_eq_some_iff.1 hc
  refine Option.bind_eq_some_iff.2 ⟨kc, H _ _ hk, Option.bind_eq_some_iff.2
    ⟨t, foldlM_mono (fun b' k c' hc' => ?_) _ _ _ ht, hc⟩⟩
  obtain ⟨v, hv, hc'⟩ := Option.bind_eq_some_iff.1 hc'
  exact Option.bind_eq_some_iff.2 ⟨v, H _ _ hv, hc'⟩

/-- **What leftP returns at a ledger it returns at every ledger that shows what that one shows.** -/
theorem leftP_mono (H : ShownLe F G) {g : Geo} {zk : Array (Array E)} {h : Heard} {L : Left}
    (e : P.leftP g zk h F = some L) : P.leftP g zk h G = some L := by
  unfold P.leftP at e ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at e ⊢
  obtain ⟨u0, g0, scores, hs, wl, hwl, u1, g1, division, hd, below, hb, on, ho, atIndex, ha, keyRow, hk, cells,
    hc, r⟩ := e
  refine ⟨u0, g0, scores, mapM_monoA (fun x c hx => ?_) _ _ hs, wl, hwl, u1, g1, division, left_mono H hd, below,
    left_mono H hb, on, left_mono H ho, atIndex, left_mono H ha, keyRow, leftKey_mono H hk, cells,
    left_mono H hc, r⟩
  obtain ⟨w, hw, hl⟩ := Option.bind_eq_some_iff.1 hx
  exact Option.bind_eq_some_iff.2 ⟨w, hw, left_mono H hl⟩

/-- So does the kind's own road from what was heard to what the claims read. -/
theorem ptsFrom_mono (H : ShownLe F G) {g : Geo} {zk : Array (Array E)} {h : Heard} {p : Pts}
    (e : P.ptsFrom g zk h F = some p) : P.ptsFrom g zk h G = some p := by
  unfold P.ptsFrom at e ⊢
  obtain ⟨L, hL, r⟩ := Option.bind_eq_some_iff.1 e
  exact Option.bind_eq_some_iff.2 ⟨L, leftP_mono H hL, r⟩

theorem ptsFrom_later (H : PscRun.Later F G) {g : Geo} {zk : Array (Array E)} {h : Heard} {p : Pts}
    (e : P.ptsFrom g zk h F = some p) : P.ptsFrom g zk h G = some p := ptsFrom_mono (shownLe_of_later H) e

open VerifiableInference.Desc (First.S) in
/-- **What the kind's runs read, at the claims' seat on the kind's own road (seatCH, Johnson/Desc/First/Att/SeatH.lean), hangs on four things alone**: what the kind heard (heard5), what its lookup heard (g), what is shown under the slots, and the arrays' numbers of columns. Where it returns at s it returns the same at every s' with the first two and the last the same, whose ledger shows what that of s shows. -/
theorem inOf_mono (c : P.ParC) {s s' : VerifiableInference.Desc.First.S} {a a' : VerifiableInference.Desc.First.AttOwn}
    (hs : s.here = .att a) (hs' : s'.here = .att a') (hg : a'.g = a.g) (h5 : a'.heard5 = a.heard5)
    (H : ShownLe a.F a'.F) (hw : widths a'.F = widths a.F) {x : P.Runs.In × ℕ}
    (e : P.inOf (P.seatCH c) c s = some x) : P.inOf (P.seatCH c) c s' = some x := by
  unfold P.inOf at e ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at e ⊢
  obtain ⟨p, hp, lk, hl, t, ht, zk, hz, K, hK, r⟩ := e
  refine ⟨p, ?_, lk, ?_, t, ht, zk, ?_, K, ?_, r⟩
  · have hp1 : (a.g.bind fun g => s.heard5?.bind fun h => P.ptsFrom c.geo g.zk h a.F) = some p := by
      have : (P.seatCH c).pts s = some p := hp
      unfold P.seatCH at this
      simp only [hs] at this
      exact this
    show (P.seatCH c).pts s' = some p
    unfold P.seatCH
    simp only [hs']
    obtain ⟨g, e1, hp2⟩ := Option.bind_eq_some_iff.1 hp1
    obtain ⟨h, e2, hp3⟩ := Option.bind_eq_some_iff.1 hp2
    have e2' : s'.heard5? = some h := by
      unfold VerifiableInference.Desc.First.S.heard5? at e2 ⊢
      rw [hs] at e2
      rw [hs']
      exact h5.trans e2
    exact Option.bind_eq_some_iff.2 ⟨g, hg.trans e1, Option.bind_eq_some_iff.2 ⟨h, e2', ptsFrom_mono H hp3⟩⟩
  · have : (P.seatCS c).look s = some lk := hl
    show (P.seatCS c).look s' = some lk
    unfold P.seatCS at this ⊢
    simp only [hs] at this
    simp only [hs', hg]
    exact this
  · have : (P.seatCS c).zk s = some zk := hz
    show (P.seatCS c).zk s' = some zk
    unfold P.seatCS at this ⊢
    simp only [hs] at this
    simp only [hs', hg]
    exact this
  · have : (P.seatCS c).cols s = some K := hK
    show (P.seatCS c).cols s' = some K
    unfold P.seatCS at this ⊢
    simp only [hs] at this
    simp only [hs', cols_of_widths hw]
    exact this

section Runs
variable (c : P.ParC) {s s' : VerifiableInference.Desc.First.S} {a a' : VerifiableInference.Desc.First.AttOwn}
  (hs : s.here = .att a) (hs' : s'.here = .att a') (hg : a'.g = a.g) (h5 : a'.heard5 = a.heard5)
  (H : ShownLe a.F a'.F) (hw : widths a'.F = widths a.F)
include hs hs' hg h5 H hw

/-- **"first" gathers at s' the very forms that it gathers at s.** -/
theorem firstK_mono {y : List Aff × VerifiableInference.Desc.First.S} (e : P.firstK (P.seatCH c) c s = some y) :
    P.firstK (P.seatCH c) c s' = some (y.1, s') := by
  unfold P.firstK at e ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at e ⊢
  obtain ⟨x, hx, f, hf, r⟩ := e
  refine ⟨x, inOf_mono c hs hs' hg h5 H hw hx, f, hf, ?_⟩
  rw [← Option.some.inj r]
  rfl

/-- **So does "second".** -/
theorem secondK_mono {y : List Aff × VerifiableInference.Desc.First.S} (e : P.secondK (P.seatCH c) c s = some y) :
    P.secondK (P.seatCH c) c s' = some (y.1, s') := by
  unfold P.secondK at e ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at e ⊢
  obtain ⟨x, hx, f, hf, r⟩ := e
  refine ⟨x, inOf_mono c hs hs' hg h5 H hw hx, f, hf, ?_⟩
  rw [← Option.some.inj r]
  rfl

/-- **And the key forms are the same.** -/
theorem keysOfK_mono {kf : Array Aff} (e : P.keysOfK (P.seatCH c) c s = some kf) :
    P.keysOfK (P.seatCH c) c s' = some kf := by
  unfold P.keysOfK at e ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at e ⊢
  obtain ⟨x, hx, k3, hk, f, hf, r⟩ := e
  refine ⟨x, inOf_mono c hs hs' hg h5 H hw hx, k3, ?_, f, hf, r⟩
  have : (P.seatCS c).pad s = some k3 := hk
  show (P.seatCS c).pad s' = some k3
  unfold P.seatCS at this ⊢
  simp only [hs] at this
  simp only [hs', hg]
  exact this

end Runs

end K5Law
