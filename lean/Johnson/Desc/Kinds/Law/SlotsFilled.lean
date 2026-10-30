-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/SlotsFilled.lean: FOR K9's PAYERS: EVERY SLOT THAT THE OUTPUT HEAD's 35 FORMS NAME IS ONE THAT THE HEAD's OWN HEARING HAS TAKEN AND FILLED: so what the forms read under slots lies in the ledger in
front of the batching's draw, and stays under "later".
  SlotsIn lo hi f   every slot in f's own list of slots is a number from lo to hi - 1. Kept by the forms' arithmetic (kept_slotsIn: Law/FormsAll.lean's Kept).
  heardBy_slots     where the part's hearing of a sumcheck returns: the lead's variables, the end values' variables and the sumcheck's own form name slots of the stretch that the hearing took alone.
  heard_slotsIn     where Head.lean's hear returns, from a WellLaid ledger F to G: HeardHas (SlotsIn F.next G.next).
  forms_slotsIn     so, at reads whose entries name no slot: every form of every run of claims: SlotsIn F.next G.next.
  forms_filled      and each such slot is FILLED in G (Law/Takes.lean: hear_takes), and in every ledger later than G, with the same shown value and the same factor.
  value_agree       a form's value in two worlds that agree on the slots and the entries which it names is the same.
  forms_value_later SO: THE VALUE OF EACH OF THE 35 FORMS IN THE WORLD OF A LATER LEDGER (Fork.worldOf, OnBytes/Model/HideLaws.lean: vp[j] - mf[j] mask[j] under slot j) IS ITS VALUE IN THE WORLD OF THE LEDGER BEHIND THE HEARING, at one mask
                    row and one reading of the entries: the slots' half of the last clause of PlainOk (Johnson/Desc/First/Batch/Law/PlainRuns.lean).
WHAT IT IS NOT. Nothing on soundness. Not PlainOk. Nothing on the entries. "join"'s form and the keys: not here. That the reads' entries name no slot is a premise (at the real seat an entry is Aff.ent, which names none: by reading).

-/
import Mathlib
import Johnson.Desc.Kinds.Law.FormsAll
import Johnson.Desc.Kinds.Law.Takes
import Johnson.Desc.Kinds.Law.NormHear
import Johnson.Desc.Kinds.Law.CoveredNormAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE oneE)
open OnBytes.Model (Aff Fork)
open OnBytes.PscRun (Later Sized)
open Norm (lt ls d lPd T S2)
open Part.MaskedSum (ownSlots hidingAt)

/-- Every slot that the form names is a number from lo to hi - 1. -/
def SlotsIn (lo hi : Nat) (f : Form) : Prop := ∀ x, x ∈ f.slots.toList → lo ≤ x.1 ∧ x.1 < hi

theorem addMul_slots (a b : Aff) (k : E) : (Aff.addMul a b k).slots.toList
    = a.slots.toList ++ b.slots.toList.map fun x => (x.1, OnBytes.mulE x.2 k) := by
  show (b.slots.foldl (fun l x => l.push (x.1, OnBytes.mulE x.2 k)) a.slots).toList = _
  rw [← Array.foldl_toList, foldl_push_toList]

theorem kept_slotsIn (lo hi : Nat) : Kept (SlotsIn lo hi) where
  addMul := fun {a b} k ha hb x hx => by
    rw [addMul_slots] at hx
    rcases List.mem_append.mp hx with h | h
    · exact ha x h
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp h
      exact hb z hz
  bare := fun f _ hs x hx => by
    rw [hs] at hx
    simp at hx

theorem slotsIn_slot {lo hi j : Nat} (h1 : lo ≤ j) (h2 : j < hi) : SlotsIn lo hi (Aff.slot j) := by
  intro x hx
  have : x = (j, oneE) := by simpa [Aff.slot] using hx
  rw [this]
  exact ⟨h1, h2⟩

theorem SlotsIn.mono {lo hi lo' hi' : Nat} {f : Form} (h : SlotsIn lo hi f) (h1 : lo' ≤ lo)
    (h2 : hi ≤ hi') : SlotsIn lo' hi' f := fun x hx => by
  have := h x hx
  omega

theorem slotsIn_empty (lo hi : Nat) : SlotsIn lo hi ({} : Form) :=
  (kept_slotsIn lo hi).bare _ rfl rfl

theorem slotsIn_onSlots {lo hi : Nat} : ∀ (u : List E) (first : Nat) (f : Form), SlotsIn lo hi f →
    lo ≤ first → first + u.length ≤ hi → SlotsIn lo hi (Part.MaskedSum.onSlots f first u) := by
  intro u
  induction u with
  | nil => intro first f hf _ _; exact hf
  | cons x xs ih =>
    intro first f hf h1 h2
    rw [List.length_cons] at h2
    exact ih (first + 1) _ ((kept_slotsIn lo hi).addMul _ hf (slotsIn_slot h1 (by omega)))
      (by omega) (by omega)

theorem slotsIn_getD {lo hi : Nat} (arr : Array Hid)
    (h : ∀ y, y ∈ arr.toList → SlotsIn lo hi y.var) (j : Nat) :
    SlotsIn lo hi (arr.getD j {}).var := by
  by_cases hj : j < arr.size
  · have : arr.getD j {} = arr[j]'hj := by simp [Array.getD, hj]
    rw [this]
    exact h _ (Array.getElem_mem_toList hj)
  · have : arr.getD j {} = {} := by simp [Array.getD, hj]
    rw [this]
    exact slotsIn_empty lo hi

theorem hide_slots {v : List E} {F G : Fork} {rs left : List Fmt.RoundView} {c : Array Hid}
    (h : hide v F rs = some (c, G, left)) (j : Nat) :
    SlotsIn F.next (F.next + v.length) (c.getD j {}).var := by
  obtain ⟨_, h'⟩ := hide_some h
  obtain ⟨_, rfl⟩ := hide_unfold h'
  refine slotsIn_getD _ (fun y hy => ?_) j
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hy
  simp only [Array.getElem_toList, Array.getElem_mapIdx]
  have hi' : i < v.length := by simpa using hi
  exact slotsIn_slot (Nat.le_add_right _ _) (by omega)

theorem hiddenFrom_slots {first n : Nat} {F G : Fork} {rs left : List Fmt.RoundView} {c : Array Hid}
    (h : hiddenFrom first n F rs = some (c, G, left)) (j : Nat) :
    SlotsIn first (first + n) (c.getD j {}).var := by
  unfold hiddenFrom at h
  cases hr : ((List.range n).mapM fun j => (F.shown (first + j)).map fun x =>
      ({ var := Aff.slot (first + j), shown := x } : Hid)) with
  | none => rw [hr] at h; simp at h
  | some X =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _, _⟩ := h
    refine slotsIn_getD _ (fun y hy => ?_) j
    obtain ⟨i, hi, e⟩ := mapM_mem _ _ _ hr y (by simpa using hy)
    have hi' : i < n := List.mem_range.mp hi
    cases hs : F.shown (first + i) with
    | none => simp [hs] at e
    | some x =>
      simp [hs] at e
      subst e
      exact slotsIn_slot (Nat.le_add_right _ _) (by omega)

/-- **Where the part's hearing of a sumcheck returns.** -/
theorem heardBy_slots {lead : Nat} {C : Array Hid → Form} {z : Point} {ends : Nat} {F0 F1 : Fork}
    {t left : List Fmt.RoundView} {c : Array Hid} {s : Sum} (hF : Sized F0)
    (h : heardBy lead C z ends F0 t = some ((c, s), F1, left)) :
    (∀ j, SlotsIn F0.next F1.next (c.getD j {}).var) ∧
      (∀ j, SlotsIn F0.next F1.next (s.end_ j).var) ∧
      (∀ lo, lo ≤ F0.next → SlotsIn lo F1.next (C c) → ∀ S0, SlotsIn lo F1.next (s.left S0)) := by
  have TT := takes_heardBy hF h
  have hn := TT.next
  unfold heardBy at h
  obtain ⟨rs, Fx, l0, h1, k1⟩ := bind_some h
  have hFx : F0 = Fx := by
    unfold Hear.stretch at h1
    split at h1
    · cases h1
    · simp only [Option.some.injEq, Prod.mk.injEq] at h1
      exact h1.2.1
  subst hFx
  obtain ⟨ld, Fy, l1, h2, k2⟩ := bind_some k1
  obtain ⟨e2, rfl, rfl⟩ := need_some h2
  obtain ⟨c', Fa, l2, h3, k3⟩ := bind_some k2
  have hld : ld.length = lead := lead_length e2
  have T1 : Takes F0 Fa lead := (takes_hide hF h3).cast hld
  obtain ⟨Fl, Fz, l3, h4, k4⟩ := bind_some k3
  obtain ⟨rfl, rfl, rfl⟩ := ledger_some h4
  obtain ⟨hG, Fw, l4, h5, k5⟩ := bind_some k4
  obtain ⟨e5, rfl, rfl⟩ := need_some h5
  obtain ⟨hd, G⟩ := hG
  dsimp only at k5
  obtain ⟨_, Tt, R, _, hread, hhd, _⟩ := Part.MaskedSum.hear_spec e5
  obtain ⟨r0, used, rv, front, _, _, _, hvr, hsv⟩ := Part.MaskedSum.readAll_spec hread
  have hlenR : R.rounds.length = (callOf lead z ends).all.length := hvr.length.2
  have hown : ownSlots (callOf lead z ends).all = 2 * z.size + 3 := own_callOf lead z ends
  obtain ⟨Fr, Fv, l5, h6, k6⟩ := bind_some k5
  obtain ⟨u, Fu, l6, h7, k7⟩ := bind_some k6
  obtain ⟨es, Ft, l7, h8, k8⟩ := bind_some k7
  obtain ⟨e9, _, _⟩ := pure_some k8
  simp only [Prod.mk.injEq] at e9
  obtain ⟨rfl, rfl⟩ := e9
  have hlen : (hidingAt (hd.vars.zip hd.r)).1.length = 2 * z.size + 3 := by
    rw [hhd]
    show (hidingAt ((callOf lead z ends).all.zip (R.rounds.map (·.2)))).1.length = _
    have hz : ((callOf lead z ends).all.zip (R.rounds.map (·.2))).map (·.1)
        = (callOf lead z ends).all := List.map_fst_zip (by rw [List.length_map, hlenR])
    rw [hidingAt_length _ ?_ ?_, hz, hown]
    · intro hnil
      have := congrArg (List.map (·.1)) hnil
      rw [hz] at this
      simp [callOf, Part.MaskedSum.Call.all] at this
    · intro y hy
      have hy' : y.1 ∈ (callOf lead z ends).all := by
        rw [← hz]; exact List.mem_map_of_mem hy
      simp only [callOf, Part.MaskedSum.Call.all, List.mem_append, List.mem_map, List.mem_cons,
        List.not_mem_nil, or_false] at hy'
      rcases hy' with ⟨w, _, hw⟩ | hw
      · rw [← hw]
        show 1 ≤ 3
        omega
      · rw [hw]
        show 1 ≤ 2 + 1
        omega
  have hfirst : hd.first = Fa.next := by rw [hhd]
  have hsEnd : hd.sEnd = Fa.next + (2 * z.size + 3) := by
    rw [hhd]
    show Fa.next + ownSlots (callOf lead z ends).all = _
    rw [hown]
  have hna := T1.next
  refine ⟨fun j => ((hide_slots h3 j).mono (Nat.le_refl _) (by omega)), fun j => ?_,
    fun lo hlo hC S0 => ?_⟩
  · exact (hiddenFrom_slots h8 j).mono (by omega) (by omega)
  · show SlotsIn _ _ (Part.MaskedSum.rowForm hd S0 {})
    unfold Part.MaskedSum.rowForm
    have K := kept_slotsIn lo F1.next
    have hst : hd.start = C c' := by rw [hhd]
    refine K.addMul _ (K.addMul _ (slotsIn_onSlots _ _ _ (K.const _) (by omega) (by omega))
      (K.sub (K.const _) (by rw [hst]; exact hC))) (slotsIn_empty _ _)

theorem sumcheck_slots {z : Point} {n : Nat} {F0 F1 : Fork} {t left : List Fmt.RoundView} {s : Sum}
    (hF : Sized F0) (h : sumcheck z n F0 t = some (s, F1, left)) :
    SlotsIn F0.next F1.next s.claimed.var ∧ (∀ j, SlotsIn F0.next F1.next (s.end_ j).var) ∧
      ∀ S0, SlotsIn F0.next F1.next (s.left S0) := by
  unfold sumcheck at h
  obtain ⟨⟨c, s0⟩, G, l, h1, k1⟩ := bind_some h
  obtain ⟨rfl, rfl, _⟩ := pure_some k1
  obtain ⟨a, b, e⟩ := heardBy_slots hF h1
  exact ⟨a 0, b, e _ (Nat.le_refl _) (a 0)⟩

theorem level_slots {z : Point} {start : Form} {F0 F1 : Fork} {t left : List Fmt.RoundView} {s : Sum}
    (hF : Sized F0) (h : level z start F0 t = some (s, F1, left)) :
    (∀ j, SlotsIn F0.next F1.next (s.end_ j).var) ∧
      (∀ lo, lo ≤ F0.next → SlotsIn lo F1.next start → ∀ S0, SlotsIn lo F1.next (s.left S0)) := by
  unfold level at h
  obtain ⟨⟨c, s0⟩, G1, l1, h1, k1⟩ := bind_some h
  dsimp only at k1
  obtain ⟨⟨a, g⟩, G2, l2, h2, k2⟩ := bind_some k1
  obtain ⟨rfl, _, _⟩ := takes_round h2
  dsimp only at k2
  obtain ⟨x, G3, l3, h3, k3⟩ := bind_some k2
  obtain ⟨_, rfl, _⟩ := need_some h3
  obtain ⟨rfl, rfl, _⟩ := pure_some k3
  obtain ⟨_, b, e⟩ := heardBy_slots hF h1
  exact ⟨b, e⟩

theorem batch_slots {n rows : Nat} {F G : Fork} {rs left : List Fmt.RoundView} {W : Array Hid} {g : E}
    (hF : Sized F) (h : sendThenBatch n rows F rs = some ((W, g), G, left)) (j : Nat) :
    SlotsIn F.next G.next (W.getD j {}).var := by
  have hn := (takes_send hF h).next
  unfold sendThenBatch at h
  obtain ⟨⟨v, gs⟩, G1, l1, h1, k1⟩ := bind_some h
  obtain ⟨rfl, hv, _⟩ := takes_round h1
  dsimp only at k1 hv
  obtain ⟨W', G2, l2, h2, k2⟩ := bind_some k1
  obtain ⟨g', G3, l3, _, k3⟩ := bind_some k2
  obtain ⟨e4, _, _⟩ := pure_some k3
  simp only [Prod.mk.injEq] at e4
  obtain ⟨rfl, _⟩ := e4
  exact (hide_slots h2 j).mono (Nat.le_refl _) (by omega)

section Whole

variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In]

/-- **Where the head's hearing returns: all that was heard names slots of the hearing's own stretch alone.** -/
theorem heard_slotsIn [FinalNorm.Reads] [Reads] {F G : Fork} {rs left : List Fmt.RoundView}
    {H : HeardAll} (hW : WellLaid F) (h : hear F rs = some (H, G, left)) :
    letI : Norm.Heard := H.1
    letI : FinalNorm.Heard := H.2.1
    letI : Heard := H.2.2
    HeardHas (SlotsIn F.next G.next) := by
  letI : Norm.Heard := H.1
  letI : FinalNorm.Heard := H.2.1
  letI : Heard := H.2.2
  have sz : ∀ {X : Fork}, WellLaid X → Sized X := fun w => ⟨w.2.1, w.2.2, w.1⟩
  obtain ⟨G1, G2, l1, hNorm, wG1, wG2, hsN, hsL, _⟩ := Came.hear_parts hW h
  obtain ⟨p0, p1, tS, p2, tP, Fa, Fb, Fc, _, _, h1, _, h3, h4, h5, wa, wb, wc⟩ :=
    norm_parts hW hNorm
  have n1 := (takes_send (sz hW) h1).next
  have n3 := (takes_level (sz wa) h3).next
  have n4 := (takes_send (sz wb) h4).next
  have n5 := (takes_sumcheck (sz wc) h5).next
  have n6 := (takes_sumcheck (sz wG1) hsN).next
  have n7 := (takes_sumcheck (sz wG2) hsL).next
  have sW := batch_slots (sz hW) h1
  have sP := batch_slots (sz wb) h4
  obtain ⟨qE, qL⟩ := level_slots (sz wa) h3
  obtain ⟨pC, pE, pL⟩ := sumcheck_slots (sz wc) h5
  obtain ⟨_, nE, nL⟩ := sumcheck_slots (sz wG1) hsN
  obtain ⟨_, lE, lL⟩ := sumcheck_slots (sz wG2) hsL
  have K := kept_slotsIn F.next G.next
  have W' : ∀ s, SlotsIn F.next G.next (H.1.W.getD s {}).var := fun s =>
    (sW s).mono (Nat.le_refl _) (by omega)
  -- the squares' level: its start form stands on the nine sums' slots, which lie in front of it
  have K2 := kept_slotsIn F.next Fb.next
  have hstart : SlotsIn F.next Fb.next (Norm.squaresStart H.1.W H.1.gam #[]) := by
    unfold Norm.squaresStart
    exact K2.smulE _ (K2.sums _ _ fun i => K2.sums _ _ fun s =>
      K2.smulE _ ((sW _).mono (Nat.le_refl _) (by omega)))
  exact
    { W := W'
      Pr := fun n => (sP n).mono (by omega) (by omega)
      sqLeft := fun S0 => (qL F.next (by omega) hstart S0).mono (Nat.le_refl _) (by omega)
      sqEnd := fun j => (qE j).mono (by omega) (by omega)
      prLeft := fun S0 => (pL S0).mono (by omega) (by omega)
      prClaimed := pC.mono (by omega) (by omega)
      prEnd := fun j => (pE j).mono (by omega) (by omega)
      nmLeft := fun S0 => (nL S0).mono (by omega) (by omega)
      nmEnd := fun j => (nE j).mono (by omega) (by omega)
      lgLeft := fun S0 => (lL S0).mono (by omega) (by omega)
      lgEnd := fun j => (lE j).mono (by omega) (by omega) }

/-- **EVERY SLOT THAT THE 35 FORMS NAME LIES IN THE STRETCH THAT THE HEARING TOOK**, at reads whose entries name no slot. -/
theorem forms_slotsIn [FinalNorm.Reads] [Reads] {F G : Fork} {rs left : List Fmt.RoundView}
    {H : HeardAll} (hW : WellLaid F) (h : hear F rs = some (H, G, left))
    (hN : ∀ r i, (FinalNorm.entry r i).slots = #[]) (hR : ∀ r i, (entry r i).slots = #[]) :
    letI : Norm.Heard := H.1
    letI : FinalNorm.Heard := H.2.1
    letI : Heard := H.2.2
    ∀ name fs, claims.lookup name = some fs → ∀ f, f ∈ fs → SlotsIn F.next G.next f := by
  letI : Norm.Heard := H.1
  letI : FinalNorm.Heard := H.2.1
  letI : Heard := H.2.2
  refine all35 (kept_slotsIn F.next G.next) ⟨fun r i x hx => ?_, fun r i x hx => ?_⟩
    (heard_slotsIn hW h)
  · rw [hN r i] at hx
    simp at hx
  · rw [hR r i] at hx
    simp at hx

/-- **AND EACH IS FILLED**, in the ledger behind the hearing and in every later one. -/
theorem forms_filled [FinalNorm.Reads] [Reads] {F G G' : Fork} {rs left : List Fmt.RoundView}
    {H : HeardAll} (hW : WellLaid F) (h : hear F rs = some (H, G, left))
    (hN : ∀ r i, (FinalNorm.entry r i).slots = #[]) (hR : ∀ r i, (entry r i).slots = #[])
    (hL : Later G G') :
    letI : Norm.Heard := H.1
    letI : FinalNorm.Heard := H.2.1
    letI : Heard := H.2.2
    ∀ name fs, claims.lookup name = some fs → ∀ f, f ∈ fs → ∀ x, x ∈ f.slots.toList →
      OnBytes.PscRun.Filled G x.1 ∧ OnBytes.PscRun.Filled G' x.1 ∧
        G'.vp.getD x.1 zeroE = G.vp.getD x.1 zeroE ∧
        G'.mf.getD x.1 zeroE = G.mf.getD x.1 zeroE := by
  intro name fs hl f hf x hx
  have hs := forms_slotsIn hW h hN hR name fs hl f hf x hx
  have TT := hear_takes (⟨hW.2.1, hW.2.2, hW.1⟩ : Sized F) h
  have hfill : OnBytes.PscRun.Filled G x.1 := TT.full x.1 hs.1 (by rw [← TT.next]; exact hs.2)
  obtain ⟨k1, k2, k3⟩ := hL.keep x.1 hfill
  exact ⟨hfill, k1, k2, k3⟩

/-- A form's value in two worlds that agree on what it names. -/
theorem value_agree {K' : Type} [CommRing K'] (ρ : OnBytes.Model.Reading K')
    (W1 W2 : OnBytes.Model.World K') (f : Form)
    (hs : ∀ x, x ∈ f.slots.toList → W1.slot x.1 = W2.slot x.1)
    (he : ∀ x, x ∈ f.ents.toList → W1.entry x.tree x.row x.idx = W2.entry x.tree x.row x.idx) :
    f.value ρ W1 = f.value ρ W2 := by
  unfold OnBytes.Model.Aff.value
  have e1 : f.ents.toList.map (OnBytes.Model.Ent.value ρ W1)
      = f.ents.toList.map (OnBytes.Model.Ent.value ρ W2) :=
    List.map_congr_left fun x hx => by
      unfold OnBytes.Model.Ent.value
      rw [he x hx]
  have e2 : f.slots.toList.map (OnBytes.Model.slotValue ρ W1)
      = f.slots.toList.map (OnBytes.Model.slotValue ρ W2) :=
    List.map_congr_left fun x hx => by
      unfold OnBytes.Model.slotValue
      rw [hs x hx]
  rw [e1, e2]

/-- **THE 35 FORMS READ THE SAME AT EVERY LATER LEDGER**, at one mask row and one reading of the entries. -/
theorem forms_value_later [FinalNorm.Reads] [Reads] {F G G' : Fork} {rs left : List Fmt.RoundView}
    {H : HeardAll} (hW : WellLaid F) (h : hear F rs = some (H, G, left))
    (hN : ∀ r i, (FinalNorm.entry r i).slots = #[]) (hR : ∀ r i, (entry r i).slots = #[])
    (hL : Later G G') {K' : Type} [CommRing K'] (ρ : OnBytes.Model.Reading K') (mask : Nat → K')
    (ent : Nat → Nat → Nat → K') :
    letI : Norm.Heard := H.1
    letI : FinalNorm.Heard := H.2.1
    letI : Heard := H.2.2
    ∀ name fs, claims.lookup name = some fs → ∀ f, f ∈ fs →
      f.value ρ (G'.worldOf ρ mask ent) = f.value ρ (G.worldOf ρ mask ent) := by
  intro name fs hl f hf
  refine value_agree ρ _ _ f (fun x hx => ?_) fun _ _ => rfl
  obtain ⟨_, _, k2, k3⟩ := forms_filled hW h hN hR hL name fs hl f hf x hx
  show ρ.val (G'.vp.getD x.1 zeroE) - ρ.val (G'.mf.getD x.1 zeroE) * mask x.1 =
    ρ.val (G.vp.getD x.1 zeroE) - ρ.val (G.mf.getD x.1 zeroE) * mask x.1
  rw [k2, k3]

end Whole

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.heard_slotsIn
#print axioms VerifiableInference.Desc.Kinds.Head.Law.forms_slotsIn
#print axioms VerifiableInference.Desc.Kinds.Head.Law.forms_filled
#print axioms VerifiableInference.Desc.Kinds.Head.Law.forms_value_later
