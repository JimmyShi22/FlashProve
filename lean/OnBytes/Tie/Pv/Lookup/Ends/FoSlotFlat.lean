-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoSlotFlat.lean: the flat description of the lookup names no slot of the
mask row outside the lookup's own slots: the FoNums.nMasks h slots from its first slot jLK on.

OnMasks (OnBytes/Tie/Pv/Lookup/Forest/FoForm.lean) says of a sparse form that all its places are
slots of the mask row, without a bound. Here the bound is added, and the rows that name cells and
keys too are covered.

 - OnP Q cf, LedP Q L, NumsP Q N: every place of a sparse form, of a sumcheck's record of places,
   of the public numbers meets a condition Q. OnP.nil, OnP.append, OnP.one, OnP.scale, onP_hideGo,
   onP_hide, onP_rowU, onP_line, onP_top, onP_lv, onP_tieInc, onP_tie, onP_fK, onP_formT,
   onP_incT0, onP_bitsForm, onP_rowEnd, onP_rowBitE, onP_rowNum, onP_rowKey, onP_rowsOfTrace,
   LedP.imp: the functions of Cb/Pv/Lookup/Out/TwV.lean make forms on such places out of records on
   such places, for every Q.
 - InSlots jLK n p: p is Pl.mask j with jLK ≤ j < jLK + n. OnMasksIn jLK n cf: every place of cf is
   so. onMasksIn_iff, OnMasksIn.onMasks. ledP_ledF.
 - numsF_leds: the five records of places of Fo.numsF h lm jLK θ
   (OnBytes/Tie/Pv/Lookup/Forest/FoV.lean) lie in InSlots jLK (FoNums.nMasks h), by the bounds of
   OnBytes/Tie/Pv/Lookup/Ends/FoSlotNums.lean.
 - onMasksIn_rows, onMasksIn_keyTop, onMasksIn_lvInc: so do every row of (endsOf h lm jLK
   rsK).rows, its cEndInc and its lvInc.
 - MaskIn jLK n p: if p is Pl.mask j then jLK ≤ j < jLK + n. maskIn_of_inSlots, numsF_maskIn.
 - forV_slots: in every row of Fo.forV h lm jLK rsK, the rows that also name cells and keys among
   them, each slot of the mask row that is named lies in jLK ≤ j < jLK + FoNums.nMasks h.
 - onMasksIn_elems, forV_slots_elems: the same at Forest.elems h (FoLedger.elems_eq).
No hypothesis on h, lm, jLK or the rounds.

Limits. Places alone: which slot is which, and with which coefficient, is not said. Of cells and
keys nothing is bounded. That a run's forms are these rows is other files' matter.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoSlotNums
import OnBytes.Tie.Pv.Lookup.Forest.FoClaimsMeet

set_option autoImplicit false

namespace Fo.Slots
open TwV _root_.Fo

/-! ### forms all of whose places meet a condition -/

section
variable {P K : Type} (Q : P → Prop)

/-- Every place that the sparse form names meets Q. -/
def OnP (cf : List (P × K)) : Prop := ∀ pc ∈ cf, Q pc.1

/-- Every place of the sumcheck's record meets Q. -/
def LedP (L : Led P) : Prop := (∀ r t, Q (L.pw r t)) ∧ Q L.c0 ∧ ∀ a, Q (L.sh a)

variable {Q}

theorem OnP.nil : OnP Q ([] : List (P × K)) := fun _ h => absurd h List.not_mem_nil

theorem OnP.append {a b : List (P × K)} (ha : OnP Q a) (hb : OnP Q b) : OnP Q (a ++ b) :=
  fun pc h => (List.mem_append.mp h).elim (ha pc) (hb pc)

theorem OnP.one {p : P} (hp : Q p) (x : K) : OnP Q [(p, x)] := fun pc h => by
  rw [List.mem_singleton.mp h]
  exact hp

variable [CommRing K]

theorem OnP.scale {a : List (P × K)} (u : K) (ha : OnP Q a) : OnP Q (scale u a) := by
  intro pc h
  unfold TwV.scale at h
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
  exact ha q hq

theorem onP_hideGo (pw : ℕ → ℕ → P) (hp : ∀ r t, Q (pw r t)) :
    ∀ (dg : List ℕ) (xs : List K) (r : ℕ), OnP Q (hideGo pw r dg xs)
  | [], _, _ => by
    intro pc h
    simp [hideGo] at h
  | _ :: _, [], _ => by
    intro pc h
    simp [hideGo] at h
  | n :: dg, x :: xs, r => by
    show OnP Q (((List.range n).map fun t => (pw r t, x ^ (t + 1))) ++ hideGo pw (r + 1) dg xs)
    refine OnP.append (fun pc h => ?_) (onP_hideGo pw hp dg xs (r + 1))
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp h
    exact hp r t

theorem onP_hide {L : Led P} (hL : LedP Q L) (dg : List ℕ) (xs : List K) :
    OnP Q (hide L dg xs) :=
  OnP.append (onP_hideGo _ hL.1 dg xs 0) (OnP.one hL.2.1 1)

theorem onP_rowU {L : Led P} (hL : LedP Q L) (dg : List ℕ) (s : Sc K) {inc : List (P × K)}
    (hi : OnP Q inc) (S0 : K) : OnP Q (rowU L dg s inc S0).cf :=
  OnP.append (onP_hide hL dg s.xs) (OnP.scale _ hi)

theorem onP_line {L : Led P} (hL : LedP Q L) (s : Sc K) (rho : K) : OnP Q (lineForm L s rho) :=
  OnP.append (a := [(L.sh 0, s.be * (1 - rho))]) (OnP.one (hL.2.2 0) _) (OnP.one (hL.2.2 1) _)

theorem onP_top {led : ℕ → Led P} (hl : ∀ l, LedP Q (led l)) {inc0 : List (P × K)}
    (h0 : OnP Q inc0) : ∀ l : List (Sc K × K), OnP Q (incTop led inc0 l)
  | [] => h0
  | s :: rest => onP_line (hl rest.length) s.1 s.2

theorem onP_lv {led : ℕ → Led P} (hl : ∀ l, LedP Q (led l)) (g : ℕ) {inc0 : List (P × K)}
    (h0 : OnP Q inc0) : ∀ l : List (Sc K × K), ∀ r ∈ lvRowsR led g inc0 l, OnP Q r.cf
  | [], _, h => absurd h List.not_mem_nil
  | s :: rest, r, h => by
    rcases List.mem_cons.mp h with rfl | h'
    · exact onP_rowU (hl _) _ _ (onP_top hl h0 rest) _
    · exact onP_lv hl g h0 rest r h'

theorem onP_tieInc {N : Nums P K} (hl : ∀ l, LedP Q (N.ledTie l)) :
    ∀ l : List (Sc K), OnP Q (tieInc N l)
  | [] => OnP.nil
  | s :: rest => OnP.one ((hl rest.length).2.2 _) s.be

theorem onP_tie {N : Nums P K} (hl : ∀ l, LedP Q (N.ledTie l)) (lam : K) :
    ∀ l : List (Sc K), ∀ r ∈ tieRowsR N lam l, OnP Q r.cf
  | [], _, h => absurd h List.not_mem_nil
  | s :: rest, r, h => by
    rcases List.mem_cons.mp h with rfl | h'
    · exact onP_rowU (hl _) _ _ (onP_tieInc hl rest) _
    · exact onP_tie hl lam rest r h'

theorem onP_fK {N : Nums P K} (hl : ∀ l, LedP Q (N.ledTie l)) (t : Trace K) : OnP Q (fK N t) :=
  OnP.one ((hl 0).2.2 0) _

theorem onP_formT {N : Nums P K} (hl : ∀ l, LedP Q (N.ledTie l)) (t : Trace K) (th : ℕ) :
    OnP Q (formT N t th) := by
  unfold formT
  split_ifs
  · exact OnP.one ((hl th).2.2 _) _
  · exact OnP.one ((hl N.n).2.2 _) _
  · exact OnP.nil

theorem onP_incT0 {N : Nums P K} (hl : ∀ l, LedP Q (N.ledTie l)) (t : Trace K) :
    OnP Q (incT0 N t) := by
  intro pc hpc
  unfold incT0 at hpc
  obtain ⟨th, _, h2⟩ := List.mem_flatMap.mp hpc
  exact OnP.scale _ (onP_formT hl t th) pc h2

theorem onP_bitsForm {N : Nums P K} (hb : ∀ u j, Q (N.bAt u j)) (pt : List K) :
    OnP Q (bitsForm N pt) := by
  intro pc h
  unfold bitsForm at h
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp h
  exact hb _ _

/-- All places of the public numbers meet Q. -/
structure NumsP (Q : P → Prop) (N : Nums P K) : Prop where
  tie : ∀ l, LedP Q (N.ledTie l)
  key : ∀ l, LedP Q (N.ledK l)
  tab : ∀ l, LedP Q (N.ledT l)
  cls : LedP Q N.ledE
  bit : LedP Q N.ledB
  bAt : ∀ u j, Q (N.bAt u j)
  kAt : ∀ b p, N.kAt b = some p → Q p

theorem onP_rowEnd {N : Nums P K} (hN : NumsP Q N) (t : Trace K) : OnP Q (rowEnd N t).cf :=
  OnP.append
    (OnP.append (onP_hide hN.cls _ _) (OnP.scale _ (onP_top hN.tab (onP_incT0 hN.tie t) _)))
    (OnP.scale _ (onP_bitsForm hN.bAt _))

theorem onP_rowBitE {N : Nums P K} (hN : NumsP Q N) (t : Trace K) : OnP Q (rowBitE N t).cf :=
  OnP.append (onP_bitsForm hN.bAt _) (OnP.one (hN.bit.2.2 0) _)

theorem onP_rowNum {N : Nums P K} (hN : NumsP Q N) : OnP Q (rowNum N).cf := by
  intro pc h
  obtain ⟨u, _, h2⟩ := List.mem_flatMap.mp h
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp h2
  exact hN.bAt u j

theorem onP_rowKey {N : Nums P K} (hN : NumsP Q N) (t : Trace K) : OnP Q (rowKey N t).cf := by
  refine OnP.append (fun pc h => ?_) (OnP.scale _ (onP_top hN.key (onP_fK hN.tie t) _))
  obtain ⟨b, _, h2⟩ := List.mem_flatMap.mp h
  cases hk : N.kAt b with
  | none =>
    rw [hk] at h2
    exact absurd h2 List.not_mem_nil
  | some p =>
    rw [hk] at h2
    rw [List.mem_singleton.mp h2]
    exact hN.kAt b p hk

/-- Every row of the flat description's function. -/
theorem onP_rowsOfTrace {N : Nums P K} (hN : NumsP Q N) (t : Trace K) :
    ∀ r ∈ rowsOfTrace N t, OnP Q r.cf := by
  intro r hr
  unfold rowsOfTrace at hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (hr | hr | (hr | rfl | rfl | rfl) | rfl) | rfl
  · exact onP_tie hN.tie _ _ r hr
  · exact onP_lv hN.key _ (onP_fK hN.tie t) _ r hr
  · exact onP_lv hN.tab _ (onP_incT0 hN.tie t) _ r hr
  · exact onP_rowEnd hN t
  · exact onP_rowU hN.bit _ _ OnP.nil _
  · exact onP_rowBitE hN t
  · exact onP_rowNum hN
  · exact onP_rowKey hN t

theorem LedP.imp {Q' : P → Prop} (hq : ∀ p, Q p → Q' p) {L : Led P} (h : LedP Q L) : LedP Q' L :=
  ⟨fun r t => hq _ (h.1 r t), hq _ h.2.1, fun a => hq _ (h.2.2 a)⟩

end

/-! ### the lookup's slots -/

/-- The place is a slot of the mask row among the n slots from jLK on. -/
def InSlots (jLK n : ℕ) (p : Pl) : Prop := ∃ j, p = Pl.mask j ∧ jLK ≤ j ∧ j < jLK + n

/-- The sparse form names slots of the mask row among the n slots from jLK on, and nothing else. -/
def OnMasksIn {K : Type} (jLK n : ℕ) (cf : List (Pl × K)) : Prop :=
  ∀ pc ∈ cf, ∃ j, pc.1 = Pl.mask j ∧ jLK ≤ j ∧ j < jLK + n

theorem onMasksIn_iff {K : Type} (jLK n : ℕ) (cf : List (Pl × K)) :
    OnMasksIn jLK n cf ↔ OnP (InSlots jLK n) cf := Iff.rfl

theorem OnMasksIn.onMasks {K : Type} {jLK n : ℕ} {cf : List (Pl × K)}
    (h : OnMasksIn jLK n cf) : OnMasks cf := fun pc hpc => by
  obtain ⟨j, e, _⟩ := h pc hpc
  exact ⟨j, e⟩

theorem ledP_ledF (jLK : ℕ) {n : ℕ} {pl : TwNums.Sizes.Ent → ℕ} (hpl : ∀ e, pl e < n) :
    LedP (InSlots jLK n) (ledF jLK pl) :=
  ⟨fun _ _ => ⟨_, rfl, Nat.le_add_right _ _, Nat.add_lt_add_left (hpl _) _⟩,
    ⟨_, rfl, Nat.le_add_right _ _, Nat.add_lt_add_left (hpl _) _⟩,
    fun _ => ⟨_, rfl, Nat.le_add_right _ _, Nat.add_lt_add_left (hpl _) _⟩⟩

section
variable {K : Type} [CommRing K] (h : FoNums.Sh) (lm jLK : ℕ)

/-- **All five records of places of the flat description lie among the lookup's own slots.** -/
theorem numsF_leds (θ : K) :
    (∀ l, LedP (InSlots jLK (FoNums.nMasks h)) ((numsF h lm jLK θ).ledTie l)) ∧
    (∀ l, LedP (InSlots jLK (FoNums.nMasks h)) ((numsF h lm jLK θ).ledK l)) ∧
    (∀ l, LedP (InSlots jLK (FoNums.nMasks h)) ((numsF h lm jLK θ).ledT l)) ∧
    LedP (InSlots jLK (FoNums.nMasks h)) (numsF h lm jLK θ).ledE ∧
    LedP (InSlots jLK (FoNums.nMasks h)) (numsF h lm jLK θ).ledB :=
  ⟨fun l => ledP_ledF jLK (pTieC_lt _ l), fun l => ledP_ledF jLK (pKeyC_lt _ l),
    fun l => ledP_ledF jLK (pTabC_lt _ l),
    ⟨(ledP_ledF jLK (pEndC_lt (FoNums.S h))).1, (ledP_ledF jLK (pEndC_lt (FoNums.S h))).2.1,
      fun _ => ⟨_, rfl, Nat.le_add_right _ _,
        Nat.add_lt_add_left (pBit_lt (FoNums.S h) (e := .shown 0) (show (0 : ℕ) < 1 by omega)) _⟩⟩,
    ledP_ledF jLK (pBitC_lt _)⟩

variable (rsK : Rounds K)

/-- **Every row of the record of end values names the lookup's own slots alone.** -/
theorem onMasksIn_rows :
    ∀ r ∈ (endsOf h lm jLK rsK).rows, OnMasksIn jLK (FoNums.nMasks h) r.cf := by
  obtain ⟨hT, hK, hTb, _, hB⟩ := numsF_leds (K := K) h lm jLK (thetaOf h rsK)
  intro r hr
  unfold Ends.rows at hr
  simp only [List.mem_append, List.mem_singleton] at hr
  rcases hr with ((hr | hr) | hr) | hr
  · have hr' : r ∈ (tieRowsR (forN h lm jLK rsK) (forTrace h lm jLK rsK).lam
        (forTrace h lm jLK rsK).tie.reverse).reverse := hr
    exact onP_tie hT _ _ r (List.mem_reverse.mp hr')
  · have hr' : r ∈ (lvRowsR (forN h lm jLK rsK).ledK 0
        (fK (forN h lm jLK rsK) (forTrace h lm jLK rsK))
        (forTrace h lm jLK rsK).keys.reverse).reverse := hr
    exact onP_lv hK _ (onP_fK hT _) _ r (List.mem_reverse.mp hr')
  · have hr' : r ∈ (lvRowsR (forN h lm jLK rsK).ledT (forN h lm jLK rsK).w
        (incT0 (forN h lm jLK rsK) (forTrace h lm jLK rsK))
        (forTrace h lm jLK rsK).tabl.reverse).reverse := hr
    exact onP_lv hTb _ (onP_incT0 hT _) _ r (List.mem_reverse.mp hr')
  · have hr' : r = rowBitU (forN h lm jLK rsK) (forTrace h lm jLK rsK) := hr
    rw [hr']
    exact onP_rowU hB _ _ OnP.nil _

/-- The form at the end of the key side. -/
theorem onMasksIn_keyTop : OnMasksIn jLK (FoNums.nMasks h) (endsOf h lm jLK rsK).cEndInc := by
  obtain ⟨hT, hK, _⟩ := numsF_leds (K := K) h lm jLK (thetaOf h rsK)
  exact onP_top hK (onP_fK hT _) _

/-- The form that comes into the leaves' sumcheck. -/
theorem onMasksIn_lvInc : OnMasksIn jLK (FoNums.nMasks h) (endsOf h lm jLK rsK).lvInc := by
  obtain ⟨hT, _, hTb, _⟩ := numsF_leds (K := K) h lm jLK (thetaOf h rsK)
  exact onP_top hTb (onP_incT0 hT _) _

/-- If the place is a slot of the mask row, it is among the n slots from jLK on. -/
def MaskIn (jLK n : ℕ) (p : Pl) : Prop := ∀ j, p = Pl.mask j → jLK ≤ j ∧ j < jLK + n

theorem maskIn_of_inSlots {jLK n : ℕ} (p : Pl) (hp : InSlots jLK n p) : MaskIn jLK n p := by
  obtain ⟨j, rfl, h1, h2⟩ := hp
  intro j' e
  obtain rfl : j = j' := Pl.mask.inj e
  exact ⟨h1, h2⟩

theorem numsF_maskIn (θ : K) : NumsP (MaskIn jLK (FoNums.nMasks h)) (numsF h lm jLK θ) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := numsF_leds (K := K) h lm jLK θ
  refine ⟨fun l => (h1 l).imp maskIn_of_inSlots, fun l => (h2 l).imp maskIn_of_inSlots,
    fun l => (h3 l).imp maskIn_of_inSlots, h4.imp maskIn_of_inSlots, h5.imp maskIn_of_inSlots,
    fun u j j' e => ?_, fun b p hb j' e => ?_⟩
  · have e' : (match FoNums.cellOf h u j with
      | some x => Pl.cell (FoNums.cellRC h lm x).1 (FoNums.cellRC h lm x).2
      | none => Pl.zero) = Pl.mask j' := e
    split at e' <;> cases e'
  · have hb' : (FoNums.keyOf h b).map (fun q => Pl.key q.1 q.2) = some p := hb
    obtain ⟨q, _, rfl⟩ := Option.map_eq_some_iff.mp hb'
    cases e

/-- **Every row that the flat description's verifier hands on: each slot of the mask row that it
names is one of the lookup's own.** -/
theorem forV_slots : ∀ r ∈ forV h lm jLK rsK, ∀ pc ∈ r.cf, ∀ j, pc.1 = Pl.mask j →
    jLK ≤ j ∧ j < jLK + FoNums.nMasks h := by
  have hN := numsF_maskIn (K := K) h lm jLK (thetaOf h rsK)
  intro r hr
  unfold forV at hr
  rcases List.mem_append.mp hr with hr | hr
  · exact onP_rowsOfTrace hN (forTrace h lm jLK rsK) r
      (by rw [rows_split]; exact List.mem_append_left _ hr)
  · rw [List.mem_singleton.mp hr]
    exact onP_rowKey hN (forTrace h lm jLK rsK)

/-- The same three at the verifier's own count of the scalars that the lookup sends. -/
theorem onMasksIn_elems :
    (∀ r ∈ (endsOf h lm jLK rsK).rows, OnMasksIn jLK (OnBytes.Model.Forest.elems h) r.cf) ∧
    OnMasksIn jLK (OnBytes.Model.Forest.elems h) (endsOf h lm jLK rsK).cEndInc ∧
    OnMasksIn jLK (OnBytes.Model.Forest.elems h) (endsOf h lm jLK rsK).lvInc := by
  rw [← FoLedger.elems_eq]
  exact ⟨onMasksIn_rows h lm jLK rsK, onMasksIn_keyTop h lm jLK rsK, onMasksIn_lvInc h lm jLK rsK⟩

theorem forV_slots_elems : ∀ r ∈ forV h lm jLK rsK, ∀ pc ∈ r.cf, ∀ j, pc.1 = Pl.mask j →
    jLK ≤ j ∧ j < jLK + OnBytes.Model.Forest.elems h := by
  rw [← FoLedger.elems_eq]
  exact forV_slots h lm jLK rsK

end

end Fo.Slots
