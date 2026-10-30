-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/SlotsCoveredKeys.lean: kind K5: THE SLOTS' TWIN OF
Claims/CoveredKeys.lean: the key forms that the run "first" hands on, and so those that "keys"
returns, name slots that meet a given predicate Ps alone, under the two records of premises of
Claims/SlotsIn.lean; and THE ONE FORM OF THE LOOKUP'S "join" at these key forms names such slots alone
IF the form g.cEnd that the lookup's hearing left does.

IS IT EMPTY HERE?
  · As in Claims/SlotsCovered.lean: at Ps := fun _ => True nothing is said; at Ps := fun _ => False
    PtsSlots cannot be met; the laws say as much as Ps is narrow; where a run refuses, nothing is said.
  · A shape without calls has no key form (by reading JoinsP.empty and JoinsP.set, Att/RunsP.lean):
    SlotsJ then holds of a record without forms.
  · The premise on g.cEnd is needed: slotsIn_joinW_cEnd: if join's form names such slots alone, so does
    g.cEnd. It is NOT shown here of any g.
  · At one toy record with one call a key form (keyWH; no other kind of key form stands there) names
    two slots and the conclusion fails at a predicate that leaves one out:
    Claims/SlotsCoveredToy2.lean [not in this library]. No lawful shape, no real size.

Main names:
  slotsIn_keyKR … slotsIn_keyWH: form by form. SlotsJ Ps j: every key form of the record meets
    SlotsIn Ps. slotsJ_empty, slotsJ_set, slotsJ_joinR16; svk_callKR, svk_claim3, svk_callKFD,
    svk_claim4, svk_claim5.
  keys_slots_K05, keysRun_slots: the key forms.
  slotsIn_joinW, join_slots_K05: join's form (joinW, joinF_is: Claims/PortJoin.lean).
  filledA_iff: Fo.FilledA G a (OnBytes/Tie/Pv/Lookup/Forest/FoEv.lean) is SlotsIn at
    "below the number of slots and filled in G", by its text. join_filled_K05: join_slots_K05 there.
Spent of PtsSlots beyond what Claims/SlotsCovered.lean spends: planes' first clause (3 ≤ np), all seven
  scalars of a softmax unit, the second of the five (s5 + 1).
Limits. NEITHER RECORD OF PREMISES IS SHOWN OF ANYTHING HERE. THAT g.cEnd NAMES FILLED SLOTS IS A
  PREMISE. The lookup's run "planes" is the lookup's own: nothing is said of it. Nothing on entries
  (keys_covered_K05). That a run or joinF returns is not shown.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.SlotsCovered
import Johnson.Desc.First.Att.Claims.PortJoin
import OnBytes.Tie.Pv.Lookup.Forest.FoEv

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model OnBytes.K.Kc OnBytes.PscRun
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P.Runs (W JoinsP)

variable {K : ℕ} {Ps : ℕ → Prop} {i : P.Runs.In}

local notation "SS" => SlotsIn Ps

local macro "slts" : tactic => `(tactic| repeat (first
  | with_reducible assumption | with_reducible exact slotsIn_ofConst _
  | with_reducible refine slotsIn_add ?_ ?_ | with_reducible refine slotsIn_sub ?_ ?_
  | with_reducible refine slotsIn_scale _ ?_ | with_reducible refine slotsIn_addMul _ ?_ ?_))

/-! ### the key forms, one by one -/

theorem slotsIn_keyKR (pc : P.RemP) (h3 : 3 ≤ pc.np) (h : ∀ x, x < pc.np → Ps (pc.s0 + x)) :
    SS (P.Runs.keyKR pc) := by
  have a0 : SS (Aff.slot pc.s0) := slotsIn_at (s := pc.s0) (x := 0) h (by omega)
  have a1 : SS (Aff.slot (pc.s0 + 1)) := slotsIn_at h (by omega)
  have a2 : SS (Aff.slot (pc.s0 + 2)) := slotsIn_at h (by omega)
  unfold P.Runs.keyKR; dsimp only; slts

theorem slotsIn_padTerm (c : P.CallG) (zk : Array E) : SS (P.Runs.padTerm c zk) := by
  unfold P.Runs.padTerm; slts

theorem slotsIn_keyKFD (gC gOm : ℕ) (k : P.ScoreP) (h : ∀ x, x < 7 → Ps (k.s0 + x)) :
    SS (P.Runs.keyKFD gC gOm k) := by
  have a0 : SS (Aff.slot k.s0) := slotsIn_at (s := k.s0) (x := 0) h (by omega)
  have a1 : SS (Aff.slot (k.s0 + 1)) := slotsIn_at h (by omega)
  have a2 : SS (Aff.slot (k.s0 + 2)) := slotsIn_at h (by omega)
  have a3 : SS (Aff.slot (k.s0 + 3)) := slotsIn_at h (by omega)
  have a4 : SS (Aff.slot (k.s0 + 4)) := slotsIn_at h (by omega)
  have a5 : SS (Aff.slot (k.s0 + 5)) := slotsIn_at h (by omega)
  have a6 : SS (Aff.slot (k.s0 + 6)) := slotsIn_at h (by omega)
  unfold P.Runs.keyKFD; dsimp only; slts

theorem slotsIn_sZO (hP : PtsSlots Ps i.g i.p) : SS (Aff.slot i.p.d.sZO) :=
  slotsIn_at (x := 1) hP.five (by omega)

theorem slotsIn_remForm (hP : PtsSlots Ps i.g i.p) : SS (P.Runs.remForm i.p.d) := by
  have a0 := slotsIn_sACC hP
  have a1 := slotsIn_sZO hP
  have a2 := slotsIn_sZC hP
  unfold P.Runs.remForm; slts

theorem slotsIn_indexForm (hP : PtsSlots Ps i.g i.p) : SS (P.Runs.indexForm i.p.d i.g.lt) := by
  unfold P.Runs.indexForm
  have key : ∀ (l : List ℕ) (s : Aff), (∀ k ∈ l, k < i.g.lt) → SS s → SS
      (l.foldl (fun s k => Aff.addMul s (Aff.slot (i.p.d.sIB + k)) (P.ofNat (2 ^ k))) s) := by
    intro l
    induction l with
    | nil => intro s _ hs; exact hs
    | cons k l ih =>
      intro s hl hs
      exact ih _ (fun k' hk' => hl k' (List.mem_cons_of_mem _ hk'))
        (slotsIn_addMul _ hs (slotsIn_at hP.bits (hl k List.mem_cons_self)))
  exact key _ _ (fun k hk => List.mem_range.1 hk) (slotsIn_ofConst _)

theorem slotsIn_keyWL (hP : PtsSlots Ps i.g i.p) : SS (P.Runs.keyWL i.p.d) := by
  have a0 := slotsIn_remForm hP
  have a2 := slotsIn_sZC hP
  have a3 := slotsIn_sRH hP
  have a4 := slotsIn_sRHP hP
  unfold P.Runs.keyWL; dsimp only; slts

theorem slotsIn_keyIX (hP : PtsSlots Ps i.g i.p) : SS (P.Runs.keyIX i.g i.p.d) := by
  have := slotsIn_indexForm hP
  unfold P.Runs.keyIX; slts

theorem slotsIn_keyWH (hP : PtsSlots Ps i.g i.p) : SS (P.Runs.keyWH i.p.d) := by
  have a0 : SS (Aff.slot i.p.d.s5h) := slotsIn_at (s := i.p.d.s5h) (x := 0) hP.two (by omega)
  have a1 : SS (Aff.slot (i.p.d.s5h + 1)) := slotsIn_at hP.two (by omega)
  unfold P.Runs.keyWH; dsimp only; slts

/-! ### the record of key forms -/

/-- Every key form of the record names such slots alone. -/
def SlotsJ (Ps : ℕ → Prop) (j : JoinsP) : Prop := ∀ f ∈ j.kf.toList, SlotsIn Ps f

local notation "SJ" => SlotsJ Ps

theorem slotsJ_empty (n : ℕ) : SJ (JoinsP.empty n) := by
  intro f hf
  unfold JoinsP.empty at hf
  simp only [Array.toList_replicate, List.mem_replicate] at hf
  rw [hf.2]
  exact slotsIn_ofConst _

theorem slotsJ_set {j : JoinsP} (hj : SJ j) (q : ℕ) {v : Aff} (hv : SS v) : SJ (j.set q v) := by
  intro f hf
  unfold JoinsP.set at hf
  simp only [Array.toList_setIfInBounds] at hf
  rcases List.mem_or_eq_of_mem_set hf with h | rfl
  · exact hj f h
  · exact hv

theorem slotsJ_joinR16 (hP : PtsSlots Ps i.g i.p) {j : JoinsP} (hj : SJ j) :
    SJ (P.Runs.joinR16 i.g i.p.d j) := by
  unfold P.Runs.joinR16
  dsimp only
  have key : ∀ (l : List (P.CallG × ℕ)) (j : JoinsP), SJ j → SJ
      (l.foldl (fun j x => if x.1.tab == .r16 then
        j.set x.2 (if x.1.holds .ix then (if x.1.holds .wl then Aff.ofConst zeroE + P.Runs.keyWL i.p.d
          else Aff.ofConst zeroE) + P.Runs.keyIX i.g i.p.d
          else (if x.1.holds .wl then Aff.ofConst zeroE + P.Runs.keyWL i.p.d else Aff.ofConst zeroE))
        else j) j) := by
    intro l
    induction l with
    | nil => intro j hj; exact hj
    | cons x l ih =>
      intro j hj
      refine ih _ ?_
      dsimp only
      split
      · refine slotsJ_set hj _ ?_
        have a : SS (if x.1.holds .wl then Aff.ofConst zeroE + P.Runs.keyWL i.p.d
            else Aff.ofConst zeroE) := by
          split
          · exact slotsIn_add (slotsIn_ofConst _) (slotsIn_keyWL hP)
          · exact slotsIn_ofConst _
        split
        · exact slotsIn_add a (slotsIn_keyIX hP)
        · exact a
      · exact hj
  exact key _ j hj

/-! ### through the claims -/

theorem svk_callKR (hP : PtsSlots Ps i.g i.p) (q : ℕ) : CV K SS SS (P.Runs.callKR i q) := by
  unfold P.Runs.callKR
  rw [← Array.foldlM_toList]
  exact CV.foldlM_mem _ _ (fun v pc hpc hv => CV.ite
    (CV.bind (sv_linPlanes pc (hP.planes pc hpc).2) fun _ _ =>
      CV.pure (slotsIn_add hv (slotsIn_keyKR pc (hP.planes pc hpc).1 (hP.planes pc hpc).2)))
    (CV.pure hv)) (slotsIn_ofConst _)

theorem svk_claim3 (hP : PtsSlots Ps i.g i.p) {j : JoinsP} (hj : SJ j) :
    CV K SS SJ (P.Runs.claim3 i j) := by
  unfold P.Runs.claim3
  exact CV.foldlM (fun j x hj => CV.ite (CV.bind (svk_callKR hP x.2) fun v hv =>
    CV.pure (slotsJ_set hj _ hv)) (CV.pure hj)) _ _ hj

theorem svk_callKFD (hP : PtsSlots Ps i.g i.p) (hR : RowsSlots Ps i.p) (q : ℕ) (c : P.CallG) :
    CV K SS SS (P.Runs.callKFD i q c) := by
  unfold P.Runs.callKFD
  refine CV.foldlM_mem _ _ (fun v x hx hv => ?_) (slotsIn_padTerm _ _)
  have hm : x.1 ∈ i.p.scores.toList := (List.mem_zipIdx hx).2.2 ▸ List.getElem_mem _
  exact CV.ite (CV.bind (sv_unitKFD hP x.2 x.1 hm (hR.units x.1 hm)) fun _ _ =>
    CV.pure (slotsIn_add hv (slotsIn_keyKFD _ _ _ (hP.scores x.1 hm).1))) (CV.pure hv)

theorem svk_claim4 (hP : PtsSlots Ps i.g i.p) (hR : RowsSlots Ps i.p) {j : JoinsP} (hj : SJ j) :
    CV K SS SJ (P.Runs.claim4 i j) := by
  unfold P.Runs.claim4
  exact CV.foldlM (fun j x hj => CV.ite (CV.bind (svk_callKFD hP hR x.2 x.1) fun v hv =>
    CV.pure (slotsJ_set hj _ hv)) (CV.pure hj)) _ _ hj

theorem svk_claim5 (hP : PtsSlots Ps i.g i.p) (hR : RowsSlots Ps i.p) {j : JoinsP} (hj : SJ j) :
    CV K SS SJ (P.Runs.claim5 i j) := by
  unfold P.Runs.claim5
  dsimp only
  refine CV.bind (sv_lessPieces (slotsIn_sZC hP) _ _ fun w => sv_readDenominator _ _ _ _) fun zc hzc => ?_
  refine CV.bind (sv_lessPieces (slotsIn_sRH hP) _ _ fun w => sv_readHead _ _ _ _ _ _) fun rh hrh => ?_
  refine CV.bind (sv_lessPieces (slotsIn_sRHP hP) _ _ fun w => sv_readHead _ _ _ _ _ _) fun rhp hrhp => ?_
  refine CV.bind (sv_lessPieces (slotsIn_at (x := 0) hP.two (by omega)) _ _
    fun w => sv_readHead _ _ _ _ _ _) fun r2 hr2 => ?_
  refine CV.bind (sv_lessPieces (slotsIn_at (x := 1) hP.two (by omega)) _ _
    fun w => sv_readHead _ _ _ _ _ _) fun r2p hr2p => ?_
  refine CV.bind (CV.lin hzc) fun _ _ => CV.bind (CV.lin hrh) fun _ _ => CV.bind (CV.lin hrhp) fun _ _ => ?_
  refine CV.bind (CV.forIn_mem _ fun k hk => ?_) fun _ _ => ?_
  · exact CV.bind (sv_lessPieces (slotsIn_at hP.bits (List.mem_range.1 hk)) _ _
      fun w => sv_readIndexBit _ _ _ _ _) fun f hf => CV.bind (CV.lin hf) fun _ _ => CV.pure trivial
  refine CV.bind (CV.lin hr2) fun _ _ => CV.bind (CV.lin hr2p) fun _ _ =>
    CV.bind (CV.lin (f := P.Runs.leftOf i.p.d.scE.row) hR.scE) fun _ _ => ?_
  refine CV.bind (CV.forIn_mem _ fun b hb => ?_) fun _ _ =>
    CV.pure (slotsJ_set (slotsJ_joinR16 hP hj) _ (slotsIn_keyWH hP))
  exact CV.bind (sv_endValuesE hP b (List.mem_range.1 hb) _) fun _ _ => CV.pure trivial

/-- **The key forms that "first" hands on name slots that meet Ps alone.** -/
theorem keys_slots_K05 {l₁ : List Aff} {j : JoinsP} (hP : PtsSlots Ps i.g i.p) (hR : RowsSlots Ps i.p)
    (h1 : P.Runs.firstRun i K = some (l₁, j)) : SlotsJ Ps j := by
  unfold P.Runs.firstRun P.Runs.gather at h1
  simp only [Option.map_eq_some_iff] at h1
  obtain ⟨_, ⟨y1, hy1, rfl⟩, e1⟩ := h1
  have c1 := (CV.bind (C := SlotsIn Ps) (svk_claim3 hP (slotsJ_empty _)) fun j3 h3 =>
    CV.bind (svk_claim4 hP hR h3) fun j4 h4 => svk_claim5 hP hR h4) #[] y1 hy1 (by simp)
  rw [← (Prod.mk.inj e1).2]
  exact c1.1

/-- **So do those that "keys" returns.** -/
theorem keysRun_slots {l₁ : List Aff} {j : JoinsP} {k3 : P.Runs.PadIn} {kf : Array Aff}
    (hP : PtsSlots Ps i.g i.p) (hR : RowsSlots Ps i.p) (h1 : P.Runs.firstRun i K = some (l₁, j))
    (hk : P.Runs.keysRun i k3 j = some kf) : ∀ f ∈ kf.toList, SlotsIn Ps f := by
  rw [keys_is _ _ _ _ hk]
  exact keys_slots_K05 hP hR h1

/-! ### the lookup's join at these key forms -/

theorem slotsIn_getD {KF : Array Aff} (hK : ∀ f ∈ KF.toList, SS f) (c : ℕ) :
    SS (KF.getD c (Aff.ofConst zeroE)) := by
  rw [Array.getD_eq_getD_getElem?]
  cases h : KF[c]? with
  | none => exact slotsIn_ofConst _
  | some f => exact hK f (Array.mem_toList_iff.2 (Array.mem_of_getElem? h))

/-- **Join's written form names the key forms' slots and g.cEnd's, and no other.** -/
theorem slotsIn_joinW {g : Forest.Heard} {KF : Array Aff} (hK : ∀ f ∈ KF.toList, SS f)
    (hc : SS g.cEnd) : SS (joinW g KF) := by
  unfold joinW
  refine slotsIn_sub (slotsIn_add ?_ (slotsIn_ofConst _)) hc
  have key : ∀ (l : List ℕ) (s : Aff), SS s → SS
      (l.foldl (fun (f : Aff) c => Aff.addMul f (Aff.ofConst (subE g.alpha (scaleE c.toUInt64 g.theta)) -
        KF.getD c (Aff.ofConst zeroE)) (g.e.getD c zeroE)) s) := by
    intro l
    induction l with
    | nil => intro s hs; exact hs
    | cons c l ih =>
      intro s hs
      exact ih _ (slotsIn_addMul _ hs (slotsIn_sub (slotsIn_ofConst _) (slotsIn_getD hK c)))
  exact key _ _ (slotsIn_ofConst _)

theorem mem_foldl_push_left {γ : Type} (g : γ → γ) (b : List γ) : ∀ (a : Array γ) (e : γ),
    e ∈ a.toList → e ∈ (b.foldl (fun l x => l.push (g x)) a).toList := by
  induction b with
  | nil => intro a e h; exact h
  | cons y b ih =>
    intro a e h
    refine ih (a.push (g y)) e ?_
    rw [Array.toList_push]
    exact List.mem_append_left _ h

theorem mem_foldl_push_right {γ : Type} (g : γ → γ) (b : List γ) : ∀ (a : Array γ) (x : γ),
    x ∈ b → g x ∈ (b.foldl (fun l x => l.push (g x)) a).toList := by
  induction b with
  | nil => intro a x h; cases h
  | cons y b ih =>
    intro a x h
    rcases List.mem_cons.1 h with rfl | h
    · refine mem_foldl_push_left g b _ _ ?_
      rw [Array.toList_push]
      exact List.mem_append_right _ List.mem_cons_self
    · exact ih _ x h

/-- What a + k b names, b names. -/
theorem slotsIn_of_addMul {a b : Aff} {k : E} (h : SS (Aff.addMul a b k)) : SS b := by
  intro x hx
  have hm := mem_foldl_push_right (fun x : ℕ × E => (x.1, mulE x.2 k)) b.slots.toList a.slots x hx
  rw [Array.foldl_toList] at hm
  have hm' : (x.1, mulE x.2 k) ∈ (Aff.addMul a b k).slots.toList := by
    unfold Aff.addMul
    exact hm
  exact h (x.1, mulE x.2 k) hm'

theorem slotsIn_of_sub {a b : Aff} (h : SS (a - b)) : SS b :=
  slotsIn_of_addMul (a := a) (k := subE zeroE oneE) h

/-- A control: **the premise on g.cEnd is needed.** -/
theorem slotsIn_joinW_cEnd {g : Forest.Heard} {KF : Array Aff} (h : SS (joinW g KF)) : SS g.cEnd := by
  unfold joinW at h
  exact slotsIn_of_sub h

/-- **The one form of the lookup's join at the key forms that "keys" returns.** -/
theorem join_slots_K05 {l₁ : List Aff} {j : JoinsP} {k3 : P.Runs.PadIn} {kf : Array Aff}
    {g : Forest.Heard} {F : Fork} {t : Tape} {x : Aff × Fork × Tape}
    (hP : PtsSlots Ps i.g i.p) (hR : RowsSlots Ps i.p) (h1 : P.Runs.firstRun i K = some (l₁, j))
    (hk : P.Runs.keysRun i k3 j = some kf) (hc : SlotsIn Ps g.cEnd)
    (hj : Look.joinF g kf F t = some x) : SlotsIn Ps x.1 := by
  rw [(joinF_is hj).1]
  exact slotsIn_joinW (keysRun_slots hP hR h1 hk) hc

/-- "Every slot that the form names is below the number of slots and filled in G" is SlotsIn, by its text. -/
theorem filledA_iff {G : Fork} {a : Aff} :
    Fo.FilledA G a ↔ SlotsIn (fun s => s < G.ns ∧ Filled G s) a := Iff.rfl

/-- **join_slots_K05 at "below the number of slots and filled in G".** -/
theorem join_filled_K05 {G : Fork} {l₁ : List Aff} {j : JoinsP} {k3 : P.Runs.PadIn} {kf : Array Aff}
    {g : Forest.Heard} {F : Fork} {t : Tape} {x : Aff × Fork × Tape}
    (hP : PtsSlots (fun s => s < G.ns ∧ Filled G s) i.g i.p)
    (hR : RowsSlots (fun s => s < G.ns ∧ Filled G s) i.p)
    (h1 : P.Runs.firstRun i K = some (l₁, j)) (hk : P.Runs.keysRun i k3 j = some kf)
    (hc : Fo.FilledA G g.cEnd) (hj : Look.joinF g kf F t = some x) : Fo.FilledA G x.1 :=
  join_slots_K05 hP hR h1 hk hc hj

end K5Law

#print axioms K5Law.keys_slots_K05
#print axioms K5Law.keysRun_slots
#print axioms K5Law.slotsIn_joinW
#print axioms K5Law.slotsIn_joinW_cEnd
#print axioms K5Law.join_slots_K05
#print axioms K5Law.filledA_iff
#print axioms K5Law.join_filled_K05
