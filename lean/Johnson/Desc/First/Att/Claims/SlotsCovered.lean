-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/SlotsCovered.lean: kind K5: THE SLOTS' TWIN OF Claims/Covered.lean, THE
LAW: every slot that a form gathered by the run "first" or the run "second" names meets a given
predicate Ps on the slots' numbers, IF along the stretch that the runs walk from each number that the
claims read of what was heard every slot meets Ps (PtsSlots) and the rows that the sumchecks leave
name such slots alone (RowsSlots). Both records and the law's statement Spec.SlotsCovered are
Claims/SlotsIn.lean's; the predicate SlotsIn and its rules are Johnson/Road/K4/Slots/SlotsIn.lean's, handed
on there. "Lies in the stretch [lo, hi)" is the case
Ps j := lo ≤ j ∧ j < hi; "is filled in the ledger" is another.

IS IT EMPTY HERE?
  · The conclusion says nothing of a form that names no slot: SlotsIn Ps holds of it at every Ps.
  · At Ps := fun _ => True both records hold of everything and the law says nothing.
  · At Ps := fun _ => False the conclusion would say "names no slot"; there PtsSlots cannot be met
    (ptsSlots_some: PtsSlots Ps g p → Ps p.d.s5). So the law is empty there, as it must be.
  · The law says as much as Ps is narrow. From a silly PtsSlots (a Ps wider than "filled") comes a
    SlotsIn at that wider Ps: NO "every named slot is filled" follows from it.
  · If a run refuses (none), the law says nothing of it. That the runs return is not shown here.
  · That a gathered form names any slot at all, that the conclusion can fail and that the premises can
    be met is shown AT ONE TOY RECORD ALONE
    (Claims/SlotsCoveredToy.lean [not in this library]: no lawful shape, no real
    size). AT A REAL SIZE NEITHER RECORD IS SHOWN TO HOLD: that is owed elsewhere.

Main names:
  CV.forM_mem, CV.forIn_mem: two rules more on CV (Claims/Covered.lean), general in the predicate:
    the loop's body is asked only at members of the list. Covered.lean's CV.forM and CV.forIn forget
    at which member the body stands; the entries' law never asked.
  sv_…: routine by routine, as Covered.lean's cv_…, at SlotsIn Ps. The readers (sv_uEnt to
    sv_readGroup) need no premise: what they return is built of entries and constants.
  slots_covered_K05 : Spec.SlotsCovered. slots_covered_K05': the same, its arguments implicit.
Used of Covered.lean as it stands: CV and its rules pure, bind, never, lin, mustAs, need, ite, foldlM,
  foldlM_mem, read.
Not used of PtsSlots: planes' first clause (3 ≤ np); of a softmax unit's seven scalars all but the
  sixth (s0 + 5); of the five the second (s5 + 1): in Att/RunsP.lean these stand in key forms alone.
  Of scF's end values the second of each member (scF.b b): no form written in Att/RunsP.lean names it.
Limits. THE KEY FORMS that "first" hands on (the record JoinsP) are not gathered into the list, and
  NOTHING IS SAID OF THEM. NEITHER RECORD OF PREMISES IS SHOWN OF ANYTHING HERE. Nothing on whether a
  slot is filled. Nothing on entries (that is reads_covered_K05).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.SlotsIn

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P.Runs (W JoinsP)

variable {α β σ : Type} {K : ℕ} {C : Aff → Prop}

/-! ### two rules more: the loop's body at members alone -/

theorem CV.forM_mem {f : α → W PUnit} :
    ∀ xs : List α, (∀ a ∈ xs, CV K C (fun _ => True) (f a)) → CV K C (fun _ => True) (xs.forM f)
  | [], _ => CV.pure trivial
  | a :: xs, h => by
    show CV K C _ (f a >>= fun _ => xs.forM f)
    exact CV.bind (h a List.mem_cons_self) fun _ _ =>
      CV.forM_mem xs fun b hb => h b (List.mem_cons_of_mem _ hb)

theorem CV.forIn_mem {f : α → PUnit → W (ForInStep PUnit)} :
    ∀ xs : List α, (∀ a ∈ xs, CV K C (fun _ => True) (f a PUnit.unit)) →
      CV K C (fun _ => True) (ForIn.forIn xs PUnit.unit f)
  | [], _ => by rw [List.forIn_nil]; exact CV.pure trivial
  | a :: xs, h => by
    rw [List.forIn_cons]
    refine CV.bind (h a List.mem_cons_self) fun r _ => ?_
    cases r with
    | done b => exact CV.pure trivial
    | yield b => exact CV.forIn_mem xs fun c hc => h c (List.mem_cons_of_mem _ hc)

/-! ### the readers: entries and constants alone -/

variable {Ps : ℕ → Prop} {i : P.Runs.In}

local notation "SS" => SlotsIn Ps
local notation "TT" => fun _ => True

theorem sv_uEnt (t x : ℕ) : CV K SS SS (P.Runs.uEnt t x) := by
  unfold P.Runs.uEnt
  exact CV.read (CV.bind (CV.mustAs _ _) fun _ _ => CV.pure (slotsIn_ent _ _ _))

theorem sv_u3at (t n : ℕ) : CV K SS SS (P.Runs.u3at i t n) := by
  unfold P.Runs.u3at
  exact CV.bind (CV.mustAs _ _) fun _ _ => sv_uEnt _ _

theorem sv_weighted (n : ℕ) (w : Array E) (f : ℕ → W Aff) (hf : ∀ k, CV K SS SS (f k)) :
    CV K SS SS (P.Runs.weighted n w f) := by
  unfold P.Runs.weighted
  exact CV.foldlM (fun s k hs => CV.bind (hf k) fun x hx => CV.pure (slotsIn_addMul _ hs hx)) _ _
    (slotsIn_ofConst _)

theorem sv_plane (t x lam a : ℕ) (z : Array E) (isD : Bool) :
    CV K SS SS (P.Runs.plane i t x lam a z isD) := by
  unfold P.Runs.plane
  exact sv_weighted _ _ _ fun _ => sv_u3at _ _

theorem sv_shV (t off nl J lam j : ℕ) : CV K SS SS (P.Runs.shV i t off nl J lam j) := by
  unfold P.Runs.shV
  exact sv_weighted _ _ _ fun _ => sv_u3at _ _

theorem sv_xl (t : ℕ) (X : P.Ten) (lam hd : ℕ) (zc : Array E) :
    CV K SS SS (P.Runs.xl i t X lam hd zc) := by
  unfold P.Runs.xl
  dsimp only
  cases P.cutLast (zc.extract 0 i.g.ldh) i.g.ls with
  | none => exact CV.never fun _ => rfl
  | some cut =>
    cases P.headFeat X hd i.g.dh with
    | none => exact CV.never fun _ => rfl
    | some j0 => exact sv_weighted _ _ _ fun _ => sv_weighted _ _ _ fun _ => sv_u3at _ _

theorem sv_overG (zg : Array E) (f : ℕ → W Aff) (hf : ∀ g, CV K SS SS (f g)) :
    CV K SS SS (P.Runs.overG i zg f) := by
  unfold P.Runs.overG
  exact sv_weighted _ _ _ hf

theorem sv_readDenominator (t : ℕ) (zg : Array E) (lam a : ℕ) :
    CV K SS SS (P.Runs.readDenominator i t zg lam a) := by
  unfold P.Runs.readDenominator
  exact sv_overG _ _ fun _ => sv_shV _ _ _ _ _ _
theorem sv_readMaximum (t : ℕ) (zg : Array E) (lam a : ℕ) :
    CV K SS SS (P.Runs.readMaximum i t zg lam a) := by
  unfold P.Runs.readMaximum
  exact sv_overG _ _ fun _ => sv_shV _ _ _ _ _ _
theorem sv_readIndexBit (t : ℕ) (zg : Array E) (lam a k : ℕ) :
    CV K SS SS (P.Runs.readIndexBit i t zg lam a k) := by
  unfold P.Runs.readIndexBit
  exact sv_overG _ _ fun _ => sv_shV _ _ _ _ _ _
theorem sv_readHead (t : ℕ) (X : P.Ten) (zg zc : Array E) (lam a : ℕ) :
    CV K SS SS (P.Runs.readHead i t X zg zc lam a) := by
  unfold P.Runs.readHead
  exact sv_overG _ _ fun _ => sv_xl _ _ _ _ _
theorem sv_readGroup (t : ℕ) (X : P.Ten) (zg zc : Array E) (lam : ℕ) :
    CV K SS SS (P.Runs.readGroup i t X zg zc lam) := by
  unfold P.Runs.readGroup
  exact sv_overG _ _ fun _ => sv_xl _ _ _ _ _

theorem sv_lessPieces {start : Aff} (hs : SS start) (pw : Array P.W1) (f : P.W1 → W Aff)
    (hf : ∀ w, CV K SS SS (f w)) : CV K SS SS (P.Runs.lessPieces start pw f) := by
  unfold P.Runs.lessPieces
  rw [← Array.foldlM_toList]
  exact CV.foldlM (fun s w hs => CV.bind (hf w) fun x hx => CV.pure (slotsIn_addMul _ hs hx)) _ _ hs

/-! ### the claims -/

/-- The slot at distance x < n from a number along whose stretch of n every slot meets Ps. -/
theorem slotsIn_at {s n x : ℕ} (h : ∀ y, y < n → Ps (s + y)) (hx : x < n) : SS (Aff.slot (s + x)) :=
  slotsIn_slot (h x hx)

theorem sv_linPlanes (pc : P.RemP) (h : ∀ x, x < pc.np → Ps (pc.s0 + x)) :
    CV K SS TT (P.Runs.linPlanes i pc) := by
  unfold P.Runs.linPlanes
  exact CV.forM_mem _ fun x hx => CV.bind (sv_lessPieces (slotsIn_at h (List.mem_range.1 hx)) _ _
    fun w => sv_plane _ _ _ _ _ _) fun f hf => CV.lin hf

theorem sv_callKR (hP : PtsSlots Ps i.g i.p) (q : ℕ) : CV K SS TT (P.Runs.callKR i q) := by
  unfold P.Runs.callKR
  rw [← Array.foldlM_toList]
  exact CV.foldlM_mem _ _ (fun v pc hpc _ => CV.ite
    (CV.bind (sv_linPlanes pc (hP.planes pc hpc).2) fun _ _ => CV.pure trivial)
    (CV.pure trivial)) trivial

theorem sv_claim3 (hP : PtsSlots Ps i.g i.p) (j : JoinsP) : CV K SS TT (P.Runs.claim3 i j) := by
  unfold P.Runs.claim3
  exact CV.foldlM (fun j x _ => CV.ite (CV.bind (sv_callKR hP x.2) fun _ _ => CV.pure trivial)
    (CV.pure trivial)) _ _ trivial

theorem sv_endValues (k : P.ScoreP) (he : ∀ y, y < 2 * k.pw.size → Ps (k.sc.ends + y))
    (tb : P.ScoreT) (rc : Array E) (b : ℕ) (hb : b < k.pw.size) (w : P.W1) :
    CV K SS TT (P.Runs.endValues i k tb rc b w) := by
  unfold P.Runs.endValues
  exact CV.bind (sv_readHead _ _ _ _ _ _) fun q hq =>
    CV.bind (CV.lin (slotsIn_sub (slotsIn_a he hb) hq)) fun _ _ =>
    CV.bind (sv_readGroup _ _ _ _ _) fun kx hk => CV.lin (slotsIn_sub (slotsIn_b he hb) hk)

theorem sv_unitKFD (hP : PtsSlots Ps i.g i.p) (n : ℕ) (k : P.ScoreP) (hk : k ∈ i.p.scores.toList)
    (hr : SS k.sc.row) : CV K SS TT (P.Runs.unitKFD i n k) := by
  obtain ⟨k1, k2⟩ := hP.scores k hk
  unfold P.Runs.unitKFD
  dsimp only
  refine CV.bind (CV.need _) fun tb _ => CV.bind (CV.need _) fun pc hpc => ?_
  have hm : pc ∈ i.p.planes.toList := Array.mem_toList_iff.2 (Array.mem_of_getElem? hpc)
  refine CV.bind (sv_linPlanes pc (hP.planes pc hm).2) fun _ _ =>
    CV.bind (sv_lessPieces (slotsIn_at (x := 5) k1 (by omega)) _ _
      fun w => sv_readMaximum _ _ _ _) fun f hf =>
    CV.bind (CV.lin hf) fun _ _ => CV.bind (CV.lin (f := P.Runs.leftOf k.sc.row) hr) fun _ _ => ?_
  refine CV.forM_mem _ fun x hx => ?_
  refine sv_endValues k k2 tb _ x.2 ?_ x.1
  have := (List.mem_zipIdx hx).2.1
  simpa using this

theorem sv_callKFD (hP : PtsSlots Ps i.g i.p) (hR : RowsSlots Ps i.p) (q : ℕ) (c : P.CallG) :
    CV K SS TT (P.Runs.callKFD i q c) := by
  unfold P.Runs.callKFD
  refine CV.foldlM_mem _ _ (fun v x hx _ => ?_) trivial
  have hm : x.1 ∈ i.p.scores.toList := (List.mem_zipIdx hx).2.2 ▸ List.getElem_mem _
  exact CV.ite (CV.bind (sv_unitKFD hP x.2 x.1 hm (hR.units x.1 hm)) fun _ _ => CV.pure trivial)
    (CV.pure trivial)

theorem sv_claim4 (hP : PtsSlots Ps i.g i.p) (hR : RowsSlots Ps i.p) (j : JoinsP) :
    CV K SS TT (P.Runs.claim4 i j) := by
  unfold P.Runs.claim4
  exact CV.foldlM (fun j x _ => CV.ite (CV.bind (sv_callKFD hP hR x.2 x.1) fun _ _ => CV.pure trivial)
    (CV.pure trivial)) _ _ trivial

theorem sv_endValuesE (hP : PtsSlots Ps i.g i.p) (b : ℕ) (hb : b < i.g.NP) (w : P.W1) :
    CV K SS TT (P.Runs.endValuesE i b w) := by
  unfold P.Runs.endValuesE
  dsimp only
  exact CV.bind (sv_readDenominator _ _ _ _) fun z hz =>
    CV.bind (CV.lin (slotsIn_sub (slotsIn_a hP.scE hb) hz)) fun _ _ =>
    CV.bind (sv_readHead _ _ _ _ _ _) fun o ho =>
    CV.lin (slotsIn_sub (slotsIn_b hP.scE hb) ho)

/-- The five scalars of the division, by their names. -/
theorem slotsIn_sACC (hP : PtsSlots Ps i.g i.p) : SS (Aff.slot i.p.d.sACC) :=
  slotsIn_at (x := 0) hP.five (by omega)
theorem slotsIn_sZC (hP : PtsSlots Ps i.g i.p) : SS (Aff.slot i.p.d.sZC) :=
  slotsIn_at (x := 2) hP.five (by omega)
theorem slotsIn_sRH (hP : PtsSlots Ps i.g i.p) : SS (Aff.slot i.p.d.sRH) :=
  slotsIn_at (x := 3) hP.five (by omega)
theorem slotsIn_sRHP (hP : PtsSlots Ps i.g i.p) : SS (Aff.slot i.p.d.sRHP) :=
  slotsIn_at (x := 4) hP.five (by omega)

theorem sv_claim5 (hP : PtsSlots Ps i.g i.p) (hR : RowsSlots Ps i.p) (j : JoinsP) :
    CV K SS TT (P.Runs.claim5 i j) := by
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
  refine CV.bind (CV.forIn_mem _ fun b hb => ?_) fun _ _ => CV.pure trivial
  exact CV.bind (sv_endValuesE hP b (List.mem_range.1 hb) _) fun _ _ => CV.pure trivial

theorem sv_valueProduct (sc : P.SumP) (he : ∀ y, y < 2 * i.g.NP → Ps (sc.ends + y)) (hr : SS sc.row)
    (tS : ℕ) (pt : Array E) (isD : Bool) (tV : ℕ) :
    CV K SS TT (P.Runs.valueProduct i sc tS pt isD tV) := by
  unfold P.Runs.valueProduct
  refine CV.bind (CV.lin (f := P.Runs.leftOf sc.row) hr) fun _ _ =>
    CV.bind (CV.forIn_mem _ fun b hb => ?_) fun _ _ => CV.pure trivial
  have hb' := List.mem_range.1 hb
  dsimp only
  refine CV.bind (sv_plane _ _ _ _ _ _) fun p3 h3 => CV.bind (sv_plane _ _ _ _ _ _) fun p4 h4 => ?_
  refine CV.bind (CV.lin (slotsIn_sub (slotsIn_a he hb')
    (slotsIn_add (slotsIn_add h3 (slotsIn_ofConst _)) (slotsIn_scale _ h4))))
    fun _ _ => CV.bind (sv_readGroup _ _ _ _ _) fun v hv => ?_
  exact CV.bind (CV.lin (slotsIn_sub (slotsIn_b he hb') (slotsIn_add (slotsIn_ofConst _) hv)))
    fun _ _ => CV.pure trivial

theorem sv_claim6 (hP : PtsSlots Ps i.g i.p) (hR : RowsSlots Ps i.p) :
    CV K SS TT (P.Runs.claim6 i) := by
  unfold P.Runs.claim6
  dsimp only
  exact CV.bind (CV.lin (slotsIn_sub (slotsIn_sub (slotsIn_add (slotsIn_at (x := 0) hP.values (by omega))
    (slotsIn_at (x := 1) hP.values (by omega))) (slotsIn_sACC hP)) (slotsIn_scale _ (slotsIn_sZC hP))))
    fun _ _ => CV.bind (sv_valueProduct _ hP.vpm hR.vpm _ _ _ _) fun _ _ =>
    sv_valueProduct _ hP.vpd hR.vpd _ _ _ _

/-- Cell (b, k) of a table of NP rows of lt lies below NP · lt. -/
theorem cell_lt {NP lt b k : ℕ} (hb : b < NP) (hk : k < lt) : b * lt + k < NP * lt :=
  calc b * lt + k < b * lt + lt := Nat.add_lt_add_left hk _
    _ = (b + 1) * lt := (Nat.succ_mul b lt).symm
    _ ≤ NP * lt := Nat.mul_le_mul_right lt hb

theorem sv_claim7 (hP : PtsSlots Ps i.g i.p) (hR : RowsSlots Ps i.p) :
    CV K SS TT (P.Runs.claim7 i) := by
  unfold P.Runs.claim7
  dsimp only
  refine CV.bind (CV.forIn_mem _ fun b hb => ?_) fun _ _ =>
    CV.bind (CV.lin (f := P.Runs.leftOf i.p.x.scF.row) hR.scF) fun _ _ =>
    CV.bind (CV.forIn_mem _ fun b hb => ?_) fun _ _ =>
    CV.bind (CV.lin (f := P.Runs.leftOf i.p.x.scd.row) hR.scd) fun _ _ =>
    CV.bind (CV.forIn_mem _ fun lam hl => ?_) fun _ _ =>
    CV.bind (CV.forIn_mem _ fun b hb => ?_) fun _ _ => CV.pure trivial
  · exact CV.bind (sv_readMaximum _ _ _ _) fun m hm =>
      CV.bind (CV.lin (slotsIn_sub (slotsIn_at hP.maxima (List.mem_range.1 hb)) hm))
      fun _ _ => CV.pure trivial
  · exact CV.bind (sv_readHead _ _ _ _ _ _) fun q hq =>
      CV.bind (CV.lin (slotsIn_sub (slotsIn_a hP.scF (List.mem_range.1 hb)) hq))
      fun _ _ => CV.pure trivial
  · have h1 := List.mem_range.1 hl
    exact CV.bind (sv_readGroup _ _ _ _ _) fun kx hk =>
      CV.bind (CV.lin (slotsIn_sub (slotsIn_at (s := i.p.x.scd.ends) hP.scd (by omega)) hk))
      fun _ _ => CV.pure trivial
  · refine CV.bind (CV.forIn_mem _ fun k hk => ?_) fun _ _ =>
      CV.bind (P := fun _ => True) (CV.pure trivial) fun _ _ => CV.pure trivial
    have h1 := cell_lt (List.mem_range.1 hb) (List.mem_range.1 hk)
    exact CV.bind (sv_readIndexBit _ _ _ _ _) fun bit hbit =>
      CV.bind (CV.lin (slotsIn_sub (slotsIn_at (s := i.p.x.scd.ends)
        (x := i.g.Lam + b * i.g.lt + k) hP.scd (by omega)) hbit))
      fun _ _ => CV.pure trivial

theorem sv_claim8 (hP : PtsSlots Ps i.g i.p) (hR : RowsSlots Ps i.p) :
    CV K SS TT (P.Runs.claim8 i) := by
  unfold P.Runs.claim8
  dsimp only
  refine CV.bind (CV.lin (f := P.Runs.leftOf i.p.x.scH.row) hR.scH) fun _ _ =>
    CV.bind (CV.forIn_mem _ fun b hb => ?_) fun _ _ => CV.pure trivial
  have ha := slotsIn_a hP.scH (List.mem_range.1 hb)
  have hb' := slotsIn_b hP.scH (List.mem_range.1 hb)
  refine CV.bind (CV.lin (slotsIn_add (slotsIn_sub hb' ha) (slotsIn_ofConst _))) fun _ _ => ?_
  refine CV.bind (P := SlotsIn Ps) (CV.foldlM (fun s k hs => CV.bind (sv_readIndexBit _ _ _ _ _)
    fun bit hbit => CV.pure (slotsIn_addMul _ hs hbit)) _ _ ha) fun f hf => ?_
  exact CV.bind (CV.lin hf) fun _ _ => CV.pure trivial

/-- **Every slot that a form gathered by "first" or "second" names meets Ps.** -/
theorem slots_covered_K05' {l₁ l₂ : List Aff} {j : JoinsP} (hP : PtsSlots Ps i.g i.p)
    (hR : RowsSlots Ps i.p) (h1 : P.Runs.firstRun i K = some (l₁, j))
    (h2 : P.Runs.secondRun i K = some l₂) : ∀ f ∈ l₁ ++ l₂, SlotsIn Ps f := by
  unfold P.Runs.firstRun P.Runs.gather at h1
  unfold P.Runs.secondRun P.Runs.gather at h2
  simp only [Option.map_eq_some_iff] at h1 h2
  obtain ⟨_, ⟨y1, hy1, rfl⟩, e1⟩ := h1
  obtain ⟨_, ⟨y2, hy2, rfl⟩, e2⟩ := h2
  have c1 := (CV.bind (C := SlotsIn Ps) (sv_claim3 hP _) fun j3 _ => CV.bind (sv_claim4 hP hR j3)
    fun j4 _ => sv_claim5 hP hR j4) #[] y1 hy1 (by simp)
  have c2 := (CV.bind (C := SlotsIn Ps) (sv_claim6 hP hR) fun _ _ => CV.bind (sv_claim7 hP hR)
    fun _ _ => sv_claim8 hP hR) #[] y2 hy2 (by simp)
  have a1 : l₁ = y1.2.toList := (Prod.mk.inj e1).1.symm
  have a2 : l₂ = y2.2.toList := e2.symm
  intro f hf
  rcases List.mem_append.1 hf with h | h
  · exact c1.2 f (a1 ▸ h)
  · exact c2.2 f (a2 ▸ h)

/-- **The law owed (Claims/SlotsIn.lean), to the letter.** -/
theorem slots_covered_K05 : Spec.SlotsCovered :=
  fun _ _ _ _ _ _ hP hR h1 h2 => slots_covered_K05' hP hR h1 h2

/-! ### is it empty? -/

/-- The premise cannot be met at a predicate that no number meets. -/
theorem ptsSlots_some {g : P.Geo} {p : P.Pts} (hP : PtsSlots Ps g p) : Ps p.d.s5 := hP.five 0 (by omega)

end K5Law

#print axioms K5Law.CV.forM_mem
#print axioms K5Law.CV.forIn_mem
#print axioms K5Law.slots_covered_K05'
#print axioms K5Law.slots_covered_K05
#print axioms K5Law.ptsSlots_some
