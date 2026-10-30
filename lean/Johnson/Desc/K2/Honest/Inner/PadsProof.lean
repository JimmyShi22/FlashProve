-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Inner/PadsProof.lean: NO ROW THAT A CODE SWITCH BETWEEN TWO SEGMENTS LAYS
HAS, READ IN THE FIELD, A COEFFICIENT AT A NEW PAD's PLACE: neither at the carrying message's pad
nor at a copy's. Under the public premises of `SwitchRowsHold` (Inner/Statement.lean). Statements
and proofs.

  `Spares`, `Spares.add`, `Spares.sum`   a function of coefficients has none at a new pad's place;
                    sums
  `pad_bare`        a pad's place of a shape without a mask row: in the main part
  `pads_same`       a kept member and its copy have one pad
  `stretch_off`     coefficients on a stretch give 0 at an index that is no place of the stretch
  `g_bare`, `copy_at`, `kept_shape`, `restBits_eq`, `gpad_inside`   g has no mask row; a copy's
                    number; a kept member for each target; two sizes
  `spares_lift`, `spares_stretch`, `spares_addKept`   the three sorts of pieces
  `spares_mask`     a mask row's generator row
  `padsUnread`      every made row

It proves the conclusion of `NewPadsUnread` UNDER MORE PREMISES than that statement has: the rest
lies in the main part; each copy has a main row; lengthsOk; both codes' log-lengths are at most 32;
every position lies below the old code's length.

Limits. Read in the field: nothing on the three words of a coefficient. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Inner.Holds
import Johnson.Desc.K2.Honest.Inner.Public
import Johnson.Top.H.SwitchPadsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.Slice (GE coefAt formAt stretchAt genMain genMask symAtB)
open Johnson.Prover.Send (Rows)
open H2K.Lift (genKept keptFrom keptForm)
open VerifiableInference.Desc.First.K2Hands (placeOf carriedOf formOn sampleRow)

/-- A function of coefficients has none at a new pad's place. -/
def Spares (S : Statement) (T : SwitchTarget) (g : Nat) (anew : Array Nat)
    (κ : Nat → Part → Nat → GE) : Prop :=
  (∀ p ∈ padPlaces S.codes T.shape, κ g p.part p.index = 0) ∧
    ∀ (a : Nat) (k : KeptTarget), T.kept[a]? = some k →
      ∀ p ∈ padPlaces S.codes k.shape, κ (anew.getD a noId) p.part p.index = 0

theorem Spares.add {S : Statement} {T : SwitchTarget} {g : Nat} {anew : Array Nat}
    {κ₁ κ₂ : Nat → Part → Nat → GE} (h₁ : Spares S T g anew κ₁) (h₂ : Spares S T g anew κ₂) :
    Spares S T g anew fun o p J => κ₁ o p J + κ₂ o p J :=
  ⟨fun p hp => by
      show κ₁ g p.part p.index + κ₂ g p.part p.index = 0
      rw [h₁.1 p hp, h₂.1 p hp, add_zero],
    fun a k hk p hp => by
      show κ₁ (anew.getD a noId) p.part p.index + κ₂ (anew.getD a noId) p.part p.index = 0
      rw [h₁.2 a k hk p hp, h₂.2 a k hk p hp, add_zero]⟩

theorem Spares.sum {α : Type} {S : Statement} {T : SwitchTarget} {g : Nat} {anew : Array Nat}
    (κ : α → Nat → Part → Nat → GE) (l : List α) (h : ∀ x ∈ l, Spares S T g anew (κ x)) :
    Spares S T g anew fun o p J => (l.map fun x => κ x o p J).sum :=
  ⟨fun p hp => List.sum_eq_zero fun v hv => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
      exact (h x hx).1 p hp,
    fun a k hk p hp => List.sum_eq_zero fun v hv => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
      exact (h x hx).2 a k hk p hp⟩

/-- A pad's place of a shape without a mask row: in the main part. -/
theorem pad_bare (codes : Codes) (s : OracleShape) (hm : s.maskRows = 0) (p : PadPlace)
    (hp : p ∈ padPlaces codes s) : p.part = .main := by
  have hh : (Send.cube codes s).hasMask = false := by
    unfold Send.cube
    simp [hm]
  unfold padPlaces Send.pad at hp
  obtain ⟨_, h2⟩ := Johnson.Top.H.mem_getD_ite _ _ p hp
  obtain ⟨_, _, _, m3⟩ := Johnson.Top.H.pad_form_mem _ _ _ _ _ _ _ p h2
  simp only [hh, Bool.false_eq_true, if_false] at m3
  exact m3

/-- A kept member and its copy have one pad. -/
theorem pads_same (codes : Codes) (o n : OracleShape) (K : _root_.Tw.K2.KeptFits codes o n) :
    padPlaces codes n = padPlaces codes o := by
  unfold padPlaces Send.pad Send.cube
  simp only [K.oldBare, K.newBare, K.rows, K.degree, K.answers, K.length, Nat.lt_irrefl,
    decide_false, Bool.false_eq_true, if_false, Bool.false_or]

/-- Coefficients on a stretch give 0 at an index that is no place of the stretch. -/
theorem stretch_off (places : SwitchPlaces) (first n : Nat) (c : Nat → GE) (J : Nat)
    (h : ∀ i, places.get (first + i) ≠ J) : stretchAt places first n c J = 0 := by
  unfold stretchAt
  exact Finset.sum_eq_zero fun i _ => if_neg (h i)

variable {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat} {anew : Array Nat}
  {W : Left} {V : Nat → Rows}

/-- g has no mask row. -/
theorem g_bare (A : AtSwitch S old T g anew W V) : T.shape.maskRows = 0 := by
  have fill := A.target.fill
  unfold _root_.Tw.K2.BlocksFill at fill
  rw [A.restMain] at fill
  exact fill.1

/-- A copy's number: among the copies', and not g. -/
theorem copy_at (A : AtSwitch S old T g anew W V) {Fr : SwitchFrame}
    (hFr : switchFrame S old T g anew = some Fr) (a : Nat) (k : KeptTarget)
    (hk : T.kept[a]? = some k) :
    anew.toList[a]? = some (anew.getD a noId) ∧ (g == anew.getD a noId) = false := by
  obtain ⟨_, _, _, hsz, _⟩ := _root_.Tw.K2.frame_inv hFr
  have hsz' : anew.size = (switchKept old).size := by simpa using hsz
  have ha : a < T.kept.size := (Array.getElem?_eq_some_iff.1 hk).1
  have hlt : a < anew.size := by
    have := A.target.keptCount
    omega
  have e : anew.toList[a]? = some (anew.getD a noId) := by
    rw [Array.getElem?_toList, Array.getElem?_eq_getElem hlt, Lists.getD_at _ hlt]
  refine ⟨e, ?_⟩
  have hap := A.seated.apart
  rw [List.cons_append, List.nodup_cons] at hap
  simp only [beq_eq_false_iff_ne]
  exact fun h => hap.1 (List.mem_append_left _ (h ▸ List.mem_of_getElem? e))

/-- **Coefficients on a stretch of the rest.** -/
theorem spares_stretch (A : AtSwitch S old T g anew W V) {Fr : SwitchFrame}
    (hFr : switchFrame S old T g anew = some Fr) (a n : Nat) (c : Nat → GE) :
    Spares S T g anew (stretchPiece S T g a n c) := by
  obtain ⟨_, _, _, hpad⟩ := SwitchPlaces.places_of_check A.check
  refine ⟨fun p hp => ?_, fun a' k hk p _ => ?_⟩
  · have hpm := pad_bare S.codes T.shape (g_bare A) p hp
    unfold stretchPiece
    rw [stretch_off _ _ _ _ _ fun i => hpad (a + i) p hp (by rw [hpm, A.restMain])]
    simp
  · unfold stretchPiece
    rw [(copy_at A hFr a' k hk).2]
    simp

/-- **A form on the old main row's message, carried to g.** -/
theorem spares_lift (A : AtSwitch S old T g anew W V) {Fr : SwitchFrame}
    (hFr : switchFrame S old T g anew = some Fr) (c : Form)
    (hc : ∀ v ∈ c.tensors, v.vars = (S.codes.base.getD old.code default).logEll) :
    Spares S T g anew (liftPiece S old T g c) := by
  have F := A.target
  refine ⟨fun p hp => ?_, fun a' k hk p _ => ?_⟩
  · obtain ⟨_, _, hM⟩ := SwitchPlaces.of_check A.check
    rw [F.mainPart] at hM
    obtain ⟨_, h0, _⟩ := VerifiableInference.Desc.First.K2Hands.check_more A.check
    have hpow : 2 ^ (S.codes.base.getD old.code default).logEll =
        (S.codes.base.getD old.code default).ell := F.power.2
    have hb : T.main.bits ≤ (S.codes.base.getD old.code default).logEll :=
      (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 (by rw [hpow]; exact F.mainSmall)
    have hR : T.main.bits ≤ switchRowBits T .main :=
      (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 (by unfold RowCut.Fits at hM; omega)
    have hn : (S.codes.base.getD old.code default).logEll ≤
        (S.codes.base.getD T.shape.code default).logEll + T.main.bits :=
      (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 (by
        rw [hpow, Nat.pow_add]
        exact Nat.le_trans F.mainRoom
          (Nat.mul_le_mul_right _ (SwitchPlaces.le_two_pow_ceilLog2' _)))
    obtain ⟨place, h1, h2⟩ := Johnson.Top.H.pad_index_at S.codes T.shape (g_bare A) F.rows p hp
    have hRr := SwitchPlaces.le_two_pow_ceilLog2' T.shape.mainRows
    have hrows := F.rows
    have hm : p.index % 2 ^ ceilLog2 T.shape.mainRows = T.shape.mainRows - 1 := by
      rw [h2, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    have hd : p.index / 2 ^ ceilLog2 T.shape.mainRows = place := by
      rw [h2, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (by omega),
        Nat.zero_add]
    have hJ : p.index < 2 ^ (switchRowBits T .main +
        (S.codes.base.getD T.shape.code default).logEll) :=
      VerifiableInference.Desc.First.K2Hands.lt_pow_of _ _ T.shape.mainRows _ _
        (by show p.index % 2 ^ ceilLog2 T.shape.mainRows < _; omega) hRr
        (by show p.index / 2 ^ ceilLog2 T.shape.mainRows < _; rw [hd]; exact h1)
        (SwitchPlaces.le_two_pow_ceilLog2' _)
    unfold liftPiece
    rw [H2K.Lift.formAt_switchLift_off c _ T.main _ _ hc hb hR (by omega)
      (by rw [h0]; exact Nat.dvd_zero _) (by rw [h0, Nat.zero_div]; exact Nat.two_pow_pos _)
      p.index hJ ?_]
    · simp
    · intro j _ e
      have hno := main_no_pad A (cutIndex T.main (switchRowBits T .main) j) (by
        show cutIndex T.main (switchRowBits T .main) j % 2 ^ switchRowBits T .main < _
        rw [cutIndex_mod hM j, h0, Nat.zero_add]
        exact Nat.mod_lt _ (Nat.two_pow_pos _))
      apply hno
      rw [e]
      exact List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hp, by
        rw [pad_bare S.codes T.shape (g_bare A) p hp]; rfl⟩, rfl⟩
  · unfold liftPiece
    rw [(copy_at A hFr a' k hk).2]
    simp

/-- There is a kept member for each target. -/
theorem kept_shape (A : AtSwitch S old T g anew W V) (a : Nat) (k : KeptTarget)
    (hk : T.kept[a]? = some k) :
    ∃ s, (sizesAt S old T).kept[a]? = some s ∧ _root_.Tw.K2.KeptFits S.codes s k.shape := by
  have ha : a < T.kept.size := (Array.getElem?_eq_some_iff.1 hk).1
  have e : (sizesAt S old T).kept.length = (switchKept old).size := by
    show ((switchKept old).toList.map _).length = _
    rw [List.length_map, Array.length_toList]
  have hlt : a < (sizesAt S old T).kept.length := by
    have := A.target.keptCount
    omega
  refine ⟨_, List.getElem?_eq_getElem hlt, ?_⟩
  exact kept_fits A a _ k (List.getElem?_eq_getElem hlt) (by rw [Array.getElem?_toList]; exact hk)

/-- **A form on a kept member's table, carried over.** -/
theorem spares_addKept (A : AtSwitch S old T g anew W V) {Fr : SwitchFrame}
    (hFr : switchFrame S old T g anew = some Fr) (a : Nat) (k : KeptPlace)
    (hk : Fr.kept[a]? = some k) (c : Form) :
    Spares S T g anew (coefAt (Fr.addKept {} k c)) := by
  have I := frameIs hFr
  obtain ⟨_, _, _, hpad⟩ := SwitchPlaces.places_of_check A.check
  obtain ⟨s, o, hs, ho, e1, e2, _, _, _, _, _⟩ := kept_at hFr a k hk
  have hap := A.seated.apart
  rw [List.cons_append, List.nodup_cons, List.nodup_append] at hap
  have hne : o ≠ g := fun e => hap.1 (List.mem_append_left _ (e ▸ List.mem_of_getElem? ho))
  have hform : Fr.addKept {} k c = switchAddKept {} (padPlaces S.codes s) o g .main
      (SwitchPlaces.make S.codes T) k.oldPadAt c := by
    unfold SwitchFrame.addKept
    rw [e2, e1, I.gIs, I.restPart, A.restMain, I.places]
  rw [hform]
  refine ⟨fun p hp => ?_, fun a' k' hk' p hp => ?_⟩
  · have hpm := pad_bare S.codes T.shape (g_bare A) p hp
    rw [hpm, OnBytes.Slice.addKept_g _ _ _ _ _ _ _ _ hne, OnBytes.Slice.coefAt_empty,
      stretch_off _ _ _ _ _ fun i => hpad (k.oldPadAt + i) p hp (by rw [hpm, A.restMain]),
      add_zero]
  · obtain ⟨s', hs', K'⟩ := kept_shape A a' k' hk'
    obtain ⟨ho', hg'⟩ := copy_at A hFr a' k' hk'
    have hpm := pad_bare S.codes k'.shape K'.newBare p hp
    rw [hpm]
    by_cases e : a' = a
    · subst e
      have es : s' = s := Option.some.inj (hs'.symm.trans hs)
      have eo : anew.getD a' noId = o := Option.some.inj (ho'.symm.trans ho)
      rw [eo, OnBytes.Slice.addKept_new _ _ _ _ _ _ _ _ hne
        (Johnson.Top.H.padPlaces_nodup S.codes s), OnBytes.Slice.coefAt_empty, if_pos, add_zero]
      rw [pads_same S.codes s' k'.shape K', es] at hp
      exact List.mem_map.2 ⟨p, hp, rfl⟩
    · have hdiff : anew.getD a' noId ≠ o := by
        intro h
        apply e
        have hlt : a' < anew.toList.length := (List.getElem?_eq_some_iff.1 ho').1
        exact (List.getElem?_inj hlt hap.2.1 (by rw [ho', ho, h]))
      rw [OnBytes.Slice.addKept_other _ _ _ _ _ _ _ _ _ .main (fun h => hdiff h.1)
        (fun h => by simp [h.1] at hg'), OnBytes.Slice.coefAt_empty]

/-- The index bits of g's table that takes the rest, in a frame. -/
theorem restBits_eq (A : AtSwitch S old T g anew W V) {Fr : SwitchFrame}
    (hFr : switchFrame S old T g anew = some Fr) :
    Fr.restBits = switchRowBits T .main + (S.codes.base.getD T.shape.code default).logEll := by
  have I := frameIs hFr
  have h := size_g A
  unfold OnBytes.Means.tableSize at h
  rw [I.restBits, A.restMain]
  split at h
  · exact Nat.pow_right_injective (le_refl 2) h
  · exact absurd h.symm (Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos _))

/-- A place of g's pad lies inside g's main table. -/
theorem gpad_inside (A : AtSwitch S old T g anew W V) (p : PadPlace)
    (hp : p ∈ padPlaces S.codes T.shape) :
    p.index < 2 ^ (switchRowBits T .main + (S.codes.base.getD T.shape.code default).logEll) := by
  have F := A.target
  obtain ⟨place, h1, h2⟩ := Johnson.Top.H.pad_index_at S.codes T.shape (g_bare A) F.rows p hp
  have hRr := SwitchPlaces.le_two_pow_ceilLog2' T.shape.mainRows
  have hrows := F.rows
  have hm : p.index % 2 ^ ceilLog2 T.shape.mainRows = T.shape.mainRows - 1 := by
    rw [h2, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have hd : p.index / 2 ^ ceilLog2 T.shape.mainRows = place := by
    rw [h2, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (by omega),
      Nat.zero_add]
  exact VerifiableInference.Desc.First.K2Hands.lt_pow_of _ _ T.shape.mainRows _ _
    (by show p.index % 2 ^ ceilLog2 T.shape.mainRows < _; omega) hRr
    (by show p.index / 2 ^ ceilLog2 T.shape.mainRows < _; rw [hd]; exact h1)
    (SwitchPlaces.le_two_pow_ceilLog2' _)

/-- **A mask row's generator row.** -/
theorem spares_mask (A : AtSwitch S old T g anew W V) {Fr : SwitchFrame}
    (hFr : switchFrame S old T g anew = some Fr)
    (hlog : (S.codes.mask.getD old.maskCode default).logN ≤ 32) (j : Nat) (hj : j < 2) (x : Nat)
    (t : E) : Spares S T g anew (coefAt (genMask Fr x j t)) := by
  have I := frameIs hFr
  obtain ⟨_, _, _, hpad⟩ := SwitchPlaces.places_of_check A.check
  obtain ⟨xo, hxo, hxs⟩ := Option.map_eq_some_iff.1 A.seated.carrying
  have M := VerifiableInference.Desc.First.K2Hands.maskAt_of_check S old T g anew Fr hFr A.check
    xo hxo hxs (by rw [I.zk]; exact hlog) j hj
  refine ⟨fun p hp => ?_, fun a' k' hk' p _ => ?_⟩
  · have hpm := pad_bare S.codes T.shape (g_bare A) p hp
    have hoff : ∀ a i, Fr.places.get (a + i) ≠ p.index := fun a i => by
      rw [I.places]
      exact hpad (a + i) p hp (by rw [hpm, A.restMain])
    rw [H2K.Lift.genMask_at Fr j _ _ M x t g p.part p.index
      (by rw [restBits_eq A hFr]; exact gpad_inside A p hp),
      stretch_off _ _ _ _ _ (hoff _), stretch_off _ _ _ _ _ (hoff _)]
    simp
  · exact mask_off Fr j _ _ M x t _ _ _ (by rw [I.gIs]; exact (copy_at A hFr a' k' hk').2)

/-- **No row that the switch lays has, read in the field, a coefficient at a new pad's place.** -/
theorem padsUnread (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : Nat)
    (anew : Array Nat) (pos : Positions) (y : Array E) (rows : List OnBytes.Row)
    (check : switchTargetCheck S old T = true) (restMain : T.rest.part = .main)
    (fits : OldFits S old) (keptPos : ∀ k ∈ T.kept.toList, 0 < k.shape.mainRows)
    (seated : SeatedAt S old T g anew) (lengths : S.codes.lengthsOk = true)
    (hlogC : (S.codes.base.getD old.code default).logN ≤ 32)
    (hlogZ : (S.codes.mask.getD old.maskCode default).logN ≤ 32)
    (hx : ∀ x ∈ pos.all.toList, x < 2 ^ (S.codes.base.getD old.code default).logN)
    (hrows : Own.swRows S old T g anew pos y = some rows) :
    ∀ r ∈ rows, Spares S T g anew (coefAt r) := by
  intro r hr
  have A := atPublic check restMain fits keptPos seated lengths
  obtain ⟨Fr, carried, L⟩ := VerifiableInference.Desc.First.K2Hands.laid_of
    (show switchRows S old T g anew pos y = some rows from hrows)
  have hFr := L.frame
  have hm := A.target.masks
  have hpow : (S.codes.base.getD old.code default).ell =
      2 ^ (S.codes.base.getD old.code default).logEll := A.target.power.2.symm
  rw [L.rows, List.cons_append, List.mem_cons, List.mem_append] at hr
  rcases hr with hr | hr | hr
  · obtain ⟨ks, hks, hc⟩ :=
      (VerifiableInference.Desc.First.K2Hands.switchCarried_iff Fr old carried).1 L.claim
    obtain ⟨_, hmem⟩ := Lists.mapM_mem _ _ _ hks
    rw [hr, hc, carried_pieces A hFr ks]
    refine Spares.add (Spares.add (Spares.add (spares_lift A hFr _ A.fits.mainVars) ?_)
      (spares_stretch A hFr _ _ _)) (spares_stretch A hFr _ _ _)
    refine Spares.sum (fun x : KeptForm × KeptPlace => coefAt (Fr.addKept {} x.2 x.1.c)) _ ?_
    intro x hxm
    obtain ⟨_, a, hk⟩ := place_at x.1 x.2 (hmem x hxm)
    exact spares_addKept A hFr a x.2 hk _
  · obtain ⟨k, hk, hr⟩ := List.mem_flatMap.1 hr
    obtain ⟨sample, _, rfl⟩ := List.mem_map.1 hr
    obtain ⟨a, ha⟩ := List.mem_iff_getElem?.1 hk
    exact spares_addKept A hFr a k ha (formOn sample)
  · obtain ⟨x, hxm, hr⟩ := List.mem_flatMap.1 hr
    obtain ⟨i, _, hlt, hget⟩ := listed_at pos x (L.listed x hxm)
    have hxin : x ∈ pos.all.toList := by
      rw [← hget, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
      exact Array.getElem_mem_toList hlt
    have hxlt := hx x hxin
    rw [H2K.Lift.switchGenerators_all, List.cons_append, List.mem_cons, List.mem_append] at hr
    rcases hr with hr | hr | hr
    · rw [hr, main_pieces A hFr hlogC x hxlt]
      exact Spares.add (spares_lift A hFr _ (tensor_vars _ x hpow)) (spares_stretch A hFr _ _ _)
    · obtain ⟨a, k, b, hk, hb, hr⟩ := mem_keptFrom Fr x _ r Fr.kept 0 hr
      rw [hr]
      simp only [Nat.zero_add]
      rw [keptGen_pieces A hFr hlogC a k hk b hb x hxlt]
      exact Spares.add (spares_addKept A hFr a k hk _) (spares_stretch A hFr _ _ _)
    · obtain ⟨jj, hjj, hr⟩ := List.mem_map.1 hr
      have hj2 : jj < 2 := by
        have := List.mem_range.1 hjj
        omega
      rw [← hr]
      exact spares_mask A hFr hlogZ jj hj2 x _

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.spares_lift
#print axioms VerifiableInference.Desc.K2.Honest.spares_stretch
#print axioms VerifiableInference.Desc.K2.Honest.spares_addKept
#print axioms VerifiableInference.Desc.K2.Honest.padsUnread
