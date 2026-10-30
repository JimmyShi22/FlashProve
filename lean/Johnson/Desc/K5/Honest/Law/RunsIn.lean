-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/RunsIn.lean: CONDITIONAL: TWO HEARINGS OF ONE SHAPE GIVE THE RUNS OF AN
ATTENTION SEGMENT's CLAIMS INPUTS THAT MEET `ShIn` (Johnson/Desc/K5/Honest/Law/RunsReaders.lean).
And the row that a masked sumcheck leaves has a shape that is a function of the sumcheck's shape.
Definitions, and statements with their proofs.

Main names:
  `lenH`, `hiding_lenH`, `zip_degrees`   how many coefficients the hiding polynomial has at the
    challenges: of the variables' numbers of coefficients and the number of challenges
  `affSh_onSlots`, `sumRowSh`, `affSh_formOf`   **the shape of the row that a sumcheck leaves
    (formOf, Johnson/Desc/First/Att/LeftP.lean, with no kept form) is sumRowSh of the sumcheck's
    shape**
  `forall₂_and_map`, `get_of_map_eq`   tools on lists
  `lensOne_of_sh`   two hearings of one shape have one set of lengths (the library's `LensOne`,
    Att/Claims/SameHeard.lean)
  `rows_sh`, `left_sh`   the rows' shapes, of what was heard
  `shIn_of`   **`ShIn` at the inputs that the two makers make of two hearings of one shape**

`shIn_of` IS CONDITIONAL on: the key points have one set of lengths at both; what the segment's own
rounds handed on has one shape at both; the two makers return at both.
Limits. No field element is compared. Nothing says that a maker returns anywhere.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.RunsClaims
import Johnson.Desc.K5.Honest.Law.TabsReturns
import Johnson.Desc.First.Att.Claims.SameHeard
import Johnson.Desc.First.Att.K5LeftAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo UnitG ParC LookIn Pts TablesP Heard Left RemP ScoreP
  SumP)
open VerifiableInference.Desc.First.Att.P.Runs (In)
open VerifiableInference.Desc.First.Shape (AffSh affSh affSh_addMul affSh_sub HeardAll heardAll
  Heard5Sh heard5Sh SumSh sumSh)
open K5Law (Same SameRem SameScore LensOne forall₂_of_get forall₂_getElem? forall₂_map_eq)

/-! ## 1 The row that a sumcheck leaves -/

/-- How many coefficients the hiding polynomial has, of its variables' numbers of coefficients (the
shape's field `degrees` holds these numbers, each one more than a degree): the last variable alone
has a constant. -/
def lenH : List Nat → Nat
  | [] => 0
  | [d] => d
  | d :: e :: rest => (d - 1) + lenH (e :: rest)

theorem hiding_lenH : ∀ l : List (MaskedSum.Var × E),
    (MaskedSum.hidingAt l).1.length = lenH (l.map (·.1.d))
  | [] => rfl
  | [(v, r)] => powers_len r v.d oneE
  | (v, r) :: y :: rest => by
    show (MaskedSum.powersFrom r (v.d - 1) _ ++ (MaskedSum.hidingAt (y :: rest)).1).length = _
    rw [List.length_append, powers_len, hiding_lenH (y :: rest)]
    rfl

/-- The variables' numbers of coefficients along the challenges. -/
theorem zip_degrees : ∀ (vs : List MaskedSum.Var) (r : List E),
    (vs.zip r).map (·.1.d) = (vs.map (·.d)).take r.length
  | [], _ => by simp
  | _ :: _, [] => by simp
  | v :: vs, _ :: r => by
    show v.d :: (vs.zip r).map (·.1.d) = _
    rw [zip_degrees vs r]
    rfl

theorem affSh_onSlots : ∀ (u : List E) (f : Aff) (first : Nat),
    affSh (MaskedSum.onSlots f first u) =
      (affSh f).append (AffSh.mk [] (List.range' first u.length))
  | [], f, first => by
    show affSh f = AffSh.mk ((affSh f).ents ++ []) ((affSh f).slots ++ [])
    rw [List.append_nil, List.append_nil]
    rfl
  | x :: u, f, first => by
    have e : MaskedSum.onSlots f first (x :: u) =
        MaskedSum.onSlots (Aff.addMul f (Aff.slot first) x) (first + 1) u := rfl
    rw [e, affSh_onSlots u, affSh_addMul]
    show AffSh.mk (((affSh f).ents ++ []) ++ [])
        (((affSh f).slots ++ [first]) ++ List.range' (first + 1) u.length) =
      AffSh.mk ((affSh f).ents ++ []) ((affSh f).slots ++ List.range' first (u.length + 1))
    rw [List.range'_succ]
    simp only [List.append_assoc, List.append_nil, List.cons_append, List.nil_append]

/-- **The shape of the row that a sumcheck leaves**: the entries of the form that the sum is claimed
to equal; the slots of the hiding polynomial's coefficients, then that form's. -/
def sumRowSh (s : SumSh) : AffSh :=
  AffSh.mk s.start.ents
    (List.range' s.first (lenH (s.degrees.take s.r)) ++ s.start.slots)

theorem affSh_formOf (h : MaskedSum.Heard) (S0 : E) :
    affSh (P.formOf h S0 {}) = sumRowSh (sumSh h) := by
  show affSh (Aff.addMul (Aff.addMul (MaskedSum.onSlots (Aff.ofConst _) h.first
    (MaskedSum.hidingAt (h.vars.zip h.r)).1) (Aff.ofConst h.target - h.start) _) {} _) = _
  rw [affSh_addMul, affSh_addMul, affSh_onSlots, affSh_sub, hiding_lenH, zip_degrees]
  show AffSh.mk ((([] ++ []) ++ ([] ++ (affSh h.start).ents)) ++ [])
    ((([] ++ List.range' h.first _) ++ ([] ++ (affSh h.start).slots)) ++ []) = _
  simp only [List.nil_append, List.append_nil]
  rfl

/-! ## 2 Tools on lists -/

theorem forall₂_and_map {α β γ : Type} {R : α → β → Prop} {f : α → γ} {f' : β → γ} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → l.map f = l'.map f' →
      List.Forall₂ (fun a b => R a b ∧ f a = f' b) l l'
  | _, _, .nil, _ => .nil
  | _, _, .cons h t, e => by
    simp only [List.map_cons, List.cons.injEq] at e
    exact .cons ⟨h, e.1⟩ (forall₂_and_map t e.2)

theorem get_of_map_eq {α β γ : Type} {l : List α} {l' : List β} {f : α → γ} {f' : β → γ}
    (e : l.map f = l'.map f') {n : Nat} {a : α} (ha : l[n]? = some a) :
    ∃ b, l'[n]? = some b ∧ f a = f' b := by
  have k := congrArg (fun x => x[n]?) e
  simp only [List.getElem?_map, ha, Option.map_some] at k
  cases hb : l'[n]? with
  | none =>
    rw [hb] at k
    cases k
  | some b =>
    rw [hb] at k
    exact ⟨b, rfl, Option.some.inj k⟩

/-! ## 3 Two hearings of one shape -/

section
variable {gl gl' : Forest.Heard} {h h' : Heard}

theorem chal_size (x : MaskedSum.Heard) : (P.chal x).size = (sumSh x).r - 1 := by
  show (x.r.dropLast.toArray).size = x.r.length - 1
  rw [List.size_toArray, List.length_dropLast]

/-- **Two hearings of one shape have one set of lengths.** -/
theorem lensOne_of_sh (ez : gl.zk.toList.map (·.size) = gl'.zk.toList.map (·.size))
    (eH : heard5Sh h = heard5Sh h') : LensOne gl.zk gl'.zk h h' := by
  have es : h.scores.toList.map (fun o => (o.1, sumSh o.2)) =
      h'.scores.toList.map (fun o => (o.1, sumSh o.2)) := congrArg Heard5Sh.scores eH
  refine ⟨fun q => by rw [zk_size, zk_size, ez], fun n o o' ho ho' => ?_, ?_, ?_, ?_⟩
  · rw [← Array.getElem?_toList] at ho ho'
    obtain ⟨b, hb, e⟩ := get_of_map_eq es ho
    obtain rfl : b = o' := Option.some.inj (hb.symm.trans ho')
    rw [chal_size, chal_size, (Prod.mk.inj e).2]
  · rw [chal_size, chal_size, show sumSh h.atIndex = sumSh h'.atIndex from
      congrArg Heard5Sh.atIndex eH]
  · rw [chal_size, chal_size, show sumSh h.below = sumSh h'.below from congrArg Heard5Sh.below eH]
  · rw [chal_size, chal_size, show sumSh h.on = sumSh h'.on from congrArg Heard5Sh.on eH]

end

/-- A row that `left` makes has the shape of its sumcheck. -/
theorem left_sh {F : Fork} {x : MaskedSum.Heard} {W : Array E} {f : Aff}
    (hf : P.left F x W = some f) : affSh f = sumRowSh (sumSh x) := by
  rw [P.left_spec hf]
  exact affSh_formOf _ _

/-- So has the row of the sumcheck for the key at the index. -/
theorem leftKey_sh {g : Geo} {F : Fork} {x : MaskedSum.Heard} {rho om' : Array E} {f : Aff}
    (hf : P.leftKey g F x rho om' = some f) : affSh f = sumRowSh (sumSh x) := by
  rw [P.leftKey_spec hf]
  exact affSh_formOf _ _

/-- **The units' rows' shapes, of what was heard.** CONDITIONAL on the return of the function of the
forms that are left. -/
theorem rows_sh {g : Geo} {zk : Array (Array E)} {h : Heard} {F : Fork} {l : Left}
    (LI : P.LeftIs g zk h F l) :
    l.scores.toList.map affSh = h.scores.toList.map fun o => sumRowSh (sumSh o.2) := by
  have e1 : (g.scores.toArray.zip h.scores).toList.map (·.2) = h.scores.toList := by
    rw [Array.toList_zip]
    refine List.map_snd_zip ?_
    have := LI.nUnits
    simp only [Array.length_toList]
    omega
  rw [← e1, List.map_map]
  exact (forall₂_map_eq (fun x f r => by
    obtain ⟨W, _, w2⟩ := r
    exact (left_sh w2).symm) LI.scores).symm

/-! ## 4 ShIn -/

/-- **THE INPUTS THAT THE TWO MAKERS MAKE OF TWO HEARINGS OF ONE SHAPE MEET ShIn.** CONDITIONAL on:
the lookup's key points have one set of lengths; one shape of what the segment's own rounds handed
on; the two makers return at both. The two ledgers are free. -/
theorem shIn_of (c : ParC) {gl gl' : Forest.Heard} {h h' : Heard} {F F' : Fork} {p p' : Pts}
    {t t' : TablesP} {lk lk' : LookIn}
    (ez : gl.zk.toList.map (·.size) = gl'.zk.toList.map (·.size))
    (eH : heard5Sh h = heard5Sh h') (hp : P.ptsFrom c.geo gl.zk h F = some p)
    (hp' : P.ptsFrom c.geo gl'.zk h' F' = some p')
    (ht : P.tablesP c.geo c.mats c.nW lk p = some t)
    (ht' : P.tablesP c.geo c.mats c.nW lk' p' = some t') :
    ShIn { g := c.geo, p := p, t := t, zk := gl.zk, iU3 := c.iU3 }
      { g := c.geo, p := p', t := t', zk := gl'.zk, iU3 := c.iU3 } := by
  obtain ⟨L, hL, hP⟩ := Option.bind_eq_some_iff.1 hp
  obtain ⟨L', hL', hP'⟩ := Option.bind_eq_some_iff.1 hp'
  have Z := lensOne_of_sh ez eH
  have S : Same { g := c.geo, p := p, t := t, zk := gl.zk, iU3 := c.iU3 }
      { g := c.geo, p := p', t := t', zk := gl'.zk, iU3 := c.iU3 } :=
    K5Law.same_of_lens rfl rfl hP hP' ht ht' Z
  have LI := P.leftP_spec hL
  have LI' := P.leftP_spec hL'
  have A := K5Law.planes_are hP
  have A' := K5Law.planes_are hP'
  have B := K5Law.points_are hP
  have B' := K5Law.points_are hP'
  have eR : h.remainders = h'.remainders :=
    Array.toList_inj.1 (congrArg Heard5Sh.remainders eH)
  have es : h.scores.toList.map (fun o => (o.1, sumSh o.2)) =
      h'.scores.toList.map (fun o => (o.1, sumSh o.2)) := congrArg Heard5Sh.scores eH
  have es1 : h.scores.toList.map (·.1) = h'.scores.toList.map (·.1) := by
    have k := congrArg (List.map Prod.fst) es
    simpa only [List.map_map, Function.comp_def] using k
  have es2 : h.scores.toList.map (fun o => sumSh o.2) =
      h'.scores.toList.map (fun o => sumSh o.2) := by
    have k := congrArg (List.map Prod.snd) es
    simpa only [List.map_map, Function.comp_def] using k
  have sum : ∀ {x x' : MaskedSum.Heard} {f f' : Aff}, sumSh x = sumSh x' →
      affSh f = sumRowSh (sumSh x) → affSh f' = sumRowSh (sumSh x') →
      ShSum (P.sumOfP x f) (P.sumOfP x' f') := fun e a a' =>
    ⟨congrArg SumSh.sEnd e, a.trans ((congrArg sumRowSh e).trans a'.symm)⟩
  obtain ⟨wl, _, _, _, lE, lM, lO, lF, lK, lH⟩ := LI.rest
  obtain ⟨wl', _, _, _, lE', lM', lO', lF', lK', lH'⟩ := LI'.rest
  refine
    { same := S, iU3 := rfl, planes := ?_, scores := ?_
      s5 := by
        show p.d.s5 = p'.d.s5
        rw [B.s5, B'.s5]
        exact congrArg Heard5Sh.five eH
      sIB := by
        show p.d.sIB = p'.d.sIB
        rw [B.sIB, B'.sIB]
        exact congrArg Heard5Sh.bits eH
      s5h := by
        show p.d.s5h = p'.d.s5h
        rw [B.s5h, B'.s5h]
        exact congrArg Heard5Sh.two eH
      sCl := by
        show p.d.sCl = p'.d.sCl
        rw [B.sCl, B'.sCl]
        exact congrArg Heard5Sh.values eH
      scE := by
        show ShSum p.d.scE p'.d.scE
        rw [B.scE, B'.scE]
        exact sum (congrArg Heard5Sh.division eH) (left_sh lE) (left_sh lE')
      vpm := by
        show ShSum p.d.vpm p'.d.vpm
        rw [B.vpm, B'.vpm]
        exact sum (congrArg Heard5Sh.below eH) (left_sh lM) (left_sh lM')
      vpd := by
        show ShSum p.d.vpd p'.d.vpd
        rw [B.vpd, B'.vpd]
        exact sum (congrArg Heard5Sh.on eH) (left_sh lO) (left_sh lO')
      sM6 := by
        show p.x.sM6 = p'.x.sM6
        rw [B.sM6, B'.sM6]
        exact congrArg Heard5Sh.maxima eH
      scF := by
        show ShSum p.x.scF p'.x.scF
        rw [B.scF, B'.scF]
        exact sum (congrArg Heard5Sh.atIndex eH) (left_sh lF) (left_sh lF')
      scd := by
        show ShSum p.x.scd p'.x.scd
        rw [B.scd, B'.scd]
        exact sum (congrArg Heard5Sh.key eH) (leftKey_sh lK) (leftKey_sh lK')
      scH := by
        show ShSum p.x.scH p'.x.scH
        rw [B.scH, B'.scH]
        exact sum (congrArg Heard5Sh.cells eH) (left_sh lH) (left_sh lH') }
  · -- the plane claims: the library's relation, and one first slot
    show List.Forall₂ ShRem p.planes.toList p'.planes.toList
    obtain ⟨_, c1, _⟩ := K5Law.points_counts hP
    obtain ⟨_, c1', _⟩ := K5Law.points_counts hP'
    have nS : h.scores.size = h'.scores.size := B.nH.symm.trans B'.nH
    refine forall₂_of_get _ _
      (by rw [Array.length_toList, Array.length_toList, c1, c1', eR, nS]) fun n a b ha hb => ?_
    have hsame : SameRem a b := by
      have k := forall₂_getElem? S.p.planes n
      have ha' : p.planes.toList[n]? = some a := ha
      have hb' : p'.planes.toList[n]? = some b := hb
      change K5Law.OptRel SameRem p.planes.toList[n]? p'.planes.toList[n]? at k
      rw [ha', hb'] at k
      exact k
    refine ⟨hsame, ?_⟩
    rw [Array.getElem?_toList] at ha hb
    rcases Nat.lt_or_ge n h.remainders.size with hn | hn
    · obtain ⟨u, hu⟩ : ∃ u, (c.geo.units .kr [.rm, .rd])[n]? = some u :=
        ⟨_, List.getElem?_eq_getElem (by rw [A.nR]; exact hn)⟩
      obtain ⟨s0, h0⟩ : ∃ x, h.remainders[n]? = some x := ⟨_, Array.getElem?_eq_getElem hn⟩
      have h0' : h'.remainders[n]? = some s0 := eR ▸ h0
      rw [A.rem n u s0 hu h0] at ha
      rw [A'.rem n u s0 hu h0'] at hb
      rw [← Option.some.inj ha, ← Option.some.inj hb]
      rfl
    · have hlt : n < p.planes.size := by
        rcases Nat.lt_or_ge n p.planes.size with h1 | h1
        · exact h1
        · rw [Array.getElem?_eq_none h1] at ha
          cases ha
      have hm : n - h.remainders.size < h.scores.size := by omega
      obtain ⟨u, hu⟩ : ∃ u, c.geo.scores[n - h.remainders.size]? = some u :=
        ⟨_, List.getElem?_eq_getElem (by rw [B.nH]; exact hm)⟩
      obtain ⟨o, ho⟩ : ∃ x, h.scores[n - h.remainders.size]? = some x :=
        ⟨_, Array.getElem?_eq_getElem hm⟩
      obtain ⟨o', ho'⟩ : ∃ x, h'.scores[n - h.remainders.size]? = some x :=
        ⟨_, Array.getElem?_eq_getElem (nS ▸ hm)⟩
      obtain ⟨k, _, kc, kp, _⟩ := A.unit _ u o hu ho
      obtain ⟨k', _, kc', kp', _⟩ := A'.unit _ u o' hu ho'
      have e1 : k.claim = n := by rw [kc]; omega
      have e2 : k'.claim = n := by rw [kc', ← eR]; omega
      rw [e1, ha] at kp
      rw [e2, hb] at kp'
      rw [Option.some.inj kp, Option.some.inj kp']
      show o.1 = o'.1
      obtain ⟨x, hx, ex⟩ := get_of_map_eq es1 (by rw [Array.getElem?_toList]; exact ho)
      rw [Array.getElem?_toList] at hx
      obtain rfl : x = o' := Option.some.inj (hx.symm.trans ho')
      exact ex
  · -- the units: the library's relation, one first slot, one first end slot, rows of one shape
    show List.Forall₂ ShScore p.scores.toList p'.scores.toList
    have a0 : p.scores.toList.map (·.s0) = p'.scores.toList.map (·.s0) := by
      rw [K5Law.s0_are B, K5Law.s0_are B', es1]
    have a1 : p.scores.toList.map (·.sc.ends) = p'.scores.toList.map (·.sc.ends) := by
      rw [K5Law.ends_are B, K5Law.ends_are B']
      have k := congrArg (List.map SumSh.sEnd) es2
      simpa only [List.map_map, Function.comp_def] using k
    have a2 : p.scores.toList.map (fun k => affSh k.sc.row) =
        p'.scores.toList.map (fun k => affSh k.sc.row) := by
      have r := congrArg (List.map affSh) (K5Law.rows_are B)
      have r' := congrArg (List.map affSh) (K5Law.rows_are B')
      rw [List.map_map, rows_sh LI] at r
      rw [List.map_map, rows_sh LI'] at r'
      have k := congrArg (List.map sumRowSh) es2
      simp only [List.map_map, Function.comp_def] at k r r'
      rw [r, r', k]
    exact (forall₂_and_map (forall₂_and_map (forall₂_and_map S.p.scores a0) a1) a2).imp
      fun _ _ r => ⟨r.1.1.1, r.1.1.2, r.1.2, r.2⟩

end H2K5.Honest

#print axioms H2K5.Honest.hiding_lenH
#print axioms H2K5.Honest.zip_degrees
#print axioms H2K5.Honest.affSh_onSlots
#print axioms H2K5.Honest.affSh_formOf
#print axioms H2K5.Honest.forall₂_and_map
#print axioms H2K5.Honest.get_of_map_eq
#print axioms H2K5.Honest.chal_size
#print axioms H2K5.Honest.lensOne_of_sh
#print axioms H2K5.Honest.left_sh
#print axioms H2K5.Honest.leftKey_sh
#print axioms H2K5.Honest.rows_sh
#print axioms H2K5.Honest.shIn_of
