-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoClaimsMeet.lean.
The forms of the byte-level verifier's lookup are worth the flat function's list of claims, member
by member.

OnBytes/Tie/Pv/Lookup/Forest/FoClaims.lean lists the claims of a sub-proof's lookup as values that
must be 0, from the record of end values (`Fo.endsOf`). This file ties the forms that the
byte-level routines make to that list, as equations of values: so it sees each sign, the order
inside the record's forms and the order inside the three forms of `Forest.planeClaims`.

Main names:
  `LedMask`, `onMasks_rowU`, `onMasks_rows`, `onMasks_keyTop`: every row of the record, and the form
    at
    the end of the key side, names entries of the mask row alone.
  `rows_claim`: the forms of the record g that the lookup's routine returns: form number i is worth
    the residue of row number i of the record of end values.
  `planes_claim`: the three forms of `Forest.planeClaims` are worth `claimLeaves`, `claimBits` and
    `countK`, at the values of the caller's forms.
  `claims_port`: the values of g's forms, then of the three, then of the form of `Forest.join`, are
    the list `claimsOf`. The order of these three stretches is set by the statement, after
    `claimsOf`; no run stands behind it. The sub-proofs add them otherwise: Attention.claims
    (OnBytes/Model/Attention.lean) and HTailF2.objectsF (OnBytes/Model/Tail.lean) add the join
    before the planes' three.
All hold in every later state of the sub-proof, for every reading ν of the places and all entries of
virtual rows; the mask row is ν on the mask's places. The values of the caller's forms stand in the
statements as letters.

Under: `HeardIs` (the record g, with a state F0, holds the flat function's end values), and a run of
`Forest.planeClaims` from a state F later than F0 that returns; the shape is
lawful (`FoNums.ok`); the caller's routines are quiet; the state's arrays have their sizes; the
caller
hands in as many key forms as there are calls.

Limits: that a run of the lookup's routine leaves a record with `HeardIs` is not stated here. What
  the
caller's forms are worth is the caller's to state. Not claimed: anything on soundness, completeness
or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPlaneHeard
import OnBytes.Tie.Pv.Lookup.Forest.FoClaimsPort

set_option autoImplicit false

namespace Cb.Fo.PlaneClaims
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.PscTie _root_.Fo

section
variable {K : Type} [CommRing K]

/-- All places of the record are entries of the mask row. -/
def LedMask (L : Led _root_.Fo.Pl) : Prop :=
  (∀ r t, ∃ j, L.pw r t = _root_.Fo.Pl.mask j) ∧ (∃ j, L.c0 = _root_.Fo.Pl.mask j) ∧ ∀ a, ∃ j,
      L.sh a = _root_.Fo.Pl.mask j

theorem ledMask_ledF (jLK : ℕ) (pl : TwNums.Sizes.Ent → ℕ) : LedMask (ledF jLK pl) :=
  ⟨fun _ _ => ⟨_, rfl⟩, ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩⟩

theorem onMasks_rowU {L : Led _root_.Fo.Pl} (hL : LedMask L) (dg : List ℕ) (s : Sc K)
    {inc : List (_root_.Fo.Pl × K)}
    (hi : OnMasks inc) (S0 : K) : OnMasks (rowU L dg s inc S0).cf :=
  onMasks_append (onMasks_hide L hL.1 hL.2.1 dg s.xs) (onMasks_scale _ hi)

omit [CommRing K] in
theorem onMasks_one {p : _root_.Fo.Pl} (hp : ∃ j, p = _root_.Fo.Pl.mask j) (x : K) : OnMasks
    [(p, x)] := fun pc h => by
  rw [List.mem_singleton.mp h]
  exact hp

theorem onMasks_top {led : ℕ → Led _root_.Fo.Pl} (hl : ∀ l, LedMask (led l))
    {inc0 : List (_root_.Fo.Pl × K)}
    (h0 : OnMasks inc0) : ∀ l : List (Sc K × K), OnMasks (incTop led inc0 l)
  | [] => h0
  | s :: rest => fun pc hpc => by
    have : pc ∈ lineForm (led rest.length) s.1 s.2 := hpc
    unfold lineForm at this
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl
    · exact (hl _).2.2 0
    · exact (hl _).2.2 1

theorem onMasks_lv {led : ℕ → Led _root_.Fo.Pl} (hl : ∀ l, LedMask (led l)) (g : ℕ)
    {inc0 : List (_root_.Fo.Pl × K)}
    (h0 : OnMasks inc0) : ∀ l : List (Sc K × K), ∀ r ∈ lvRowsR led g inc0 l, OnMasks r.cf
  | [], _, h => absurd h List.not_mem_nil
  | s :: rest, r, h => by
    rcases List.mem_cons.mp h with rfl | h'
    · exact onMasks_rowU (hl _) _ _ (onMasks_top hl h0 rest) _
    · exact onMasks_lv hl g h0 rest r h'

theorem onMasks_tie {P : Nums _root_.Fo.Pl K} (hl : ∀ l, LedMask (P.ledTie l)) (lam : K) :
    ∀ l : List (Sc K), ∀ r ∈ tieRowsR P lam l, OnMasks r.cf
  | [], _, h => absurd h List.not_mem_nil
  | s :: rest, r, h => by
    rcases List.mem_cons.mp h with rfl | h'
    · refine onMasks_rowU (hl _) _ _ ?_ _
      cases rest with
      | nil => exact OnMasks.nil
      | cons s' rest' => exact onMasks_one ((hl _).2.2 _) _
    · exact onMasks_tie hl lam rest r h'

variable (h : Forest.Shape) (lm jLK : ℕ) (rsK : Rounds K)

theorem onMasks_fK : OnMasks (fK (forN h lm jLK rsK) (forTrace h lm jLK rsK)) :=
  onMasks_one ⟨_, rfl⟩ _

/-- The form at the end of the key side. -/
theorem onMasks_keyTop : OnMasks (endsOf h lm jLK rsK).cEndInc :=
  onMasks_top (fun _ => ledMask_ledF _ _) (onMasks_fK h lm jLK rsK) _

theorem onMasks_incT0 (θ : K) (t : Trace K) : OnMasks (incT0 (numsF h lm jLK θ) t) := by
  intro pc hpc
  unfold incT0 at hpc
  obtain ⟨th, _, h2⟩ := List.mem_flatMap.mp hpc
  refine onMasks_scale _ (fun q hq => ?_) pc h2
  unfold formT at hq
  split_ifs at hq
  · rw [List.mem_singleton.mp hq]
    exact ⟨_, rfl⟩
  · rw [List.mem_singleton.mp hq]
    exact ⟨_, rfl⟩
  · exact absurd hq List.not_mem_nil

/-- Every row of the record of end values names entries of the mask row alone. -/
theorem onMasks_rows : ∀ r ∈ (endsOf h lm jLK rsK).rows, OnMasks r.cf := by
  intro r hr
  unfold Ends.rows at hr
  simp only [List.mem_append, List.mem_singleton] at hr
  rcases hr with ((hr | hr) | hr) | hr
  · have hr' : r ∈ (tieRowsR (forN h lm jLK rsK) (forTrace h lm jLK rsK).lam
        (forTrace h lm jLK rsK).tie.reverse).reverse := hr
    exact onMasks_tie (fun _ => ledMask_ledF _ _) _ _ r (List.mem_reverse.mp hr')
  · have hr' : r ∈ (lvRowsR (forN h lm jLK rsK).ledK 0
        (fK (forN h lm jLK rsK) (forTrace h lm jLK rsK))
        (forTrace h lm jLK rsK).keys.reverse).reverse := hr
    exact onMasks_lv (fun _ => ledMask_ledF _ _) _ (onMasks_fK h lm jLK rsK) _ r
      (List.mem_reverse.mp hr')
  · have hr' : r ∈ (lvRowsR (forN h lm jLK rsK).ledT (forN h lm jLK rsK).w
        (incT0 (forN h lm jLK rsK) (forTrace h lm jLK rsK))
        (forTrace h lm jLK rsK).tabl.reverse).reverse := hr
    exact onMasks_lv (fun _ => ledMask_ledF _ _) _ (onMasks_incT0 h lm jLK _ _) _ r
      (List.mem_reverse.mp hr')
  · have hr' : r = rowBitU (forN h lm jLK rsK) (forTrace h lm jLK rsK) := hr
    rw [hr']
    exact onMasks_rowU (ledMask_ledF _ _) _ _ OnMasks.nil _

end

section
variable {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K)

/-- **The forms that the lookup's routine returns, number by number.** -/
theorem rows_claim (g : Heard) (lm jLK : ℕ) (rsK : Rounds K) (F : Fork)
    (hI : HeardIs ρ g F (endsOf g.shape lm jLK rsK)) (H : Fork) (hH : Later F H)
        (ν : _root_.Fo.Pl → K)
    (entry : ℕ → ℕ → ℕ → K) :
    (g.rows.toList.map fun a => a.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)) =
      (endsOf g.shape lm jLK rsK).rows.map (rowRes ν) := by
  refine List.ext_getElem (by simp [hI.nRows]) fun i h1 h2 => ?_
  have hi : i < g.rows.size := by simpa using h1
  have hi' : i < (endsOf g.shape lm jLK rsK).rows.length := by simpa using h2
  have e := hI.rows i hi H hH (fun j => ν (.mask j)) entry
  rw [List.getElem_map, List.getElem_map, Array.getElem_toList]
  have e1 : g.rows.getD i {} = g.rows[i] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
    rfl
  have e2 : (endsOf g.shape lm jLK rsK).rows.getD i ⟨[], 0⟩ =
      (endsOf g.shape lm jLK rsK).rows[i] := List.getD_eq_getElem _ _ hi'
  rw [e1, e2] at e
  rw [e]
  unfold rowRes
  rw [evalL_muOf (onMasks_rows g.shape lm jLK rsK _ (List.getElem_mem hi')) ν]

/-- **The three forms that read the planes, at the values of the caller's forms.** -/
theorem planes_claim (g : Heard) (lm jLK : ℕ) (rsK : Rounds K) (bit : ℕ → ℕ → SubM Aff)
    (pin : ℕ → SubM Aff) (hb : ∀ e col, Quiet (bit e col)) (hp : ∀ col, Quiet (pin col))
    (F0 F G : Fork) (c c' : Ctx) (rows : Array Aff)
    (h : planeClaims g lm bit pin F c = .ok ((rows, G), c'))
    (hI : HeardIs ρ g F0 (endsOf g.shape lm jLK rsK)) (h0 : Later F0 F)
    (hok : FoNums.ok g.shape = true) (hF : Sized F) :
    c' = c ∧ Later F G ∧ Sized G ∧ G.next = F.next ∧
      ∀ H, Later G H → ∀ (ν : _root_.Fo.Pl → K) (entry : ℕ → ℕ → ℕ → K),
        (rows.toList.map fun a => a.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)) =
          [claimLeaves g.shape lm jLK rsK ν fun col =>
              (got (bit 0 col) F c).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry),
            claimBits g.shape lm jLK rsK ν fun col =>
              (got (bit 1 col) F c).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry),
            Pin.countK g.shape lm fun col =>
              (got (pin col) F c).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)] := by
  obtain ⟨mu, zd, rs, hRan, _, hdg⟩ := hI.lvRan
  have hdg' : dgOf zd = dgE (numsF g.shape lm jLK (thetaOf g.shape rsK)) := by
    have e1 : dgOf zd = (zd.map fun p => p.2).map (· - 1) := by
      unfold dgOf
      rw [List.map_map]
      rfl
    rw [e1, hdg, List.map_map]
    have e2 : ((fun x : ℕ => x - 1) ∘ fun x => x + 1) = id := funext fun x => by simp
    rw [e2, List.map_id]
    rfl
  have hL : LedAt (ledF jLK (FoNums.S g.shape).pEndC) (jLK + (FoNums.S g.shape).fEnd)
      (dgOf zd) 0 := by
    rw [hdg', (nums_led g.shape jLK lm (thetaOf g.shape rsK)).2.2.2.2.2.2]
    exact ledAt_end g.shape jLK
  have hv : g.shape.v < 64 := lt_trans (Cb.Fo.ok_parts hok).1.2.2.2.2.1 (by decide)
  obtain ⟨_, a1, a2, a3, a4, r0, r1, r2, hr, hval⟩ :=
    planeClaims_rows ρ g lm bit pin hb hp F0 F G c c' rows h hRan hI.lvStart hI.lvTg h0 hF hL hv []
  refine ⟨a1, a2, a3, a4, fun H hH ν entry => ?_⟩
  obtain ⟨v0, v1, v2⟩ := hval H hH (fun j => ν (.mask j)) entry
  rw [hr]
  show [r0.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry),
    r1.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry),
    r2.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)] = _
  rw [v0, v1, v2]
  have hM : OnMasks (hide (ledF jLK (FoNums.S g.shape).pEndC)
      (dgE (numsF g.shape lm jLK (thetaOf g.shape rsK))) (endsOf g.shape lm jLK rsK).lvXs ++
        scale (endsOf g.shape lm jLK rsK).lvEps (endsOf g.shape lm jLK rsK).lvInc) :=
    onMasks_append (onMasks_hide _ (fun _ _ => ⟨_, rfl⟩) ⟨_, rfl⟩ _ _)
      (onMasks_scale _ (onMasks_incTop g.shape lm jLK _ _))
  have hA : (endsOf g.shape lm jLK rsK).leavesA =
      leavesAK g.shape (endsOf g.shape lm jLK rsK).theta (endsOf g.shape lm jLK rsK).alpha
        (endsOf g.shape lm jLK rsK).zb0 :=
    tab_ext_g g.shape hok _ _ _ (by
      rw [byVar_len]
      exact ordE_len g.shape)
  have hS := (hI.sBitAt H ((h0.trans a2).trans hH)).2 (fun j => ν (.mask j)) entry
  rw [Aff.value_slot, evalL_muOf (onMasks_one ⟨_, rfl⟩ _) ν] at hS
  refine congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ rfl)
  · rw [hdg', hI.lvEps, hI.lvFin, show g.leaves.r.toList.map ρ.val = _ from hI.lvXs, hI.leavesA,
      show rdL ρ g.zb0 = _ from hI.zb0, hA]
    unfold rowRes rowU claimLeaves
    simp only
    rw [evalL_muOf hM ν, evalL_append, evalL_scale]
    show _ = evalL ν _ + _ * evalL ν _ + _ - _
    rw [show hide (forN g.shape lm jLK rsK).ledE (dgE (forN g.shape lm jLK rsK))
        (endsOf g.shape lm jLK rsK).lvXs =
      hide (ledF jLK (FoNums.S g.shape).pEndC) (dgE (numsF g.shape lm jLK (thetaOf g.shape rsK)))
        (endsOf g.shape lm jLK rsK).lvXs from rfl]
    ring
  · rw [hS, show rdL ρ g.zb1 = _ from hI.zb1]
    unfold claimBits
    show _ - ((endsOf g.shape lm jLK rsK).bitBe * ν
        (_root_.Fo.Pl.mask (endsOf g.shape lm jLK rsK).sBit) + 0) -
      _ = _
    rw [add_zero]
    rfl

/-- **The byte-level verifier's forms are worth the list of claims, number by number.** -/
theorem claims_port (g : Heard) (lm jLK : ℕ) (rsK : Rounds K) (bit : ℕ → ℕ → SubM Aff)
    (pin : ℕ → SubM Aff) (hb : ∀ e col, Quiet (bit e col)) (hp : ∀ col, Quiet (pin col))
    (F0 F G : Fork) (c c' : Ctx) (rows : Array Aff)
    (h : planeClaims g lm bit pin F c = .ok ((rows, G), c'))
    (hI : HeardIs ρ g F0 (endsOf g.shape lm jLK rsK)) (h0 : Later F0 F)
    (hok : FoNums.ok g.shape = true) (hF : Sized F) (KF : Array Aff) (hs : KF.size = g.shape.NC)
        (H : Fork) (hH : Later G H)
    (ν : _root_.Fo.Pl → K) (entry : ℕ → ℕ → ℕ → K) :
    ((g.rows.toList ++ rows.toList ++ [joinForm g KF]).map fun a =>
        a.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)) =
      claimsOf g.shape lm jLK rsK ν
        (fun col => (got (bit 0 col) F c).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry))
        (fun col => (got (bit 1 col) F c).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry))
        (fun col => (got (pin col) F c).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry))
        (fun k => (KF.getD k (Aff.ofConst zeroE)).value ρ
          (H.worldOf ρ (fun j => ν (.mask j)) entry)) := by
  obtain ⟨_, a2, _, _, hpl⟩ :=
    planes_claim ρ g lm jLK rsK bit pin hb hp F0 F G c c' rows h hI h0 hok hF
  have hcE : g.cEnd.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
      AffK.val ((endsOf g.shape lm jLK rsK).cEndF, (endsOf g.shape lm jLK rsK).cEndC) ν := by
    rw [(hI.cEnd H ((h0.trans a2).trans hH)).2 (fun j => ν (.mask j)) entry,
      evalL_muOf (onMasks_keyTop g.shape lm jLK rsK) ν]
    show _ = evalL ν (scale (-1) (endsOf g.shape lm jLK rsK).cEndInc) + _
    rw [evalL_scale]
    ring
  have hJ := join_claim ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) g KF hok hs lm jLK rsK ν
    hI.theta hI.alpha (fun k _ => by
      rw [rdL_getD, show rdL ρ g.e = _ from hI.e]) hI.zy hcE
  unfold claimsOf
  rw [List.map_append, List.map_append, rows_claim ρ g lm jLK rsK F0 hI H ((h0.trans a2).trans hH) ν
      entry,
    hpl H hH ν entry, List.map_singleton, hJ, List.append_assoc]
  rfl

end
end Cb.Fo.PlaneClaims
