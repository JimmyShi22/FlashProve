-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/RunShape.lean: THE LAYERS' OWN ROUNDS (K4): WHAT ITS TWO RUNS OF
CLAIMS, "front" AND "back", OWE ON SHAPES (RunLaw, Johnson/Desc/First/Batch/Shape/ClaimShape.lean),
at the block at the state that the first chain carries (blockAtC, Johnson/Desc/First/K4/AtC.lean).
General laws: nothing is evaluated.

  ownClaim_sh, rowOfSh, rowForm_sh, filledBy   A LATE CLAIM: at a ledger at which the sumcheck is
                  still open it returns; the claim is the sumcheck's row, whose shape is read off
                  the sumcheck's shape; the ledger's shape behind has the sumcheck's own slots
                  filled.
  shownB, shown_of_B   a slot is there and filled, on the ledger's shape.
  backG, formsBack_sh   "back" ON SHAPES: one test (the merge's sumcheck is open: openB,
                  Johnson/Desc/First/Shape/Parts.lean); the four forms' shapes by the listing itself
                  at the blank record (Johnson/Desc/First/Shape/OwnBlank.lean); the ledger's shape
                  behind: the merge's own slots filled, the lookup's join marked as added.
  frontG, formsFront_sh   "front" ON SHAPES: three tests (the row products' end values are shown;
                  their sumcheck is open; the lookup's leaves' sumcheck is open at the ledger's
                  shape behind the first late claim); the forms' shapes by the listing itself at the
                  blank record; the ledger's shape behind.
  owedNorm, seatRun, k4RunG, chainSh_k4Fork, owedNorm_eq, seatRun_follows   a run of K4's at the
                  state, and on the chain's shape.
  claims_are, front_is, back_is   the block states just these two runs.
  PlanEnv         THE TWO RUNS' PREMISE ON THE STATE: the environment of what was heard has the
                  plan's layout and table of scales. The chain's shape sees neither.
  **frontRunLaw**, **backRunLaw**   runG := k4RunG (frontG p.P p.g) | k4RunG (backG p.P.y p.P.sc);
                  pre := PlanEnv p.P. The first: where the lookup states its own claims as a run.

NEITHER pre HOLDS A TEST ON VALUES. Both runs can turn the count of rows that waits: K4's part of
the state reads "some 0" as none and lays none back (owedNorm).
Limits. One direction alone: from a return of the run nothing is concluded unless the run on shapes
returns too. THAT THE RUN ON SHAPES RETURNS AT A SHAPE WHICH THE CHAIN REACHES IS NOT SHOWN, and it
has been evaluated nowhere. The forms' shapes are said by running the listing at a blank record: at
the full size that is as dear as the listing. PlanEnv IS IDLE AS THE PREMISE OF "back": backG's
value does not hang on the layout and the table of scales; the law is weaker than it could be, and
its callers carry a premise that is not needed. "Marked as added" holds where the debt's number lies
in the list: outside it paidB marks nothing and nothing refuses, as the run's Fork.paid does.
Nothing on what a claim is worth. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.K4.Returns.FormsShape
import Johnson.Desc.First.K4.Returns.AtChain
import Johnson.Desc.First.K4.Returns.Points
import Johnson.Desc.First.Shape.OwnBlank
import Johnson.Desc.First.Batch.Shape.ClaimShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt
open OnBytes OnBytes.K.Kc D6.Ret
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer (Pub HPlan2 Own)
open OnBytes.Flat (All2 OptRel)
open OnBytes.PscRun (Sized Filled)
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.First.Shape

/-! ## A late claim, on shapes -/

/-- **A sumcheck's own claim at a ledger at which it is still open**: it returns; the claim is the
sumcheck's row; the ledger's shape behind is the shape in front with the sumcheck's own slots
filled. -/
theorem ownClaim_sh {p : Psc} {G : Fork} (h : Open p G) (S0 : E) (kept : Aff) :
    ∃ H, ownClaim p S0 kept G = some (p.rowForm S0 kept, H) ∧
      ledSh H = (ledSh G).setGot (fillB (ledSh G).got p.first (taken p)) := by
  have hsz : (Array.replicate p.walk.1.length zeroE : Array E).size = taken p := by
    rw [Array.size_replicate, walk_taken h]
  obtain ⟨H, hH, -, -, a3⟩ := hide_of_free (F := G) (first := p.first)
    (v := Array.replicate p.walk.1.length zeroE) h.sized (by rw [hsz]; exact h.fits)
    (fun i hi => h.own _ (by omega) (by rw [hsz] at hi; omega)) (subE zeroE oneE)
  rw [hsz] at a3
  have hv : p.vars.isEmpty = false := by
    cases hq : p.vars.toList with
    | nil => exact absurd hq h.some
    | cons a l =>
      have : p.vars.size ≠ 0 := by
        rw [← Array.length_toList, hq]
        simp
      simpa [Array.isEmpty] using this
  have hb : (!p.rowMade && p.started && !p.vars.isEmpty && p.r.size == p.vars.size) = true := by
    rw [h.noRow, h.started, hv, h.sizes]
    simp
  refine ⟨H, ?_, a3⟩
  have e : Fl.pscRow p S0 kept G [] =
      some ((p.rowForm S0 kept, { p with rowMade := true }), H, []) := by
    unfold Fl.pscRow
    exact bindR (mustR hb _ _) (bindR (changeR hH _) rfl)
  unfold ownClaim
  rw [e]
  rfl

/-- The shape of a sumcheck's row, off the sumcheck's shape and the kept terms' shape: where the
sumcheck is open (rowForm_sh's premise). -/
def rowOfSh (p : PscSh) (kept : AffSh) : AffSh :=
  rowFormSh p.first (takenSh p.degrees) p.start kept

theorem rowForm_sh {p : Psc} {G : Fork} (h : Open p G) (S0 : E) (kept : Aff) :
    affSh (p.rowForm S0 kept) = rowOfSh (pscSh p) (affSh kept) := by
  rw [affSh_rowForm, walk_taken h, ← taken_sh]
  rfl

/-- The ledger's shape with a sumcheck's own slots filled: meant where the sumcheck is open (openB):
backG and frontG call it behind that test alone. -/
def filledBy (p : PscSh) (L : LedSh) : LedSh :=
  L.setGot (fillB L.got p.first (takenSh p.degrees))

/-- The slot is there and filled, on the ledger's shape. -/
def shownB (L : LedSh) (j : Nat) : Bool := decide (j < L.ns) && L.got.getD j false

theorem shown_of_B {F : Fork} {j : Nat} (h : shownB (ledSh F) j = true) :
    ∃ x, F.shown j = some x := by
  unfold shownB at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  have h1 : j < F.ns := h.1
  have h2 : F.gotF.toList.getD j false = true := h.2
  have h3 : F.gotF.getD j false = true := by
    by_cases hl : j < F.gotF.size
    · simpa [Array.getD, List.getD, hl] using h2
    · simp [List.getD, hl] at h2
  unfold Fork.shown
  rw [h3]
  simp [h1]

/-! ## "back" -/

/-- A form as a claim's shape. -/
def claimOfSh (a : AffSh) : ClaimSh := ClaimSh.mk none a []

theorem claimOf_sh (a : Aff) : claimSh (claimOf a) = claimOfSh (affSh a) := rfl

/-- **"back" ON SHAPES**: of the shape of what the hearing left and the ledger's shape: the four
claims' shapes and the ledger's shape behind. y, sc: the plan's layout and table of scales: THE
VALUE DOES NOT HANG ON THEM: the listing "back" reads nothing of the record's environment, into
which alone OwnSh.blank lays them. -/
def backG (y : Layer.Lay) (sc : Layer.Scales) (ow : OwnSh) (L : LedSh) :
    Option (List AffSh × LedSh) :=
  if openB ow.wo.p L then
    some ((back (ow.blank y sc []) (rowOfSh ow.wo.p (AffSh.mk [] [])).blank).map affSh,
      (filledBy ow.wo.p L).setOwed (paidB (filledBy ow.wo.p L).owed ow.H.fo.owedJoin))
  else none

/-- Where "back" on shapes returns, the listing returns, with these shapes. -/
theorem formsBack_sh {o : Own} {F : Fork} {z : List AffSh × LedSh}
    (h : backG o.v.y o.v.sc (ownSh o) (ledSh F) = some z) :
    ∃ fs G, formsBack o F = some (fs, G) ∧ z = (fs.toList.map affSh, ledSh G) := by
  unfold backG at h
  by_cases hb : openB (ownSh o).wo.p (ledSh F) = true
  · rw [if_pos hb] at h
    have hO : Open o.wo.toWsMerged.p F := open_of_B hb
    obtain ⟨H, e, hL⟩ := ownClaim_sh hO o.wo.toWsMerged.fvp {}
    refine ⟨_, _, by unfold formsBack; rw [e]; rfl, ?_⟩
    rw [← Option.some.inj h]
    have hA : OwnAlike o ((ownSh o).blank o.v.y o.v.sc []) :=
      ⟨(ownSh_blank _ _ _ _).symm, rfl, rfl⟩
    have hM : SameSh (o.wo.toWsMerged.p.rowForm o.wo.toWsMerged.fvp {})
        (rowOfSh (ownSh o).wo.p (AffSh.mk [] [])).blank := by
      unfold SameSh
      rw [affSh_blank, rowForm_sh hO]
      rfl
    refine Prod.ext ?_ ?_
    · exact (shapes_eq (back_rel hA hM)).symm
    · show _ = ledSh (H.paid o.H.fo.owedJoin)
      rw [ledSh_paid, hL, ← taken_sh]
      rfl
  · rw [if_neg hb] at h
    cases h

/-! ## "front" -/

/-- **"front" ON SHAPES** (the lookup's own claims not listed): of the plan, the shape of what the
hearing left and the ledger's shape: the claims' shapes and the ledger's shape behind. -/
def frontG (P : Pub) (g : Nat) (ow : OwnSh) (L : LedSh) : Option (List AffSh × LedSh) :=
  if ((List.range (4 * P.y.NI)).all (fun i => shownB L (ow.H.tV.sEnd + i)) &&
      openB ow.H.tV.p L && openB ow.H.fo.leaves (filledBy ow.H.tV.p L)) = true then
    (planesParts (ow.blank P.y P.sc []).v (ow.blank P.y P.sc []).H.fo).bind fun pp =>
      (front false P g (ow.blank P.y P.sc []) (rowOfSh ow.H.tV.p (AffSh.mk [] [])).blank
        (rowOfSh ow.H.fo.leaves (affSh pp.1)).blank).map fun fs =>
          (fs.map affSh,
            (filledBy ow.H.fo.leaves (filledBy ow.H.tV.p L)).setOwed
              (paidB (filledBy ow.H.fo.leaves (filledBy ow.H.tV.p L)).owed ow.H.fo.owedPlanes))
  else none

/-- Where "front" on shapes returns, the listing returns, with these shapes. The environment's
layout and table of scales are the plan's. -/
theorem formsFront_sh {P : Pub} {g : Nat} {o : Own} {F : Fork} {z : List AffSh × LedSh}
    (hy : o.v.y = P.y) (hsc : o.v.sc = P.sc)
    (h : frontG P g (ownSh o) (ledSh F) = some z) :
    ∃ fs G, formsFrontWith false P g o F = some (fs, G) ∧ z = (fs.toList.map affSh, ledSh G) := by
  unfold frontG at h
  split at h
  case isFalse => cases h
  case isTrue hb =>
    simp only [Bool.and_eq_true] at hb
    obtain ⟨⟨b1, b2⟩, b3⟩ := hb
    have hA : OwnAlike o ((ownSh o).blank P.y P.sc []) :=
      ⟨(ownSh_blank _ _ _ _).symm, hy, hsc⟩
    -- the shown values
    obtain ⟨sh, hsh⟩ := mapM_some (fun i => F.shown (o.H.tV.sEnd + i)) (List.range (4 * P.y.NI))
      fun i hi => shown_of_B (List.all_eq_true.1 b1 i hi)
    have hsh' : ((Array.range (4 * P.y.NI)).mapM fun i => F.shown (o.H.tV.sEnd + i)) =
        some sh.toArray := by
      rw [Array.mapM_eq_mapM_toList, Array.toList_range, hsh]
      rfl
    -- the two late claims
    have hO1 : Open o.H.tV.p F := open_of_B b2
    obtain ⟨F1, e1, hL1⟩ := ownClaim_sh hO1 (rowsSummand P.y o.H sh.toArray) {}
    have hL1' : ledSh F1 = filledBy (ownSh o).H.tV.p (ledSh F) := by
      rw [hL1, ← taken_sh]
      rfl
    have hO2 : Open o.H.fo.leaves F1 := open_of_B (by rw [hL1']; exact b3)
    -- the planes' parts
    obtain ⟨pp₀, hpp₀, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨fs₀, hfs₀, hz⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨pp, hpp, rpp⟩ := RtPub.OptRel.of_right (planesParts_rel hA.keys
      (congrArg HeardAll.shape hA.fo) (congrArg HeardAll.sBit hA.fo)) hpp₀
    obtain ⟨F2, e2, hL2⟩ := ownClaim_sh hO2 oneE pp.1
    have hV : SameSh (o.H.tV.p.rowForm (rowsSummand P.y o.H sh.toArray) {})
        (rowOfSh (ownSh o).H.tV.p (AffSh.mk [] [])).blank := by
      unfold SameSh
      rw [affSh_blank, rowForm_sh hO1]
      rfl
    have hLr : SameSh (o.H.fo.leaves.rowForm oneE pp.1)
        (rowOfSh (ownSh o).H.fo.leaves (affSh pp₀.1)).blank := by
      unfold SameSh
      rw [affSh_blank, rowForm_sh hO2, rpp.1]
      rfl
    obtain ⟨fs, hfs, rfs⟩ := RtPub.OptRel.of_right (front_rel P g hA hV hLr) hfs₀
    refine ⟨fs.toArray, F2.paid o.H.fo.owedPlanes, ?_, ?_⟩
    · unfold formsFrontWith
      simp only [hsh', e1, hpp, e2, hfs, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Bool.false_eq_true, if_false]
    · rw [← hz]
      refine Prod.ext ?_ ?_
      · exact (shapes_eq rfs).symm
      · show _ = ledSh (F2.paid o.H.fo.owedPlanes)
        rw [ledSh_paid, hL2, hL1', ← taken_sh]
        rfl

/-! ## The two runs at the state that the first chain carries -/

/-- A count of rows that waits, as K4's part of the state reads it: "some 0" and "none" alike. -/
def owedNorm : Option Nat → Option Nat
  | some r => if r == 0 then none else some r
  | none => none

/-- A run of K4's at the state, as the block at the state lays it (runOf, liftPart, atClaims). -/
def seatRun (name : String) (f : Own → Fork → Option (Array Aff × Fork)) (s : S) :
    Except String (List Claim × S) :=
  ((VerifiableInference.Desc.named "the part is not there" (part? s)).bind fun q =>
    (runOf seatOwn name f q).map fun y => (y.1, setPart s y.2)).map fun y =>
      (y.1.map claimOf, y.2)

/-- **A RUN OF K4's ON THE CHAIN's SHAPE**, of the listing on shapes. -/
def k4RunG (fG : OwnSh → LedSh → Option (List AffSh × LedSh)) (a : ChainSh) :
    Except String (List ClaimSh × ChainSh) :=
  if a.here != 1 then .error "K4's run: no layers' link is open" else
  match a.own, a.led with
  | some ow, some L =>
    match fG ow L with
    | some z => .ok (z.1.map claimOfSh, (a.setLed z.2).setRowsOwed (owedNorm a.rowsOwed))
    | none => .error "K4's run: the listing on shapes refuses"
  | _, _ => .error "K4's run: what was heard is not there"

/-- The ledger laid at a layers' link, and the count of rows, seen through the shape. -/
theorem chainSh_k4Fork (s : S) (a : LayOwn) (hh : s.here = .lay a) (G : Fork) (d : Option Nat) :
    chainSh { s with here := .lay { a with F := G }, rowsOwed := d } =
      ((chainSh s).setLed (ledSh G)).setRowsOwed d := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  obtain rfl : here = .lay a := hh
  rfl

theorem owedNorm_eq (s : S) :
    (if s.noneWaits = true then none else s.rowsOwed) = owedNorm s.rowsOwed := by
  unfold S.noneWaits owedNorm
  cases s.rowsOwed with
  | none => rfl
  | some r => cases h : (r == 0) <;> simp [h]

/-- **Where the run on shapes returns y, and what was heard is good, the run returns, and y is its
claims' shapes and the state's shape behind.** Good: the listing's own premise on what was heard. -/
theorem seatRun_follows (name : String) {f : Own → Fork → Option (Array Aff × Fork)}
    {fG : OwnSh → LedSh → Option (List AffSh × LedSh)} {Good : Own → Prop}
    (hf : ∀ o F z, Good o → fG (ownSh o) (ledSh F) = some z →
      ∃ fs G, f o F = some (fs, G) ∧ z = (fs.toList.map affSh, ledSh G))
    (s : S) (y : List ClaimSh × ChainSh) (hg : k4RunG fG (chainSh s) = .ok y)
    (hp : ∀ o, s.own? = some o → Good o) :
    ∃ cs s', seatRun name f s = .ok (cs, s') ∧ y = (cs.map claimSh, chainSh s') := by
  unfold k4RunG at hg
  by_cases h1 : ((chainSh s).here != 1) = true
  · rw [if_pos h1] at hg
    cases hg
  rw [if_neg h1] at hg
  have h1' : hereNo s.here = 1 := by
    have : ((chainSh s).here != 1) = false := by simpa using h1
    simpa using this
  obtain ⟨a, hh⟩ : ∃ a, s.here = .lay a := by
    cases hx : s.here with
    | lay a => exact ⟨a, rfl⟩
    | head a =>
      rw [hx] at h1'
      simp only [hereNo] at h1'
      split at h1' <;> cases h1'
    | _ =>
      rw [hx] at h1'
      cases h1'
  have hown : s.own? = a.own := by
    unfold S.own?
    rw [hh]
  have e1 : (chainSh s).own = a.own.map ownSh := by
    show s.own?.map ownSh = _
    rw [hown]
  have e2 : (chainSh s).led = some (ledSh a.F) := by
    show s.fork?.map ledSh = _
    unfold S.fork?
    rw [hh]
    rfl
  rw [e1, e2] at hg
  cases ho : a.own with
  | none =>
    rw [ho] at hg
    cases hg
  | some o =>
    rw [ho] at hg
    have hg' : (match fG (ownSh o) (ledSh a.F) with
      | some z => (.ok (z.1.map claimOfSh,
          ((chainSh s).setLed z.2).setRowsOwed (owedNorm (chainSh s).rowsOwed)) :
          Except String (List ClaimSh × ChainSh))
      | none => .error "K4's run: the listing on shapes refuses") = .ok y := hg
    cases hz : fG (ownSh o) (ledSh a.F) with
    | none =>
      rw [hz] at hg'
      cases hg'
    | some z =>
      rw [hz] at hg'
      obtain ⟨fs, G, ef, rfl⟩ := hf o a.F z (hp o (by rw [hown, ho])) hz
      refine ⟨fs.toList.map claimOf,
        { s with here := .lay { a with F := G }, rowsOwed := owedNorm s.rowsOwed }, ?_, ?_⟩
      · unfold seatRun part?
        rw [hh]
        show ((runOf seatOwn name f (a, (if s.noneWaits = true then none else s.rowsOwed),
          s.tokv)).map fun y => (y.1, setPart s y.2)).map (fun y => (y.1.map claimOf, y.2)) = _
        unfold runOf
        show (((VerifiableInference.Desc.named "K4.what-was-heard-is-not-there" a.own).bind
          fun o => (VerifiableInference.Desc.named name (f o a.F)).bind fun x =>
            (pure (x.1.toList, (({ a with F := x.2 } : LayOwn),
              (if s.noneWaits = true then none else s.rowsOwed), s.tokv)) :
              Except String (List Aff × Part))).map fun y => (y.1, setPart s y.2)).map
                (fun y => (y.1.map claimOf, y.2)) = _
        rw [ho, owedNorm_eq]
        show Except.map _
          (Except.map _ ((VerifiableInference.Desc.named name (f o a.F)).bind _)) = _
        rw [ef]
        rfl
      · rw [← Except.ok.inj hg', chainSh_k4Fork s a hh]
        refine Prod.ext ?_ rfl
        show (fs.toList.map affSh).map claimOfSh = (fs.toList.map claimOf).map claimSh
        rw [List.map_map, List.map_map]
        rfl

/-! ## The block's two runs, and what they owe on shapes -/

/-- The runs that K4's block at the state states, by name. -/
theorem claims_are (p : Par) :
    (blockAtC p).claims =
      [("front", fun _ s => seatRun "K4.claims-front"
          ((if p.k3Runs then formsFrontNoRows else formsFront) p.P p.g) s),
       ("back", fun _ s => seatRun "K4.claims-back" formsBack s)] := rfl

theorem front_is {p : Par} {run : Nat → S → Except String (List Claim × S)}
    (hk : p.k3Runs = true) (hrun : ("front", run) ∈ (blockAtC p).claims) :
    run = fun _ s => seatRun "K4.claims-front" (formsFrontWith false p.P p.g) s := by
  rw [claims_are, hk] at hrun
  rcases List.mem_cons.1 hrun with h | h
  · exact (Prod.mk.inj h).2
  · rcases List.mem_cons.1 h with h | h
    · exact absurd (Prod.mk.inj h).1 (by decide)
    · cases h

theorem back_is {p : Par} {run : Nat → S → Except String (List Claim × S)}
    (hrun : ("back", run) ∈ (blockAtC p).claims) :
    run = fun _ s => seatRun "K4.claims-back" formsBack s := by
  rw [claims_are] at hrun
  rcases List.mem_cons.1 hrun with h | h
  · exact absurd (Prod.mk.inj h).1 (by decide)
  · rcases List.mem_cons.1 h with h | h
    · exact (Prod.mk.inj h).2
    · cases h

/-- **The two runs' premise on the state**: the environment of what was heard has the plan's layout
and table of scales. The chain's shape sees neither. -/
def PlanEnv (P : Pub) (s : S) : Prop := ∀ o, s.own? = some o → o.v.y = P.y ∧ o.v.sc = P.sc

/-- **What the run "front" owes on shapes**, where the lookup states its own claims as a run. -/
def frontRunLaw (p : Par) (run : Nat → S → Except String (List Claim × S))
    (hk : p.k3Runs = true) (hrun : ("front", run) ∈ (blockAtC p).claims) :
    VerifiableInference.Desc.K9.Shape.RunLaw run where
  runG := fun _ a => k4RunG (frontG p.P p.g) a
  pre := fun _ s => PlanEnv p.P s
  carries := fun n s s' cs y hp hr hg => by
    obtain ⟨cs', s'', e, hy⟩ := seatRun_follows "K4.claims-front"
      (f := formsFrontWith false p.P p.g) (Good := fun o => o.v.y = p.P.y ∧ o.v.sc = p.P.sc)
      (fun o F z hG hz => formsFront_sh hG.1 hG.2 hz) s y hg hp
    rw [front_is hk hrun] at hr
    have hr' : seatRun "K4.claims-front" (formsFrontWith false p.P p.g) s = .ok (cs, s') := hr
    rw [hr'] at e
    cases e
    exact hy
  returns := fun n s y hg hp => by
    obtain ⟨cs', s'', e, -⟩ := seatRun_follows "K4.claims-front"
      (f := formsFrontWith false p.P p.g) (Good := fun o => o.v.y = p.P.y ∧ o.v.sc = p.P.sc)
      (fun o F z hG hz => formsFront_sh hG.1 hG.2 hz) s y hg hp
    rw [front_is hk hrun]
    exact ⟨_, e⟩

/-- **What the run "back" owes on shapes.** Its pre is idle: the proofs spend it only to rewrite
backG's two idle arguments. -/
def backRunLaw (p : Par) (run : Nat → S → Except String (List Claim × S))
    (hrun : ("back", run) ∈ (blockAtC p).claims) :
    VerifiableInference.Desc.K9.Shape.RunLaw run where
  runG := fun _ a => k4RunG (backG p.P.y p.P.sc) a
  pre := fun _ s => PlanEnv p.P s
  carries := fun n s s' cs y hp hr hg => by
    obtain ⟨cs', s'', e, hy⟩ := seatRun_follows "K4.claims-back" (f := formsBack)
      (Good := fun o => o.v.y = p.P.y ∧ o.v.sc = p.P.sc)
      (fun o F z hG hz => formsBack_sh (by rw [hG.1, hG.2]; exact hz)) s y hg hp
    rw [back_is hrun] at hr
    have hr' : seatRun "K4.claims-back" formsBack s = .ok (cs, s') := hr
    rw [hr'] at e
    cases e
    exact hy
  returns := fun n s y hg hp => by
    obtain ⟨cs', s'', e, -⟩ := seatRun_follows "K4.claims-back" (f := formsBack)
      (Good := fun o => o.v.y = p.P.y ∧ o.v.sc = p.P.sc)
      (fun o F z hG hz => formsBack_sh (by rw [hG.1, hG.2]; exact hz)) s y hg hp
    rw [back_is hrun]
    exact ⟨_, e⟩

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.ownClaim_sh
#print axioms OnBytes.Desc.First.K4.Rt.rowForm_sh
#print axioms OnBytes.Desc.First.K4.Rt.shown_of_B
#print axioms OnBytes.Desc.First.K4.Rt.claimOf_sh
#print axioms OnBytes.Desc.First.K4.Rt.formsBack_sh
#print axioms OnBytes.Desc.First.K4.Rt.formsFront_sh
#print axioms OnBytes.Desc.First.K4.Rt.chainSh_k4Fork
#print axioms OnBytes.Desc.First.K4.Rt.owedNorm_eq
#print axioms OnBytes.Desc.First.K4.Rt.seatRun_follows
#print axioms OnBytes.Desc.First.K4.Rt.claims_are
#print axioms OnBytes.Desc.First.K4.Rt.front_is
#print axioms OnBytes.Desc.First.K4.Rt.back_is
#print axioms OnBytes.Desc.First.K4.Rt.frontRunLaw
#print axioms OnBytes.Desc.First.K4.Rt.backRunLaw
#print axioms OnBytes.Desc.First.K4.Rt.rowOfSh
#print axioms OnBytes.Desc.First.K4.Rt.filledBy
#print axioms OnBytes.Desc.First.K4.Rt.shownB
#print axioms OnBytes.Desc.First.K4.Rt.claimOfSh
#print axioms OnBytes.Desc.First.K4.Rt.backG
#print axioms OnBytes.Desc.First.K4.Rt.frontG
#print axioms OnBytes.Desc.First.K4.Rt.owedNorm
#print axioms OnBytes.Desc.First.K4.Rt.seatRun
#print axioms OnBytes.Desc.First.K4.Rt.k4RunG
#print axioms OnBytes.Desc.First.K4.Rt.PlanEnv
