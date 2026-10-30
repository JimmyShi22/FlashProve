-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/ParOwnChecks.lean: the proofs of ten of the eleven statements of
Johnson/FrontRoad/ParOwnChecksSpec.lean: at all public files in scope that can be read, under
LaidAt, the planner's test on the range checks passes at the checks of the parameters that parOwn
names, at the planner's own four arguments. The eleventh, Spec.premises_met_at_full, is proved in
the side library.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
  Lemmas on lists   map_dropLast', filterMap_k8, filterMap_none', flatMap_map', mapM_some,
      filterMap_mapO, tails_in_a_row.
  ownAt, parOwn_eq, tlAt   parOwn's text in two steps; the tail of the built segment at a link.
  placesW_k8, placesW_last   two closed facts on the written list of places (placesW,
      Johnson/IMR/WrittenList.lean), each by an evaluation in Lean's kernel.
  The steps   places_first, pars_list, built_at, checks_k8Par, checksOfPars_cons, checks_along,
      shapesWith_checks, closing_own. places_first is places_scope (Johnson/IMR/PlacesScope.lean) at
      the description's first chain. built_at and closing_own rest on ground_tails
      (Johnson/IMR/K8Seat.lean) and scope_plans (Johnson/Goal/Meaning/PlanShapes.lean).
      shapesWith_checks: shapesWith (OnBytes/Model/VerifySubproofs.lean) lays rangeChecksOf X into
      the field rangeChecks.
  The ten proofs   k8_places_front, pars_at_parOwn, checks_are_own, lines_are_frame,
      planner_passes_at_parOwn, missed_at_none, none_not_own, bent_not_own (with bumpP, bumpC,
      checks_bump, bump_fixes_none), sessionStops_of_pinned_files, sessionStops_of_tiedOwn_files.

How it fits. planner_passes_at_parOwn joins three theorems of the library. pub_configure
(Johnson/Desc/ProofFile/Law/PlainMade.lean): the planner's value in the public part is what
Params.configure returned at the parameter file's lines and the run's own shapes. gates_of_configure
(E2E/GateOfConfigure.lean): what the planner returns has passed its four tests, at the shapes' own
range checks. plain_shapesOf_cut (Johnson/Loose/H2K12/PlainPartsCut.lean), with shapesWith_checks:
these are rangeChecksOf X. checks_are_own says that they are the checks of ownPars. All limits: the
head of Johnson/FrontRoad/ParOwnChecksSpec.lean. Not one of the release's goal statements.
-/
import Johnson.FrontRoad.ParOwnChecksSpec
import E2E.GateOfConfigure
import Johnson.G.MadeSpelled
import Johnson.Desc.ProofFile.Law.PlainMade
import Johnson.Loose.H2K12.PlainPartsCut
import Johnson.IMR.PlacesScope
import Johnson.IMR.K8Seat
import Johnson.Goal.Meaning.PlanShapes

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open AtPublicFiles.AtFiles AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Flat (RecFull)
open OnBytes.Params (Lines RangeCheck missedInTheChecks clog2)
open OnBytes.Maker (WholeD)
open OnBytes.Model.Verify (publicOf)
open OnBytes.HonestTrace (Tr cellsC cellsSmall_cellOf ServesAt theTrace meetsAll_theTrace
  servesAt_iff_in_scope TraceHinge)
open Inst.Model (Instance ppref)
open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.First.K8 (Par)
open ProofFile.Honest (Prover ProverCoinCounts Sides Ready Coins ready)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (protocolDataWellFormed)
open P5J

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off within this namespace,
so that no statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) nonemptyPadZ_parOwnChecks : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

/- The same of this one. -/
local instance (priority := high) nonemptyOfInhabited_parOwnChecks {α : Type} [Inhabited α] :
    Nonempty α := ⟨default⟩

/-! ## Lemmas on lists -/

theorem map_dropLast' {α β : Type} (f : α → β) : ∀ l : List α, l.dropLast.map f = (l.map f).dropLast
  | [] => rfl
  | [_] => rfl
  | a :: b :: l => by
    show f a :: ((b :: l).dropLast.map f) = f a :: ((b :: l).map f).dropLast
    rw [map_dropLast' f (b :: l)]

theorem filterMap_k8 {β : Type} (f : ℕ → Option β) : ∀ ps : List Place,
    ps.filterMap (fun a => if a.kind = KindName.K8 then a.link.bind f else none) =
      ((ps.filter fun a => a.kind == KindName.K8).map (·.link)).filterMap (·.bind f)
  | [] => rfl
  | a :: ps => by
    by_cases h : a.kind = KindName.K8
    · have hb : (a.kind == KindName.K8) = true := by rw [h]; rfl
      rw [List.filter_cons_of_pos (p := fun a : Place => a.kind == KindName.K8) hb, List.map_cons,
        List.filterMap_cons, List.filterMap_cons, if_pos h, filterMap_k8 f ps]
    · have hb : ¬ (a.kind == KindName.K8) = true := by simpa using h
      rw [List.filter_cons_of_neg (p := fun a : Place => a.kind == KindName.K8) hb,
        List.filterMap_cons, if_neg h, filterMap_k8 f ps]

theorem filterMap_none' {α β : Type} : ∀ l : List α, l.filterMap (fun _ => (none : Option β)) = []
  | [] => rfl
  | _ :: l => by rw [List.filterMap_cons, filterMap_none' l]

theorem flatMap_map' {α β γ : Type} (f : α → β) (g : β → List γ) :
    ∀ l : List α, (l.map f).flatMap g = l.flatMap fun a => g (f a)
  | [] => rfl
  | a :: l => by rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, flatMap_map' f g l]

theorem mapM_some {α β : Type} (f : α → Option β) (h : α → β) :
    ∀ l : List α, (∀ a ∈ l, f a = some (h a)) → l.mapM f = some (l.map h)
  | [], _ => by simp
  | a :: l, H => by
    rw [List.mapM_cons, H a List.mem_cons_self,
      mapM_some f h l fun b hb => H b (List.mem_cons_of_mem _ hb)]
    rfl

theorem filterMap_mapO {α β γ : Type} (f : α → Option β) (g : β → γ) :
    ∀ l : List α, l.filterMap (fun a => (f a).map g) = (l.filterMap f).map g
  | [] => rfl
  | a :: l => by
    rw [List.filterMap_cons, List.filterMap_cons]
    cases f a with
    | none => exact filterMap_mapO f g l
    | some b =>
      show g b :: _ = g b :: _
      rw [filterMap_mapO f g l]

/-- Twelve pairs and one more, in a row, are the twenty-five. -/
theorem tails_in_a_row {α : Type} (T : ℕ → α) :
    ((List.range 12).map fun g => [T (2 * g), T (2 * g + 1)]).flatten ++ [T 24] =
      (List.range 25).map T := rfl

/-! ## parOwn's text in two steps -/

/-- What parOwn names at a place of the kind K8 with the link l. -/
def ownAt (Zp : ProofFile.Pub) (mats : ℕ → List (ℕ × String × ℕ)) (l : ℕ) :
    Option (Par × List (ℕ × String × ℕ)) :=
  (ProofFile.blankBy ProofFile.pureRoad.links Zp).bind fun G₀ =>
    (G₀.built[l]?).map fun Xl => (ProofFile.k8Par Zp G₀ Xl l, mats l)

theorem parOwn_eq (Zp : ProofFile.Pub) (mats : ℕ → List (ℕ × String × ℕ)) :
    parOwn Zp mats =
      fun a => if a.kind = KindName.K8 then a.link.bind (ownAt Zp mats) else none := rfl

/-- The tail of the built segment at the link l; the empty tail where there is none. -/
def tlAt (G₀ : ProofFile.Ground) (l : ℕ) : OnBytes.Model.HTailF2 := ((G₀.built[l]?).map (·.tl)).getD {}

/-! ## Two closed facts on the written list of places -/

set_option maxRecDepth 1000000 in
/-- The written list of places without its last member, filtered by the kind K8, is the twenty-five
places k8PlaceAt l, in order. placesW is a closed term (flatPlacesOf at the written row of sorts),
which the kernel evaluates. -/
theorem placesW_k8 : (IM.placesW.dropLast.filter fun a => a.kind == KindName.K8) =
    (List.range 25).map k8PlaceAt := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The last member of the written list of places is of the kind frame. -/
theorem placesW_last : IM.placesW.getLast?.map (·.kind) = some KindName.frame := by decide +kernel

/-! ## The steps -/

section
variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
  (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)

theorem places_first (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    {D : WholeD} {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    (descZ Zp Np cF).first.blocksInOrder.map (·.place) = IM.placesW := by
  obtain ⟨Bs, base, O⟩ := L.opened
  exact IM.places_scope scope hr O

theorem k8_places_front : Spec.k8_places_front := by
  intro Z Zp Np cF scope pp hr D r L
  have hp := places_first Z Zp Np cF scope hr L
  refine ⟨?_, ?_⟩
  · rw [map_dropLast', hp]
    exact placesW_k8
  · have e : ((descZ Zp Np cF).first.blocksInOrder.getLast?).map (·.place.kind) =
        (((descZ Zp Np cF).first.blocksInOrder.map (·.place)).getLast?).map (·.kind) := by
      rw [List.getLast?_map, Option.map_map]
      rfl
    rw [e, hp]
    exact placesW_last

theorem pars_list (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    {D : WholeD} {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (mats : ℕ → List (ℕ × String × ℕ)) :
    ((descZ Zp Np cF).first.blocksInOrder.dropLast.filterMap fun b => parOwn Zp mats b.place) =
      (List.range 25).filterMap (ownAt Zp mats) := by
  have h1 : ((descZ Zp Np cF).first.blocksInOrder.dropLast.filterMap fun b => parOwn Zp mats b.place) =
      ((descZ Zp Np cF).first.blocksInOrder.dropLast.map (·.place)).filterMap (parOwn Zp mats) := by
    rw [List.filterMap_map]
    rfl
  rw [h1, map_dropLast', places_first Z Zp Np cF scope hr L, parOwn_eq, filterMap_k8, placesW_k8,
    List.map_map, List.filterMap_map]
  rfl

/-- In scope the built segments have an entry at each link below 25. -/
theorem built_at (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    {D : WholeD} {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {G₀ : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) (l : ℕ) (hl : l < 25) :
    ∃ Xl, G₀.built[l]? = some Xl := by
  obtain ⟨tails, lh, eh, -⟩ := IM.ground_tails scope hr L.pub hG
  by_cases h24 : l = 24
  · subst h24
    exact ⟨lh, eh⟩
  · obtain ⟨hp, a, x, x', -, -, e, -, -, -, -, -, e', -⟩ := tails (l / 2) (by omega)
    rcases Nat.mod_two_eq_zero_or_one l with h | h
    · have el : 2 * (l / 2) = l := by omega
      rw [el] at e
      exact ⟨x, e⟩
    · have el : 2 * (l / 2) + 1 = l := by omega
      rw [el] at e'
      exact ⟨x', e'⟩

end

/-- The checks of the description's own parameters at a link are the verifier's checks of that
segment's tail. -/
theorem checks_k8Par (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) (Xl : OnBytes.Model.Stages.LinkH) (l : ℕ) :
    (matricesOf (ProofFile.k8Par Zp G₀ Xl l)).map (fun x => checkOf x.1 x.2.1 x.2.2) =
      Xl.tl.mats.toList.map (OnBytes.Model.rangeCheckOf Xl.tl.tau) := by
  show ((((Xl.tl.mats.toList.map (·.m)).zip (Xl.tl.mats.toList.map (·.k))).map
    fun x => (x.1, x.2, Xl.tl.tau)).map fun x => checkOf x.1 x.2.1 x.2.2) = _
  rw [List.zip_map', List.map_map, List.map_map]
  rfl

theorem checksOfPars_cons (p : Par) (Ps : List Par) :
    checksOfPars (p :: Ps) =
      (matricesOf p).map (fun x => checkOf x.1 x.2.1 x.2.2) ++ checksOfPars Ps := by
  unfold checksOfPars
  rw [List.flatMap_cons, List.map_append]

/-- Along a list of links at each of which the built segments have an entry, the checks of what
parOwn names are the verifier's checks of these segments' tails, in the list's order. -/
theorem checks_along (Zp : ProofFile.Pub) (mats : ℕ → List (ℕ × String × ℕ)) {G₀ : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) :
    ∀ ls : List ℕ, (∀ l ∈ ls, ∃ Xl, G₀.built[l]? = some Xl) →
      checksOfPars ((ls.filterMap (ownAt Zp mats)).map (·.1)) =
        ls.flatMap fun l =>
          (tlAt G₀ l).mats.toList.map (OnBytes.Model.rangeCheckOf (tlAt G₀ l).tau)
  | [], _ => rfl
  | l :: ls, H => by
    obtain ⟨Xl, e⟩ := H l List.mem_cons_self
    have e1 : ownAt Zp mats l = some (ProofFile.k8Par Zp G₀ Xl l, mats l) := by
      unfold ownAt
      rw [hG]
      show ((G₀.built[l]?).map fun Xl => (ProofFile.k8Par Zp G₀ Xl l, mats l)) = _
      rw [e]
      rfl
    have e2 : tlAt G₀ l = Xl.tl := by
      unfold tlAt
      rw [e]
      rfl
    rw [List.filterMap_cons, e1, List.map_cons, checksOfPars_cons, checks_k8Par,
      checks_along Zp mats hG ls fun l' h' => H l' (List.mem_cons_of_mem _ h'),
      List.flatMap_cons, e2]

/-- shapesWith lays rangeChecksOf X into the field rangeChecks. -/
theorem shapesWith_checks {X : OnBytes.Model.Verify.Public} {links : List OnBytes.Params.ReqLink}
    {layout : OnBytes.Params.ReqLayout} {ids : List ℕ} {x : OnBytes.Params.Shapes}
    (h : OnBytes.Model.Verify.shapesWith X links layout ids = .ok x) :
    OnBytes.Model.Verify.rangeChecksOf X = some x.rangeChecks := by
  unfold OnBytes.Model.Verify.shapesWith at h
  extract_lets at h
  obtain ⟨rc, hrc, h⟩ := OnBytes.Params.exc_bind h
  replace h := OnBytes.Params.exc_guard h
  replace h := OnBytes.Params.exc_guard h
  obtain ⟨ranges, _, h⟩ := OnBytes.Params.exc_bind h
  cases h
  exact OnBytes.Params.orRefuse_ok hrc

section
variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
  (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)

/-- In scope the verifier's closing parts are the built segments' tails (tlAt), in the links' order.
That each of the twenty-five links has an entry, so that no tail here is tlAt's empty one, is
built_at. -/
theorem closing_own (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    {D : WholeD} {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {G₀ : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) :
    OnBytes.Model.Verify.closingParts Zp.p.X = some ((List.range 25).map (tlAt G₀)) := by
  obtain ⟨Bs, base, O⟩ := L.opened
  obtain rfl : Bs.G₀ = G₀ := Option.some.inj (O.blank.symm.trans hG)
  have hW : Bs.G₀.W = Zp.p.X := O.W
  have hX : publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := hW ▸ O.public
  obtain ⟨hq, hN, -, -⟩ := Meaning.scope_plans scope hr hX
  obtain ⟨tails, lh, eh, etl, -⟩ := IM.ground_tails scope hr L.pub hG
  have hc : ∀ g ∈ List.range 12, OnBytes.Model.Verify.closingPartsOf Zp.p.X g =
      some [tlAt Bs.G₀ (2 * g), tlAt Bs.G₀ (2 * g + 1)] := by
    intro g hg
    obtain ⟨hp, a, x, x', ehp, ea, e, et, -, -, -, -, e', et', -⟩ := tails g (List.mem_range.1 hg)
    rw [hW] at ehp ea
    unfold OnBytes.Model.Verify.closingPartsOf
    rw [ehp, ea]
    show some (if Zp.p.X.p4 then [hp.tl, a.seam.tl] else [hp.tl]) = _
    rw [hq, if_pos rfl]
    unfold tlAt
    rw [e, e']
    show some [hp.tl, a.seam.tl] = some [x.tl, x'.tl]
    rw [et, et']
  unfold OnBytes.Model.Verify.closingParts
  rw [hN, mapM_some _ _ _ hc]
  show some (((List.range 12).map fun g => [tlAt Bs.G₀ (2 * g), tlAt Bs.G₀ (2 * g + 1)]).flatten ++
    [Zp.p.X.H.tl]) = _
  have e24 : Zp.p.X.H.tl = tlAt Bs.G₀ 24 := by
    unfold tlAt
    rw [eh]
    show _ = lh.tl
    rw [etl, hW]
  rw [e24, tails_in_a_row]

end

/-! ## The ten -/

theorem pars_at_parOwn : Spec.pars_at_parOwn := by
  intro Z Zp Np cF scope pp hr D r L mats
  obtain ⟨Bs, base, O⟩ := L.opened
  have hG := O.blank
  have e := pars_list Z Zp Np cF scope hr L mats
  have e' : (List.range 25).filterMap (ownAt Zp mats) = (List.range 25).filterMap (fun l =>
      (Bs.G₀.built[l]?).map fun Xl => (ProofFile.k8Par Zp Bs.G₀ Xl l, mats l)) := by
    unfold ownAt
    rw [hG]
    rfl
  refine ⟨Bs.G₀, hG, e.trans e', ?_⟩
  rw [e, e']
  have hs : ∀ ls : List ℕ, (∀ l ∈ ls, ∃ Xl, Bs.G₀.built[l]? = some Xl) →
      (ls.filterMap fun l =>
        (Bs.G₀.built[l]?).map fun Xl => (ProofFile.k8Par Zp Bs.G₀ Xl l, mats l)).length = ls.length := by
    intro ls
    induction ls with
    | nil => intro _; rfl
    | cons l ls ih =>
      intro H
      obtain ⟨Xl, eX⟩ := H l List.mem_cons_self
      rw [List.filterMap_cons, eX]
      show (_ :: _).length = _
      rw [List.length_cons, List.length_cons, ih fun l' h' => H l' (List.mem_cons_of_mem _ h')]
  rw [hs _ fun l hl => built_at Z Zp Np cF scope hr L hG l (List.mem_range.1 hl)]
  rfl

theorem checks_are_own : Spec.checks_are_own := by
  intro Z Zp Np cF scope pp hr D r L mats
  obtain ⟨Bs, base, O⟩ := L.opened
  have hG := O.blank
  unfold OnBytes.Model.Verify.rangeChecksOf
  rw [closing_own Z Zp Np cF scope hr L hG]
  show some (OnBytes.Model.rangeChecksH ((List.range 25).map (tlAt Bs.G₀))) = _
  unfold OnBytes.Model.rangeChecksH
  rw [flatMap_map']
  show _ = some (checksOfPars
    (((descZ Zp Np cF).first.blocksInOrder.dropLast.filterMap fun b => parOwn Zp mats b.place).map (·.1)))
  rw [pars_list Z Zp Np cF scope hr L mats,
    checks_along Zp mats hG _ fun l hl => built_at Z Zp Np cF scope hr L hG l (List.mem_range.1 hl)]

theorem lines_are_frame : Spec.lines_are_frame := by
  intro Z Zp Np cF scope pp hr D r L
  obtain ⟨ls, -, hm, -, -⟩ := ProofFile.Law.pub_configure (o := OnBytes.secondHashFunction) L.pub
  obtain ⟨f, s, s2, o1, ks, k2, Gt⟩ := AtPublicFiles.Gate.gates_of_configure hm
  exact Johnson.G.MadeFree.sized_lines (AtPublicFiles.Gate.asMade_of_configure hm Gt.key).sizes

theorem planner_passes_at_parOwn : Spec.planner_passes_at_parOwn := by
  intro Z Zp Np cF scope pp hr D r L mats
  obtain ⟨ls, hs, hm, -, -⟩ := ProofFile.Law.pub_configure (o := OnBytes.secondHashFunction) L.pub
  obtain ⟨f, s, s2, o1, ks, k2, Gt⟩ := AtPublicFiles.Gate.gates_of_configure hm
  obtain ⟨reqLinks, lay', links0, declared, file, -, -, -, -, hw⟩ :=
    H2K.Made.plain_shapesOf_cut (links := ls.1) (x := ls.2) hs
  have e : ls.2.rangeChecks = checksOfPars (ownPars Zp Np cF mats) :=
    Option.some.inj ((shapesWith_checks hw).symm.trans (checks_are_own Z Zp Np cF scope hr L mats))
  have g := Gt.checks
  rw [e] at g
  exact g

theorem missed_at_none : Spec.missed_at_none := by
  intro Zp Np cF l oneTime columnsFirst batches
  rw [filterMap_none']
  rfl

theorem none_not_own : Spec.none_not_own := by
  intro Z Zp Np cF scope pp hr D r L h
  have e := (checks_are_own Z Zp Np cF scope hr L fun _ => []).symm.trans h
  have g := planner_passes_at_parOwn Z Zp Np cF scope hr L fun _ => []
  rw [Option.some.inj e, missed_at_none Zp Np cF] at g
  cases g

/-- A place's parameters with the number of combinations raised by 1. -/
def bumpP (p : Par) : Par := { p with tau := p.tau + 1 }

/-- A check with the number of combinations raised by 1. -/
def bumpC (c : RangeCheck) : RangeCheck := { c with combinations := c.combinations + 1 }

theorem checks_bump : ∀ Ps : List Par, checksOfPars (Ps.map bumpP) = (checksOfPars Ps).map bumpC
  | [] => rfl
  | p :: Ps => by
    have e : (matricesOf (bumpP p)).map (fun x => checkOf x.1 x.2.1 x.2.2) =
        ((matricesOf p).map fun x => checkOf x.1 x.2.1 x.2.2).map bumpC := by
      unfold matricesOf
      rw [List.map_map, List.map_map, List.map_map]
      rfl
    rw [List.map_cons, checksOfPars_cons, checksOfPars_cons, List.map_append, checks_bump Ps, e]

theorem bump_fixes_none : ∀ cs : List RangeCheck, cs.map bumpC = cs → cs = []
  | [], _ => rfl
  | c :: cs, h => by
    have h1 : bumpC c = c := (List.cons.inj h).1
    have h2 : c.combinations + 1 = c.combinations := congrArg RangeCheck.combinations h1
    omega

theorem bent_not_own : Spec.bent_not_own := by
  intro Z Zp Np cF scope pp hr D r L mats h
  have e := (checks_are_own Z Zp Np cF scope hr L mats).symm.trans h
  have eb : (((descZ Zp Np cF).first.blocksInOrder.dropLast.filterMap fun b =>
      parBent Zp mats b.place).map (·.1)) = (ownPars Zp Np cF mats).map bumpP := by
    have e1 : ((descZ Zp Np cF).first.blocksInOrder.dropLast.filterMap fun b => parBent Zp mats b.place) =
        ((descZ Zp Np cF).first.blocksInOrder.dropLast.filterMap fun b => parOwn Zp mats b.place).map
          fun P => (bumpP P.1, P.2) :=
      filterMap_mapO (fun b => parOwn Zp mats (Block.place b)) (fun P => (bumpP P.1, P.2)) _
    rw [e1, List.map_map, List.map_map]
    rfl
  rw [eb, checks_bump] at e
  have e0 := bump_fixes_none _ (Option.some.inj e).symm
  have g := planner_passes_at_parOwn Z Zp Np cF scope hr L mats
  rw [e0] at g
  cases g

theorem sessionStops_of_pinned_files : Spec.sessionStops_of_pinned_files := by
  intro Z Zp Np cF R₂ R₃ _ _ _ _ run₂ run₃ Tr X₀ Xh B G H scope pp hr live D r L w₀ rc x₀ k₀ R hR hn
    Yes mats cells h₁ h₃ hP ok Gs
  exact sessionStops_of_pinned_own Z Zp Np cF run₂ run₃ B G H scope hr live L hR hn Yes mats cells
    (linesAt Zp) (oneTimeAt Zp) (columnsFirstAt Zp) (batchesAt Zp) h₁ h₃
    (planner_passes_at_parOwn Z Zp Np cF scope hr L mats) hP ok Gs

theorem sessionStops_of_tiedOwn_files : Spec.sessionStops_of_tiedOwn_files := by
  intro Z Zp Np cF R₂ R₃ _ _ _ _ run₂ run₃ X₀ Xh B G H scope pp hr live D r L w₀ rc x₀ k₀ R hR hn
    Yes mats h₁ h₃ hO ok Gs
  exact sessionStops_of_tiedOwn_own Z Zp Np cF run₂ run₃ B G H scope hr live L hR hn Yes mats
    (linesAt Zp) (oneTimeAt Zp) (columnsFirstAt Zp) (batchesAt Zp) h₁ h₃
    (planner_passes_at_parOwn Z Zp Np cF scope hr L mats) hO ok Gs

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.nonemptyPadZ_parOwnChecks
#print axioms OnBytes.FrontRoad.nonemptyOfInhabited_parOwnChecks
#print axioms OnBytes.FrontRoad.map_dropLast'
#print axioms OnBytes.FrontRoad.filterMap_k8
#print axioms OnBytes.FrontRoad.filterMap_none'
#print axioms OnBytes.FrontRoad.flatMap_map'
#print axioms OnBytes.FrontRoad.mapM_some
#print axioms OnBytes.FrontRoad.tails_in_a_row
#print axioms OnBytes.FrontRoad.ownAt
#print axioms OnBytes.FrontRoad.parOwn_eq
#print axioms OnBytes.FrontRoad.tlAt
#print axioms OnBytes.FrontRoad.placesW_k8
#print axioms OnBytes.FrontRoad.placesW_last
#print axioms OnBytes.FrontRoad.places_first
#print axioms OnBytes.FrontRoad.k8_places_front
#print axioms OnBytes.FrontRoad.pars_list
#print axioms OnBytes.FrontRoad.built_at
#print axioms OnBytes.FrontRoad.checks_k8Par
#print axioms OnBytes.FrontRoad.checksOfPars_cons
#print axioms OnBytes.FrontRoad.checks_along
#print axioms OnBytes.FrontRoad.shapesWith_checks
#print axioms OnBytes.FrontRoad.closing_own
#print axioms OnBytes.FrontRoad.pars_at_parOwn
#print axioms OnBytes.FrontRoad.checks_are_own
#print axioms OnBytes.FrontRoad.lines_are_frame
#print axioms OnBytes.FrontRoad.planner_passes_at_parOwn
#print axioms OnBytes.FrontRoad.missed_at_none
#print axioms OnBytes.FrontRoad.none_not_own
#print axioms OnBytes.FrontRoad.filterMap_mapO
#print axioms OnBytes.FrontRoad.bumpP
#print axioms OnBytes.FrontRoad.bumpC
#print axioms OnBytes.FrontRoad.checks_bump
#print axioms OnBytes.FrontRoad.bump_fixes_none
#print axioms OnBytes.FrontRoad.bent_not_own
#print axioms OnBytes.FrontRoad.sessionStops_of_pinned_files
#print axioms OnBytes.FrontRoad.sessionStops_of_tiedOwn_files
