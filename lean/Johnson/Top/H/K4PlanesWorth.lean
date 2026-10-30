-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K4PlanesWorth.lean: AT THE LAYERS THE LOOKUP's THREE CLAIMS ON THE PLANES ARE THE
LAYERS' OWN KIND's TEXT (OnBytes/Desc/First/K4/Claims.lean: planesParts, with the leaves' own claim
made by ownClaim, OnBytes/Desc/First/K4/Plain.lean). WHERE THESE THREE FORMS ARE WORTH 0 IN A WORLD
WITH TRUE READS OF THE THREE TABLES, THE ROW OUT's ITEM "planes" HOLDS (K3OutPlanes,
Johnson/Top/H/K3RowOut.lean). Definitions, statements and proofs. A tie: no error term.

Why. At an attention link the three claims are stated by the lookup's own run "planes", and
Johnson/Top/H/K3OutPaid.lean goes from that run's claims to the item. At a
layers' link no such run
is called: the layers' kind lists the three forms among its own. Its text is the run's text
(Johnson/Desc/First/Look/LookPlanes.lean: planeClaimsF) line for line, in Option, but that it hands
back the summand of the leaves' own claim and leaves the making of that claim to its caller.

Main names:
  `k4Col`, `k4Bit`, `k4Pin`: the text's three readers, at the three tables' first entries.
  `foldlM_need`: a fold in Option that returns, returns in the flat monad too, and leaves ledger and
    tape, where each step does.
  `planesParts_cut`: what a return of planesParts is made of.
  `planeClaimsF_of_parts`: where planesParts returns (a0, [c1, c2]) and ownClaim makes rowL of a0
    from the ledger F, leaving F': planeClaimsF at the three readers returns #[rowL, c1, c2] from F,
    leaving F'.
  `k4_planes_worth`: the three forms' values in every later world are the library's three numbers
    at the values of the readers' forms.
  `k4_planes_out`: THE END: K3OutPlanes.
  `K4ReadsTrue`: the three true reads as one sentence, at the tables' first entries by name.
  `planesParts_tabs`, `front_cut`: what a return of the text, and of the layers' first run, is made
    of, as far as the planes go.
  `k4_planes_out_front`: THE END IN THE LETTERS OF THE LAYERS' OWN FIRST RUN: where formsFrontWith
    returns (fs, G) and every form of fs is worth 0 in G's own world, with true reads there:
    K3OutPlanes.

OBJECT: OnBytes.Desc.First.K4.formsFrontWith (OnBytes/Desc/First/K4/Plain.lean), through planesParts
and ownClaim.
USER: nobody. Meant for whoever shows that the first run's zeros give the statement's letter on
the planes at the layers.
LETTERS: rows, P, g, o, F as that run is called; the world is that of the ledger G which the run
leaves; nu's masks are the world's masks.

ITS PREMISES. t0, t1, tp: the three tables' first entries, by name. hpp, hrow: the two returns.
hok: the library's bounds on the heard shape. hF, h0: the ledger from which the own claim is made
has its sizes and is later than the one that the hearing left. hH: the world's ledger is later than
F'. hz: THE THREE FORMS ARE WORTH 0 IN THAT WORLD. b0, b1, pn: TRUE READS: the form that the text
reads at a column of the planes' matrix is worth, in that world, the library's value of that column
at the leaves' point, at the bits' point, and the column's count.

Limits. WHO PAYS hz (the three forms are members of a list whose sum was tested) AND THE TRUE READS
(the law of the reads at the layers) IS NOT SAID HERE. That the heard record fo is the one that the
lookup left is a premise of whoever calls it (K3OutPlanes speaks at all rounds for which fo, with
F0, stands). One direction. NOTHING IS TRIED FOR EMPTINESS: that hz and the three true reads can
hold together in one world is shown by no file.
Compiled with the whole library.
The driver's text and K3Own.lean do not lie beneath this file. Over other versions of
Johnson/Desc/Block.lean, Johnson/Desc/First/State.lean, Johnson/Desc/First/Look/K3Lookup.lean or
LookKind.lean it is to be compiled again.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3RowOut
import Johnson.Top.H.K3RunsLaw
import Johnson.Top.H.K3OutProof
import OnBytes.Desc.First.K4.Plain
import OnBytes.Desc.First.K4.ClaimsLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.PscTie _root_.Fo
open Cb Cb.Fo Cb.Fo.PlaneClaims Cb.Fo.Pin
open OnBytes.K.Kc
open OnBytes.Model.Layer (Env)
open OnBytes.Desc.First.K4 (planesParts ownClaim)
open VerifiableInference.Desc.First.Look (planesAtF planeClaimsF)

/-! ## The text's readers -/

/-- Entry x of the family of reads that begins at t; none from the layout's count on. -/
def k4Col (v : Env) (t x : ℕ) : Option Aff := if x < v.y.kbm then v.U3at t x else none

/-- The planes' column at the leaves' point (e = 0) or the bits' point. -/
def k4Bit (v : Env) (tB0 tB1 e x : ℕ) : Option Aff := k4Col v (if e == 0 then tB0 else tB1) x

/-- The counts' column. -/
def k4Pin (v : Env) (tP c : ℕ) : Option Aff := k4Col v tP c

/-! ## From Option to the flat monad -/

theorem foldlM_need {α σ : Type} (f : σ → α → Option σ) (fF : σ → α → Fl σ)
    (hf : ∀ s a s', f s a = some s' → ∀ F c, fF s a F c = .ok ((s', F), c)) :
    ∀ (l : List α) (s s' : σ), l.foldlM f s = some s' →
      ∀ (F : Fork) (c : Tape), (l.foldlM fF s) F c = .ok ((s', F), c)
  | [], s, s', h, Fk, c => by
    have e : s = s' := Option.some.inj h
    rw [Fo.Tp.foldlM_nil_ok, e]
  | a :: l, s, s', h, Fk, c => by
    rw [List.foldlM_cons] at h
    obtain ⟨s₁, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    exact (Fo.Tp.foldlM_cons_ok fF s a l Fk c _).2
      ⟨s₁, Fk, c, hf s a s₁ h1 Fk c, foldlM_need f fF hf l s₁ s' h2 Fk c⟩

/-- A step "read x, then return k x". -/
theorem need_then {α β : Type} (x : Option α) (k : α → β) (b : β) (h : x.map k = some b) (F : Fork)
    (c : Tape) : (Fl.need x >>= fun a => (pure (k a) : Fl β)) F c = .ok ((b, F), c) := by
  obtain ⟨a, ha, hb⟩ := Option.map_eq_some_iff.1 h
  exact (Fo.Tp.bind_ok _ _ F c _).2
    ⟨a, F, c, (Fo.Tp.get_ok x F c _).2 ⟨a, ha, rfl⟩, (Fo.Tp.pure_ok _ F c _).2 (by rw [hb])⟩

theorem planesAtF_of (g : Forest.Heard) (lm e : ℕ) (bit : ℕ → ℕ → Option Aff) (a : Aff)
    (h : OnBytes.Desc.First.K4.planesAt g lm e bit = some a) (F : Fork) (c : Tape) :
    planesAtF g lm e (fun e x => Fl.need (bit e x)) F c = .ok ((a, F), c) := by
  unfold OnBytes.Desc.First.K4.planesAt at h
  unfold planesAtF
  exact foldlM_need _ _ (fun s col s' hs F c => need_then (bit e col) _ s' hs F c) _ _ _ h F c

/-! ## What a return of the text is made of -/

theorem planesParts_cut (v : Env) (fo : Forest.Heard) (pp : Aff × List Aff) {tB0 tB1 tP : ℕ}
    (t0 : v.tabAt "b-bits-0" = some tB0) (t1 : v.tabAt "b-bits-1" = some tB1)
    (tp : v.tabAt "b-pin" = some tP) (h : planesParts v fo = some pp) :
    ∃ at0 at1 count,
      (Forest.planeCols fo.shape v.y.h.lmb).toBool = true ∧
      OnBytes.Desc.First.K4.planesAt fo v.y.h.lmb 0 (k4Bit v tB0 tB1) = some at0 ∧
      OnBytes.Desc.First.K4.planesAt fo v.y.h.lmb 1 (k4Bit v tB0 tB1) = some at1 ∧
      (List.range (fo.shape.NC * 2 ^ (fo.shape.kT + 5 - v.y.h.lmb))).foldlM
        (fun (f : Aff) c => (k4Pin v tP c).map fun x => f + x)
        (Aff.ofConst (negE (ofF (2 ^ fo.shape.v - fo.shape.padding).toUInt64))) = some count ∧
      pp = (Aff.scale at0 fo.leavesA, [Aff.slot fo.sBit - at1, count]) := by
  unfold planesParts at h
  obtain ⟨x0, e0, h⟩ := Option.bind_eq_some_iff.1 h
  obtain rfl : x0 = tB0 := Option.some.inj (e0.symm.trans t0)
  obtain ⟨x1, e1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain rfl : x1 = tB1 := Option.some.inj (e1.symm.trans t1)
  obtain ⟨xp, ep, h⟩ := Option.bind_eq_some_iff.1 h
  obtain rfl : xp = tP := Option.some.inj (ep.symm.trans tp)
  obtain ⟨_, hc, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨at0, h0, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨at1, h1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨count, h2, h⟩ := Option.bind_eq_some_iff.1 h
  refine ⟨at0, at1, count, ?_, h0, h1, h2, (Option.some.inj h).symm⟩
  unfold OnBytes.Desc.First.K4.need at hc
  split at hc
  · assumption
  · cases hc

/-! ## The text is the run's text -/

theorem planeClaimsF_of_parts (v : Env) (fo : Forest.Heard) (a0 c1 c2 rowL : Aff) (F F' : Fork)
    {tB0 tB1 tP : ℕ} (t0 : v.tabAt "b-bits-0" = some tB0) (t1 : v.tabAt "b-bits-1" = some tB1)
    (tp : v.tabAt "b-pin" = some tP)
    (hpp : planesParts v fo = some (a0, [c1, c2]))
    (hrow : ownClaim fo.leaves oneE a0 F = some (rowL, F')) :
    planeClaimsF fo v.y.h.lmb (fun e x => Fl.need (k4Bit v tB0 tB1 e x))
      (fun c => Fl.need (k4Pin v tP c)) F [] = .ok ((#[rowL, c1, c2], F'), []) := by
  obtain ⟨at0, at1, count, hc, h0, h1, h2, e⟩ := planesParts_cut v fo _ t0 t1 tp hpp
  obtain ⟨ea, el⟩ := Prod.mk.inj e
  obtain ⟨e1, el⟩ := List.cons.inj el
  obtain ⟨e2, -⟩ := List.cons.inj el
  unfold ownClaim at hrow
  obtain ⟨⟨⟨row, ps⟩, G, u⟩, hr, er⟩ := Option.map_eq_some_iff.1 hrow
  obtain ⟨er1, er2⟩ := Prod.mk.inj er
  have hr' : Fl.pscRow fo.leaves oneE a0 F [] = .ok (((row, ps), G), u) := hr
  have hu : u = [] := (Fo.Tp.pscRow_ok _ _ _ _ _ _ _ _ _ hr').2.2.2.2.1
  unfold planeClaimsF
  refine (Fo.Tp.bind_ok _ _ F [] _).2 ⟨(), F, [], (Fo.Tp.must_ok _ F [] _).2 ⟨hc, rfl⟩, ?_⟩
  refine (Fo.Tp.bind_ok _ _ F [] _).2 ⟨at0, F, [], planesAtF_of fo _ 0 _ at0 h0 F [], ?_⟩
  refine (Fo.Tp.bind_ok _ _ F [] _).2 ⟨at1, F, [], planesAtF_of fo _ 1 _ at1 h1 F [], ?_⟩
  refine (Fo.Tp.bind_ok _ _ F [] _).2 ⟨count, F, [],
    foldlM_need _ _ (fun s col s' hs F c => need_then (k4Pin v tP col) _ s' hs F c) _ _ _ h2 F [],
    ?_⟩
  refine (Fo.Tp.bind_ok _ _ F [] _).2 ⟨(row, ps), G, u, ?_, ?_⟩
  · rw [← ea]
    exact hr'
  · refine (Fo.Tp.pure_ok _ _ _ _).2 ?_
    have r1 : row = rowL := er1
    have r2 : G = F' := er2
    rw [r1, r2, hu, e1, e2]

/-! ## What the three forms are worth -/

section
variable {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K)

theorem k4_planes_worth (v : Env) (fo : Forest.Heard) (a0 c1 c2 rowL : Aff) (F0 F F' : Fork)
    (first : ℕ) (rs : Rounds K) {tB0 tB1 tP : ℕ} (t0 : v.tabAt "b-bits-0" = some tB0)
    (t1 : v.tabAt "b-bits-1" = some tB1) (tp : v.tabAt "b-pin" = some tP)
    (hpp : planesParts v fo = some (a0, [c1, c2]))
    (hrow : ownClaim fo.leaves oneE a0 F = some (rowL, F'))
    (hI : HeardIs ρ fo F0 (endsOf fo.shape v.y.h.lmb first rs)) (h0 : Later F0 F)
    (hok : FoNums.ok fo.shape = true) (hF : Sized F) (H : Fork) (hH : Later F' H)
    (ν : _root_.Fo.Pl → K) (entry : ℕ → ℕ → ℕ → K) :
    ([rowL, c1, c2].map fun a => a.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)) =
      [claimLeaves fo.shape v.y.h.lmb first rs ν fun col =>
          ((k4Bit v tB0 tB1 0 col).getD {}).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry),
        claimBits fo.shape v.y.h.lmb first rs ν fun col =>
          ((k4Bit v tB0 tB1 1 col).getD {}).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry),
        Pin.countK fo.shape v.y.h.lmb fun col =>
          ((k4Pin v tP col).getD {}).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)] := by
  have hrun := planeClaimsF_of_parts v fo a0 c1 c2 rowL F F' t0 t1 tp hpp hrow
  obtain ⟨-, -, -, -, hv⟩ := Fo.Tp.planes_claim ρ fo v.y.h.lmb first rs
    (fun e x => Fl.need (k4Bit v tB0 tB1 e x)) (fun c => Fl.need (k4Pin v tP c))
    (fun _ _ => quiet_need _) (fun _ => quiet_need _) F0 F F' [] [] _ hrun hI h0 hok hF
  have w := hv H hH ν entry
  simp only [got_need] at w
  exact w

/-- **THE END: the row out's item "planes", at the layers' own text.** -/
theorem k4_planes_out (v : Env) (fo : Forest.Heard) (a0 c1 c2 rowL : Aff) (F0 F F' H : Fork)
    (first : ℕ) (ν : _root_.Fo.Pl → K) (entry : ℕ → ℕ → ℕ → K) {tB0 tB1 tP : ℕ}
    (t0 : v.tabAt "b-bits-0" = some tB0) (t1 : v.tabAt "b-bits-1" = some tB1)
    (tp : v.tabAt "b-pin" = some tP)
    (hpp : planesParts v fo = some (a0, [c1, c2]))
    (hrow : ownClaim fo.leaves oneE a0 F = some (rowL, F'))
    (hok : FoNums.ok fo.shape = true) (hF : Sized F) (h0 : Later F0 F) (hH : Later F' H)
    (hz : ∀ f ∈ [rowL, c1, c2], f.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) = 0)
    (b0 : ∀ col, col < fo.shape.NC * 2 ^ (fo.shape.kT + 5 - v.y.h.lmb) →
      ((k4Bit v tB0 tB1 0 col).getD {}).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
        colsK fo.shape v.y.h.lmb (rdA ρ fo.zb0) ν col)
    (b1 : ∀ col, col < fo.shape.NC * 2 ^ (fo.shape.kT + 5 - v.y.h.lmb) →
      ((k4Bit v tB0 tB1 1 col).getD {}).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
        colsK fo.shape v.y.h.lmb (rdA ρ fo.zb1) ν col)
    (pn : ∀ col, col < fo.shape.NC * 2 ^ (fo.shape.kT + 5 - v.y.h.lmb) →
      ((k4Pin v tP col).getD {}).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
        pinColK v.y.h.lmb ν col) :
    K3OutPlanes fo.shape v.y.h.lmb first ν ρ fo F0 := by
  intro rs hI
  have w := k4_planes_worth ρ v fo a0 c1 c2 rowL F0 F F' first rs t0 t1 tp hpp hrow hI h0 hok hF H
    hH ν entry
  rw [claimLeaves_congr _ _ _ _ _ _
      (colsK fo.shape v.y.h.lmb (endsOf fo.shape v.y.h.lmb first rs).zb0 ν)
      (fun col hc => by rw [← hI.zb0]; exact b0 col hc),
    claimBits_congr _ _ _ _ _ _
      (colsK fo.shape v.y.h.lmb (endsOf fo.shape v.y.h.lmb first rs).zb1 ν)
      (fun col hc => by rw [← hI.zb1]; exact b1 col hc),
    Cb.Fo.PlaneClaims.countK_congr _ _ _ _ fun col hc => pn col hc] at w
  have z : ∀ y ∈ [rowL, c1, c2].map (fun a =>
      a.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)), y = 0 := by
    intro y hy
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hy
    exact hz f hf
  rw [w] at z
  exact ⟨z _ (by simp), z _ (by simp), z _ (by simp)⟩

/-! ## The end in the letters of the layers' own first run -/

/-- **The three true reads, as one sentence**: at the three tables' first entries, whatever they
are: the form that the text reads at a column is worth, in H's world, the library's value of that
column at the leaves' point, at the bits' point, and the column's count. -/
def K4ReadsTrue (v : Env) (fo : Forest.Heard) (H : Fork) (ν : _root_.Fo.Pl → K)
    (entry : ℕ → ℕ → ℕ → K) : Prop :=
  ∀ tB0 tB1 tP, v.tabAt "b-bits-0" = some tB0 → v.tabAt "b-bits-1" = some tB1 →
    v.tabAt "b-pin" = some tP →
    (∀ col, col < fo.shape.NC * 2 ^ (fo.shape.kT + 5 - v.y.h.lmb) →
      ((k4Bit v tB0 tB1 0 col).getD {}).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
        colsK fo.shape v.y.h.lmb (rdA ρ fo.zb0) ν col) ∧
    (∀ col, col < fo.shape.NC * 2 ^ (fo.shape.kT + 5 - v.y.h.lmb) →
      ((k4Bit v tB0 tB1 1 col).getD {}).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
        colsK fo.shape v.y.h.lmb (rdA ρ fo.zb1) ν col) ∧
    (∀ col, col < fo.shape.NC * 2 ^ (fo.shape.kT + 5 - v.y.h.lmb) →
      ((k4Pin v tP col).getD {}).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
        pinColK v.y.h.lmb ν col)

/-- Where the text returns, its three tables are there. -/
theorem planesParts_tabs {v : Env} {fo : Forest.Heard} {pp : Aff × List Aff}
    (h : planesParts v fo = some pp) :
    ∃ tB0 tB1 tP, v.tabAt "b-bits-0" = some tB0 ∧ v.tabAt "b-bits-1" = some tB1 ∧
      v.tabAt "b-pin" = some tP := by
  unfold planesParts at h
  obtain ⟨x0, e0, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨x1, e1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨xp, ep, -⟩ := Option.bind_eq_some_iff.1 h
  exact ⟨x0, x1, xp, e0, e1, ep⟩

/-- What a return of the layers' first run is made of, as far as the planes go. -/
theorem front_cut {rows : Bool} {P : OnBytes.Model.Layer.Pub} {g : ℕ}
    {o : OnBytes.Model.Layer.Own} {F G : Fork} {fs : Array Aff}
    (h : OnBytes.Desc.First.K4.formsFrontWith rows P g o F = some (fs, G)) :
    ∃ (F1 F2 : Fork) (pp : Aff × List Aff) (rowL : Aff),
      F.hideRun o.H.tV.p.first (Array.replicate o.H.tV.p.walk.1.length zeroE)
        (subE zeroE oneE) = some F1 ∧
      planesParts o.v o.H.fo = some pp ∧
      ownClaim o.H.fo.leaves oneE pp.1 F1 = some (rowL, F2) ∧
      rowL ∈ fs.toList ∧ (∀ f ∈ pp.2, f ∈ fs.toList) ∧
      G = (if rows then F2.paid o.H.fo.owedObjects else F2).paid o.H.fo.owedPlanes := by
  unfold OnBytes.Desc.First.K4.formsFrontWith at h
  obtain ⟨sh, _, h1⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨rowV, F1⟩, a2, h2⟩ := Option.bind_eq_some_iff.mp h1
  dsimp only at h2
  obtain ⟨pp, a3, h3⟩ := Option.bind_eq_some_iff.mp h2
  obtain ⟨⟨rowL, F2⟩, a4, h4⟩ := Option.bind_eq_some_iff.mp h3
  dsimp only at h4
  obtain ⟨l, a5, h5⟩ := Option.bind_eq_some_iff.mp h4
  obtain ⟨-, -, r2⟩ := OnBytes.Desc.First.K4.ownClaim_some a2
  have e := Option.some.inj h5
  have ef : fs = l.toArray := (congrArg Prod.fst e).symm
  obtain ⟨-, -, -, -, -, -, -, m8, m9, -⟩ := OnBytes.Desc.First.K4.mem_front a5
  refine ⟨F1, F2, pp, rowL, r2, a3, a4, ?_, ?_, (congrArg Prod.snd e).symm⟩
  · rw [ef]
    exact m8
  · intro f hf
    rw [ef]
    exact m9 pp a3 f hf

/-- **THE END IN THE LETTERS OF THE LAYERS' OWN FIRST RUN.** -/
theorem k4_planes_out_front {rows : Bool} {P : OnBytes.Model.Layer.Pub} {g : ℕ}
    {o : OnBytes.Model.Layer.Own} {F G : Fork} {fs : Array Aff}
    (h : OnBytes.Desc.First.K4.formsFrontWith rows P g o F = some (fs, G)) (F0 : Fork) (first : ℕ)
    (ν : _root_.Fo.Pl → K) (entry : ℕ → ℕ → ℕ → K) (hok : FoNums.ok o.H.fo.shape = true)
    (hF : Sized F) (h0 : _root_.Fo.Later F0 F)
    (hz : ∀ f ∈ fs.toList, f.value ρ (G.worldOf ρ (fun j => ν (.mask j)) entry) = 0)
    (hT : K4ReadsTrue ρ o.v o.H.fo G ν entry) :
    K3OutPlanes o.H.fo.shape o.v.y.h.lmb first ν ρ o.H.fo F0 := by
  obtain ⟨F1, F2, pp, rowL, r2, a3, a4, m1, m2, eG⟩ := front_cut h
  obtain ⟨tB0, tB1, tP, t0, t1, tp⟩ := planesParts_tabs a3
  obtain ⟨at0, at1, count, -, -, -, -, e⟩ := planesParts_cut o.v o.H.fo pp t0 t1 tp a3
  subst e
  obtain ⟨b0, b1, pn⟩ := hT tB0 tB1 tP t0 t1 tp
  have hF1 : Sized F1 := hideRun_sized hF r2
  have hL1 : _root_.Fo.Later F0 F1 := h0.trans (_root_.Fo.hideRun_later hF r2)
  have hL2 : _root_.Fo.Later F2 G := by
    rw [eG]
    split
    · exact (paid_laterFo _ _).trans (paid_laterFo _ _)
    · exact paid_laterFo _ _
  refine k4_planes_out ρ o.v o.H.fo _ _ _ rowL F0 F1 F2 G first ν entry t0 t1 tp a3 a4 hok hF1 hL1
    hL2 (fun f hf => ?_) b0 b1 pn
  rcases List.mem_cons.1 hf with rfl | hf
  · exact hz _ m1
  · exact hz _ (m2 _ hf)

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.planeClaimsF_of_parts
#print axioms VerifiableInference.OnPublicFiles.k4_planes_worth
#print axioms VerifiableInference.OnPublicFiles.k4_planes_out
#print axioms VerifiableInference.OnPublicFiles.front_cut
#print axioms VerifiableInference.OnPublicFiles.k4_planes_out_front
