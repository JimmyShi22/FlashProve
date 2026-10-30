-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/AtShape.lean: THE LAYERS' OWN ROUNDS (K4): ITS HEARING MEMBER AS A
STEP ON THE CHAIN's SHAPE ALONE (chainSh, Johnson/Desc/First/Shape/Chain.lean), at the block at the
state that the first chain carries (blockAtC, Johnson/Desc/First/K4/AtC.lean). General laws: nothing
is evaluated.

  rowSh_blank, treeSh_blank, ledSh_blank   the blank ledger of a shape has that shape.
  blankRound, blankTape, tape_alike   the tape of a table's shape: every element sent 0, every
                  element drawn 1.
  **ownOf p h L** K4's HEARING ON SHAPES: the hearing itself at the blank lookup's record, the blank
                  ledger, the blank tape of K4's own table and as many tokens 0 as the layout
                  counts: the shape of what it leaves, its tables' shapes, the ledger's shape
                  behind. A function of the plan and two components of the chain's shape.
  **own_of_shape**   what the hearing leaves at a state has that shape, where the stretch fits K4's
                  table and both return.
  **k4G p**       THE STEP: it reads .here, .look and .led; it lays .led, .own, .tables, .rowsOwed.
  **k4_carries**  a yes of the block at the state, and the step returns at the state's shape: then
                  the step has returned the shape of the state behind. NO PREMISE ON A VALUE, NONE
                  ON THE PLAN.

Limits. THAT THE STEP RETURNS AT A SHAPE WHICH THE CHAIN REACHES IS NOT SHOWN. The step is as dear
as the hearing. THE STEP IS LAXER THAN THE MEMBER ON TWO POINTS OF STRUCTURE: K4's block refuses
where a count of rows waits (stretchB's first clause, AtChain.lean), and k4G never reads rowsOwed;
the block refuses where the stretch is not used up (heardAt takes `some (o, G, [])` alone), and
ownOf drops what is left of the blank tape. So a return of k4G does not say that the member's guards
on the structure pass; k4_carries, which stands under a yes, is not touched.
(Johnson/AtFull/Shape/K4Fit.lean lays the first test in front of the step.) own_of_shape spends of
stretchB the fit and the strict reading alone. ledBlank here is K8.Honest's (EqAllShape.lean): of
its namesake H2K5.Honest.ledBlank, which lays no root, ledSh_blank is not shown. "Returns" (the step
returns, and the tests on values hold: then the block says yes) is not here:
Johnson/Desc/First/K4/Returns/AtChainPays.lean has a law of that kind under tests with code on the
plan and the shape in front, not under this step's return. Nothing on soundness, completeness or
hiding.
-/
import Johnson.Desc.First.K4.Returns.FlRelTop
import Johnson.Desc.First.K4.Returns.RunPays
import Johnson.Desc.K8.Honest.EqAllShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt
open OnBytes OnBytes.K.Kc D6.Ret
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer (Pub HPlan2 Own)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.First.K8.Honest (rowBlank treeBlank ledBlank)

/-! ## The way back for the ledger is a way back -/

theorem rowSh_blank (r : RowSh) : rowSh (rowBlank r) = r := by
  obtain ⟨a, b, c, d, e, f⟩ := r
  simp [rowSh, rowBlank, RowSh.mk, RowSh.coef, RowSh.entries, RowSh.col0, RowSh.form, RowSh.ones,
    RowSh.first]

theorem treeSh_blank (T : TreeSh) : treeSh (treeBlank T) = T := by
  obtain ⟨a, b, c, d, e, f⟩ := T
  cases b <;> cases f <;>
    simp [treeSh, treeBlank, TreeSh.mk, TreeSh.name, TreeSh.symbols, TreeSh.R, TreeSh.K,
      TreeSh.rows, TreeSh.rooted, rowSh_blank, Function.comp_def]

theorem ledSh_blank (L : LedSh) : ledSh (ledBlank L) = L := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩ := L
  simp [ledSh, ledBlank, LedSh.mk, LedSh.ns, LedSh.shown, LedSh.factors, LedSh.got, LedSh.owed,
    LedSh.planClaims, LedSh.trees, LedSh.next, LedSh.coefs, LedSh.claims, LedSh.drawn,
    LedSh.handed, LedSh.shut, treeSh_blank, Function.comp_def]

/-! ## A blank tape -/

/-- A round of a row's shape: every element sent is 0; every element drawn is 1, so that the one
drawn element which the hearing asks to be other than 0 is. -/
def blankRound (d : Rd) : FlatRound :=
  ⟨some d.name.name, d.notZero, d.rows, List.replicate d.sent zeroE, List.replicate d.drawn oneE⟩

/-- The tape of a table's shape. -/
def blankTape (ds : List Rd) : Tape := ds.map blankRound

theorem tape_alike : ∀ {ds : List Rd} {t : Tape}, TapeOf ds t → TapeAlike t (blankTape ds)
  | [], [], _ => rfl
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | d :: ds, r :: t, h => by
    obtain ⟨⟨a1, a2, a3, a4, a5⟩, h2⟩ : At d r ∧ TapeOf ds t := h
    refine alike_mk ?_ (tape_alike h2)
    show (r.name, r.nz, r.rows, r.sent.length, r.drawn.length) =
      (some d.name.name, d.notZero, d.rows, (List.replicate d.sent zeroE).length,
        (List.replicate d.drawn oneE).length)
    rw [a1, a2, a3, a4, a5, List.length_replicate, List.length_replicate]

/-! ## The hearing on shapes -/

/-- **K4's HEARING ON SHAPES**: the hearing itself, at the blank lookup's record, the blank ledger,
the blank tape of K4's own table, and as many tokens 0 as the layout counts: the shape of what it
leaves, its tables' shapes and the ledger's shape behind. A function of the plan, the lookup's
record's shape and the ledger's shape. What is left of the blank tape is dropped: it returns whether
or not the blank run used its tape up. -/
def ownOf (p : Par) (h : HeardAll) (L : LedSh) : Option (OwnSh × List FunSh × LedSh) :=
  (hearFl { p.P with tokv := Array.replicate p.P.y.T 0 } p.hp p.g h.blank (ledBlank L)
    (blankTape (rounds p.P p.hp p.g))).map fun x =>
      (ownSh x.1, x.1.funs.toList.map funSh, ledSh x.2.1)

/-- **What the hearing leaves at a state has the shape that the hearing on shapes says**, where the
stretch fits K4's table and both return. -/
theorem own_of_shape {p : Par} {s : S} {rs : List Fmt.RoundView} {a : LayOwn} {fo : Forest.Heard}
    {o : Own} {G : Fork} (hh : s.here = .lay a) (hfo : a.fo = some fo)
    (hS : stretchB p s rs = true) (hv : heardAt p s rs = some (o, G))
    {z : OwnSh × List FunSh × LedSh} (hz : ownOf p (heardAll fo) (ledSh a.F) = some z) :
    z = (ownSh o, o.funs.toList.map funSh, ledSh G) := by
  -- the run at the state
  unfold heardAt at hv
  rw [hh] at hv
  have hv' : (a.fo.bind fun fo =>
      match hearFl { p.P with tokv := s.tokv } p.hp p.g fo a.F
          (paired rs (entries p.P p.hp p.g)) with
      | some (o, G, []) => some (o, G)
      | _ => none) = some (o, G) := hv
  rw [hfo] at hv'
  have hv2 : (match hearFl { p.P with tokv := s.tokv } p.hp p.g fo a.F
          (paired rs (entries p.P p.hp p.g)) with
      | some (o, G, []) => some (o, G)
      | _ => none) = some (o, G) := hv'
  cases e : hearFl { p.P with tokv := s.tokv } p.hp p.g fo a.F
      (paired rs (entries p.P p.hp p.g)) with
  | none =>
    rw [e] at hv2
    cases hv2
  | some x =>
    obtain ⟨o', G', u⟩ := x
    rw [e] at hv2
    cases u with
    | cons _ _ => cases hv2
    | nil =>
      obtain ⟨rfl, rfl⟩ : o' = o ∧ G' = G := by
        have k : (o', G') = (o, G) := Option.some.inj hv2
        exact ⟨congrArg (·.1) k, congrArg (·.2) k⟩
      -- the blank run
      obtain ⟨x₀, e₀, rfl⟩ := Option.map_eq_some_iff.1 hz
      obtain ⟨o₀, G₀, u₀⟩ := x₀
      -- the tape has the table's shape
      unfold stretchB at hS
      simp only [Bool.and_eq_true] at hS
      have hT : TapeOf (rounds p.P p.hp p.g) (paired rs (entries p.P p.hp p.g)) :=
        tape_of_fits _ _ hS.1.2 hS.2
      obtain ⟨⟨r1, r2⟩, r3, -⟩ := hear_rel p.P s.tokv (Array.replicate p.P.y.T 0) p.hp p.g
        (fo := fo) (fo' := (heardAll fo).blank) (heardAll_blank _).symm
        a.F (ledBlank (ledSh a.F)) _ _ o' G' [] o₀ G₀ u₀ (ledSh_blank _).symm (tape_alike hT) e e₀
      show (ownSh o₀, o₀.funs.toList.map funSh, ledSh G₀) = _
      rw [← r1, ← r3, show o₀.funs.toList.map funSh = o'.funs.toList.map funSh from r2.symm]

/-- **K4's HEARING MEMBER AS A STEP ON THE CHAIN's SHAPE ALONE.** LAXER THAN THE MEMBER ON TWO
POINTS OF STRUCTURE: it never reads rowsOwed (it lays it to none), and its hearing does not ask that
the tape be used up: see the head's Limits. -/
def k4G (p : Par) (a : ChainSh) : Option ChainSh :=
  if a.here != 1 then none else
  match a.look, a.led with
  | some h, some L =>
    (ownOf p h L).map fun z =>
      (((a.setLed z.2.2).layOwn (some z.1)).layTables (some z.2.1)).setRowsOwed none
  | _, _ => none

/-- **CARRIES, FROM A YES ALONE**: a yes of K4's block at the state, and the step returns at the
state's shape: then the step has returned the shape of the state behind. No premise on a value. -/
theorem k4_carries {p : Par} {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (blockAtC p).decide s rs gs = .ok s') {t : ChainSh} (hg : k4G p (chainSh s) = some t) :
    t = chainSh s' := by
  obtain ⟨a, o, G, hh, hv, rfl⟩ := decide_lays h
  have hS : stretchB p s rs = true := by
    have k := k4_seat p s rs gs
    rw [h] at k
    by_contra hc
    rw [if_neg hc] at k
    cases k
  have hled : (chainSh s).led = some (ledSh a.F) := by
    show s.fork?.map ledSh = _
    unfold S.fork?
    rw [hh]
    rfl
  have hlook : (chainSh s).look = a.fo.map heardAll := by
    show s.look?.map heardAll = _
    unfold S.look?
    rw [hh]
  have hfin := chainSh_k4Laid s a hh o G
  unfold k4G at hg
  split at hg
  · cases hg
  · rw [hlook, hled] at hg
    cases hfo : a.fo with
    | none =>
      rw [hfo] at hg
      cases hg
    | some fo =>
      rw [hfo] at hg
      obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 hg
      rw [hfo] at hfin
      rw [own_of_shape hh hfo hS hv hz, hfin]

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.rowSh_blank
#print axioms OnBytes.Desc.First.K4.Rt.treeSh_blank
#print axioms OnBytes.Desc.First.K4.Rt.ledSh_blank
#print axioms OnBytes.Desc.First.K4.Rt.tape_alike
#print axioms OnBytes.Desc.First.K4.Rt.own_of_shape
#print axioms OnBytes.Desc.First.K4.Rt.k4_carries
#print axioms OnBytes.Desc.First.K4.Rt.blankRound
#print axioms OnBytes.Desc.First.K4.Rt.blankTape
#print axioms OnBytes.Desc.First.K4.Rt.ownOf
#print axioms OnBytes.Desc.First.K4.Rt.k4G
