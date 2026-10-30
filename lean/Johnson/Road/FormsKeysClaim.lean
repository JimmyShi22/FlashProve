-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysClaim.lean: from one weight claim of a layer sub-proof to a tensor claim of
the library: the steps that all panels share.

The verifier makes a weight claim by ClaimEnv.claim (OnBytes/Model/LayerPanels.lean): it looks up
the unit of a kind at a layer of the group and asks a function fac for one factor for each of the
unit's groups. Johnson/Road/FormsKeysTnP.lean shows that the sum which such a claim speaks of
(claimVal) is the functional of a tensor claim of the library, if the claim's factors weigh the
indices as a list of functions does. This file brings the two together, so that for each panel only
the factors are left to compare.

Main definitions: ClaimFits. Main theorems.
 - claim_inv: what a claim that ClaimEnv.claim returns is made of.
 - claim_Tn: the generic step. For a claim on the unit of kind X at layer lam of the group:
   claimVal is the functional of the library's claim on unit number first (L0 + lam) + i, where i
   is the place of X among the kinds of the layer, with any list of functions fs that the factors
   agree with.
 - facs_two, facs_three: the factors of a unit with two or three groups, one by one.
 - wid_le_lamS, wcol_le_lamS: on the library alone: a panel's bits are among those of all panels.
 - Ec_at, Er_at: the factor that the verifier makes from the coordinates of the batched sumcheck's
   place weighs an index as the library's Ec or Er of a panel does.

What is compared with what. claim_inv: the verifier with itself. claim_Tn, Ec_at, Er_at: the
verifier's claim and factors against the library's TClaim.Tn, Pan.Ec, Pan.Er.

The record ClaimFits gathers what is asked: the two shapes agree (SizedW; five widths and the two
numbers of layers of a group); the layout of the weights is what wsLayOf returns; L0 is the number
of the group's first layer, it is even, and the group's layers are layers of the model; there are
routed experts; and ζ is the batched sumcheck's point in the library's order, on the library's lamS
D coordinates. The verifier's own number of rounds is not read: facRs reads the coordinates of the
place from bit 0 up, and it is enough that ζ holds them in the last places.
Johnson/Road/FormsKeysAim.lean concludes it from the two layouts (claimFits_of_layout), and
Johnson/Road/FormsKeysAimV.lean from the calls of the verifier's public part, with sizes of the
library that meet what is left. The sizes dimOf h of Johnson/Road/FormsKeysFits.lean have the
vocabulary 0; the record then asks that wsLayOf return on a shape with the vocabulary 0, which by
its text it does not (no theorem shows that). The points of the lookup's calls are not in it: they
enter through the factors on the segments' entries, which other files compare.

What is not claimed: see Johnson/Road/FormsKeysKit.lean. The program does not import this file.
-/
import Johnson.Road.FormsKeysTnP
import Johnson.Road.FormsKeysFacRs
import Johnson.Road.FormsKeysFold
import Johnson.Road.FormsKeysVec
import Inst.Model.FF.Objects

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading WsShape WsGrp WsUnit WsLay WsFac WsClaim wsLayOf)
open OnBytes.Model.Layer (ClaimEnv)
open Inst.Model (TClaim)
open Inst.Model.Layout (UnitS units first)
open Inst.Model.FFSeg (Dim Pan pans panTotal lamS)

variable {K : Type} [Field K]

/-! ## Lists -/

/-- A list whose image has two members has two members. -/
theorem map_two {α β : Type} {f : α → β} {l : List α} {a b : β} (h : l.map f = [a, b]) :
    ∃ x y, l = [x, y] ∧ f x = a ∧ f y = b := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨w, l⟩⟩⟩
  · simp at h
  · simp at h
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
    exact ⟨x, y, rfl, h.1, h.2⟩
  · simp at h

/-- A list whose image has three members has three members. -/
theorem map_three {α β : Type} {f : α → β} {l : List α} {a b c : β} (h : l.map f = [a, b, c]) :
    ∃ x y w, l = [x, y, w] ∧ f x = a ∧ f y = b ∧ f w = c := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨w, _ | ⟨v, l⟩⟩⟩⟩
  · simp at h
  · simp at h
  · simp at h
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
    exact ⟨x, y, w, rfl, h.1, h.2.1, h.2.2⟩
  · simp at h

/-- A member's share is at most the sum. -/
theorem le_sum_map {α : Type} (f : α → ℕ) : ∀ (l : List α) (x : α), x ∈ l → f x ≤ (l.map f).sum
  | [], _, h => by cases h
  | y :: l, x, h => by
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with e | h'
    · rw [e]
      exact Nat.le_add_right _ _
    · exact Nat.le_trans (le_sum_map f l x h') (Nat.le_add_left _ _)

/-! ## What a claim is made of -/

/-- A claim that ClaimEnv.claim returns: its number is that of the unit of kind X at the layer, the
layout has a unit under that number, and the claim's factors are fac's, one for each group. -/
theorem claim_inv {c : ClaimEnv} {X lam : ℕ} {fac : WsGrp → Option WsFac} {cl : WsClaim}
    (h : c.claim X lam fac = some cl) :
    ∃ u, c.wsLay.unitOf X (c.v.lay lam) = some cl.ui ∧ c.wsLay.U[cl.ui]? = some u ∧
      u.g.mapM fac = some cl.f := by
  unfold ClaimEnv.claim at h
  obtain ⟨ui, h1, h⟩ := bind_some h
  obtain ⟨u, h2, h⟩ := bind_some h
  obtain ⟨F, h3, h⟩ := bind_some h
  cases h
  exact ⟨u, h1, h2, h3⟩

/-! ## The record of hypotheses -/

/-- What is asked for a weight claim of the verifier to be read as a tensor claim of the library. -/
structure ClaimFits (ρ : Reading K) (c : ClaimEnv) (s : WsShape) (D : Dim) (lk L0 : ℕ)
    (ζ : ℕ → K) : Prop where
  /-- the shape of the weights agrees with the library's parameters -/
  sized : SizedW s D.P
  /-- the layout of the weights is the one that wsLayOf returns, with routed experts -/
  lay : wsLayOf s true lk = .ok c.wsLay
  /-- the number of the group's first layer in the model -/
  base : L0 = c.v.g * c.v.y.Lam
  /-- it is even -/
  even : L0 % 2 = 0
  /-- there are routed experts -/
  p3 : c.v.y.h.p3 = true
  /-- the group's layers are layers of the model -/
  layers : ∀ lam, lam < c.v.y.Lam → L0 + lam < D.P.layers
  /-- the batched sumcheck's point in the library's order: the top bit's coordinate first -/
  zeta : ∀ t, t < lamS D → ζ t = ρ.val (c.rs.getD (lamS D - 1 - t) zeroE)
  /-- the width of the residual stream -/
  d : c.v.y.h.d = D.d
  /-- the hidden units of a layer -/
  f : c.v.y.h.f = D.f
  /-- the hidden units of an expert -/
  fe : c.v.y.h.fe = D.fe
  /-- the experts -/
  NE : c.v.y.h.NE = D.nx
  /-- the width of all query heads -/
  dq : c.v.y.dq = D.dq
  /-- the layers of a group -/
  Lam : c.v.y.Lam = D.nl
  /-- those with routed experts -/
  LamM : c.v.y.LamM = D.ne

/-! ## The generic step -/

/-- From a claim of the verifier to a tensor claim of the library. The claim is on the unit of kind
X at layer lam of the group; i is the place of X among the kinds of that layer; U is the library's
unit under the number first (L0 + lam) + i. If the factors that fac gives for the groups of the
verifier's unit agree with the functions fs (hf: there the unit's numbers, coordinates, names and
classes may be used), then the sum that the claim speaks of is the functional of the library's
claim on that unit with the factors fs. -/
theorem claim_Tn {ρ : Reading K} {c : ClaimEnv} {s : WsShape} {D : Dim} {lk L0 : ℕ} {ζ : ℕ → K}
    (F : ClaimFits ρ c s D lk L0 ζ) (W : Wm K) {X lam i : ℕ} {fac : WsGrp → Option WsFac}
    {cl : WsClaim} (hcl : c.claim X lam fac = some cl) (hlam : lam < c.v.y.Lam)
    (hX : (kindsOf (L0 + lam))[i]? = some X) {U : UnitS}
    (hU : (units D.P)[first D.P (L0 + lam) + i]? = some U) {fs : List (ℕ → K)}
    (hf : ∀ u, UnitOK lk u → u.g.map coordOf = U.coords →
      u.g.map (fun y => (y.name, y.cls)) = groupsOf X →
      ∀ Fs, u.g.mapM fac = some Fs → FacsAre ρ (Fs.zip u.g) fs) :
    claimVal ρ c.wsLay W cl = (⟨first D.P (L0 + lam) + i, U, fs⟩ : TClaim K).Tn D.P lk W := by
  obtain ⟨u, h1, h2, h3⟩ := claim_inv hcl
  have hl : c.v.lay lam = L0 + lam := by
    rw [F.base]
    rfl
  have hL := F.layers lam hlam
  rw [hl, (unitOf_eq F.sized F.lay).1 (L0 + lam) hL i X hX] at h1
  have hui : cl.ui = first D.P (L0 + lam) + i := (Option.some.inj h1).symm
  obtain ⟨-, -, -, hall⟩ := layout_eq F.sized F.lay
  obtain ⟨u', hu', ok, hnl, -, -, hco, -, -, hcell⟩ := hall _ U hU
  rw [hui] at h2
  have e : u' = u := Option.some.inj (hu'.symm.trans h2)
  subst e
  have hg := unit_groups F.sized F.lay (L0 + lam) hL i X hX u' hu'
  have hlen : cl.f.length = u'.g.length := (list_mapM_some _ _ _ h3).1
  have hu'' : c.wsLay.U[cl.ui]? = some u' := by
    rw [hui]
    exact hu'
  exact claimVal_Tn ρ hu'' hco hlen hnl hcell (hf u' ok hco hg cl.f h3)

/-- The factors of a unit with two groups. -/
theorem facs_two {ρ : Reading K} {g1 g2 : WsGrp} {fac : WsGrp → Option WsFac} {Fs : List WsFac}
    (h : [g1, g2].mapM fac = some Fs) {f1 f2 : ℕ → K}
    (h1 : ∀ X, fac g1 = some X → ∀ v, v < g1.R → facAt ρ X g1 v = f1 v)
    (h2 : ∀ X, fac g2 = some X → ∀ v, v < g2.R → facAt ρ X g2 v = f2 v) :
    FacsAre ρ (Fs.zip [g1, g2]) [f1, f2] := by
  obtain ⟨X1, r1, e1, ha, rfl⟩ := mapM_cons_some h
  obtain ⟨X2, r2, e2, hb, rfl⟩ := mapM_cons_some ha
  have hr : r2 = [] := by simpa using hb.symm
  subst hr
  exact List.Forall₂.cons (h1 X1 e1) (List.Forall₂.cons (h2 X2 e2) List.Forall₂.nil)

/-- The factors of a unit with three groups. -/
theorem facs_three {ρ : Reading K} {g1 g2 g3 : WsGrp} {fac : WsGrp → Option WsFac}
    {Fs : List WsFac} (h : [g1, g2, g3].mapM fac = some Fs) {f1 f2 f3 : ℕ → K}
    (h1 : ∀ X, fac g1 = some X → ∀ v, v < g1.R → facAt ρ X g1 v = f1 v)
    (h2 : ∀ X, fac g2 = some X → ∀ v, v < g2.R → facAt ρ X g2 v = f2 v)
    (h3 : ∀ X, fac g3 = some X → ∀ v, v < g3.R → facAt ρ X g3 v = f3 v) :
    FacsAre ρ (Fs.zip [g1, g2, g3]) [f1, f2, f3] := by
  obtain ⟨X1, r1, e1, ha, rfl⟩ := mapM_cons_some h
  obtain ⟨X2, r2, e2, hb, rfl⟩ := mapM_cons_some ha
  obtain ⟨X3, r3, e3, hc, rfl⟩ := mapM_cons_some hb
  have hr : r3 = [] := by simpa using hc.symm
  subst hr
  exact List.Forall₂.cons (h1 X1 e1) (List.Forall₂.cons (h2 X2 e2)
    (List.Forall₂.cons (h3 X3 e3) List.Forall₂.nil))

/-- A group of class 'E' of a unit whose numbers fit has o 2^z indices. -/
theorem size_of_ok {lk : ℕ} {u : WsUnit} (ok : UnitOK lk u) {g : WsGrp} (hg : g ∈ u.g)
    (hE : g.cls = 'E') : g.R = g.o * 2 ^ g.z := by
  rcases ok.grp g hg with ⟨-, h, -, -⟩ | ⟨hA, -, -⟩
  · exact h
  · rw [hE] at hA
    exact absurd hA (by decide)

/-! ## The bits of a panel, on the library alone -/

/-- The bits of a panel of the list are among the bits of all panels together. -/
theorem wid_le_lamS (D : Dim) {p : Pan} (hp : p ∈ pans D) : p.wid D ≤ lamS D := by
  have h1 : 2 ^ p.wid D ≤ panTotal D := le_sum_map (fun q : Pan => 2 ^ q.wid D) (pans D) p hp
  have h2 : panTotal D ≤ 2 ^ lamS D := Nat.le_pow_clog (by decide) _
  exact (Nat.pow_le_pow_iff_right (by decide)).mp (Nat.le_trans h1 h2)

/-- So are the bits of its columns. -/
theorem wcol_le_lamS (D : Dim) {p : Pan} (hp : p ∈ pans D) : p.wcol D ≤ lamS D :=
  Nat.le_trans (Nat.le_add_left _ _) (wid_le_lamS D hp)

/-! ## The factors from the coordinates of the batched sumcheck's place -/

section Place

variable {ρ : Reading K} {c : ClaimEnv} {s : WsShape} {D : Dim} {lk L0 : ℕ} {ζ : ℕ → K}
  (F : ClaimFits ρ c s D lk L0 ζ)

include F in
/-- The factor from the lowest wy coordinates of the place, where wy is the number of bits of a
column of the library's panel p, weighs an index as the library's Ec of the panel does. -/
theorem Ec_at {p : Pan} (hp : p ∈ pans D) {G : WsGrp} (hE : G.cls = 'E')
    (hR : G.R = G.o * 2 ^ G.z) {wy : ℕ} (hwy : wy = p.wcol D) {X : WsFac}
    (hX : c.facRs G 0 wy = some X) : ∀ v, v < G.R → facAt ρ X G v = p.Ec D ζ v := by
  intro v hv
  have hle := wcol_le_lamS D hp
  subst hwy
  rw [facRs_lib ρ c G 0 (p.wcol D) (lamS D) (beq_iff_eq.mpr hE) (by omega) hX v (hR ▸ hv),
    Nat.zero_add]
  unfold Pan.Ec
  exact eqN_agree _ _ (fun j hj => (F.zeta _ (by omega)).symm) v

include F in
/-- The factor from the coordinates of the place above those of a column, as many as the rows of the
library's panel p have bits, weighs an index as the library's Er of the panel does. -/
theorem Er_at {p : Pan} (hp : p ∈ pans D) {G : WsGrp} (hE : G.cls = 'E')
    (hR : G.R = G.o * 2 ^ G.z) {wk wr : ℕ} (hwk : wk = p.wcol D)
    (hwr : wr = Nat.clog 2 (p.nr D)) {X : WsFac} (hX : c.facRs G wk wr = some X) :
    ∀ v, v < G.R → facAt ρ X G v = p.Er D ζ v := by
  intro v hv
  have hle := wid_le_lamS D hp
  have hw : p.wid D = Nat.clog 2 (p.nr D) + p.wcol D := rfl
  subst hwk hwr
  rw [facRs_lib ρ c G (p.wcol D) (Nat.clog 2 (p.nr D)) (lamS D) (beq_iff_eq.mpr hE) (by omega) hX
    v (hR ▸ hv)]
  unfold Pan.Er
  have e1 : p.wid D - p.wcol D = Nat.clog 2 (p.nr D) := by omega
  have e2 : p.wcol D + Nat.clog 2 (p.nr D) = p.wid D := by omega
  rw [e1, e2]
  exact eqN_agree _ _ (fun j hj => (F.zeta _ (by omega)).symm) v

end Place

#print axioms claim_inv
#print axioms claim_Tn
#print axioms facs_two
#print axioms facs_three
#print axioms wid_le_lamS
#print axioms Ec_at
#print axioms Er_at

end OnBytes.Road
