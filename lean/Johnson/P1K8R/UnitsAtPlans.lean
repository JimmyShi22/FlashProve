-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/UnitsAtPlans.lean: THE SMALLNESS TEST: THE PUBLIC TEST `unitsLaid`
(Johnson/Desc/K8/Honest/FallCount.lean) SAYS YES AT THE PLAN OF EVERY ATTENTION SUB-PROOF AND OF THE
HEAD's, AT THE PLAN's OWN LENGTHS OF THE VECTORS OF READS. Lemmas; none of the library's goals. On
the routines that make a plan alone: no state, no prover.

The like of Johnson/P1K8R/UnitsAtPlan.lean (feed-forward sub-proofs). Behind the routine that lays
the arrays these two sorts of plan pass through routines that note owners and borders; these write
two lists of places alone.
  `SameU a b`   b has a's fields that `SameP` names, and a's parts of the vectors given to tables
      and lengths
  `borderMeans_sameU`, `ownerPlace_sameU`, `ownerPlaces_sameU`, `owners_sameU`, `ownerHeld_sameU`
      the library's proofs on `SameP` (OnBytes/Tie/Pv/Lookup/Ends/FoZPublic.lean, FoZMade.lean),
      repeated for the three fields more
  `seam_units`, `planA_units`, `planH2_units`
  **`public_A_units`**, **`public_H_units`**   at every attention member A[g] and at the head's
      member H of the public parameters that Verify.publicOf returns
Limits. Nothing on a value that a later routine of a run has turned.

-/
import Johnson.P1K8R.UnitsAtPlan
import OnBytes.Tie.Pv.Lookup.Ends.FoZPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc.First.K8.Honest (unitsLaid)
open _root_.Fo (SameP SameRec pureE_ok)
open _root_.Fo.BatRows _root_.Fo.Pub _root_.Fo.ZPlan

/-- The fields that `SameP` names, and three more. -/
structure SameU (a b : HTailF2) : Prop where
  same : SameP a b
  tabFirst : b.tabFirst = a.tabFirst
  tabLen : b.tabLen = a.tabLen
  nUF : b.nUF = a.nUF

theorem SameU.refl (a : HTailF2) : SameU a a := ⟨SameP.refl a, rfl, rfl, rfl⟩

theorem SameU.trans {a b c : HTailF2} (h : SameU a b) (k : SameU b c) : SameU a c :=
  ⟨h.same.trans k.same, k.tabFirst.trans h.tabFirst, k.tabLen.trans h.tabLen, k.nUF.trans h.nUF⟩

theorem borderMeans_sameU {a b : HTailF2} {iF ownerNo index : Nat}
    (e : a.borderMeans iF ownerNo index = .ok b) : SameU a b := by
  obtain ⟨b1, b2, b3⟩ := borderMeans_tabs e
  exact ⟨borderMeans_sameP e, b1, b2, b3⟩

theorem ownerPlace_sameU {g : Nat} {O X X' : Verify.SubPlan}
    (h : Verify.attentionOwnerPlace g O X = .ok X') : SameU X.tl X'.tl := by
  unfold Verify.attentionOwnerPlace at h
  obtain ⟨tl, h1, h⟩ := bindE_ok h
  obtain ⟨own, _, h⟩ := bindE_ok h
  dsimp only at h
  split at h
  · cases h
  · obtain rfl := Except.ok.inj h
    exact borderMeans_sameU h1

/-- What the loop keeps. -/
def SameUKept (A out : Array Verify.SubPlan) : Prop :=
  ∀ (i : Nat) (s : Verify.SubPlan), out[i]? = some s → ∃ s0, A[i]? = some s0 ∧ SameU s0.tl s.tl

theorem ownerPlaces_sameU (G A : Array Verify.SubPlan) : ∀ (l : List Nat)
    (out r : Array Verify.SubPlan), SameUKept A out →
    l.foldlM (fun (out : Array Verify.SubPlan) g =>
      match G[g]?, out[g]? with
      | some O, some X => do pure (out.set! g (← Verify.attentionOwnerPlace g O X))
      | _, _ => throw "internal-a-owner-shape") out = .ok r → SameUKept A r
  | [], out, r, hk, h => by
    obtain rfl : out = r := Except.ok.inj h
    exact hk
  | g :: l, out, r, hk, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨out1, h1, h⟩ := bindE_ok h
    refine ownerPlaces_sameU G A l out1 r ?_ h
    split at h1
    · rename_i O X hO hX
      obtain ⟨X', h2, h1⟩ := bindE_ok h1
      obtain rfl := Except.ok.inj h1
      intro i s hi
      by_cases hig : i = g
      · subst hig
        obtain ⟨s0, e0, a0⟩ := hk i X hX
        have hlt : i < out.size := by
          obtain ⟨hl, _⟩ := Array.getElem?_eq_some_iff.1 hX
          exact hl
        have e : (out.set! i X')[i]? = some X' := by
          simp [Array.set!, hlt]
        rw [e] at hi
        obtain rfl := Option.some.inj hi
        exact ⟨s0, e0, a0.trans (ownerPlace_sameU h2)⟩
      · have e : (out.set! g X')[i]? = out[i]? := by
          simp [Array.set!, Ne.symm hig]
        rw [e] at hi
        exact hk i s hi
    · cases h1

theorem owners_sameU {p4 : Bool} {NGr : Nat} {G A r : Array Verify.SubPlan}
    (h : Verify.attentionOwners p4 NGr G A = .ok r) : SameUKept A r := by
  unfold Verify.attentionOwners at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    exact ownerPlaces_sameU G A _ A r (fun i s hi => ⟨s, hi, SameU.refl _⟩) h
  · obtain rfl : A = r := Except.ok.inj h
    exact fun i s hi => ⟨s, hi, SameU.refl _⟩

theorem ownerHeld_sameU {O : Head.Owner} {NGr : Nat} {tl tl' : HTailF2} {Fp : Fork} {Tp : Tail2}
    (e : Head.ownerHeld O NGr tl Fp Tp = .ok tl') : SameU tl tl' := by
  unfold Head.ownerHeld at e
  dsimp only at e
  split at e
  · obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl2, hB, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain rfl := pureE_ok e
    exact borderMeans_sameU hB
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

/-! ## Attention -/

theorem seamPlan_nU {s s' : Attention.Seam} {nU3 hb hbLine : Nat}
    (e : s.plan nU3 hb hbLine = .ok s') : s'.nU = #[0, 0, nU3] := by
  unfold Attention.Seam.plan at e
  dsimp only at e
  obtain ⟨⟨tl1, Fp, T⟩, hA, e⟩ := bindE_ok e
  dsimp only at e
  split at e
  · cases e
  · obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    cases e
    rfl

theorem seam_units {g : Settings} {m : Array TMat} {tau col0F ktO aO nU3 hb hbLine : Nat}
    {s s' : Attention.Seam} (e : Attention.Seam.shape g m tau col0F ktO aO = .ok s)
    (e' : s.plan nU3 hb hbLine = .ok s') (tlc : HTailF2) (hr : SameU s'.tl tlc) :
    unitsLaid s'.nU tlc 0 = true := by
  obtain ⟨tl₀, m1, txOf, f, hS⟩ := seamShape_lit e
  obtain ⟨T, hA⟩ := seamPlan_cut e'
  rw [seamPlan_nU e']
  exact units_made hS hA tlc hr.same hr.tabFirst hr.tabLen hr.nUF

theorem planA_units (settings : Settings) (i : Attention.In) (cf : Attention.Cfg)
    (P : Attention.Plan) (e : Attention.plan settings i cf = .ok P) (tlc : HTailF2)
    (hr : SameU P.seam.tl tlc) : unitsLaid P.seam.nU tlc 0 = true := by
  obtain ⟨seam0, h0, h1, -⟩ := planA_rows0 settings i cf P e
  exact seam_units h0 h1 tlc hr

/-! ## The head -/

theorem planH2_units (g : Settings) (h : Head.Shape) (L : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2)
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) : unitsLaid hp.nU hp.tl 0 = true := by
  unfold Head.planH2 at e
  repeat obtain ⟨_, _, e⟩ := bindE_ok e
  dsimp only at e
  split at e
  · obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl, hS, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨⟨tl1, Fp, Tp⟩, hA, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl2, hO, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    cases e
    have k := ownerHeld_sameU hO
    exact units_made hS hA _ k.same k.tabFirst k.tabLen k.nUF
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

/-! ## The public parameters -/

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

/-- **At the head's member of the public parameters.** -/
theorem public_H_units (h : Verify.publicOf pol KL layout = .ok X) :
    unitsLaid X.H.nU X.H.tl 0 = true := by
  obtain ⟨H0, h0, e⟩ := public_H h
  have k := planH2_units _ _ _ _ _ _ _ H0 h0
  rw [e]
  exact k

/-- **At every attention member of the public parameters.** -/
theorem public_A_units (h : Verify.publicOf pol KL layout = .ok X) (g : Nat)
    (a : Attention.Plan) (hg : X.A[g]? = some a) : unitsLaid a.seam.nU a.seam.tl 0 = true := by
  obtain ⟨_, _, _, _, _, sc, A0, seen, k2, k3, k6, k7⟩ := publicOf_cut pol KL layout X h
  rw [k7] at hg
  have hz : ∃ a0 s, A0[g]? = some a0 ∧ seen[g]? = some s ∧
      a = { a0 with seam := { a0.seam with tl := s.tl } } := by
    rw [← Array.getElem?_toList, Array.toList_zipWith] at hg
    obtain ⟨a0, s, e1, e2, e3⟩ := List.getElem?_zipWith_eq_some.1 hg
    exact ⟨a0, s, by simpa using e1, by simpa using e2, e3.symm⟩
  obtain ⟨a0, s, e1, e2, e3⟩ := hz
  obtain ⟨s0, f1, f2⟩ := owners_sameU k6 g s e2
  have f3 : s0 = ⟨a0.seam.tl, a0.seam.Fp, a0.seam.Tp⟩ := by
    unfold seenA0 at f1
    rw [Array.getElem?_map, e1] at f1
    exact (Option.some.inj f1).symm
  rcases k3 with ⟨_, c, k9, rfl⟩ | ⟨_, rfl⟩
  · obtain ⟨lines, l1, l2⟩ := config_at k9
    obtain ⟨cf, m1, m2⟩ := group_plan (l2 g a0 e1)
    subst e3
    show unitsLaid a0.seam.nU s.tl 0 = true
    rw [f3] at f2
    exact planA_units _ _ _ a0 m2 s.tl f2
  · simp at e1

end

end P1K8

#print axioms P1K8.owners_sameU
#print axioms P1K8.ownerHeld_sameU
#print axioms P1K8.planA_units
#print axioms P1K8.planH2_units
#print axioms P1K8.public_H_units
#print axioms P1K8.public_A_units
