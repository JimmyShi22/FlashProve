-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.PayPub
import Johnson.Desc.K12.Law.GpOfPass
import Johnson.Desc.Means.TestsB
import OnBytes.Slice.BlkBegin
/-
Johnson/Desc/K12/Law/MemberOf.lean: FROM TESTS WITH CODE AT A PLACE AND A RECORD TO «WHAT THE PAYER OF THE BATCHING's CONVERSE ASKS», WITH WHAT THE RECORD FIXES SHOWN TO BE THERE. Definitions, statements and proofs. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
FixesP · PayKP · PayYP · PayRecP · PayNumP ARE TWINS, LIFTED BY PROGRAM, the names alone turned (‹X› ↦ ‹X›P): Fixes: Johnson/Desc/K12/Coin/Sheet.lean · PayK: Johnson/Desc/K12/Law/BatValsPay.lean · PayY: Johnson/Desc/K12/Coin/PaidY.lean · PayRec | PayNum: Johnson/Desc/K12/Law/BatValsPayAt.lean. Those files import the coin; this one does not. EACH TWIN IS ITS ORIGINAL, BY rfl: Coin/MemberOTrue.lean.
Main names:
  member_of: at any place π, radii r and record t: the first stage, the group, the layout and the plain data as equations; johOk π r; the written rounds; combineAt; the layout's four numbers; «the test takes in as many rows as the plan's "BAT" counts» GIVE FixesP π t a rest G0 Ly D ∧ PayKP π (fun s => r s.st) (batV0 π r) t.
  payY_of | payRec_of | payNum_of: PayKP gives the three shorter forms.
  memberB π r t: ONE test with code for all of member_of's premises. IsMember π r t: what the record fixes is there ∧ PayKP at v₀ := batV0 π r. member_of_B: the test's yes gives IsMember.
  no_fixes: at a record without a group of that number nothing is fixed. not_pay_below: under the test's yes PayKP fails at every v < batV0 π r: the number is sharp.
Limits: every premise of member_of is an equation between values with code, but johOk's theorem stands over the facts on codes (ChainJoh.lean). No member is shown here: MemberW.lean [not in this library].
-/
set_option autoImplicit false
namespace H2K.Member
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (sgOf WR writtenOf johOk batV0 PayPub payPub_of_joh)
open H2K.First (gpOf Plain)

def FixesP (π : P12) (t : T12) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group)
    (Ly : GroupLayout) (D : Plain) : Prop :=
  π.nums.stages = a :: rest ∧ t.st.groups[t.g]? = some G0 ∧ t.st.layout t.g = some Ly ∧
    ∀ row, gpOf π { t with st := begun t.st t.g G0, pass := .claim row Ly } a Ly = some D

def PayKP (π : P12) (rad : Sg → ℕ) (v₀ : ℕ) (t : T12) : Prop :=
  ∀ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain),
    FixesP π t a rest G0 Ly D →
    (sgOf a).StageJ (rad (sgOf a)) ∧
    combineAt (begun t.st t.g G0) t.g ⟨Ly, runRows t.st G0⟩ = true ∧
    Ly.k = (sgOf a).h + (sgOf a).g ∧ Ly.h = (sgOf a).h ∧
    2 ^ Ly.logEll = (sgOf a).C.l ∧ 2 ^ Ly.logEllZk = (sgOf a).Z.l ∧
    (sgOf a).lstJ (rad (sgOf a)) * ((runRows t.st G0).size - 1) ≤ v₀

def PayYP (π : P12) (rad : Sg → ℕ) (v₀ : ℕ) (t : T12) : Prop :=
  ∀ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain),
    FixesP π t a rest G0 Ly D →
    (sgOf a).StageJ (rad (sgOf a)) ∧
    combineAt (begun t.st t.g G0) t.g ⟨Ly, runRows t.st G0⟩ = true ∧
    2 ^ Ly.logEll = (sgOf a).C.l ∧ 2 ^ Ly.logEllZk = (sgOf a).Z.l ∧
    (sgOf a).lstJ (rad (sgOf a)) * ((runRows t.st G0).size - 1) ≤ v₀

def PayRecP (π : P12) (t : T12) : Prop :=
  ∀ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain),
    FixesP π t a rest G0 Ly D →
    combineAt (begun t.st t.g G0) t.g ⟨Ly, runRows t.st G0⟩ = true

def PayNumP (π : P12) (t : T12) : Prop :=
  ∀ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain),
    FixesP π t a rest G0 Ly D →
    Ly.k = (sgOf a).h + (sgOf a).g ∧ Ly.h = (sgOf a).h ∧
    2 ^ Ly.logEll = (sgOf a).C.l ∧ 2 ^ Ly.logEllZk = (sgOf a).Z.l

/-- **From tests with code to the promise, and what the record fixes is there.** -/
theorem member_of (π : P12) (r : Fmt.M1.Stage → ℕ) (t : T12) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hs : π.nums.stages = a :: rest) (hG : t.st.groups[t.g]? = some G0)
    (hL : t.st.layout t.g = some Ly)
    (hD : gpOf π { t with st := begun t.st t.g G0, pass := .nothing } a Ly = some D)
    (hj : johOk π r = true) (w0 : WR) (l : List WR) (hw : writtenOf π.nums = some (w0 :: l))
    (hc : combineAt (begun t.st t.g G0) t.g ⟨Ly, runRows t.st G0⟩ = true)
    (hk : Ly.k = a.h + (a.k - a.h)) (hh : Ly.h = a.h) (hl : 2 ^ Ly.logEll = a.C.l)
    (hz : 2 ^ Ly.logEllZk = a.Z.l) (hrows : (runRows t.st G0).size = w0.entry.rows) :
    FixesP π t a rest G0 Ly D ∧ PayKP π (fun s => r s.st) (batV0 π r) t := by
  refine ⟨⟨hs, hG, hL, fun _ => hD⟩, ?_⟩
  intro a' rest' G0' Ly' D' hf
  obtain ⟨rfl, rfl⟩ := List.cons.inj (hs.symm.trans hf.1)
  obtain rfl := Option.some.inj (hG.symm.trans hf.2.1)
  obtain rfl := Option.some.inj (hL.symm.trans hf.2.2.1)
  obtain ⟨p1, p2⟩ := payPub_of_joh π r (fun s => r s.st) (fun _ => rfl) hj w0 l hw a rest hs
  exact ⟨p1, hc, hk, hh, hl, hz, by rw [hrows]; exact p2⟩

theorem payY_of {π : P12} {rad : Sg → ℕ} {v₀ : ℕ} {t : T12} (h : PayKP π rad v₀ t) :
    PayYP π rad v₀ t := fun a rest G0 Ly D hf =>
  let ⟨p1, p2, _, _, p5, p6, p7⟩ := h a rest G0 Ly D hf
  ⟨p1, p2, p5, p6, p7⟩

theorem payRec_of {π : P12} {rad : Sg → ℕ} {v₀ : ℕ} {t : T12} (h : PayKP π rad v₀ t) :
    PayRecP π t := fun a rest G0 Ly D hf => (h a rest G0 Ly D hf).2.1

theorem payNum_of {π : P12} {rad : Sg → ℕ} {v₀ : ℕ} {t : T12} (h : PayKP π rad v₀ t) :
    PayNumP π t := fun a rest G0 Ly D hf =>
  let ⟨_, _, p3, p4, p5, p6, _⟩ := h a rest G0 Ly D hf
  ⟨p3, p4, p5, p6⟩

/-- **One test with code for all of member_of's premises.** -/
def memberB (π : P12) (r : Fmt.M1.Stage → ℕ) (t : T12) : Bool :=
  match π.nums.stages, t.st.groups[t.g]?, t.st.layout t.g, writtenOf π.nums with
  | a :: _, some G0, some Ly, some (w0 :: _) =>
    (gpOf π { t with st := begun t.st t.g G0, pass := .nothing } a Ly).isSome && johOk π r &&
      combineAt (begun t.st t.g G0) t.g ⟨Ly, runRows t.st G0⟩ && Ly.k == a.h + (a.k - a.h) &&
      Ly.h == a.h && 2 ^ Ly.logEll == a.C.l && 2 ^ Ly.logEllZk == a.Z.l &&
      (runRows t.st G0).size == w0.entry.rows
  | _, _, _, _ => false

/-- What counts: what the record fixes is there, and the promise holds at v₀ := batV0. -/
def IsMember (π : P12) (r : Fmt.M1.Stage → ℕ) (t : T12) : Prop :=
  (∃ a rest G0 Ly D, FixesP π t a rest G0 Ly D) ∧ PayKP π (fun s => r s.st) (batV0 π r) t

theorem member_of_B (π : P12) (r : Fmt.M1.Stage → ℕ) (t : T12) (h : memberB π r t = true) :
    IsMember π r t := by
  unfold memberB at h
  split at h
  · rename_i a rest G0 Ly w0 l hs hG hL hw
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
    obtain ⟨D, hD⟩ := Option.isSome_iff_exists.1 h1
    obtain ⟨m1, m2⟩ := member_of π r t a rest G0 Ly D hs hG hL hD h2 w0 l hw h3 h4 h5 h6 h7 h8
    exact ⟨⟨a, rest, G0, Ly, D, m1⟩, m2⟩
  · cases h

/-- Where the record has no group of that number, nothing is fixed. -/
theorem no_fixes (π : P12) (t : T12) (h : t.st.groups[t.g]? = none) :
    ¬ ∃ a rest G0 Ly D, FixesP π t a rest G0 Ly D := by
  rintro ⟨a, rest, G0, Ly, D, hf⟩
  have h2 := hf.2.1
  rw [h] at h2
  cases h2

/-- The promise fails at every smaller number, where something is fixed and the list bound and the rows
are as batV0 takes them. -/
theorem not_pay_below (π : P12) (r : Fmt.M1.Stage → ℕ) (t : T12) (h : memberB π r t = true)
    (v : ℕ) (hv : v < batV0 π r) : ¬ PayKP π (fun s => r s.st) v t := by
  intro hP
  unfold memberB at h
  split at h
  · rename_i a rest G0 Ly w0 l hs hG hL hw
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, h8⟩ := h
    obtain ⟨D, hD⟩ := Option.isSome_iff_exists.1 h1
    have hle := (hP a rest G0 Ly D ⟨hs, hG, hL, fun _ => hD⟩).2.2.2.2.2.2
    have hb : batV0 π r = H2K.Pub.lstJB (H2K.Pub.stN a) (r (H2K.Pub.stN a)) * (w0.entry.rows - 1) := by
      unfold batV0 H2K.Pub.batAtB
      rw [hs, hw]
      rfl
    rw [h8] at hle
    rw [hb, H2K.Pub.lstJB_eq] at hv
    exact absurd hle (Nat.not_le.2 hv)
  · cases h

end H2K.Member

#print axioms H2K.Member.member_of
#print axioms H2K.Member.member_of_B
#print axioms H2K.Member.not_pay_below
