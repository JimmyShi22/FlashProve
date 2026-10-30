--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/WalkTests.lean: three more claims of the shared rounds as tests with code, and
the claims at a border stated without a frame.

  omegaColB, dotOmB, foldAtB   compute OmegaCol, DotOmAt, FoldAt (GoodFold.lean and Borders.lean of
                               this folder) at words given as the program's elements.
                               omegaCol_of_B, dotOmAt_of_B, foldAt_of_B: a yes gives the claim.
                               omE, uE: what they read.
  sameUB, sameU_of_B           two records note the same point and the same o_u.
  claimsW                      claimsC (Johnson/Desc/K14/Law/BordersU.lean) at a record and a table,
                               in the place of a pair of a record and the oracles' string.
  claimsC_iff                  it is claimsC, at every frame.

What is not claimed. The converse of a test. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K14.Law.WFoldMember
import Johnson.Desc.K14.Law.BordersU

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Means (Words)
open VerifiableInference.Desc.Sound (Frame)

/-! ## Three more claims as tests with code -/

/-- omega_col's entry j, as the words hold it. -/
def omE (S : LinShape) (d : St) (mE : Words E) (j : Nat) : E :=
  mE d.loc.oOmega .main ((linLayOmega d.st.codes S).index j)

/-- u's entry k. -/
def uE (d : St) (mE : Words E) (k : Nat) : E := mE d.loc.oU.oracle .main (d.loc.oU.lay.index k)

/-- omega_col is col_psi_lo(u) on the rows of M: computed. -/
def omegaColB (S : LinShape) (d : St) (mE : Words E) : Bool :=
  (List.range S.matrixRows).all fun j =>
    decide (omE S d mE j = sumE (2 ^ S.kLo) fun t =>
      mulE (eqE (d.loc.psiSh.take S.kLo) t) (uE d mE (t + 2 ^ S.kLo * j)))

theorem omegaCol_of_B {K : Type} [Field K] (ρ : OnBytes.Model.Reading K) (S : LinShape) (d : St)
    (mE : Words E) (h : omegaColB S d mE = true) : OmegaCol ρ S d (wordsOf ρ mE) := by
  intro j hj
  simp only [omegaColB, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  have e := congrArg ρ.val (h j hj)
  simp only [val_sumE, ρ.mul, val_eqE] at e
  exact e

/-- (Dot)'s equation at o_omega: computed. -/
def dotOmB (S : LinShape) (gE : Nat → E) (d : St) (mE : Words E) (VE : Nat → E) : Bool :=
  decide ((sumE S.matrixRows fun y => mulE (gE y) (omE S d mE y)) =
    sumE (2 ^ S.kCol) fun c => mulE (eqE d.loc.psiSh c) (VE c))

theorem dotOmAt_of_B (S : LinShape) (gE : Nat → E) (d : St) (mE : Words E) (VE : Nat → E)
    (h : dotOmB S gE d mE VE = true) :
    DotOmAt S (fun y => OnBytes.Model.Reading.gl.val (gE y)) d
      (wordsOf OnBytes.Model.Reading.gl mE) (fun c => OnBytes.Model.Reading.gl.val (VE c)) := by
  simp only [dotOmB, decide_eq_true_eq] at h
  have e := congrArg OnBytes.Model.Reading.gl.val h
  simp only [val_sumE, OnBytes.Model.Reading.gl.mul, val_eqE] at e
  unfold DotOmAt DotEq
  exact e

/-- (fold)'s equation at the point that the record notes: computed. -/
def foldAtB (S : LinShape) (d : St) (mE : Words E) : Bool :=
  decide ((sumE S.matrixRows fun j => mulE (eqE d.loc.zFd j) (omE S d mE j)) =
    sumE S.matrixRows fun j => sumE (2 ^ S.kLo) fun t =>
      mulE (mulE (eqE (d.loc.psiSh.take S.kLo) t) (eqE d.loc.zFd j))
        (uE d mE (t + 2 ^ S.kLo * j)))

theorem foldAt_of_B {K : Type} [Field K] (ρ : OnBytes.Model.Reading K) (S : LinShape) (d : St)
    (mE : Words E) (h : foldAtB S d mE = true) : FoldAt ρ S d (wordsOf ρ mE) := by
  simp only [foldAtB, decide_eq_true_eq] at h
  have e := congrArg ρ.val h
  simp only [val_sumE, ρ.mul, val_eqE] at e
  unfold FoldAt FoldEq
  exact e

/-- Two records note the same point and the same o_u: computed. -/
def sameUB (d d' : St) : Bool :=
  decide (d'.loc.psiSh = d.loc.psiSh) && decide (d'.loc.oU.oracle = d.loc.oU.oracle) &&
    decide (d'.loc.oU.lay = d.loc.oU.lay)

theorem sameU_of_B (d d' : St) (h : sameUB d d' = true) :
    d'.loc.psiSh = d.loc.psiSh ∧ d'.loc.oU = d.loc.oU := by
  simp only [sameUB, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1.1, ?_⟩
  cases hx : d'.loc.oU with
  | mk o l =>
    cases hy : d.loc.oU with
    | mk o' l' =>
      have h1 := h.1.2
      have h2 := h.2
      rw [hx, hy] at h1 h2
      simp only at h1 h2
      rw [h1, h2]

/-! ## The claims at a border, without a frame -/

/-- claimsC (Johnson/Desc/K14/Law/BordersU.lean) at a record and a table, in the pair's place. -/
def claimsW (p : Par) (e' : Nat) (g : Nat → GE) :
    Nat → St → (Nat → List UInt64) → Words GE → (Nat → GE) → Prop
  | 0 => fun d tab m V => NearAt OnBytes.Model.Reading.gl p (withNext p d) m tab e' ∧
      RecAll OnBytes.Model.Reading.gl p (withNext p d) m ∧ DotUAt p.S g (withNext p d).loc m V
  | 1 => fun d tab m V => NearAt OnBytes.Model.Reading.gl p d m tab e' ∧
      RecAll OnBytes.Model.Reading.gl p d m ∧ DotUAt p.S g d.loc m V
  | 2 => fun d tab m V => NearAt OnBytes.Model.Reading.gl p d m tab e' ∧ DotUAt p.S g d.loc m V
  | 3 => fun d _ m V => DotUAt p.S g d.loc m V
  | 4 => fun d _ m V => OmegaCol OnBytes.Model.Reading.gl p.S d m ∧ DotOmAt p.S g d m V
  | 5 => fun d _ m V => OmegaCol OnBytes.Model.Reading.gl p.S d m ∧ DotOmAt p.S g d m V
  | 6 => fun d _ m V => FoldAt OnBytes.Model.Reading.gl p.S d m ∧ DotOmAt p.S g d m V
  | _ => fun d _ m V => DotOmAt p.S g d m V

/-- It is claimsC. -/
theorem claimsC_iff {F : Frame} (p : Par) (e' : Nat) (g : Nat → GE) (a : St × F.E.Str)
    (m : Words GE) (V : Nat → GE) : ∀ j,
    claimsC p e' g j a m V ↔ claimsW p e' g j a.1 (tabOf a.2) m V
  | 0 => Iff.rfl
  | 1 => Iff.rfl
  | 2 => Iff.rfl
  | 3 => Iff.rfl
  | 4 => Iff.rfl
  | 5 => Iff.rfl
  | 6 => Iff.rfl
  | _ + 7 => Iff.rfl

end Desc.K14.Law
