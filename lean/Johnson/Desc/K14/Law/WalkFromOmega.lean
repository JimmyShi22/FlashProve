--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/WalkFromOmega.lean: THE CLAIMS AT THE SHARED CHAIN's BORDERS 3 TO 7, AND (Dot)
AT u AT THE FOUR STATES IN FRONT, FROM FEW TESTS WITH CODE: one on "omega_col is col_psi_lo(u)",
four on (Dot) at o_omega, six that compare letters of two states. For an example at a size at which
a walk over the folded row u is dear: u is walked ONCE, and by shares.

  omegaColShareB, omegaColB_of_shares   omegaColB (Johnson/Desc/K14/Law/WalkTests.lean) is an "all"
                   over the rows j of M: share i of n takes the j with j % n = i, the point's low
                   weights off a table made once (eqTab, RowsB.lean): ALL SHARES GIVE THE WHOLE.
  sameOmB, omegaColB_same   the test reads four letters of the verifier's state (the point, o_u,
                   o_omega's number, the code table): at a state with the same four it says the
                   same.
  FoldAt.of_omega  where omega_col is col_psi_lo(u), (fold)'s equation holds at every point.
  claims_from_omega   THE ASSEMBLY. (Dot) at u: by DotUAt.of_omega and DotUAt.of_same
                   (Borders.lean, BordersU.lean).

What is not claimed. The claims at the borders 0 to 2 whole ("near" and the key's OOD sample are not
among the conclusions). That any words are an honest prover's. Nothing on soundness, on an honest
prover or on hiding.

-/
import Johnson.Desc.K14.Law.WalkTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Means (Words)

theorem sumE_congr (n : Nat) (f g : Nat → E) (h : ∀ t < n, f t = g t) : sumE n f = sumE n g := by
  unfold sumE
  exact List.foldl_ext _ _ _ fun a b hb => by rw [h b (List.mem_range.1 hb)]

/-- One row's equation, the weights off a table. -/
def omRowB (S : LinShape) (d : St) (mE : Words E) (tab : Array E) (j : Nat) : Bool :=
  decide (omE S d mE j = sumE (2 ^ S.kLo) fun t =>
    mulE (tab.getD t zeroE) (uE d mE (t + 2 ^ S.kLo * j)))

/-- Share i of n. -/
def omegaColShareB (S : LinShape) (d : St) (mE : Words E) (n i : Nat) : Bool :=
  let tab := eqTab (d.loc.psiSh.take S.kLo) (2 ^ S.kLo)
  (List.range S.matrixRows).all fun j => j % n != i || omRowB S d mE tab j

/-- **All shares give the whole.** -/
theorem omegaColB_of_shares (S : LinShape) (d : St) (mE : Words E) (n : Nat) (hn : 0 < n)
    (h : ∀ i < n, omegaColShareB S d mE n i = true) : omegaColB S d mE = true := by
  simp only [omegaColB, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  intro j hj
  have k := h (j % n) (Nat.mod_lt _ hn)
  simp only [omegaColShareB, List.all_eq_true, List.mem_range, Bool.or_eq_true] at k
  rcases k j hj with r | r
  · simp at r
  · unfold omRowB at r
    rw [decide_eq_true_eq] at r
    rw [r]
    exact sumE_congr _ _ _ fun t ht => by rw [eqTab_getD _ _ _ ht]

/-- The four letters that the test reads of the verifier's state. -/
def sameOmB (d d' : St) : Bool :=
  decide (d'.loc.psiSh = d.loc.psiSh) && decide (d'.loc.oU.oracle = d.loc.oU.oracle) &&
    decide (d'.loc.oU.lay = d.loc.oU.lay) && decide (d'.loc.oOmega = d.loc.oOmega) &&
    decide (d'.st.codes = d.st.codes)

theorem omegaColB_same (S : LinShape) (d d' : St) (mE : Words E) (h : sameOmB d d' = true) :
    omegaColB S d' mE = omegaColB S d mE := by
  simp only [sameOmB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  unfold omegaColB omE uE
  rw [h1, h2, h3, h4, h5]

/-- **Where omega_col is col_psi_lo(u), (fold)'s equation holds**, whatever the point. -/
theorem FoldAt.of_omega {K : Type} [Field K] (ρ : OnBytes.Model.Reading K) {S : LinShape} {d : St}
    {m : Words K} (hO : OmegaCol ρ S d m) : FoldAt ρ S d m := by
  unfold FoldAt FoldEq
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [hO j (Finset.mem_range.1 hj), Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => by ring

/-- **THE ASSEMBLY.** d1 … d8: the verifier's states behind the shared chain's eight sub-protocols.
-/
theorem claims_from_omega (p : Par) (e' : Nat) (tab : Nat → List UInt64)
    (d1 d2 d3 d4 d5 d6 d7 d8 : St) (mE : Words E) (gE VE : Nat → E)
    (O5 : omegaColB p.S d5 mE = true)
    (D5 : dotOmB p.S gE d5 mE VE = true) (D6 : dotOmB p.S gE d6 mE VE = true)
    (D7 : dotOmB p.S gE d7 mE VE = true) (D8 : dotOmB p.S gE d8 mE VE = true)
    (S6 : sameOmB d5 d6 = true) (S7 : sameOmB d5 d7 = true)
    (U1 : sameUB (withNext p d1) d5 = true) (U2 : sameUB d2 d5 = true)
    (U3 : sameUB d3 d5 = true) (U4 : sameUB d4 d5 = true) :
    (fun (l : Lin) => DotUAt p.S (fun y => OnBytes.Model.Reading.gl.val (gE y)) l
      (wordsOf OnBytes.Model.Reading.gl mE) (fun c => OnBytes.Model.Reading.gl.val (VE c))) |>
    fun U => (fun (j : Nat) (d : St) => claimsW p e' (fun y => OnBytes.Model.Reading.gl.val (gE y))
      j d tab (wordsOf OnBytes.Model.Reading.gl mE)
      (fun c => OnBytes.Model.Reading.gl.val (VE c))) |>
    fun C => U (withNext p d1).loc ∧ U d2.loc ∧ U d3.loc ∧
      C 3 d4 ∧ C 4 d5 ∧ C 5 d6 ∧ C 6 d7 ∧ C 7 d8 := by
  have o5 := omegaCol_of_B OnBytes.Model.Reading.gl _ _ _ O5
  have o6 := omegaCol_of_B OnBytes.Model.Reading.gl _ _ _
    ((omegaColB_same p.S d5 d6 mE S6).trans O5)
  have o7 := omegaCol_of_B OnBytes.Model.Reading.gl _ _ _
    ((omegaColB_same p.S d5 d7 mE S7).trans O5)
  have u5 := DotUAt.of_omega o5 (dotOmAt_of_B _ _ _ _ _ D5)
  have at_ : ∀ d : St, sameUB d d5 = true → DotUAt p.S
      (fun y => OnBytes.Model.Reading.gl.val (gE y)) d.loc (wordsOf OnBytes.Model.Reading.gl mE)
      (fun c => OnBytes.Model.Reading.gl.val (VE c)) := fun d h =>
    DotUAt.of_same (sameU_of_B _ _ h).1 (sameU_of_B _ _ h).2 u5
  exact ⟨at_ _ U1, at_ _ U2, at_ _ U3, at_ _ U4, ⟨o5, dotOmAt_of_B _ _ _ _ _ D5⟩,
    ⟨o6, dotOmAt_of_B _ _ _ _ _ D6⟩, ⟨FoldAt.of_omega _ o7, dotOmAt_of_B _ _ _ _ _ D7⟩,
    dotOmAt_of_B _ _ _ _ _ D8⟩

end Desc.K14.Law
