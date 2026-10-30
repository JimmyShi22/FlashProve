--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/PlacesHold.lean: the linear claim's shared rounds, place by place: where a
place accepts, and an honest prover's words met all that the statement claimed in front of it, they
meet all that the statement claims behind it.

The proposition that goes from place to place is AllMet (Johnson/Desc/Means/Forth/AllMet.lean): the
statement is in order, and every open row of every group and every sample row of every oracle
message holds of the words. Here are the kind's own six places, and what the kind writes into its
state behind each of the two sendings. The two sendings themselves are another kind's.

  first_kept      the start: at the state in front of the first round, at all words
  linPoint_kept, behindU_kept, behindOmega_kept, joins_kept, linZeta_kept   these five lay no new
                  constraint
  laysRec_kept    "(rec_gamma)": by rec_say
  loc_kept        "LOC": by loc_say
  split_kept      "SPLIT", where the shape splits: by says_split

"A place accepts" means here: the place's plain function (Johnson/Desc/K14/Text.lean) returns a
state. No sub-protocol stands in a statement of this file; a sub-protocol's decide function is that
function under the names of its tests (Johnson/Desc/K14/Blocks.lean).

What is assumed, as premises. The place accepts. The committed table's shape is in order (hi). At
every statement that grows out of the one in front, the messages have their tables (hP). That wide
form is the library's own: hi with hP is what on4_of_seatedUB concludes
(Johnson/Desc/K14/Law/Shapes.lean),
hS with hP is OnSplit (Johnson/Desc/K14/Law/GoodFoldAt.lean); each proof spends it at one statement
in between. The table of weights has as many entries as the committed table has rows (hsz). The
words hold the honest values (hu, hO). Each row's OOD answers in the key and each opened column are
that row's own (hR, hC). At "SPLIT": the shape splits (hS: with one code (fold) goes whole to the
one group: not treated); the element that is sent reads as the left side of the constraint on
G_omega at the statement at which that constraint is laid (hmu): of the two new constraints that one
holds by this premise; where it is met: Johnson/Desc/K14/Honest/ChainHolds.lean (the call of
`split_kept`).
What is not claimed. That a place accepts. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K14.Honest.RowsHold
import Johnson.Desc.Means.Forth.AllMet
import Johnson.Desc.K14.Law.Run

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Means (Words InOrder Holds)
open VerifiableInference.Desc (Grows)
open VerifiableInference.Desc.Ground
open Desc.K14.Law

variable {K : Type} [Field K] (ρ : OnBytes.Model.Reading K)

/-- The start: the state in front of the first round, at all words. -/
theorem first_kept (codes : Codes) (key : TableKey) (m : Words K) :
    Means.AllMet ρ (first codes key).st m :=
  Means.allMet_start ρ codes m

/-- If "LIN point" accepts and AllMet holds in front of it, AllMet holds behind it: two groups are
opened, which have no row. -/
theorem linPoint_kept (p : Par) (d d' : St) (rs : List Fmt.RoundView) (m : Words K)
    (h : linPoint p d rs = some d') (hK : Means.AllMet ρ d.st m) : Means.AllMet ρ d'.st m := by
  unfold linPoint at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨u0, _, ⟨gU, d1⟩, h1, h2⟩ := h
    have k1 : Means.AllMet ρ d1.st m := Means.newGroupP_met ρ h1 hK
    split at h2
    · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h2
      obtain ⟨⟨gO, d2⟩, h3, rfl⟩ := h2
      show Means.AllMet ρ d2.st m
      exact ⟨Means.newGroupP_keeps h3 k1.1, Means.newGroupP_forth ρ h3 k1.1 k1.2⟩
    · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h2
      obtain ⟨⟨gO, d2⟩, h3, rfl⟩ := h2
      simp only [Prod.mk.injEq] at h3
      show Means.AllMet ρ d2.st m
      rw [← h3.2]
      exact k1
  · cases h

/-- What the kind writes into its state behind o_u's sending leaves the statement as it is. -/
theorem behindU_kept (p : Par) (d d' : St) (ids : Array Nat) (m : Words K)
    (h : behindU p d ids = some d') (hK : Means.AllMet ρ d.st m) : Means.AllMet ρ d'.st m := by
  rw [(behindU_inv p d d' ids h).1]
  exact hK

/-- What the kind writes into its state behind o_omega's sending leaves the statement as it is. -/
theorem behindOmega_kept (p : Par) (d d' : St) (ids : Array Nat) (m : Words K)
    (h : behindOmega p d ids = some d') (hK : Means.AllMet ρ d.st m) : Means.AllMet ρ d'.st m := by
  rw [(behindOmega_inv p d d' ids h).1]
  exact hK

/-- **If "(rec_gamma)" accepts and AllMet holds in front of it, AllMet holds behind it**, where the
words at o_u hold the rows' fold and the key's OOD answers are the rows' own. -/
theorem laysRec_kept (p : Par) (d d' : St) (rs : List Fmt.RoundView) (m : Words K)
    (Rw : Nat → Nat → K) (h : laysRec p d rs = some d')
    (hi : p.S.fold.index.ok = true) (hP : ∀ T, Grows d.st T → PlacedU T p.S.fold d.loc.oU)
    (hu : IsFold p.S.fold (wOf ρ p.S d.loc) Rw (uOf d.loc m))
    (hR : ∀ x ∈ d.loc.key.seeds.zipIdx, ∀ r < p.S.fold.index.rows,
      RowAnswer p.S.fold.index (x.1.z.map ρ.val) (ρ.val x.1.beta) (fun t => ρ.val (thetaE t)) x.2
        (Rw r) (ρ.val (d.loc.key.record.getD (r * p.S.fold.index.answers + x.2) zeroE)))
    (hK : Means.AllMet ρ d.st m) : Means.AllMet ρ d'.st m := by
  have hok := (laysRecW p d d' rs h).1
  unfold laysRec at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨u0, _, d1, hj, rows, hm, ha⟩ := h
  have hI1 := Means.joinP_keeps hj hK.1
  have hH1 := Means.joinP_forth ρ hj hK.1 hK.2
  have hs := rec_say ρ p d.loc d1.st m Rw rows hm hok hi
    (hP _ (joinP_grows d d1 _ _ _ hj)) hu hR
  exact ⟨Means.addRowsP_keeps ha hI1, Means.addRowsP_forth ρ ha hI1 hH1 hs⟩

/-- **If "LOC" accepts and AllMet holds in front of it, AllMet holds behind it**, where the words at
o_u hold the rows' fold and each opened column holds each row's own symbol. -/
theorem loc_kept (p : Par) (d d' : St) (r : Fmt.RoundView) (cols : List (Nat × List UInt64))
    (m : Words K) (Rw : Nat → Nat → K) (h : loc p d [r] [cols] = some d')
    (hi : p.S.fold.index.ok = true) (hP : ∀ T, Grows d.st T → PlacedU T p.S.fold d.loc.oU)
    (hu : IsFold p.S.fold (wOf ρ p.S d.loc) Rw (uOf d.loc m))
    (hsz : (weights p.S d.loc).size = p.S.fold.index.rows)
    (hC : ∀ x ∈ locations p r, ∀ col, cols.lookup x = some col → ∀ q < p.S.fold.index.rows,
      ρ.val (ofF (col.toArray.getD q 0)) = genK ρ p.S.fold x (Rw q))
    (hK : Means.AllMet ρ d.st m) : Means.AllMet ρ d'.st m := by
  unfold loc at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨rows, hm, ha⟩ := h
  have hs := loc_say ρ p d r cols d.st m Rw rows hm hi (hP _ (Grows.refl _)) hu hsz hC
  exact ⟨Means.addRowsP_keeps ha hK.1, Means.addRowsP_forth ρ ha hK.1 hK.2 hs⟩

/-- If the joinings accept and AllMet holds in front of them, AllMet holds behind them. -/
theorem joins_kept (p : Par) (d d' : St) (rs : List Fmt.RoundView) (m : Words K)
    (h : joins p d rs = some d') (hK : Means.AllMet ρ d.st m) : Means.AllMet ρ d'.st m := by
  unfold joins at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨u0, _, d1, h1, h2⟩ := h
  have k1 : Means.AllMet ρ d1.st m := ⟨Means.joinP_keeps h1 hK.1, Means.joinP_forth ρ h1 hK.1 hK.2⟩
  split at h2
  · simp only [Option.bind_eq_some_iff] at h2
    obtain ⟨d2, h3, h4⟩ := h2
    have k2 : Means.AllMet ρ d2.st m := Means.joinP_met ρ h3 k1
    exact ⟨Means.joinP_keeps h4 k2.1, Means.joinP_forth ρ h4 k2.1 k2.2⟩
  · simp only [Option.some.injEq] at h2
    subst h2
    exact k1

/-- "LIN zeta" leaves the statement as it is. -/
theorem linZeta_kept (d d' : St) (r : Fmt.RoundView) (m : Words K) (h : linZeta d [r] = some d')
    (hK : Means.AllMet ρ d.st m) : Means.AllMet ρ d'.st m := by
  rw [linZeta_inv d d' r h]
  exact hK

/-- **If "SPLIT" accepts and AllMet holds in front of it, AllMet holds behind it**, where the shape
splits, the words at o_omega hold what the folded row gives at psi_lo, and the element that is sent
reads as the honest scalar's value. -/
theorem split_kept (p : Par) (d d' : St) (r : Fmt.RoundView) (m : Words K)
    (hS : p.S.sharedSplitNeeded = true) (h : split p d [r] = some d')
    (hP : ∀ T, Grows d.st T → Placed T p.S d.loc (linLayOmega d.st.codes p.S))
    (hO : ∀ j < p.S.matrixRows, omegaOf d.loc (linLayOmega d.st.codes p.S) m j =
      ∑ t ∈ Finset.range (2 ^ p.S.kLo),
        eqK ((d.loc.psiSh.take p.S.kLo).map ρ.val) t * uOf d.loc m (t + 2 ^ p.S.kLo * j))
    (hmu : ∀ row x G kappa d₁, fold p.S d.loc (linLayOmega d.st.codes p.S) = some row →
      r.vals = [.e x] → d.st.groups[d.loc.gOmega]? = some G →
      takeMaskP d d.loc.oSp = some (kappa, d₁) →
      ρ.val (E.ofTriple x) = muVal ρ d₁.st row G.members d.loc.oSp kappa m)
    (hK : Means.AllMet ρ d.st m) : Means.AllMet ρ d'.st m := by
  obtain ⟨row, x, G, kappa, d₁, d₂, hf, hx, hG, _, hk, h2, h3⟩ := split_inv p d d' r hS h
  have k1 : Means.AllMet ρ d₁.st m := Means.takeMaskP_met ρ hk hK
  have hrow : Means.Says ρ d₁.st row m :=
    (foldMeansW ρ d₁.st p.S d.loc _ row hf (hP _ (takeMaskP_grows d d₁ _ _ hk)) m).2
      (foldEq_of_col p.S _ _ _ _ hO)
  obtain ⟨sa, sb⟩ := says_split ρ d₁.st row G.members d.loc.oSp kappa (E.ofTriple x) m
    (hmu row x G kappa d₁ hf hx hG hk) hrow
  obtain ⟨hI2, _, _, _, e2⟩ := Means.addRowP_keeps h2 k1.1
  have hH2 := Means.addRowP_forth ρ h2 k1.1 k1.2 sa
  have sb2 : Means.Says ρ d₂.st (onU row G.members d.loc.oSp kappa (E.ofTriple x)) m := by
    have hv : Means.value ρ d₂.st (onU row G.members d.loc.oSp kappa (E.ofTriple x)) m =
        Means.value ρ d₁.st (onU row G.members d.loc.oSp kappa (E.ofTriple x)) m := by
      rw [e2]
      exact Means.value_congr ρ rfl rfl _ m
    show Means.value ρ d₂.st (onU row G.members d.loc.oSp kappa (E.ofTriple x)) m = _
    rw [hv]
    exact sb
  exact ⟨(Means.addRowP_keeps h3 hI2).1, Means.addRowP_forth ρ h3 hI2 hH2 sb2⟩

end Desc.K14.Honest

#print axioms Desc.K14.Honest.first_kept
#print axioms Desc.K14.Honest.linPoint_kept
#print axioms Desc.K14.Honest.behindU_kept
#print axioms Desc.K14.Honest.behindOmega_kept
#print axioms Desc.K14.Honest.laysRec_kept
#print axioms Desc.K14.Honest.loc_kept
#print axioms Desc.K14.Honest.joins_kept
#print axioms Desc.K14.Honest.linZeta_kept
#print axioms Desc.K14.Honest.split_kept
