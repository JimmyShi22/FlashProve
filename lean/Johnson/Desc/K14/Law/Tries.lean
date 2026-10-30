-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/Tries.lean: the law of (fold) tried on two functions that are no verifier's.

The joined law has two halves: FoldSoundOf (few points z_fd at which a yes goes with constraints
that hold) and YesOf (where the named tests hold, the function says yes). A function that says yes
to all and lays nothing fails the first half; a function that says no to all fails the second.
Both are shown at one small instance: a matrix of one row and one column.
Main names: YesOf, FoldLawOf, split_yes, tiny_yes, not_foldSoundOf_yes, not_yesOf_no.

What is not claimed. The small instance is no instance of a release. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.Lays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Model (Reading)
open OnBytes.Means (Words)
open VerifiableInference.Desc.Ground (addRowP takeMaskP ok rowL takeMaskL)

variable {K : Type} [Field K] (ρ : Reading K)

/-- Where the named tests hold and the effects can be made, the function says yes. -/
def YesOf (sp : Par → St → List Fmt.RoundView → Option St) : Prop :=
  ∀ (p : Par) (d d' : St) (r : Fmt.RoundView) (row : Row) (x : UInt64 × UInt64 × UInt64) (G : Group)
    (kappa : Nat) (d₁ d₂ : St), p.S.sharedSplitNeeded = true →
    fold p.S d.loc (linLayOmega d.st.codes p.S) = some row → r.vals = [.e x] →
    d.st.groups[d.loc.gOmega]? = some G → ok (splitL d row) = true →
    takeMaskP d d.loc.oSp = some (kappa, d₁) →
    addRowP d₁ d.loc.gOmega (onOmega row G.members d.loc.oSp kappa (E.ofTriple x)) = some d₂ →
    addRowP d₂ d.loc.gU (onU row G.members d.loc.oSp kappa (E.ofTriple x)) = some d' →
    sp p d [r] = some d'

/-- The joined law of (fold), of any function in the place of "SPLIT". -/
def FoldLawOf [Fintype K] (sp : Par → St → List Fmt.RoundView → Option St) : Prop :=
  FoldSoundOf ρ sp ∧ YesOf sp

/-- "SPLIT" says yes where its named tests hold. -/
theorem split_yes : YesOf split := by
  intro p d d' r row x G kappa d₁ d₂ hS hf hx hG hok hk h2 h3
  unfold onOmega at h2
  unfold onU at h3
  simp [split, hS, hf, hx, hG, hok, hk, h2, h3]

/-! ## A small instance -/

/-- One row, one column; two codes. -/
def tinyS : LinShape :=
  { (default : LinShape) with
    matrixRows := 1, kLo := 0, omega := { code := 0, mainRows := 1 },
    fold := { (default : FoldeqShape) with u := { code := 1, mainRows := 1 } } }

/-- Three messages: omega_col, u, the mask row. Two groups. -/
def tinyT : Statement :=
  { oracles :=
      #[{ shape := { code := 0, mainRows := 1 } }, { shape := { code := 1, mainRows := 1 } },
        { shape := { mainRows := 0, maskRows := 1 },
          ledger := some { next := 0, left := 1, rows := 1, logRows := 0 } }],
    groups := #[{ code := 1, members := #[1, 2] }, { code := 0, members := #[0, 2] }] }

@[inherit_doc tinyT]
def tinyD : St :=
  { st := tinyT, book := { trees := #[], place := #[] }, roots := 0, opened := [],
    loc := { gU := 0, gOmega := 1, oU := { oracle := 1, lay := {} }, oOmega := 0, oSp := 2 } }

@[inherit_doc tinyS]
def tinyP : Par := { samples := 0, firstTree := 0, S := tinyS, key := {}, entries := [] }

/-- A round with one scalar. -/
def tinyR : Fmt.RoundView := ⟨[.e (0, 0, 0)], ⟨[], [], [], none⟩⟩

/-- The small shape has two codes. -/
theorem tiny_needed : tinyP.S.sharedSplitNeeded = true := by decide

/-- One row of M: no coordinate of z_fd. -/
theorem tiny_kRow : tinyP.S.kRow = 0 := by decide

/-- An option that is there is its own value. -/
theorem eq_some_getD {α : Type} (o : Option α) (a : α) (h : o.isSome = true) :
    o = some (o.getD a) := by
  cases o with
  | none => cases h
  | some x => rfl

/-- (fold) at the small instance. -/
def tinyRow : Row := (fold tinyS tinyD.loc (linLayOmega tinyD.st.codes tinyS)).getD {}

/-- (fold) can be made at the small instance. -/
theorem tiny_f1 : (fold tinyS tinyD.loc (linLayOmega tinyD.st.codes tinyS)).isSome = true := by
  decide

/-- The tensor without a variable. -/
def tinyV (s : E) : Tensor := { scalar := s }

/-- (fold) at the small instance, written out. -/
theorem tinyRow_eq : tinyRow =
    { terms := #[⟨0, .main, tinyV oneE⟩, ⟨1, .main, tinyV (negE oneE)⟩] } := rfl

/-- The two constraints that "SPLIT" lays at the small instance. -/
def tinyA : Row :=
  { terms := #[⟨0, .main, tinyV oneE⟩], units := #[⟨2, .mask, 0, oneE⟩],
    target := E.ofTriple (0, 0, 0) }

@[inherit_doc tinyA]
def tinyB : Row :=
  { terms := #[⟨1, .main, tinyV (negE oneE)⟩], units := #[⟨2, .mask, 0, negE oneE⟩],
    target := subE zeroE (E.ofTriple (0, 0, 0)) }

/-- The states on the way: the mask entry taken; one constraint laid; both. -/
def tinyD1 : St :=
  { tinyD with st := { tinyT with oracles :=
      #[{ shape := { code := 0, mainRows := 1 } }, { shape := { code := 1, mainRows := 1 } },
        { shape := { mainRows := 0, maskRows := 1 },
          ledger := some { next := 1, left := 0, rows := 1, logRows := 0 } }] } }

@[inherit_doc tinyD1]
def tinyD2 : St := { tinyD1 with st := withRow tinyD1.st 1 tinyA }

@[inherit_doc tinyD1]
def tinyD3 : St := { tinyD2 with st := withRow tinyD2.st 0 tinyB }

/-- The five clauses at "SPLIT" hold. -/
theorem tiny_f2 : ok (splitL tinyD tinyRow) = true := by
  rw [tinyRow_eq]
  simp [ok, splitL, tinyD, tinyT, Row.oracles]

/-- The mask entry is taken. -/
theorem tiny_f3 : takeMaskP tinyD 2 = some (0, tinyD1) := rfl

/-- The part on G_omega, written out. -/
theorem tiny_a : onOmega tinyRow #[0, 2] 2 0 (E.ofTriple (0, 0, 0)) = tinyA := by
  rw [tinyRow_eq]
  simp [onOmega, part, Row.addUnit, tinyA]

/-- The part on G_u, written out. -/
theorem tiny_b : onU tinyRow #[0, 2] 2 0 (E.ofTriple (0, 0, 0)) = tinyB := by
  rw [tinyRow_eq]
  simp [onU, part, Row.addUnit, tinyB]

/-- The first constraint is added. -/
theorem tiny_f4 : addRowP tinyD1 1 tinyA = some tinyD2 := by
  have h : ok (rowL tinyD1.st 1 tinyA) = true := by
    simp [ok, rowL, VerifiableInference.Desc.Ground.on,
      VerifiableInference.Desc.Ground.has, tinyD1, tinyD, tinyT, tinyV, tinyA,
      VerifiableInference.Desc.Own.placeFits, VerifiableInference.Desc.Own.tableThere,
      VerifiableInference.Desc.Own.tensorInOrder, Statement.tableBits, Statement.rowBits,
      Statement.placeBits, OracleShape.rows, ceilLog2, Tensor.vars]
    rfl
  unfold addRowP
  rw [if_pos h]
  rfl

/-- The second constraint is added. -/
theorem tiny_f5 : addRowP tinyD2 0 tinyB = some tinyD3 := by
  have h : ok (rowL tinyD2.st 0 tinyB) = true := by
    simp [ok, rowL, VerifiableInference.Desc.Ground.on,
      VerifiableInference.Desc.Ground.has, tinyD2, withRow, tinyD1, tinyD, tinyT,
      tinyV, tinyB, VerifiableInference.Desc.Own.placeFits,
      VerifiableInference.Desc.Own.tableThere, VerifiableInference.Desc.Own.tensorInOrder,
      Statement.tableBits, Statement.rowBits, Statement.placeBits, OracleShape.rows, ceilLog2,
      Tensor.vars]
    try rfl
  unfold addRowP
  rw [if_pos h]
  rfl

/-- "SPLIT" says yes at the small instance. -/
theorem tiny_yes : (split tinyP tinyD [tinyR]).isSome = true := by
  rw [split_yes tinyP tinyD tinyD3 tinyR tinyRow (0, 0, 0) { code := 0, members := #[0, 2] } 0
    tinyD1 tinyD2 tiny_needed (eq_some_getD _ _ tiny_f1) rfl rfl tiny_f2 tiny_f3
    (by
      show addRowP tinyD1 1 (onOmega tinyRow #[0, 2] 2 0 (E.ofTriple (0, 0, 0))) = some tinyD2
      rw [tiny_a]; exact tiny_f4)
    (by
      show addRowP tinyD2 0 (onU tinyRow #[0, 2] 2 0 (E.ofTriple (0, 0, 0))) = some tinyD3
      rw [tiny_b]; exact tiny_f5)]
  rfl

/-- A function that says no to all does not meet the law's second half. -/
theorem not_yesOf_no : ¬ YesOf fun _ _ _ => none := by
  intro h
  obtain ⟨d', hd⟩ := Option.isSome_iff_exists.1 tiny_yes
  obtain ⟨row, x, G, kappa, d₁, d₂, hf, hx, hG, hok, hk, h2, h3⟩ :=
    split_inv tinyP tinyD d' tinyR tiny_needed hd
  have := h tinyP tinyD d' tinyR row x G kappa d₁ d₂ tiny_needed hf hx hG hok hk h2 h3
  cases this

/-- The small instance's messages have their tables. -/
theorem tiny_placed : Placed tinyT tinyP.S tinyD.loc (linLayOmega tinyD.st.codes tinyP.S) :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- A function that says yes to all and lays nothing does not meet the law's first half. -/
theorem not_foldSoundOf_yes [Fintype K] : ¬ FoldSoundOf ρ fun _ d _ => some d := by
  classical
  intro h
  have h1 : omegaOf tinyD.loc (linLayOmega tinyD.st.codes tinyP.S)
      (fun o _ _ => if o = 0 then (1 : K) else 0) 0 = 1 := by simp [omegaOf, tinyD]
  have h2 : ∀ k, uOf tinyD.loc (fun o _ _ => if o = 0 then (1 : K) else 0) k = 0 := by
    intro k; simp [uOf, tinyD]
  have h3 := h tinyP tinyD tinyT (fun o _ _ => if o = 0 then 1 else 0) tiny_needed tiny_placed
    ⟨0, by decide, by rw [h1]; simp [h2]⟩
  have hb : tinyP.S.kRow * Fintype.card K ^ (tinyP.S.kRow - 1) = 0 := by rw [tiny_kRow]; simp
  rw [hb, Nat.le_zero, Finset.card_eq_zero] at h3
  refine Finset.filter_eq_empty_iff.1 h3 (Finset.mem_univ fun _ => 0)
    ⟨[], tinyR, _, ?_, rfl, ?_, ?_⟩
  · exact (List.ofFn_eq_nil_iff.2 tiny_kRow).symm
  · intro r hr
    simp [rowsOn, tinyD, tinyT] at hr
  · intro r hr
    simp [rowsOn, tinyD, tinyT] at hr

/-- Neither function meets the joined law. -/
theorem not_foldLawOf_yes [Fintype K] : ¬ FoldLawOf ρ fun _ d _ => some d :=
  fun h => not_foldSoundOf_yes ρ h.1

@[inherit_doc not_foldLawOf_yes]
theorem not_foldLawOf_no [Fintype K] : ¬ FoldLawOf ρ fun _ _ _ => none :=
  fun h => not_yesOf_no h.2

end Desc.K14.Law
