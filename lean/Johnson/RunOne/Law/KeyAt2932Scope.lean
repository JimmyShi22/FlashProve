-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/KeyAt2932Scope.lean: PUBLIC PREMISES OF K12's FILES' LAWS AT THE KEY FILE's LATER PROXIMITY TESTS (rows 2.9, 2.10 and 3.2 of the tables), IN SCOPE, AT The21AtName's TERMS: what the IOP as written in Lean tells of the six committed messages' trees · two numbers of the fold's shape · two facts on the tables' filling. Statements with proofs: calls, and one evaluation in the kernel. IT PAYS NO FIELD OF THE TABLES: IT PAYS PREMISES.
OBJECT. Fk X N P's telling at the six seats atSix · shapeAt X · baseAt X decN recBack.
USER. back_29 (K12Back29.lean) | back_210 (K12Back210.lean) and the like at 3.2.
LETTERS. X N P. PREMISES. The scope's four (the public files are in scope · the policy read · the chains made, at any digest · the source of them); for the seats also: the tests planOk and wantedOk accept · the data of the key file are DK's at the frame's depth, and these are the written data (the form in which the tables' filler holds them). AT THE SECOND MEMBER seats_six_scope says again what hlog_fits | told_fits (Johnson/RunOne/KeyAt15Fits.lean) say at row 1.15: a twin at one index.

  told_hlog_of_noFault: GENERAL: where the plain test on a seat finds no fault, the tree is told and has the shape's length. One call of seat_of_noFault (Johnson/Desc/Sound/PlanMemProofs.lean).
  seats_six_scope: at each of the six members: its tree is told, and whatever is told there has the length of the member's shape. By the six "no fault at the seat" in scope (seven_at, Johnson/RunOne/KeySevenInScope.lean; six_at, Johnson/RunOne/KeyTenInScope.lean).
  fold_full, fold_scope: the fold's index message bears an answer; the fold has a column.
  hi_at, hSm_at: on the filling: by layIdem_h₂ and smOnlyK.
Limits. That the premises can be met together is not shown here. One size. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.KeyTenInScope
import Johnson.RunOne.KeyFillSmOnly
import Johnson.RunOne.KeyFillBase
import Johnson.RunOne.KeyRowsAtFk
import Johnson.Top.Fire.Code.KeyAtName
import Johnson.Desc.Sound.PlanMemProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

namespace Johnson.RunOne.Law.KeyAt2932
open OnBytes OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key (Source madeAt sourceOf LayIdem)
open VerifiableInference.Desc.Key.Fill (six)
open Johnson.G.OfPlan (Made)
open Johnson.Pack (aOf)
open Johnson.Top.H (csKey)
open Lk6.AtPlan (keyFull)
open Johnson.RunOne.KeyRows23 (Fk numSix atSix seatAt shapeAt)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (key_in_scope)
open Johnson.RunOne.KeyLetters (seven_at six_at chains_of)
open LPFD (baseAt decN recBack)

/-- Where the plain test on a seat finds no fault, the tree is told and has the shape's length. -/
theorem told_hlog_of_noFault {Xi : Type} (G : FileDescription Xi) (cs : OnBytes.Codes) (tag : String)
    (s : OnBytes.OracleShape) (j t : ℕ) (h : seatFaultAt G cs tag s j t = none) :
    (G.oracleAt j).isSome = true ∧ ∀ o, G.oracleAt j = some o → o.logLength = aOf cs s := by
  obtain ⟨o, _, ho, _, hlen, _⟩ := seat_of_noFault G cs tag s j t h
  refine ⟨by rw [ho]; rfl, fun o' ho' => ?_⟩
  obtain rfl := Option.some.inj (ho'.symm.trans ho)
  exact hlen

variable {X : Source} {N : H2U.PlaceNums} {P : VerifiableInference.Desc.Key.LaterPlaces}

/-- **At each of the six members: its tree is told, and has the length of the member's shape.** -/
theorem seats_six_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : OnBytes.Model.Verify.Public} (hP : ReadOf Zp.pol Z)
    {cfg : ByteArray} {m : Made} (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true) (DK : WholeD)
    (hD₀ : (Fk X N P).data "key file" = .ok (DK.at OnBytes.Slice.frS.P.T.a)) (hDK : DK.at OnBytes.Slice.frS.P.T.a = Johnson.G.writtenKFull) :
    ∀ i : Fin six.length, ((Fk X N P).oracleAt (seatAt six numSix atSix i).1).isSome = true ∧
      ∀ o, (Fk X N P).oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1 := by
  have hD : (Fk X N P).data "key file" = .ok Johnson.G.writtenKFull := by rw [hD₀, hDK]
  obtain ⟨h0, h1, h2⟩ := (seven_at hZ hP hm hX hp hw hD).1 "" "" ""
  obtain ⟨h3, h4, h5⟩ := (six_at hZ hP hm hX hp hw hD).1 "" "" ""
  intro i
  match i with
  | ⟨0, _⟩ => exact told_hlog_of_noFault _ _ _ _ _ _ h0
  | ⟨1, _⟩ => exact told_hlog_of_noFault _ _ _ _ _ _ h1
  | ⟨2, _⟩ => exact told_hlog_of_noFault _ _ _ _ _ _ h2
  | ⟨3, _⟩ => exact told_hlog_of_noFault _ _ _ _ _ _ h3
  | ⟨4, _⟩ => exact told_hlog_of_noFault _ _ _ _ _ _ h4
  | ⟨5, _⟩ => exact told_hlog_of_noFault _ _ _ _ _ _ h5
  | ⟨n + 6, hn⟩ =>
    exact absurd hn (by
      show ¬ n + 6 < 6
      omega)

theorem fold_full : keyFull.once.shape.fold.index.answers ≠ 0 ∧ keyFull.once.shape.fold.columns ≠ 0 := by
  decide +kernel

/-- The fold's index message bears an answer; the fold has a column. -/
theorem fold_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : OnBytes.Model.Verify.Public} (hP : ReadOf Zp.pol Z)
    {cfg : ByteArray} {m : Made} (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) :
    (shapeAt X).fold.index.answers ≠ 0 ∧ (shapeAt X).fold.columns ≠ 0 := by
  have e : shapeAt X = keyFull.once.shape := by
    show X.chains.made.sized.key.once.shape = _
    rw [chains_of hX, key_in_scope hZ hP hm]
  rw [e]
  exact fold_full

/-- On the filling. -/
theorem hi_at (X : Source) : LayIdem (baseAt X decN recBack).h₂ :=
  Johnson.RunOne.KeyRows23.layIdem_h₂ _ _ _ _ _ _ _ _

theorem hSm_at (X : Source) : (baseAt X decN recBack).SmOnly :=
  Johnson.RunOne.KeyRows23.smOnlyK _ _ _ _ _ _ _

end Johnson.RunOne.Law.KeyAt2932

#print axioms Johnson.RunOne.Law.KeyAt2932.told_hlog_of_noFault
#print axioms Johnson.RunOne.Law.KeyAt2932.seats_six_scope
#print axioms Johnson.RunOne.Law.KeyAt2932.fold_full
#print axioms Johnson.RunOne.Law.KeyAt2932.fold_scope
#print axioms Johnson.RunOne.Law.KeyAt2932.hi_at
#print axioms Johnson.RunOne.Law.KeyAt2932.hSm_at
