-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5AtMgAll.lean: kind K5: THE EQUATIONS THAT THE KIND's LAW AT THE TABLE TAKES OF THE FILLING AND OF ITS DATA, AT THE COMPOSED MEANING ITSELF: mgAll 𝔇 Mg
(Johnson/Desc/Sound/MgAll.lean), GENERAL IN THE STRUCTURE OF PARAMETERS 𝔇 AND IN THE MEANING BENEATH.

Compiled with the whole library.
(Where this and lean/THEOREM.md differ, the page holds.)

Typed by reading MgAll.lean · MgAllAt.lean · MgBase.lean · Johnson/P5J/MeansQ.lean.

Why. The structures DataIs · DataSent · MgGains (K5AtEqsPlus.lean · K5DoorAtPlus.lean · K5GainsPlus.lean) and some fields of K5Rest (K5AtMgPaid.lean) are equations of letters, taken so far on the word of docstrings.
Here each is a theorem at the term, by rfl or by a lemma of the composed meaning's own files.

Main names:
  `dataIs_any`, `dataSent_any`: the two structures on the data, at D := 𝔇.pubD · Wv := X · links := 𝔇.links · Dn := 𝔇.sent · cs := 𝔇.cs.
  `mgGains_any`: MgGains at the NARROW filling mgAll 𝔇 Mg, at seatT := fun j => 𝔇.l3.seat x.link false j.1 · arrL := 𝔇.l3.arr · rad := 𝔇.l3.rad; by mgAll_formsT (Johnson/Desc/Sound/MgAll.lean) and mgAll_worth_att_planes | _keys | _rider (Johnson/Desc/Sound/MgAllAt.lean)
    with attAt_plus · pieceAt_plus (K5LeftFitsE.lean). `l3_arr`: 𝔇.l3.arr = 𝔇.arr.
  `hpub_any`: the bridge's hpub. `runsIs_any`, `mHIs_any`, `rdIs_any`: three fields of K5Rest. `nsOf_any`: what the field nsOf says at the term: NOT the field: that wants a law on the built segments.
  `bodyAll`, `constrIs_any`: the field constrIs at dP := 𝔇.digitsPart · bsW := 𝔇.H.base · Hd := Holds · body := bodyAll 𝔇. `bodySmall_any`: the field bodySmall there, at an odd number that is not the output head's.
  `baseIn_base`, `baseMakes_base`: two fields at the closed meaning beneath (mgBase).
NOT HERE: MgIs (it stands at the wider filling, whose make is turning) · baseP (at the closed base it is a test against a written table) · whatever speaks of a closed 𝔇 (K5AtConstant.lean).
Is it empty here? Equations: they hold at every 𝔇.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgBase
import Johnson.Desc.First.Att.Door.Law.K5GainsPlus
import Johnson.Desc.First.Att.Door.Law.K5DoorAtPlus
import Johnson.Desc.First.Att.Door.Law.K5LeftFitsE

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open OnBytes OnBytes.Model
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.First.Att.P (PlanIs behind)
open VerifiableInference.OnPublicFiles (headLink)

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **The composed data's letters are the kind's.** -/
theorem dataIs_any (m : ℕ) : DataIs 𝔇.pubD X 𝔇.links m := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **The law's Sent is the composed data's.** -/
theorem dataSent_any : DataSent 𝔇.pubD 𝔇.cs 𝔇.sent := ⟨rfl, rfl, rfl⟩

/-- The bridge's hpub. -/
theorem hpub_any : (mgAll 𝔇 Mg).pub = pubAll 𝔇.pubD Mg.pub := mgAll_pub 𝔇 Mg

theorem runsIs_any : 𝔇.pubD.runs = runsAt 𝔇.links := rfl

theorem mHIs_any : 𝔇.pubD.mH = (if X.p4 then 2 else 1) * X.NGr := rfl

theorem rdIs_any : 𝔇.pubD.Rd = K9.readersAt 𝔇.lk X 𝔇.pubD.mH := rfl

/-- What the field nsOf says at the term. -/
theorem nsOf_any (m : ℕ) : 𝔇.pubD.nsOf m = (𝔇.built[m]?).map (·.ns) := rfl

/-- The lookup arguments' arr is the term's own. -/
theorem l3_arr : 𝔇.l3.arr = 𝔇.arr := rfl

/-- **Four more equations on the filling**, at the narrow filling. -/
theorem mgGains_any {g : ℕ} {a : Attention.Plan} {x : Look.Place} (hP : PlanIs X) (h4 : X.p4 = true) (ha : X.A[g]? = some a)
    (hx : lookAt X (2 * g + 1) false = some x) :
    MgGains (mgAll 𝔇 Mg) 𝔇.cs 𝔇.arr 𝔇.ms 𝔇.Rd 𝔇.runs 𝔇.St 𝔇.N 𝔇.wt (2 * g + 1) x a.S a.seam.tl 𝔇.sent 𝔇.l3.rad
      (fun j => 𝔇.l3.seat x.link false j.1) 𝔇.l3.arr where
  formsT := mgAll_formsT 𝔇 Mg
  planes := fun a' y w => by
    have h := mgAll_worth_att_planes 𝔇 Mg (2 * g + 1) (attAt_plus hP h4 ha hx) a' y w
    rwa [pieceAt_plus h4] at h
  keys := fun a' y w => by
    have h := mgAll_worth_att_keys 𝔇 Mg (2 * g + 1) (attAt_plus hP h4 ha hx) a' y w
    rwa [pieceAt_plus h4] at h
  rider := fun a' y w => by
    have h := mgAll_worth_att_rider 𝔇 Mg (2 * g + 1) (attAt_plus hP h4 ha hx) a' y w
    rwa [pieceAt_plus h4] at h

/-- The body of a constraint at the term: constrQAt's three arms (Johnson/P5J/MeansQ.lean). -/
def bodyAll (n : ℕ) (p : First.Part) (i : IdxQ) (a : P × S) (y : Strs) (w : Wit (CellsQ rows cols) Tok MsgT) : Prop :=
  if n = headLink X then 𝔇.headPart p i a y w
  else if n % 2 = 0 then P5J.partG X i (𝔇.put (𝔇.H.req a) (𝔇.H.hid w).tok).val (𝔇.H.hid w).MG (n / 2) p
  else P5J.partA (OnBytes.Road.Hd.shapeA X (n / 2)) ((𝔇.H.hid w).MA (n / 2)) p

/-- **The field constrIs.** -/
theorem constrIs_any : ∀ n p a₁ y w, (mgAll 𝔇 Mg).constr n p a₁ y w ↔
    if p = .lookDigits then 𝔇.digitsPart n a₁ y w
    else (p = .small → 𝔇.H.base n w) ∧
      ∀ M i, 𝔇.decT y.cell a₁ = some M → VerifiableInference.OnPublicFiles.Flat.Holds M i → bodyAll 𝔇 n p i a₁ y w :=
  fun _ _ _ _ _ => Iff.rfl

/-- **The field bodySmall**: at an odd number that is not the output head's the body reads neither the verifier's state nor the strings. -/
theorem bodySmall_any {g : ℕ} (hH : 2 * g + 1 ≠ headLink X) : ∀ i a₁ a₂ y y' w,
    bodyAll 𝔇 (2 * g + 1) .small i a₁ y w → bodyAll 𝔇 (2 * g + 1) .small i a₂ y' w := by
  intro i a₁ a₂ y y' w h
  unfold bodyAll at h ⊢
  rw [if_neg hH, if_neg (by omega)] at h ⊢
  exact h

end

section
variable {P W : Type}

/-- **The field baseIn** at the closed meaning beneath. -/
theorem baseIn_base : ∀ (π : P) s a h G, s.here = .att a → (mgBase (P := P) (W := W)).inOrder (π, s) = true →
    (mgBase (P := P) (W := W)).inOrder (π, behind s a h G) = true := fun _ _ _ _ _ _ _ => rfl

/-- **The field baseMakes** at the closed meaning beneath. -/
theorem baseMakes_base (links : List ModelPart) (pl : Place) : ((mgBase (P := P) (W := W)).more.rows links pl).makes = [] := rfl

end

end H2K5.Door

#print axioms H2K5.Door.dataIs_any
#print axioms H2K5.Door.dataSent_any
#print axioms H2K5.Door.hpub_any
#print axioms H2K5.Door.runsIs_any
#print axioms H2K5.Door.mHIs_any
#print axioms H2K5.Door.rdIs_any
#print axioms H2K5.Door.nsOf_any
#print axioms H2K5.Door.l3_arr
#print axioms H2K5.Door.mgGains_any
#print axioms H2K5.Door.constrIs_any
#print axioms H2K5.Door.bodySmall_any
#print axioms H2K5.Door.baseIn_base
#print axioms H2K5.Door.baseMakes_base
