-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5MgIsAll.lean: kind K5: THE FIFTEEN EQUATIONS ON THE FILLING (MgIs, K5AtEqsPlus.lean) AND THE FOUR MORE (MgGains, K5GainsPlus.lean) AT THE WIDER FILLING mgPlus (PlusBridge.lean) OVER THE
COMPOSED MEANING mgAll 𝔇 Mg (Johnson/Desc/Sound/MgAll.lean): GENERAL IN 𝔇 AND Mg FIRST, THEN AT THE CLOSED CONSTANT mgAtAll h (Johnson/P5J/MgAtAll.lean) OVER mgBase.

Why. The kind's law at the table (k5_tiedAtR_owes, K5TiedOwes.lean) takes E : MgIs … and G : MgGains … as premises. Here both are theorems at the term.

Main names:
  `mgB0`: the closed meaning beneath, with its two types written. `mgPlusAll h Ld Ms`: the wider filling over the constant.
  `mgIs_any`, `mgIs_all`: MgIs, at in0 := the base's own "in order" · c5 := "the request file's bytes are a request's" · D13 := d13 𝔇.
  `mgGains_plus`: the wider filling leaves formsT and worth: MgGains rides up. `mgGainsPlus_any`, `mgGainsPlus_all`: MgGains in the letters of the law's premise G.
  `hM0_all`: the base's list of extra public tests is empty. `hm_all`: the constant's list, as the law's top writes it. `hpubPlus_all`: the bridge's hpub at mgB0.
Is it empty here? Equations: they hold at every 𝔇; at the constant under the head h : AtMgA …: A MEMBER OF IT IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5AtConstant
import Johnson.Desc.First.Att.Door.Law.PlusBridge
import Johnson.Top.H0.Fill.PubP1

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (Sent lookAt sigListCalls)
open VerifiableInference.Desc.First.Att.P (PlanIs uArm)
open VerifiableInference.Desc.K9 (Readers)
open VerifiableInference.Desc.K12.Door (Laid)
open P5J (AtMgA mgAtAll TS)

section
variable {Pp Cells Tok : Type} {Mg : Meaning Pp (Wit Cells Tok MsgT)} {cs : Codes} {arr : ℕ → ℕ → ℕ} {ms : List Mem}
  {Rd : ℕ → Readers} {runs : ℕ → ℕ → String → List (ℕ × String)} {St : Stated} {N : Numbers}
  {wt : ℕ → Pp × S → Strs → Wit Cells Tok MsgT → Prop} {m : ℕ}
  {x : Look.Place} {A : Attention.Shape} {tl : HTailF2} {Dn : Sent} {rad : OracleShape → ℕ}
  {seatT : Fin (sigListCalls Dn rad x.link).length → ℕ × ℕ} {arrL : ℕ → ℕ → ℕ}

/-- **The wider filling leaves formsT and worth.** -/
theorem mgGains_plus (G : MgGains Mg cs arr ms Rd runs St N wt m x A tl Dn rad seatT arrL) (M0 : More) (D : PubData) (L : Laid)
    (M : List OracleShape) (base : Pub → Pp × S → Bool) (cs' : Codes) :
    MgGains (mgPlus Mg M0 D L M base cs') cs arr ms Rd runs St N wt m x A tl Dn rad seatT arrL :=
  ⟨G.formsT, G.planes, G.keys, G.rider⟩

end

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **The fifteen equations, at the wider filling over the composed meaning.** -/
theorem mgIs_any (Ld : Laid) (Ms : List OracleShape) :
    MgIs (mgPlus (mgAll 𝔇 Mg) Mg.more 𝔇.pubD Ld Ms Mg.pub 𝔇.sent.codes) Mg 𝔇.pubD 𝔇.sent.codes 𝔇.G 𝔇.arr 𝔇.smp 𝔇.ms 𝔇.decT Mg.inOrder
      (fun p => (_root_.Meaning.backReq (𝔇.reqB p)).isSome) Ld Ms (d13 𝔇) where
  pub := rfl
  pubPl := fun m a => by
    show (if isWideQ (.left m) = true then True else (mgAll 𝔇 Mg).pubP (.left m) a) = _
    rw [if_neg (by intro h; cases h), mgAll_pubP]
    rfl
  pubPlo := fun m a => by
    show (if isWideQ (.leftOn m) = true then True else (mgAll 𝔇 Mg).pubP (.leftOn m) a) = _
    rw [if_neg (by intro h; cases h), mgAll_pubP]
    rfl
  pubPo := fun q a h1 h2 h0 => by
    show (if isWideQ q = true then True else (mgAll 𝔇 Mg).pubP q a)
    split
    · trivial
    rw [mgAll_pubP, Look.fill_pubP_other _ _ _ q a h1 h2]
    show (if FillP1.p1Item q = true then True else Mg.pubP q a)
    split
    · trivial
    · exact h0
  pubPw := fun q a hq => by
    show (if isWideQ q = true then True else (mgAll 𝔇 Mg).pubP q a)
    rw [if_pos hq]
    trivial
  held := mgAll_held 𝔇 Mg
  shown := mgAll_shown 𝔇 Mg
  noColl := mgAll_noColl 𝔇 Mg
  decodes := mgAll_decodes 𝔇 Mg
  inOrder := fun a => by
    show ((mgAll 𝔇 Mg).inOrder a && decide (a.2.st.codes = 𝔇.sent.codes)) = _
    rw [mgAll_inOrder_at 𝔇 Mg a]
  pin := mgAll_pin 𝔇 Mg
  pinW := mgAll_pinW 𝔇 Mg
  row := mgAll_row 𝔇 Mg
  pile := mgAll_pile 𝔇 Mg
  more := rfl

/-- **MgGains in the letters of the law's premise G**, at the wider filling. -/
theorem mgGainsPlus_any {g : ℕ} {a : Attention.Plan} {x : Look.Place} (hA : 𝔇.uA = uArm X) (hP : PlanIs X) (h4 : X.p4 = true)
    (ha : X.A[g]? = some a) (hx : lookAt X (2 * g + 1) false = some x) (Ld : Laid) (Ms : List OracleShape) :
    MgGains (mgPlus (mgAll 𝔇 Mg) Mg.more 𝔇.pubD Ld Ms Mg.pub 𝔇.sent.codes) 𝔇.sent.codes 𝔇.arr 𝔇.ms 𝔇.pubD.Rd 𝔇.pubD.runs
      (Stated.of (uBySort 𝔇.uL (uArm X) 𝔇.uH)) 𝔇.pubD.N 𝔇.wt (2 * g + 1) x a.S a.seam.tl 𝔇.sent 𝔇.l3.rad
      (fun j => 𝔇.l3.seat x.link false j.1) 𝔇.arr := by
  have G := mgGains_plus (mgGains_any 𝔇 Mg hP h4 ha hx) Mg.more 𝔇.pubD Ld Ms Mg.pub 𝔇.sent.codes
  rw [← hA]
  exact G

end

/-! ## At the closed constant -/

/-- The closed meaning beneath, with its two types written. -/
abbrev mgB0 : Meaning ProofFile.InstPub (Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT) := mgBase

section
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA o Z D r Zp Np cF x)

/-- **The wider filling over the constant.** -/
noncomputable abbrev mgPlusAll (Ld : Laid) (Ms : List OracleShape) :
    Meaning ProofFile.InstPub (Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT) :=
  mgPlus (mgAtAll h) mgB0.more h.𝔇.pubD Ld Ms mgB0.pub h.𝔇.sent.codes

theorem mgIs_all (Ld : Laid) (Ms : List OracleShape) :
    MgIs (mgPlusAll h Ld Ms) mgB0 h.𝔇.pubD h.𝔇.sent.codes h.𝔇.G h.𝔇.arr h.𝔇.smp h.𝔇.ms h.𝔇.decT mgB0.inOrder
      (fun p => (_root_.Meaning.backReq (h.𝔇.reqB p)).isSome) Ld Ms (d13 h.𝔇) := mgIs_any h.𝔇 mgB0 Ld Ms

theorem mgGainsPlus_all {g : ℕ} {a : Attention.Plan} {x₁ : Look.Place} (h4 : (P5J.At.X Zp).p4 = true) (ha : (P5J.At.X Zp).A[g]? = some a)
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) (Ld : Laid) (Ms : List OracleShape) :
    MgGains (mgPlusAll h Ld Ms) h.𝔇.sent.codes h.𝔇.arr h.𝔇.ms h.𝔇.pubD.Rd h.𝔇.pubD.runs
      (Stated.of (uBySort h.𝔇.uL (uArm (P5J.At.X Zp)) h.𝔇.uH)) h.𝔇.pubD.N h.𝔇.wt (2 * g + 1) x₁ a.S a.seam.tl h.𝔇.sent h.𝔇.l3.rad
      (fun j => h.𝔇.l3.seat x₁.link false j.1) h.𝔇.arr :=
  mgGainsPlus_any h.𝔇 mgB0 rfl (planIs_all h) h4 ha hx Ld Ms

/-- The base's list of extra public tests is empty. -/
theorem hM0_all : mgB0.more = {} := rfl

/-- The constant's list of extra public tests, as the law's top writes it. -/
theorem hm_all : (mgAtAll h).more = (moreOver9 {}).strike leavesName := more_all h

/-- The bridge's hpub, at mgB0. -/
theorem hpubPlus_all : (mgAtAll h).pub = pubAll h.𝔇.pubD mgB0.pub := hpub_any h.𝔇 mgB0

end

end H2K5.Door

#print axioms H2K5.Door.mgGains_plus
#print axioms H2K5.Door.mgIs_any
#print axioms H2K5.Door.mgGainsPlus_any
#print axioms H2K5.Door.mgIs_all
#print axioms H2K5.Door.mgGainsPlus_all
#print axioms H2K5.Door.hM0_all
#print axioms H2K5.Door.hm_all
#print axioms H2K5.Door.hpubPlus_all
