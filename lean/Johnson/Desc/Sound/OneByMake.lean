-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/OneByMake.lean: "WHAT THE STORED TABLE DECODES TO": THE FIRST TABLE's DECODER IS THE SHARED CHAIN's, AT THAT CHAIN's FIRST STATE, BY MAKE; AND AT EVERY PUBLIC PART THAT IS MADE OF AN INSTANCE IT IS THE TOP STATEMENTS' OWN conf.D AT THE INSTANCE's RECORD. One definition, six theorems.

Why. The first joint's two premises (TP) "decodes at the first chain gives the shared chain's promise on the table" and (PW) "the shared chain's pin on the cells gives the first chain's" (Johnson/Desc/Sound/TieEnd.lean) are asked AT EVERY PUBLIC PART, with no promise. With the first table's decoder made of conf.D at the record that
recBack reads off the key they would want (KEY) at every key: by key_iff (Johnson/Desc/Sound/KeyAlong.lean) (KEY) IS FALSE AT A KEY WITH A FACTOR 0, and no text forbids such a key in a public part. So the one real equation is moved to the one place where "no factor is 0" is had and where the equation is spent: the start's glue.
  decShared … st₂: the first table's letter decT := decK at st₂ of the public part.
  decShared_is: it is decAtRec of the guarded decoder at the reader recAt ∘ st₂ ∘ fst: rfl · decK_is: decK is decAtRec of the same at recAt: rfl.
  tp_by_make, pw_by_make: **(TP) and (PW), TO THE LETTER OF TieEnd.lean, AT EVERY b**: by tpAtKey |
    pwAtKey (Johnson/Desc/Sound/TablePromiseAt.lean), whose equation of records is had from one
    premise: get leaves the public part as it is (hget). BESIDE IT TWO PREMISES EACH: hM (Mg₁.decodes
    | Mg₁.pinW is made of decShared at start₂) and hP (Pm.tablePromise | Mg.pinT is made of decK).
  shared_at_instance: **AT THE RELEASE's CONFIGURATION AT THE WRITTEN SIZES: at a public part q whose key is keyOf of rec (eKey's form), where st₂ lays the public part's key into its state (hkey): decShared … c (q, s) = (kcReq N pp E).conf.D (tabBack frS.P.T.a c) rec.**
  shared_at_oracles: the same at the reader that strsOf makes of a statement's oracles: = conf.D y rec: the form in which the end theorem's premise "hd" is asked.
THE HINGE ("(KEY) holds only where no seed's factor is 0: settle one of three: the first chain's promise excludes such records · conf.D returns none there · a premise paid across the joint"): NONE OF THE THREE AS WORDED; NEAREST THE FIRST. The equation with conf.D is asked AT INSTANCES' PUBLIC PARTS ALONE, where the
key is written of a record whose factors are not 0 by type; at every other public part the two tables read ONE decoder by make, and nothing is said of conf.D.

Limits. hkey and the key's equation are premises: by the texts of a description's start₂ and of the map from instances (other files have the first at their description; the second is the end theorem's eKey). The plan's table's shape at the full size: a premise. At a public part that is no instance's, decShared may decode at a sample
with a factor 0: no law may read it as conf.D there. At heldFull the first table's decoder is typed at the full size alone. NO MEMBER.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.DataAlong

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker OnBytes.Flat KObj Desc.Plain
open _root_.Run.PQ (CK SgX)
open _root_.Iop (oneExternalString)
open VerifiableInference.Desc (Strs Wit Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS PromMeaning)
open VerifiableInference.Desc.First (Meaning Numbers)
open VerifiableInference.Desc.Sound (tabBack tabBack_cellAt decGuard decAtRec CellsOf decodesOf pinWOf MsgT strsOf
  strsOfAct frameAt EAll Three actQ tiedNumbers tpAtKey pwAtKey)
open VerifiableInference.OnPublicFiles (kcReq)

section Make
variable {Cells : Type} (p : Par) (err₂ eM : Nat)
  (rank : ((Fin p.S.fold.index.v → Bool) →
    Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
  (held : ((ixOf2 p.S.fold err₂ eM rank).Row × Fin p.S.fold.index.code.ell → GE) → Option Cells)

/-- **The first table's decoder, made of the shared chain's**: decK at the state that st₂ makes of the public part. -/
noncomputable def decShared {P S : Type} (st₂ : P → St) : CellsOf → P × S → Option Cells :=
  fun c x => decK p err₂ eM rank held c (st₂ x.1)

/-- It is the guarded decoder at a reader of the record. -/
theorem decShared_is {P S : Type} (st₂ : P → St) :
    decShared (S := S) p err₂ eM rank held st₂ =
      decAtRec (decGuard (collAt p err₂ eM rank) (dcdAt p err₂ eM rank) held)
        (fun x : P × S => recAt p err₂ eM rank (st₂ x.1)) := rfl

/-- So is decK. -/
theorem decK_is :
    decK p err₂ eM rank held =
      decAtRec (decGuard (collAt p err₂ eM rank) (dcdAt p err₂ eM rank) held) (recAt p err₂ eM rank) := rfl

/-- **(TP), to the letter, at every b: by make.** -/
theorem tp_by_make (C : CK) (D : WholeD) (all : List LeftT) (Y P S₁' S₃' X₁ X₂ Cl W : Type) (start₂ : P → St)
    (T : Three C D all Y (P × S₁') ((P × S₁') × St) ((P × S₁' × St) × S₃') X₁ X₂ Cl W)
    (get : P × S₁' → P × VerifiableInference.Desc.First.S) (hget : ∀ a, (get a).1 = a.1) (N₁ : Numbers)
    (Mg₁ : Meaning P W) (Ns : NumbersS) (Pm : PromMeaning St)
    (hM : Mg₁.decodes = decodesOf (decShared p err₂ eM rank held start₂))
    (hP : Pm.tablePromise = decodesOf (decK p err₂ eM rank held)) :
    ∀ b : (P × S₁') × (EAll D all).Str,
      Mg₁.decodes (get b.1) (strsOf (frameAt D all D.key₁ T.ft₁) b.2) →
      Pm.tablePromise (start₂ b.1.1) (strsOfAct (frameAt D all D.key₂ T.ft₂)
        ((actQ (tiedNumbers N₁ Ns) T.p₂ T.l₂ 0).2 ((b.1, start₂ b.1.1), b.2))) :=
  tpAtKey C D all Y P P S₁' St S₃' X₁ X₂ Cl W _ Cells start₂ T get N₁ Mg₁ Ns Pm
    (decGuard (collAt p err₂ eM rank) (dcdAt p err₂ eM rank) held)
    (fun x => recAt p err₂ eM rank (start₂ x.1)) (recAt p err₂ eM rank) hM hP
    (fun a => congrArg (fun q => recAt p err₂ eM rank (start₂ q)) (hget a).symm)

/-- **(PW), to the letter, at every b and w: by make.** -/
theorem pw_by_make {Tok : Type} (C : CK) (D : WholeD) (all : List LeftT) (Y P S₁' S₃' X₁ X₂ Cl : Type)
    (start₂ : P → St)
    (T : Three C D all Y (P × S₁') ((P × S₁') × St) ((P × S₁' × St) × S₃') X₁ X₂ Cl (Wit Cells Tok MsgT))
    (get : P × S₁' → P × VerifiableInference.Desc.First.S) (hget : ∀ a, (get a).1 = a.1) (N₁ : Numbers)
    (Mg₁ : Meaning P (Wit Cells Tok MsgT)) (Ns : NumbersS) (Mg : MeaningS St (P × S₁') (Wit Cells Tok MsgT))
    (hM : Mg₁.pinW = pinWOf (decShared p err₂ eM rank held start₂))
    (hP : Mg.pinT = pinWOf (decK p err₂ eM rank held)) :
    ∀ (b : (P × S₁') × (EAll D all).Str) (w : Wit Cells Tok MsgT),
      Mg.pinT (start₂ b.1.1) (strsOfAct (frameAt D all D.key₂ T.ft₂)
        ((actQ (tiedNumbers N₁ Ns) T.p₂ T.l₂ 0).2 ((b.1, start₂ b.1.1), b.2))) w →
      Mg₁.pinW (get b.1) (strsOf (frameAt D all D.key₁ T.ft₁) b.2) w :=
  pwAtKey C D all Y P P S₁' St S₃' X₁ X₂ Cl _ Cells Tok start₂ T get N₁ Mg₁ Ns Mg
    (decGuard (collAt p err₂ eM rank) (dcdAt p err₂ eM rank) held)
    (fun x => recAt p err₂ eM rank (start₂ x.1)) (recAt p err₂ eM rank) hM hP
    (fun a => congrArg (fun q => recAt p err₂ eM rank (start₂ q)) (hget a).symm)

end Make

section Full
variable (p : Par) (err sb : Nat) (h : p.S.fold.index = ⟨⟨32, 402653184, 44040191⟩, 11, 1, sb⟩)
  (N : MatrixNums) (pp : Inst.Model.ScalesAndPolicy) (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) N pp))

/-- **At a public part that is made of an instance the first table's decoder is the top statements' own at the instance's record.** -/
theorem shared_at_instance {P S : Type} (st₂ : P → St) (keyB : P → TableKey)
    (hkey : ∀ q, (st₂ q).loc.key = keyB q) (q : P) (rec : (kcReq N pp E).conf.Rec)
    (hq : keyB q = keyOf (fun β : NZ => β.val) rec) (c : CellsOf) (s : S) :
    decShared p err 2852142980 (rankLib p.S.fold) (heldFull p err sb h N pp E) st₂ c (q, s) =
      (kcReq N pp E).conf.D (tabBack frS.P.T.a c) rec :=
  dec_full_keyOf p err sb h N pp E c (st₂ q) rec ((hkey q).trans hq)

/-- The same at a statement's oracles: the end theorem's premise on the decoder, in its form. -/
theorem shared_at_oracles {P S : Type} (st₂ : P → St) (keyB : P → TableKey)
    (hkey : ∀ q, (st₂ q).loc.key = keyB q) (q : P) (rec : (kcReq N pp E).conf.Rec)
    (hq : keyB q = keyOf (fun β : NZ => β.val) rec) (DP : WholeD) (all : List LeftT) (key : ℕ → ℕ) (ft : ℕ)
    (y : (frameAt (DP.at frS.P.T.a) all key ft).E.Str) (s : S) :
    decShared p err 2852142980 (rankLib p.S.fold) (heldFull p err sb h N pp E) st₂
        (strsOf (frameAt (DP.at frS.P.T.a) all key ft) y).cell (q, s) =
      (kcReq N pp E).conf.D y.1 rec := by
  rw [shared_at_instance p err sb h N pp E st₂ keyB hkey q rec hq]
  exact congrArg (fun t => (kcReq N pp E).conf.D t rec)
    (tabBack_cellAt (frameAt (DP.at frS.P.T.a) all key ft) y)

end Full

end Desc.K14.Law

#print axioms Desc.K14.Law.decShared_is
#print axioms Desc.K14.Law.tp_by_make
#print axioms Desc.K14.Law.pw_by_make
#print axioms Desc.K14.Law.shared_at_instance
#print axioms Desc.K14.Law.shared_at_oracles
