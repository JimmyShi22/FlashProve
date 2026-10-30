-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/LeftOfRest.lean: K9's LAW OF A LINK: THE FIELD hLeft OF WHAT IS LEFT OF
THE CORE (`CoreLeft`, CoreLeft.lean beside this file), TO ITS LETTER, FROM A NAMED REST OF NINE
SENTENCES, EACH SMALLER THAN THE FIELD AND EACH WITH ITS OWN NAME. A structure and two theorems: a
joining. A law file; no running text imports it.
  `LeftRest`          the nine. PUBLIC (no state, no witness): dig · maskPub · first. ON THE READER,
                    AT EVERY WITNESS: oneCells · oneMask. ON A STATE IN FRONT OF THE BATCHING, UNDER
                    THE PROMISE: cells · mask. ON THE RUN BEHIND IT, UNDER THOSE OF hLeft's OWN
                    HYPOTHESES THAT EACH READS: three (the heard lookup's shape, "five", the points'
                    sizes) · slots (the full state's ledger has its sizes, and every slot that a
                    form of the first four claims names is filled in it).
  `hLeft_of_rest`     LeftRest ⊢ hLeft's text (cut by program out of CoreLeft.lean).
  `coreLeft_lays`     LEAN's WORD THAT THE END IS THE FIELD's TYPE: a CoreLeft with its field hLeft
laid anew by hLeft_of_rest. HOW. digitsLeft_of (LeftThree.lean): DigitsLeft from the binding of y, a
part in front, LeftAsks and the three. "A part is there in front", LeftAsks.arrays and "the full
state's ledger is later" come out of hLeft's own hypothesis Fx9 … t (part_of_fx, LeftLight.lean);
LeftAsks.slots by slots_of_full.

Limits. AN IMPLICATION: LeftRest IS THE DEBT: it is shown of nothing here; that its nine can be met
together is not tried here. Nothing on soundness or on hiding.
-/
import Johnson.Desc.First.Link.Law.CoreLeft
import Johnson.Desc.First.Link.Law.LeftLight

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open TwV OnBytes OnBytes.Model OnBytes.PscRun OnBytes.DgP Cb.Fo Cb.LdLkp
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Fo _root_.Fo.Eq
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.K9 (Where atS segAt?)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers pinsOf formsOf shift openSets
  rowsDue FoldFacts FoldData)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First.K8.Four (unknownOf)
open VerifiableInference.Desc.First.TailClaims (equations)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open VerifiableInference.Desc.K4Values (winOf)
open VerifiableInference.Desc.JoinAtBlocks
open _root_.Run (ckP)
open Johnson.Desc.First.Walk.Tied (Reach MeantAt)
open VerifiableInference.Desc.Kinds.Head.Law (headPartK6)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) {F : Sound.Frame}
  (links : List ModelPart) (pl : List Place)
  (z : P) (Rz : ℕ → S × F.E.Str → Prop) (k m : ℕ)

local notation "Mg" => mgAll 𝔇 mgBase
local notation "rdW" => rdC (Cells := CellsQ rows cols) (Tok := Tok) 𝔇.cs 𝔇.arr 𝔇.ms
local notation "own" => 𝔇.N.group m
local notation "cx" => ctxPins 𝔇.N (mgAll 𝔇 mgBase) z m
local notation "onK" => onTR 𝔇.N (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rz
local notation "o0" => onTR 𝔇.N (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rz k
local notation "o1" => onTR 𝔇.N (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rz (k + 1)
local notation "o2" => onTR 𝔇.N (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rz (k + 1 + 1)
local notation "o3" => onTR 𝔇.N (mgAll 𝔇 mgBase) links pl (fun s : S => (z, s)) Rz (k + 1 + 1 + 1)

open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.EntryUnit (entUnit)

variable {β : Type}

open VerifiableInference.Desc.First.Att.P (OneReader ReadMsgOf)

/-- **The named rest of hLeft.** -/
structure LeftRest (L : Link S Claim) (u : HTailF2) (ψ : S → β)
    (Ok : Phi β × Option Pub9 → Prop) (nU : Array ℕ) (p : Where) (x : First.Look.Place)
    (tlD : HTailF2) (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) : Prop where
  /-- public: the digits' lookup's plan holds -/
  dig : ∃ set pp, DigOK set x tlD 𝔇.sent 𝔇.l3.rad pp
  /-- public: the test on the mask's seat -/
  maskPub : maskB 𝔇.sent (digList x 𝔇.sent 𝔇.l3.rad) x.link x.arrays.ns = true
  /-- public: each piece's first column is its call's -/
  first : ∀ q < 2, ∀ pc ∈ piecesL tlD q, pc.c0 = q * tlD.mz
  /-- the exchange's reading of the witness and the table's reader are one, at the cells -/
  oneCells : ∀ w, OneReader (ReadMsgOf (cellAddr tlD) (seatOf 𝔇.sent x.link)) 𝔇.sent.codes
    (digList x 𝔇.sent 𝔇.l3.rad) sT
    (msgsOf 𝔇.sent.codes (digList x 𝔇.sent 𝔇.l3.rad) sT 𝔇.l3.arr w) (rdW w)
  /-- and at the mask -/
  oneMask : ∀ w, OneReader (ReadMsgOf (maskAddr x.arrays.ns) (seatOf 𝔇.sent x.link)) 𝔇.sent.codes
    (digList x 𝔇.sent 𝔇.l3.rad) sT
    (msgsOf 𝔇.sent.codes (digList x 𝔇.sent 𝔇.l3.rad) sT 𝔇.l3.arr w) (rdW w)
  /-- at the part in front of the batching: the dictionary on the digits' cells -/
  cells : ∀ a pa, o0 a → atS.get? a.1 = some pa → CellOkR x tlD 𝔇.sent 𝔇.l3.rad sT own pa
  /-- and on the mask row -/
  mask : ∀ a pa, o0 a → atS.get? a.1 = some pa → MaskOkR x 𝔇.sent 𝔇.l3.rad sT own pa
  /-- what the digits' lookup returned fits the structure at which the equations are made -/
  three : ∀ a (e : S) (tl : HTailF2) (g : Forest.Heard), o0 a → e.tl? = some tl →
    tl.heard = some g →
    Fx9 (phiAll u ψ) (fun q => Ok q ∧ (rowsFit p.rows pi8) q) (fixed9 (phiAll u ψ) a.1) e →
    tl.f9 = g.shape ∧ 5 ≤ g.shape.kT + g.shape.cK ∧
      ∀ q < 2, (g.zk.getD q #[]).size = (tl.zOf q).call.n
  /-- the first four claims' forms name filled slots of the full state's ledger -/
  slots : ∀ a (t e : S) (b : K9.Part) (front : ℕ) (Fe : Fork) (tl tl' : HTailF2)
    (funs : Array HFun) (F1 : Fork) (c : List Claim), o0 a → atS.get? t = some b →
    e.fork? = some Fe → e.tl? = some tl → e.funs? = some funs →
    equations (Fe.nClaim + front) tl funs Fe = .ok (tl', F1, c) →
    Fx9 (phiAll u ψ) (fun q => Ok q ∧ (rowsFit p.rows pi8) q) (fixed9 (phiAll u ψ) a.1) e →
    Fx9 (phiAll u ψ) (fun q => Ok q ∧ (rowsFit p.rows pi8) q) (fixed9 (phiAll u ψ) a.1) t →
    laterK atS (O9 (K := GE8) (phiAll u ψ) (fun q => Ok q ∧ (rowsFit p.rows pi8) q) (FullAt nU))
      ((e.putTl tl').putFork F1) t →
    Sized b.F ∧ ∀ kc ∈ c.take 4, ∀ s ∈ kc.form.slots.toList, Filled b.F s.1

/-- **hLeft, to its letter, from the named rest.** -/
theorem hLeft_of_rest (L : Link S Claim) (u : HTailF2) (ψ : S → β)
    (Ok : Phi β × Option Pub9 → Prop) (nU : Array ℕ) (p : Where) (x : First.Look.Place)
    (tlD : HTailF2) (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (R : LeftRest 𝔇 links pl z Rz k m L u ψ Ok nU p x tlD sT) :
    ∀ a τ b' w₀ y, o0 a → pb.ior.red.out a τ = some b' → boundAt atS (fun a w => tabAt own
    (rdW w) a.1) cx a (pb.ext a τ w₀) y → ∀ (t e' : S) (b : K9.Part) (Fc : Fork) (tlX : HTailF2) (g
    : Forest.Heard) (front : ℕ) (e : S) (Fe : Fork) (tl tl' : HTailF2) (funs : Array HFun) (F1 :
    Fork) (c : List Claim), K9L.afterOf ((moves₂ (α := Phi β) L).map (·.move)) b'.1 = .ok t →
    atS.get? t = some b → k8Tests nU e' = .ok t → e'.fork? = some Fc → e'.tl? = some tlX → tlX.heard
    = some g → b.F = coefAll tlX g Fc → e.fork? = some Fe → e.tl? = some tl → e.funs? = some funs →
    blank u tl = blank u tlX → tl.heard = some g → equations (Fe.nClaim + front) tl funs Fe = .ok
    (tl', F1, c) → Fx9 (phiAll u ψ) (fun q => Ok q ∧ (rowsFit p.rows pi8) q) (fixed9 (phiAll u ψ)
    a.1) e → Fx9 (phiAll u ψ) (fun q => Ok q ∧ (rowsFit p.rows pi8) q) (fixed9 (phiAll u ψ) a.1) t →
    laterK atS (O9 (K := GE8) (phiAll u ψ) (fun q => Ok q ∧ (rowsFit p.rows pi8) q) (FullAt nU))
    ((e.putTl tl').putFork F1) t → DigitsLeft x tlD 𝔇.sent 𝔇.l3.rad sT 𝔇.l3.arr (pb.ext a τ w₀) g
    tl c b.L y := by
  intro a τ b' w₀ y ho _ hbd t e' b Fc tlX g front e Fe tl tl' funs F1 c _ hb _ _ _ _ _ h8 h9 h10 _
    h12 h13 fxe fxt hlat
  obtain ⟨pa, hpa, harr, hLater⟩ := part_of_fx fxt hb
  obtain ⟨s1, s2, s3⟩ := R.three a e tl g ho h9 h12 fxe
  obtain ⟨hS, hF⟩ := R.slots a t e b front Fe tl tl' funs F1 c ho hb h8 h9 h10 h13 fxe fxt hlat
  exact digitsLeft_of x tlD 𝔇.sent 𝔇.l3.rad sT 𝔇.l3.arr own rdW cx hbd hpa
    ⟨R.dig, R.oneCells _, R.oneMask _, R.cells a pa ho hpa, R.mask a pa ho hpa, R.maskPub, harr,
      R.first, slots_of_full hLater hS hF⟩ s1 s2 s3

/-- Lean's word that the end is the field's type. -/
theorem coreLeft_lays (sub : First.ModelPart) (L : Link S Claim) (u : HTailF2) (ψ : S → β)
    (Ok : Phi β × Option Pub9 → Prop) (nU : Array ℕ) (p : Where)
    (tmOf : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → Phi β × Option Pub9 → ℕ) (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (o : ℕ × String)
    (run : ℕ → S → Except String (List Claim × S)) (x : First.Look.Place)
    (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData)
    (H : CoreLeft 𝔇 links pl z Rz k m sub L u ψ Ok nU p tmOf lenOf d N pb items o run x tlD set pp
      sT fd)
    (R : LeftRest 𝔇 links pl z Rz k m L u ψ Ok nU p x tlD sT) :
    CoreLeft 𝔇 links pl z Rz k m sub L u ψ Ok nU p tmOf lenOf d N pb items o run x tlD set pp sT
      fd :=
  { H with hLeft := hLeft_of_rest 𝔇 links pl z Rz k m L u ψ Ok nU p x tlD sT pb R }

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.hLeft_of_rest
#print axioms VerifiableInference.Desc.LinkJoin.coreLeft_lays
