-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/CoreLeftC.lean: ON THE SECOND ROAD: BENEATH THE LIST OF THE
FIELDS OF `LinkRestC` THAT NO CHOICE OF THE LETTERS LAYS IN (`CoreRest2C`, LinkRestAtSortC.lean):
THE SAME LIST LESS THE FIELDS FOR WHICH A PAYER LIES AT THE CLOSED CONSTANT (a payer may leave
another debt in a field's place: the caller's head says which): Ahds, Ahbk, Ahs1, AhN, Ainside,
hbook₂, hAt, HD, hdig, hruns, hmem, hN, tot, mh, notIx. A structure (cut by program out of
`CoreRest2C`'s own text) and one theorem.

What is said.
  `CoreLeftC …`: the 7 fields that are left, each to the letter as in `CoreRest2C`.
    `coreRest2C_of_left`: **`CoreRest2C` from `CoreLeftC` and the 15 paid fields** (premises of the
    theorem, each in its field's own type).

Limits. BOOK-KEEPING. `CoreLeftC` IS THE DEBT. The fields bear no comments here: what each says is
said over its like in `LinkListC`. The count of fields is no measure. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkRestAtSortC

set_option autoImplicit false
set_option relaxedAutoImplicit false

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

/-- **WHAT NO CHOICE OF THE LETTERS LAYS IN, LESS WHAT HAS A PAYER AT THE CLOSED CONSTANT.** -/
structure CoreLeftC (sub : First.ModelPart) (L : Link S Claim) (u : HTailF2) (ψ : S → β)
    (Ok : Phi β × Option Pub9 → Prop) (nU : Array ℕ) (p : Where)
    (tmOf : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → Phi β × Option Pub9 → ℕ) (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (o : ℕ × String)
    (run : ℕ → S → Except String (List Claim × S)) (x : First.Look.Place)
    (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData) : Prop where
  Anumbers : OwesNumbers L (phiAll u ψ) (fun q => Ok q ∧ (rowsLen p.rows pi8 (fun q => lenRuns q
    (rlOf L tmOf lenOf))) q) tmOf lenOf d
  AreadyS : ∀ a, ((o0 a ∧ k9OnA a.1 = true) ∧ (rowsFit p.rows pi8) (fixed9 (phiAll u ψ) a.1)) → Ok
    (fixed9 (phiAll u ψ) a.1)
  hitems : ∀ a w, o0 a → ∀ e ∈ items, ∃ (b : K9.Part) (R : K9.Read) (rs : List (TermedRun S (Phi β ×
    Option Pub9) GQ × (Phi β × Option Pub9 → Bound GQ → List GQ))), atS.get? a.1 = some b ∧ (∀ x ∈
    rs, x.1 ∈ rlOf L tmOf lenOf ∧ ∀ n y, (x.1.tm n (fixed9 (phiAll u ψ) a.1) y).map (·.2) = x.2
    (fixed9 (phiAll u ψ) a.1) y) ∧ (𝔇.Rd m).forms e.1 e.2 a.1 = some R ∧ K9.formsIn (𝔇.Rd m) own
    e.1 e.2 a.1 = true ∧ ∀ f ∈ R.forms, f.value Reading.gl (worldOwn b R.late (dataQ own b (rdW w)))
    ∈ rs.flatMap fun x => x.2 (fixed9 (phiAll u ψ) a.1) (dataQ own b (rdW w))
  hLeft : ∀ a τ b' w₀ y, o0 a → pb.ior.red.out a τ = some b' → boundAt atS (fun a w => tabAt own
    (rdW w) a.1) cx a (pb.ext a τ w₀) y → ∀ (t e' : S) (b : K9.Part) (Fc : Fork) (tlX : HTailF2) (g
    : Forest.Heard) (front : ℕ) (e : S) (Fe : Fork) (tl tl' : HTailF2) (funs : Array HFun) (F1 :
    Fork) (c : List Claim), K9L.afterOf ((moves₂ (α := Phi β) L).map (·.move)) b'.1 = .ok t →
    atS.get? t = some b → k8Tests nU e' = .ok t → e'.fork? = some Fc → e'.tl? = some tlX → tlX.heard
    = some g → b.F = coefAll tlX g Fc → e.fork? = some Fe → e.tl? = some tl → e.funs? = some funs →
    blank u tl = blank u tlX → tl.heard = some g → equations (Fe.nClaim + front) tl funs Fe = .ok
    (tl', F1, c) → Fx9 (phiAll u ψ) (fun q => Ok q ∧ (rowsLen p.rows pi8 (fun q => lenRuns q (rlOf L
    tmOf lenOf))) q) (fixed9 (phiAll u ψ) a.1) e → Fx9 (phiAll u ψ) (fun q => Ok q ∧ (rowsLen p.rows
    pi8 (fun q => lenRuns q (rlOf L tmOf lenOf))) q) (fixed9 (phiAll u ψ) a.1) t → laterK atS (O9 (K
    := GE8) (phiAll u ψ) (fun q => Ok q ∧ (rowsLen p.rows pi8 (fun q => lenRuns q (rlOf L tmOf
    lenOf))) q) (FullAt nU)) ((e.putTl tl').putFork F1) t → DigitsLeft x tlD 𝔇.sent 𝔇.l3.rad sT
    𝔇.l3.arr (pb.ext a τ w₀) g tl c b.L y
  inSeg : ∀ a, onK k a → ∀ x, segAt? a.1 = some x → InsideAt 𝔇.cs 𝔇.ms own x
  inRun : ∀ b, onK (k + 1) b → ∀ s' a, L.runBehind b.1 = .ok s' → atS.get? s' = some a → InsideAt
    𝔇.cs 𝔇.ms own a
  inTot : ∀ b, onK (k + 1 + 1) b → ∀ a, atS.get? b.1 = some a → InsideAt 𝔇.cs 𝔇.ms own a

/-- **THE ELDER LIST FROM WHAT IS LEFT.** -/
theorem coreRest2C_of_left (sub : First.ModelPart) (L : Link S Claim) (u : HTailF2) (ψ : S → β)
    (Ok : Phi β × Option Pub9 → Prop) (nU : Array ℕ) (p : Where)
    (tmOf : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → Phi β × Option Pub9 → ℕ) (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (o : ℕ × String)
    (run : ℕ → S → Except String (List Claim × S)) (x : First.Look.Place)
    (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData)
    (Ahds : pb.ds = [k9Round p])
    (Ahbk : pb.back = [])
    (Ahs1 : ∀ b, o1 b → (atS.get? b.1).isSome = true)
    (AhN : ∀ s, o2 s → ∀ a, atS.get? s.1 = some a → a.d.st.oracles.size ≤ N)
    (Ainside : ∀ s, o2 s → ∀ a, atS.get? s.1 = some a → ∀ born name r, reqArray
      a.L.check.rows.layout born name = some r → ∀ bl ∈ r.blocks, Inside r bl)
    (hbook₂ : ∀ m ∈ (moves₂ (α := Phi β) L).map (·.move), MoveBook m)
    (hAt : At L o run)
    (HD : DigOK set x tlD 𝔇.sent 𝔇.l3.rad pp)
    (hdig : digAt X m = some (x, tlD))
    (hruns : ∀ kk r, Item.forms m kk r ∈ formsOf sub m → ∀ p ∈ 𝔇.runs m kk r, p ∈ items)
    (hmem : membersThereB fd 𝔇.ms own (𝔇.N.msgsAt pl[k + 1 + 1 + 1]?) = true)
    (hN : fd.M.length ≤ N)
    (tot : ∀ a, onK (k + 1 + 1) a → K9.totalIn own a.1 = true)
    (mh : MeantHead 𝔇)
    (notIx : ∀ a, onK (k + 1 + 1) a → OwnNotIndex a.1)
    (H : CoreLeftC 𝔇 links pl z Rz k m sub L u ψ Ok nU p tmOf lenOf d N pb items o run x tlD set pp
      sT fd) :
    CoreRest2C 𝔇 links pl z Rz k m sub L u ψ Ok nU p tmOf lenOf d N pb items o run x tlD set pp
      sT fd :=
  ⟨Ahds, Ahbk, H.Anumbers, H.AreadyS, Ahs1, AhN, Ainside, hbook₂, H.hitems, hAt, HD, H.hLeft, hdig,
    hruns, H.inSeg, H.inRun, H.inTot, hmem, hN, tot, mh, notIx⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.coreRest2C_of_left
