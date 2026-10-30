-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/LinkRestAtSortC.lean: ON THE SECOND ROAD (the law's letter C at
`rowsLen`, Batch/Law/RowsLen.lean): BENEATH `LinkRestC` (LinkRestC.lean): THE CORE OF
WHAT IS LEFT AT A LINK, AT φ := phiAll u ψ AND π := pi8. Structures (cut by program out of
LinkRestAtSort.lean and LinkRestAtSort2.lean, which stand as they are) and theorems: assemblies and
monotony. EACH NAME IS THE ELDER NAME WITH "C" AT ITS END.

What turns against the elder texts, and nothing else: (1) where a field names the public sentence,
rowsFit p.rows pi8 has become rowsLen p.rows pi8 (fun q => lenRuns q (rlOf L tmOf lenOf)) · (2) BUT
NOT IN Aready, which is now AreadyS and keeps rowsFit alone on its left (at the place where it is
called the second half of C is not yet in hand) · (3) THE DEBTS ON THE RUNS ARE TAKEN ONCE, AT THE
BARE PROMISE (ArunsB): the form at the promise with C (the field Aruns) is drawn by monotony
(owesRuns_and), the field hrunsB by rlOf_runOk · (4) one new field: hk (the link's gatherer keeps
the map of weights, the plan's number and the count).

What is said. `quietOk_and`, `owesRuns_and`: monotony in the promise · `CoreRestC`,
`linkRestC_core`: LinkRestC from CoreRestC, ArunsB, Afull, hc, hψ, hord · `CoreRest2C`,
`coreRestC_of2`: CoreRestC from CoreRest2C and the fields that the sorts pay (ho, hu, ht, share,
numB, numQ, hk).

Limits. BOOK-KEEPING. CoreRest2C IS THE DEBT. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkRestC
import Johnson.Desc.First.Link.Law.RunsPaid
import Johnson.Desc.First.Link.Law.FullAtSort
import Johnson.Desc.First.Link.Law.LinkRestAtSort2

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

/-- QuietOk at the bare promise gives it at the promise with C. -/
theorem quietOk_and {α : Type} {φ : S → α} {Ok₀ : α × Option Pub9 → Prop} {Fu : S → Prop}
    (C : α × Option Pub9 → Prop) {h : S → Except String S}
    (H : QuietOk atS (O9 (K := Cb.Gl.E) φ Ok₀ Fu) (Fx9 φ Ok₀) h) :
    QuietOk atS (O9 (K := Cb.Gl.E) φ (fun q => Ok₀ q ∧ C q) Fu) (Fx9 φ (fun q => Ok₀ q ∧ C q))
      h := by
  intro q e a e₁ hf hg ha hs hr
  obtain ⟨a₁, h1, h2, h3, h4, h5⟩ := H q e a e₁ (fx9_bare hf) hg ha hs hr
  exact ⟨a₁, h1, h2, h3, h4, fx9_and h5 hf.1.2⟩

/-- **THE DEBTS ON THE RUNS AT THE BARE PROMISE GIVE THEM AT THE PROMISE WITH C.** -/
theorem owesRuns_and {α : Type} {sub : First.ModelPart} {L : Link S Claim} {φ : S → α}
    {Ok₀ : α × Option Pub9 → Prop} {Fu : S → Prop}
    {tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E)}
    {lenOf : ℕ × String → α × Option Pub9 → ℕ} (C : α × Option Pub9 → Prop)
    (A : OwesRuns sub L φ Ok₀ Fu tmOf lenOf) :
    OwesRuns sub L φ (fun q => Ok₀ q ∧ C q) Fu tmOf lenOf where
  hφ := A.hφ
  hpay := fun o ho run hr => runOk_and C (A.hpay o ho run hr)
  hpayd := A.hpayd
  hquiet := fun o ho run hr => quietOk_and C (A.hquiet o ho run hr)
  hquietd := A.hquietd

/-- **THE FIELDS OF LinkRestC THAT ARE NOT LAID IN HERE**, at φ := phiAll u ψ and π := pi8. -/
structure CoreRestC (sub : First.ModelPart) (L : Link S Claim) (u : HTailF2) (ψ : S → β)
    (Ok : Phi β × Option Pub9 → Prop) (nU : Array ℕ) (p : Where)
    (tmOf : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → Phi β × Option Pub9 → ℕ) (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (o : ℕ × String)
    (run : ℕ → S → Except String (List Claim × S)) (x : First.Look.Place)
    (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData) : Prop where
  Ahds : pb.ds = [k9Round p]
  Ahbk : pb.back = []
  Anumbers : OwesNumbers L (phiAll u ψ) (fun q => Ok q ∧ (rowsLen p.rows pi8 (fun q => lenRuns q
    (rlOf L tmOf lenOf))) q) tmOf lenOf d
  AreadyS : ∀ a, ((o0 a ∧ k9OnA a.1 = true) ∧ (rowsFit p.rows pi8) (fixed9 (phiAll u ψ) a.1)) → Ok
    (fixed9 (phiAll u ψ) a.1)
  Ahs1 : ∀ b, o1 b → (atS.get? b.1).isSome = true
  AhN : ∀ s, o2 s → ∀ a, atS.get? s.1 = some a → a.d.st.oracles.size ≤ N
  Ainside : ∀ s, o2 s → ∀ a, atS.get? s.1 = some a → ∀ born name r, reqArray a.L.check.rows.layout
    born name = some r → ∀ bl ∈ r.blocks, Inside r bl
  hbook₂ : ∀ m ∈ (moves₂ (α := Phi β) L).map (·.move), MoveBook m
  hitems : ∀ a w, o0 a → ∀ e ∈ items, ∃ (b : K9.Part) (R : K9.Read) (rs : List (TermedRun S (Phi β ×
    Option Pub9) GQ × (Phi β × Option Pub9 → Bound GQ → List GQ))), atS.get? a.1 = some b ∧ (∀ x ∈
    rs, x.1 ∈ rlOf L tmOf lenOf ∧ ∀ n y, (x.1.tm n (fixed9 (phiAll u ψ) a.1) y).map (·.2) = x.2
    (fixed9 (phiAll u ψ) a.1) y) ∧ (𝔇.Rd m).forms e.1 e.2 a.1 = some R ∧ K9.formsIn (𝔇.Rd m) own e.1
    e.2 a.1 = true ∧ ∀ f ∈ R.forms, f.value Reading.gl (worldOwn b R.late (dataQ own b (rdW w))) ∈
    rs.flatMap fun x => x.2 (fixed9 (phiAll u ψ) a.1) (dataQ own b (rdW w))
  ho : o ∈ L.order
  hAt : At L o run
  hu : Under run k8Run.2
  ht : tmOf o = fun n q y => numbered n (vals4 pi8 (ent4 pi8) q y) ++ tmRest pi8 q y
  HD : DigOK set x tlD 𝔇.sent 𝔇.l3.rad pp
  hLeft : ∀ a τ b' w₀ y, o0 a → pb.ior.red.out a τ = some b' → boundAt atS (fun a w => tabAt own
    (rdW w) a.1) cx a (pb.ext a τ w₀) y → ∀ (t e' : S) (b : K9.Part) (Fc : Fork) (tlX : HTailF2) (g
    : Forest.Heard) (front : ℕ) (e : S) (Fe : Fork) (tl tl' : HTailF2) (funs : Array HFun) (F1 :
    Fork) (c : List Claim), K9L.afterOf ((moves₂ (α := Phi β) L).map (·.move)) b'.1 = .ok t →
    atS.get? t = some b → k8Tests nU e' = .ok t → e'.fork? = some Fc → e'.tl? = some tlX → tlX.heard
    = some g → b.F = coefAll tlX g Fc → e.fork? = some Fe → e.tl? = some tl → e.funs? = some funs →
    blank u tl = blank u tlX → tl.heard = some g → equations (Fe.nClaim + front) tl funs Fe = .ok
    (tl', F1, c) → Fx9 (phiAll u ψ) (fun q => Ok q ∧ (rowsLen p.rows pi8 (fun q => lenRuns q (rlOf
      L tmOf lenOf))) q) (fixed9 (phiAll u ψ)
    a.1) e → Fx9 (phiAll u ψ) (fun q => Ok q ∧ (rowsLen p.rows pi8 (fun q => lenRuns q (rlOf L tmOf
      lenOf))) q) (fixed9 (phiAll u ψ) a.1) t →
    laterK atS (O9 (K := GE8) (phiAll u ψ) (fun q => Ok q ∧ (rowsLen p.rows pi8 (fun q => lenRuns q
      (rlOf L tmOf lenOf))) q) (FullAt nU))
    ((e.putTl tl').putFork F1) t → DigitsLeft x tlD 𝔇.sent 𝔇.l3.rad sT 𝔇.l3.arr (pb.ext a τ w₀) g tl
    c b.L y
  share : LinkShare L p
  numB : ∀ mv ∈ ([.add (claimsInBy L.each L.hear L.order)] : List (Move S)), MoveNum u mv
  numQ : ∀ mv ∈ ([.quiet L.runBehind] : List (Move S)), MoveNum u mv
  hdig : digAt X m = some (x, tlD)
  hruns : ∀ kk r, Item.forms m kk r ∈ formsOf sub m → ∀ p ∈ 𝔇.runs m kk r, p ∈ items
  inSeg : ∀ a, onK k a → ∀ x, segAt? a.1 = some x → InsideAt 𝔇.cs 𝔇.ms own x
  inRun : ∀ b, onK (k + 1) b → ∀ s' a, L.runBehind b.1 = .ok s' → atS.get? s' = some a → InsideAt
    𝔇.cs 𝔇.ms own a
  inTot : ∀ b, onK (k + 1 + 1) b → ∀ a, atS.get? b.1 = some a → InsideAt 𝔇.cs 𝔇.ms own a
  hmem : membersThereB fd 𝔇.ms own (𝔇.N.msgsAt pl[k + 1 + 1 + 1]?) = true
  hN : fd.M.length ≤ N
  tot : ∀ a, onK (k + 1 + 1) a → K9.totalIn own a.1 = true
  mh : MeantHead 𝔇
  notIx : ∀ a, onK (k + 1 + 1) a → OwnNotIndex a.1
  hk : KeepsKap atS (claimsInBy L.each L.hear L.order)

/-- **LinkRestC FROM CoreRestC.** -/
theorem linkRestC_core (sub : First.ModelPart) (L : Link S Claim) (u : HTailF2) (ψ : S → β)
    (Ok : Phi β × Option Pub9 → Prop) (nU : Array ℕ) (p : Where)
    (tmOf : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → Phi β × Option Pub9 → ℕ) (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (o : ℕ × String)
    (run : ℕ → S → Except String (List Claim × S)) (x : First.Look.Place)
    (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData) (pw : Where) (b₃ :
      Block S Claim)
    (pq pe : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT)) (ft : ℕ)
    (bs : List (Block S Claim)) (st0 : P → S) (reqW : P → Array UInt32)
    (hc : ∀ q, Ok q → OkCore nU tlD q) (hψ : Rests u ψ)
    (hord : L.order = First.orderOf sub)
    (ArunsB : OwesRuns sub L (phiAll u ψ) Ok (FullAt nU) tmOf lenOf)
    (Afull : OwesFull L (FullAt nU) tmOf lenOf)
    (H : CoreRestC 𝔇 links pl z Rz k m sub L u ψ Ok nU p tmOf lenOf d N pb items o run x tlD set pp
      sT fd) :
    LinkRestC 𝔇 links pl z Rz k m (Phi β) sub L (phiAll u ψ) Ok nU p pw tmOf lenOf d N b₃ pb pq pe
      items u pi8 o run x tlD set pp sT ft bs st0 fd reqW where
  Ahds := H.Ahds
  Ahbk := H.Ahbk
  Aruns := owesRuns_and _ ArunsB
  Anumbers := H.Anumbers
  Afull := Afull
  Ahs1 := H.Ahs1
  AhN := H.AhN
  Ainside := H.Ainside
  AreadyS := H.AreadyS
  hrunsB := rlOf_runOk Reading.gl atS _ _ L tmOf lenOf fun o ho run hr =>
    ArunsB.hpay o (hord ▸ ho) run hr
  hk := H.hk
  hbook₂ := H.hbook₂
  hitems := H.hitems
  hπ := fun _ => rfl
  hkeep := fun s tl tl' F1 h hb => phi_k8_keep u ψ hψ s tl tl' F1 h hb
  hOk4 := core_hOk4 hc _
  ho := H.ho
  hAt := H.hAt
  hu := H.hu
  ht := H.ht
  HD := H.HD
  okDig := core_okDig hc _
  okEnts := core_okEnts hc _
  hLeft := H.hLeft
  share := H.share
  numB := H.numB
  numQ := H.numQ
  hdig := H.hdig
  hruns := H.hruns
  inSeg := H.inSeg
  inRun := H.inRun
  inTot := H.inTot
  hmem := H.hmem
  hN := H.hN
  tot := H.tot
  mh := H.mh
  notIx := H.notIx

/-- **THE FIELDS OF LinkRestC THAT ARE STILL NOT LAID IN.** -/
structure CoreRest2C (sub : First.ModelPart) (L : Link S Claim) (u : HTailF2) (ψ : S → β)
    (Ok : Phi β × Option Pub9 → Prop) (nU : Array ℕ) (p : Where)
    (tmOf : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → Phi β × Option Pub9 → ℕ) (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (o : ℕ × String)
    (run : ℕ → S → Except String (List Claim × S)) (x : First.Look.Place)
    (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData) : Prop where
  Ahds : pb.ds = [k9Round p]
  Ahbk : pb.back = []
  Anumbers : OwesNumbers L (phiAll u ψ) (fun q => Ok q ∧ (rowsLen p.rows pi8 (fun q => lenRuns q
    (rlOf L tmOf lenOf))) q) tmOf lenOf d
  AreadyS : ∀ a, ((o0 a ∧ k9OnA a.1 = true) ∧ (rowsFit p.rows pi8) (fixed9 (phiAll u ψ) a.1)) → Ok
    (fixed9 (phiAll u ψ) a.1)
  Ahs1 : ∀ b, o1 b → (atS.get? b.1).isSome = true
  AhN : ∀ s, o2 s → ∀ a, atS.get? s.1 = some a → a.d.st.oracles.size ≤ N
  Ainside : ∀ s, o2 s → ∀ a, atS.get? s.1 = some a → ∀ born name r, reqArray a.L.check.rows.layout
    born name = some r → ∀ bl ∈ r.blocks, Inside r bl
  hbook₂ : ∀ m ∈ (moves₂ (α := Phi β) L).map (·.move), MoveBook m
  hitems : ∀ a w, o0 a → ∀ e ∈ items, ∃ (b : K9.Part) (R : K9.Read) (rs : List (TermedRun S (Phi β ×
    Option Pub9) GQ × (Phi β × Option Pub9 → Bound GQ → List GQ))), atS.get? a.1 = some b ∧ (∀ x ∈
    rs, x.1 ∈ rlOf L tmOf lenOf ∧ ∀ n y, (x.1.tm n (fixed9 (phiAll u ψ) a.1) y).map (·.2) = x.2
    (fixed9 (phiAll u ψ) a.1) y) ∧ (𝔇.Rd m).forms e.1 e.2 a.1 = some R ∧ K9.formsIn (𝔇.Rd m) own e.1
    e.2 a.1 = true ∧ ∀ f ∈ R.forms, f.value Reading.gl (worldOwn b R.late (dataQ own b (rdW w))) ∈
    rs.flatMap fun x => x.2 (fixed9 (phiAll u ψ) a.1) (dataQ own b (rdW w))
  hAt : At L o run
  HD : DigOK set x tlD 𝔇.sent 𝔇.l3.rad pp
  hLeft : ∀ a τ b' w₀ y, o0 a → pb.ior.red.out a τ = some b' → boundAt atS (fun a w => tabAt own
    (rdW w) a.1) cx a (pb.ext a τ w₀) y → ∀ (t e' : S) (b : K9.Part) (Fc : Fork) (tlX : HTailF2) (g
    : Forest.Heard) (front : ℕ) (e : S) (Fe : Fork) (tl tl' : HTailF2) (funs : Array HFun) (F1 :
    Fork) (c : List Claim), K9L.afterOf ((moves₂ (α := Phi β) L).map (·.move)) b'.1 = .ok t →
    atS.get? t = some b → k8Tests nU e' = .ok t → e'.fork? = some Fc → e'.tl? = some tlX → tlX.heard
    = some g → b.F = coefAll tlX g Fc → e.fork? = some Fe → e.tl? = some tl → e.funs? = some funs →
    blank u tl = blank u tlX → tl.heard = some g → equations (Fe.nClaim + front) tl funs Fe = .ok
    (tl', F1, c) → Fx9 (phiAll u ψ) (fun q => Ok q ∧ (rowsLen p.rows pi8 (fun q => lenRuns q (rlOf
      L tmOf lenOf))) q) (fixed9 (phiAll u ψ)
    a.1) e → Fx9 (phiAll u ψ) (fun q => Ok q ∧ (rowsLen p.rows pi8 (fun q => lenRuns q (rlOf L tmOf
      lenOf))) q) (fixed9 (phiAll u ψ) a.1) t →
    laterK atS (O9 (K := GE8) (phiAll u ψ) (fun q => Ok q ∧ (rowsLen p.rows pi8 (fun q => lenRuns q
      (rlOf L tmOf lenOf))) q) (FullAt nU))
    ((e.putTl tl').putFork F1) t → DigitsLeft x tlD 𝔇.sent 𝔇.l3.rad sT 𝔇.l3.arr (pb.ext a τ w₀) g tl
    c b.L y
  hdig : digAt X m = some (x, tlD)
  hruns : ∀ kk r, Item.forms m kk r ∈ formsOf sub m → ∀ p ∈ 𝔇.runs m kk r, p ∈ items
  inSeg : ∀ a, onK k a → ∀ x, segAt? a.1 = some x → InsideAt 𝔇.cs 𝔇.ms own x
  inRun : ∀ b, onK (k + 1) b → ∀ s' a, L.runBehind b.1 = .ok s' → atS.get? s' = some a → InsideAt
    𝔇.cs 𝔇.ms own a
  inTot : ∀ b, onK (k + 1 + 1) b → ∀ a, atS.get? b.1 = some a → InsideAt 𝔇.cs 𝔇.ms own a
  hmem : membersThereB fd 𝔇.ms own (𝔇.N.msgsAt pl[k + 1 + 1 + 1]?) = true
  hN : fd.M.length ≤ N
  tot : ∀ a, onK (k + 1 + 1) a → K9.totalIn own a.1 = true
  mh : MeantHead 𝔇
  notIx : ∀ a, onK (k + 1 + 1) a → OwnNotIndex a.1

/-- CoreRestC from CoreRest2C and the seven. -/
theorem coreRestC_of2 (sub : First.ModelPart) (L : Link S Claim) (u : HTailF2) (ψ : S → β)
    (Ok : Phi β × Option Pub9 → Prop) (nU : Array ℕ) (p : Where)
    (tmOf : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → Phi β × Option Pub9 → ℕ) (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (o : ℕ × String)
    (run : ℕ → S → Except String (List Claim × S)) (x : First.Look.Place)
    (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData)
    (ho : o ∈ L.order) (hu : Under run k8Run.2)
    (ht : tmOf o = fun n q y => numbered n (vals4 pi8 (ent4 pi8) q y) ++ tmRest pi8 q y)
    (share : LinkShare L p)
    (numB : ∀ mv ∈ ([.add (claimsInBy L.each L.hear L.order)] : List (Move S)), MoveNum u mv)
    (numQ : ∀ mv ∈ ([.quiet L.runBehind] : List (Move S)), MoveNum u mv)
    (hk : KeepsKap atS (claimsInBy L.each L.hear L.order))
    (H : CoreRest2C 𝔇 links pl z Rz k m sub L u ψ Ok nU p tmOf lenOf d N pb items o run x tlD set pp
      sT fd) :
    CoreRestC 𝔇 links pl z Rz k m sub L u ψ Ok nU p tmOf lenOf d N pb items o run x tlD set pp sT
      fd where
  Ahds := H.Ahds
  Ahbk := H.Ahbk
  Anumbers := H.Anumbers
  AreadyS := H.AreadyS
  Ahs1 := H.Ahs1
  AhN := H.AhN
  Ainside := H.Ainside
  hbook₂ := H.hbook₂
  hitems := H.hitems
  ho := ho
  hAt := H.hAt
  hu := hu
  ht := ht
  HD := H.HD
  hLeft := H.hLeft
  share := share
  numB := numB
  numQ := numQ
  hdig := H.hdig
  hruns := H.hruns
  inSeg := H.inSeg
  inRun := H.inRun
  inTot := H.inTot
  hmem := H.hmem
  hN := H.hN
  tot := H.tot
  mh := H.mh
  notIx := H.notIx
  hk := hk

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.quietOk_and
#print axioms VerifiableInference.Desc.LinkJoin.owesRuns_and
#print axioms VerifiableInference.Desc.LinkJoin.linkRestC_core
#print axioms VerifiableInference.Desc.LinkJoin.coreRestC_of2
