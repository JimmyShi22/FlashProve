-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/LinkRestAtSort.lean: WHAT IS LEFT OF A LINK's LAW (`LinkRest`,
LinkRest.lean: 35 fields) AT THE CHOSEN LETTERS OF EACH SORT OF LINK, FROM ONE NAMED STRUCTURE A
SORT. SEVEN OF THE 35 ARE LAID IN. Structures of sentences, and theorems: assemblies.

Why. Beneath K9's condition the law's letters (α, φ, Ok, tmOf, lenOf, π ..) stand under one "there
are" a link. Several payers hold at chosen letters, a sort at a time. Here the letters are
chosen: α := Phi β · φ := phiAll u ψ · π := pi8 · Ok := the sort's named Ok (OkOne.lean) · tmOf |
lenOf := the sort's (tmL | tmA | tmH at entUnit; lenL | lenA | lenH).

What is said.
  `CoreRest`: the 28 fields of LinkRest that are not laid in here, at φ := phiAll u ψ and π := pi8:
    THEIR TEXTS ARE CUT BY PROGRAM OUT OF LinkRest's OWN.
  `linkRest_core`: LinkRest from CoreRest, "Ok holds the core" (hc), Rests u ψ, and the lists
    "runs" and "full": hπ by definition · hkeep by phi_k8_keep · hOk4, okDig, okEnts: the named
    Ok's clauses read back (NO PAYMENTS).
  `LayersRest`, `AttRest`, `HeadRest`: what is then left at a sort: seg · what is left of the
    sort's Take (ties, hψ, hrd | hkap, h4, k3, k3d: RunsPaid.lean) · k3g (the lookup's runs keep
    "good") · core.
  `linkRest_layers`, `linkRest_att`, `linkRest_head`: **LinkRest at the sort's letters**: Aruns by
    the sort's Take (RunsPaid.lean), Afull by full_layers | full_attention | full_head
    (FullAtSort.lean).

Limits. BOOK-KEEPING. NOTHING IS SHOWN OF ANY STATE OR RUN. 28 fields of 35 stay, Aready (the named
Ok at what is fixed in front of the batching: THE ONE DEBT ON WHICH THE CLAUSES READ BACK REST)
among them. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkRest
import Johnson.Desc.First.Link.Law.RunsPaid
import Johnson.Desc.First.Link.Law.FullAtSort

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

/-- **THE FIELDS OF LinkRest THAT ARE NOT LAID IN HERE**, at φ := phiAll u ψ and π := pi8. -/
structure CoreRest (sub : First.ModelPart) (L : Link S Claim) (u : HTailF2) (ψ : S → β)
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
  Anumbers : OwesNumbers L (phiAll u ψ) (fun q => Ok q ∧ (rowsFit p.rows pi8) q) tmOf lenOf d
  Aready : ∀ a, ((o0 a ∧ k9OnA a.1 = true) ∧ (rowsFit p.rows pi8) (fixed9 (phiAll u ψ) a.1)) → Ok
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
    (tl', F1, c) → Fx9 (phiAll u ψ) (fun q => Ok q ∧ (rowsFit p.rows pi8) q) (fixed9 (phiAll u ψ)
    a.1) e → Fx9 (phiAll u ψ) (fun q => Ok q ∧ (rowsFit p.rows pi8) q) (fixed9 (phiAll u ψ) a.1) t →
    laterK atS (O9 (K := GE8) (phiAll u ψ) (fun q => Ok q ∧ (rowsFit p.rows pi8) q) (FullAt nU))
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

/-- **LinkRest FROM CoreRest.** -/
theorem linkRest_core (sub : First.ModelPart) (L : Link S Claim) (u : HTailF2) (ψ : S → β)
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
    (Aruns : OwesRuns sub L (phiAll u ψ) (fun q => Ok q ∧ (rowsFit p.rows pi8) q) (FullAt nU) tmOf
      lenOf)
    (Afull : OwesFull L (FullAt nU) tmOf lenOf)
    (H : CoreRest 𝔇 links pl z Rz k m sub L u ψ Ok nU p tmOf lenOf d N pb items o run x tlD set pp
      sT fd) :
    LinkRest 𝔇 links pl z Rz k m (Phi β) sub L (phiAll u ψ) Ok nU p pw tmOf lenOf d N b₃ pb pq pe
      items u pi8 o run x tlD set pp sT ft bs st0 fd reqW where
  Ahds := H.Ahds
  Ahbk := H.Ahbk
  Aruns := Aruns
  Anumbers := H.Anumbers
  Afull := Afull
  Aready := H.Aready
  Ahs1 := H.Ahs1
  AhN := H.AhN
  Ainside := H.Ainside
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

/-- **WHAT IS LEFT AT A LAYERS' LINK**, at the sort's chosen letters. -/
structure LayersRest (p4 : OnBytes.Desc.First.K4.Par)
    (tm4 : ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (l3 : ℕ × String → Phi β × Option Pub9 → ℕ)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β)
    (nU : Array ℕ) (p : Where)
    (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (o : ℕ × String)
    (run : ℕ → S → Except String (List Claim × S)) (x : First.Look.Place)
    (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData) : Prop where
  seg : SegAt m .layers L
  ties : LayersTies L p4 nU
  hψ : Rests u ψ
  h4 : ∀ q front e a c e₁, Fx9 (phiAll u ψ) (fun q => OkLayers p4 nU tlD q ∧ (rowsFit p.rows pi8) q)
    q e → good9 e → atS.get? e = some a → k8Run.2 front e = .ok (c, e₁) → ∀ t y, laterK atS (O9 (K
    := GE8) (phiAll u ψ) (fun q => OkLayers p4 nU tlD q ∧ (rowsFit p.rows pi8) q) (FullAt nU)) e₁ t
    → (FullAt nU) t → wsumK atS Reading.gl t y (Reading.gl.val a.F.theta) (a.F.nClaim + front)
    (c.take 4) = termsAt GE8 (tm4 (a.F.nClaim + front) q y) (Reading.gl.val a.F.theta)
  k3 : ∀ o ∈ [(1, "objects"), (6, "objects")], ∀ run, At L o run → RunOk Reading.gl atS (O9 (phiAll
    u ψ) (fun q => OkLayers p4 nU tlD q ∧ (rowsFit p.rows pi8) q) (FullAt nU)) (Fx9 (phiAll u ψ)
    (fun q => OkLayers p4 nU tlD q ∧ (rowsFit p.rows pi8) q)) run (t3 o) (l3 o)
  k3d : ∀ o ∈ [(1, "objects"), (6, "objects")], ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c,
    e₁) → KeepsDoor atS e e₁
  k3g : ∀ o ∈ [(1, "objects"), (6, "objects")], ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c,
    e₁) → good9 e → good9 e₁
  core : CoreRest 𝔇 links pl z Rz k m .layers L u ψ (OkLayers p4 nU tlD) nU p
    (tmL p4 entUnit tm4 t3) (lenL p4 l3) d N pb items o run x tlD set pp sT fd

/-- **LinkRest AT A LAYERS' LINK.** -/
theorem linkRest_layers (p4 : OnBytes.Desc.First.K4.Par)
    (tm4 : ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (l3 : ℕ × String → Phi β × Option Pub9 → ℕ)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β)
    (nU : Array ℕ) (p : Where)
    (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (o : ℕ × String)
    (run : ℕ → S → Except String (List Claim × S)) (x : First.Look.Place)
    (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData) (pw : Where) (b₃ :
      Block S Claim)
    (pq pe : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT)) (ft : ℕ)
    (bs : List (Block S Claim)) (st0 : P → S) (reqW : P → Array UInt32)
    (R : LayersRest 𝔇 links pl z Rz k m p4 tm4 t3 l3 L u ψ nU p d N pb items o run x tlD set pp
      sT fd) :
    LinkRest 𝔇 links pl z Rz k m (Phi β) .layers L (phiAll u ψ) (OkLayers p4 nU tlD) nU p pw
      (tmL p4 entUnit tm4 t3) (lenL p4 l3) d N b₃ pb pq pe items u pi8 o run x tlD set pp sT ft bs
      st0 fd reqW :=
  have A := layersTake_of (Ok := (fun q => OkLayers p4 nU tlD q ∧ (rowsFit p.rows pi8) q))
    (tlD := tlD) (fun _ h => h.1) R.ties R.hψ R.h4 R.k3 R.k3d
  linkRest_core 𝔇 links pl z Rz k m .layers L u ψ _ nU p _ _ d N pb items o run x tlD set pp sT fd
    pw
    b₃ pq pe ft bs st0 reqW (fun _ h => h.core) R.hψ (runs_layers A) (full_layers R.seg A R.k3g)
      R.core

/-- **WHAT IS LEFT AT AN ATTENTION LINK**, at the sort's chosen letters. -/
structure AttRest (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)) (c : First.Att.P.ParC)
    (tm4 : ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (l3 : ℕ × String → Phi β × Option Pub9 → ℕ)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β)
    (nU : Array ℕ) (p : Where)
    (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (o : ℕ × String)
    (run : ℕ → S → Except String (List Claim × S)) (x : First.Look.Place)
    (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData) : Prop where
  seg : SegAt m .attention L
  ties : AttTies L c nU
  hψ : Rests u ψ
  hrd : ∀ e, rd (phiAll u ψ e) = psiAtt e
  h4 : ∀ q front e a c' e₁, Fx9 (phiAll u ψ) (fun q => OkAtt rd c nU tlD q ∧ (rowsFit p.rows pi8) q)
    q e → good9 e → atS.get? e = some a → k8Run.2 front e = .ok (c', e₁) → ∀ t y, laterK atS (O9 (K
    := GE8) (phiAll u ψ) (fun q => OkAtt rd c nU tlD q ∧ (rowsFit p.rows pi8) q) (FullAt nU)) e₁ t →
    (FullAt nU) t → wsumK atS Reading.gl t y (Reading.gl.val a.F.theta) (a.F.nClaim + front)
    (c'.take 4) = termsAt GE8 (tm4 (a.F.nClaim + front) q y) (Reading.gl.val a.F.theta)
  k3 : ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")], ∀ run, At L o run → RunOk
    Reading.gl atS (O9 (phiAll u ψ) (fun q => OkAtt rd c nU tlD q ∧ (rowsFit p.rows pi8) q) (FullAt
    nU)) (Fx9 (phiAll u ψ) (fun q => OkAtt rd c nU tlD q ∧ (rowsFit p.rows pi8) q)) run (t3 o) (l3
    o)
  k3d : ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")], ∀ run, At L o run → ∀ n
    e c' e₁, run n e = .ok (c', e₁) → KeepsDoor atS e e₁
  k3g : ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")], ∀ run, At L o run → ∀ n
    e c e₁, run n e = .ok (c, e₁) → good9 e → good9 e₁
  core : CoreRest 𝔇 links pl z Rz k m .attention L u ψ (OkAtt rd c nU tlD) nU p
    (tmA rd c entUnit tm4 t3) (lenA rd c l3) d N pb items o run x tlD set pp sT fd

/-- **LinkRest AT AN ATTENTION LINK.** -/
theorem linkRest_att (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard))
    (c : First.Att.P.ParC)
    (tm4 : ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (l3 : ℕ × String → Phi β × Option Pub9 → ℕ)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β)
    (nU : Array ℕ) (p : Where)
    (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (o : ℕ × String)
    (run : ℕ → S → Except String (List Claim × S)) (x : First.Look.Place)
    (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData) (pw : Where) (b₃ :
      Block S Claim)
    (pq pe : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT)) (ft : ℕ)
    (bs : List (Block S Claim)) (st0 : P → S) (reqW : P → Array UInt32)
    (R : AttRest 𝔇 links pl z Rz k m rd c tm4 t3 l3 L u ψ nU p d N pb items o run x tlD set pp
      sT fd) :
    LinkRest 𝔇 links pl z Rz k m (Phi β) .attention L (phiAll u ψ) (OkAtt rd c nU tlD) nU p pw
      (tmA rd c entUnit tm4 t3) (lenA rd c l3) d N b₃ pb pq pe items u pi8 o run x tlD set pp sT ft
        bs
      st0 fd reqW :=
  have A := attTake_of (Ok := (fun q => OkAtt rd c nU tlD q ∧ (rowsFit p.rows pi8) q))
    (tlD := tlD) (fun _ h => h.1) R.ties R.hψ R.hrd R.h4 R.k3 R.k3d
  linkRest_core 𝔇 links pl z Rz k m .attention L u ψ _ nU p _ _ d N pb items o run x tlD set pp sT
    fd pw
    b₃ pq pe ft bs st0 reqW (fun _ h => h.core) R.hψ (runs_attention A) (full_attention R.seg A
      R.k3g) R.core

/-- **WHAT IS LEFT AT THE HEAD's LINK**, at the sort's chosen letters. -/
structure HeadRest (hS : OnBytes.Model.Head.Shape) (iU3 l' piece : ℕ) (p6 : Kinds.Head.Par)
    (kap : Phi β → Option Kinds.Head.Law.Seen) (tm4 : ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E →
      List (ℕ × Cb.Gl.E))
    (t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (l3 : ℕ × String → Phi β × Option Pub9 → ℕ)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β)
    (nU : Array ℕ) (p : Where)
    (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (o : ℕ × String)
    (run : ℕ → S → Except String (List Claim × S)) (x : First.Look.Place)
    (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData) : Prop where
  seg : SegAt m .head L
  ties : HeadTies L hS iU3 l' piece p6 nU
  hψ : Rests u ψ
  hkap : ∀ e, kap (phiAll u ψ e) = Kinds.Head.Law.seenOf e
  h4 : ∀ q front e a c e₁, Fx9 (phiAll u ψ) (fun q => OkHead hS iU3 p6 kap nU tlD q ∧ (rowsFit
    p.rows pi8) q) q e → good9 e → atS.get? e = some a → k8Run.2 front e = .ok (c, e₁) → ∀ t y,
    laterK atS (O9 (K := GE8) (phiAll u ψ) (fun q => OkHead hS iU3 p6 kap nU tlD q ∧ (rowsFit p.rows
    pi8) q) (FullAt nU)) e₁ t → (FullAt nU) t → wsumK atS Reading.gl t y (Reading.gl.val a.F.theta)
    (a.F.nClaim + front) (c.take 4) = termsAt GE8 (tm4 (a.F.nClaim + front) q y) (Reading.gl.val
    a.F.theta)
  k3 : ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run → RunOk Reading.gl
    atS (O9 (phiAll u ψ) (fun q => OkHead hS iU3 p6 kap nU tlD q ∧ (rowsFit p.rows pi8) q) (FullAt
    nU)) (Fx9 (phiAll u ψ) (fun q => OkHead hS iU3 p6 kap nU tlD q ∧ (rowsFit p.rows pi8) q)) run
    (t3 o) (l3 o)
  k3d : ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run → ∀ n e c e₁, run n
    e = .ok (c, e₁) → KeepsDoor atS e e₁
  k3g : ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run → ∀ n e c e₁, run n
    e = .ok (c, e₁) → good9 e → good9 e₁
  core : CoreRest 𝔇 links pl z Rz k m .head L u ψ (OkHead hS iU3 p6 kap nU tlD) nU p
    (tmH hS iU3 p6 kap entUnit tm4 t3) (lenH hS iU3 p6 kap l3) d N pb items o run x tlD set pp sT fd

/-- **LinkRest AT THE HEAD's LINK.** -/
theorem linkRest_head (hS : OnBytes.Model.Head.Shape) (iU3 l' piece : ℕ) (p6 : Kinds.Head.Par)
    (kap : Phi β → Option Kinds.Head.Law.Seen) (tm4 : ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E →
      List (ℕ × Cb.Gl.E))
    (t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (l3 : ℕ × String → Phi β × Option Pub9 → ℕ)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β)
    (nU : Array ℕ) (p : Where)
    (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (o : ℕ × String)
    (run : ℕ → S → Except String (List Claim × S)) (x : First.Look.Place)
    (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData) (pw : Where) (b₃ :
      Block S Claim)
    (pq pe : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT)) (ft : ℕ)
    (bs : List (Block S Claim)) (st0 : P → S) (reqW : P → Array UInt32)
    (R : HeadRest 𝔇 links pl z Rz k m hS iU3 l' piece p6 kap tm4 t3 l3 L u ψ nU p d N pb items o
      run x tlD set pp
      sT fd) :
    LinkRest 𝔇 links pl z Rz k m (Phi β) .head L (phiAll u ψ) (OkHead hS iU3 p6 kap nU tlD) nU p pw
      (tmH hS iU3 p6 kap entUnit tm4 t3) (lenH hS iU3 p6 kap l3) d N b₃ pb pq pe items u pi8 o run
        x tlD set pp sT ft bs
      st0 fd reqW :=
  have A := headTake_of (Ok := (fun q => OkHead hS iU3 p6 kap nU tlD q ∧ (rowsFit p.rows pi8) q))
    (tlD := tlD) (fun _ h => h.1) R.ties R.hψ R.hkap R.h4 R.k3 R.k3d
  linkRest_core 𝔇 links pl z Rz k m .head L u ψ _ nU p _ _ d N pb items o run x tlD set pp sT fd pw
    b₃ pq pe ft bs st0 reqW (fun _ h => h.core) R.hψ (runs_head A) (full_head R.seg A R.k3g) R.core

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.linkRest_core
#print axioms VerifiableInference.Desc.LinkJoin.linkRest_layers
#print axioms VerifiableInference.Desc.LinkJoin.linkRest_att
#print axioms VerifiableInference.Desc.LinkJoin.linkRest_head
