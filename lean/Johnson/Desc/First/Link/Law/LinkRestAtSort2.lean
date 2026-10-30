-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/LinkRestAtSort2.lean: WHAT IS LEFT OF A LINK's LAW (`LinkRest`,
LinkRest.lean: 35 fields) AT THE CHOSEN LETTERS OF EACH SORT OF LINK: A SECOND FORM, OVER THE FIRST
(LinkRestAtSort.lean, which stands as it is): SIX MORE FIELDS ARE LAID IN: 13 OF 35. Structures of
sentences, and theorems: assemblies.

Two more letters are chosen: o := the sort's entry of the smallness test's equations ((4,
"K8.equations"); at the head's link (5, "K8.equations")) · tm4 := tmFour: the four values numbered.

What is laid in, and from what.
  ho: the entry stands in the sort's order (by the segment's own order; decided).
  hu: the run there stands under the smallness test's run (the sort's tie tEq, at hAt).
  ht: the terms at that entry are the four numbered and the rest (by the sort's table of terms and
    the choice of tm4).
  share (`LinkShare`: six fields): hb₁ := drawB · rows (both stay premises) · stand:
    rel_layers | rel_attention | rel_head at the sort's Take, with k3p ("a yes of a lookup's run
    puts a ledger") · eqIn: the tie tEq · sizedLS, sized: run_layers | .. at rests_fork
    sizedLS_rests | sized_rests, with k3sL, k3s (the lookup's runs keep these two).
  numB, numQ: moveNum_layers | .. at the sort's Take, with k3f (the lookup's runs
    keep the numbers).

What is said. `tmFour` · `CoreRest2`: the 22 fields of LinkRest that are not laid in (TEXTS
CUT BY PROGRAM) · `coreRest_of2` · `LayersRest2`, `AttRest2`, `HeadRest2` · `linkRest_layers2`,
`linkRest_att2`, `linkRest_head2`: **LinkRest at the sort's letters.**

Limits. BOOK-KEEPING. NOTHING IS SHOWN OF ANY STATE OR RUN. THE LOOKUP's ENTRIES (2, 4 and 3 of
them) NOW BEAR SEVEN PREMISES EACH SORT: k3, k3d, k3g, k3f, k3p, k3s, k3sL: THE LOOKUPS' FILES' TO
SHOW. 22 fields of 35 stay, Aready among them. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkRestAtSort
import Johnson.Desc.First.Link.Law.NumRuns
import Johnson.Desc.First.Link.Law.LinkAtSort

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

/-- The four values of the smallness test's first four claims, numbered. -/
def tmFour (n : ℕ) (q : Phi β × Option Pub9) (y : Bound Cb.Gl.E) : List (ℕ × Cb.Gl.E) :=
  numbered n (vals4 pi8 (ent4 pi8) q y)

/-- **THE FIELDS OF LinkRest THAT ARE STILL NOT LAID IN.** -/
structure CoreRest2 (sub : First.ModelPart) (L : Link S Claim) (u : HTailF2) (ψ : S → β)
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
  hAt : At L o run
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

/-- CoreRest from CoreRest2 and the six. -/
theorem coreRest_of2 (sub : First.ModelPart) (L : Link S Claim) (u : HTailF2) (ψ : S → β)
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
    (H : CoreRest2 𝔇 links pl z Rz k m sub L u ψ Ok nU p tmOf lenOf d N pb items o run x tlD set pp
      sT fd) :
    CoreRest 𝔇 links pl z Rz k m sub L u ψ Ok nU p tmOf lenOf d N pb items o run x tlD set pp sT
      fd where
  Ahds := H.Ahds
  Ahbk := H.Ahbk
  Anumbers := H.Anumbers
  Aready := H.Aready
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

/-- **WHAT IS LEFT AT A LAYERS' LINK, SECOND FORM.** -/
structure LayersRest2 (p4 : OnBytes.Desc.First.K4.Par)
    (t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (l3 : ℕ × String → Phi β × Option Pub9 → ℕ)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β) (nU : Array ℕ) (p : Where) (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (run : ℕ → S → Except String (List Claim × S))
    (x : First.Look.Place) (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData) : Prop where
  seg : SegAt m .layers L
  ties : LayersTies L p4 nU
  hψ : Rests u ψ
  h4 : ∀ q front e a c e₁, Fx9 (phiAll u ψ) (fun q => OkLayers p4 nU tlD q ∧ (rowsFit p.rows pi8) q)
    q e → good9 e → atS.get? e = some a → k8Run.2 front e = .ok (c, e₁) → ∀ t y, laterK atS (O9 (K
    := GE8) (phiAll u ψ) (fun q => OkLayers p4 nU tlD q ∧ (rowsFit p.rows pi8) q) (FullAt nU)) e₁ t
    → (FullAt nU) t → wsumK atS Reading.gl t y (Reading.gl.val a.F.theta) (a.F.nClaim + front)
    (c.take 4) = termsAt GE8 (tmFour (a.F.nClaim + front) q y) (Reading.gl.val a.F.theta)
  k3 : ∀ o ∈ [(1, "objects"), (6, "objects")], ∀ run, At L o run → RunOk Reading.gl atS (O9 (phiAll
    u ψ) (fun q => OkLayers p4 nU tlD q ∧ (rowsFit p.rows pi8) q) (FullAt nU)) (Fx9 (phiAll u ψ)
    (fun q => OkLayers p4 nU tlD q ∧ (rowsFit p.rows pi8) q)) run (t3 o) (l3 o)
  k3d : ∀ o ∈ [(1, "objects"), (6, "objects")], ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c,
    e₁) → KeepsDoor atS e e₁
  k3g : ∀ o ∈ [(1, "objects"), (6, "objects")], ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c,
    e₁) → good9 e → good9 e₁
  k3f : ∀ o ∈ [(1, "objects"), (6, "objects")], ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c,
    e₁) → numOf u e₁ = numOf u e
  k3p : ∀ o ∈ [(1, "objects"), (6, "objects")], ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c,
    e₁) → ∃ G, e₁ = e.putFork G
  k3s : ∀ o ∈ [(1, "objects"), (6, "objects")], ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c,
    e₁) → HasFork Sized e → HasFork Sized e₁
  k3sL : ∀ o ∈ [(1, "objects"), (6, "objects")], ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c,
    e₁) → HasFork (fun F => Sized F ∧ F.LS.size = F.ns) e → HasFork (fun F => Sized F ∧ F.LS.size =
    F.ns) e₁
  drawB : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB
  rows : p.rows ≠ 0
  core : CoreRest2 𝔇 links pl z Rz k m .layers L u ψ (OkLayers p4 nU tlD) nU p
    (tmL p4 entUnit tmFour t3) (lenL p4 l3) d N pb items (4, "K8.equations") run x tlD set pp sT fd

/-- **LinkRest AT A LAYERS' LINK, FROM THE SECOND FORM's STRUCTURE.** -/
theorem linkRest_layers2 (p4 : OnBytes.Desc.First.K4.Par)
    (t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (l3 : ℕ × String → Phi β × Option Pub9 → ℕ)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β) (nU : Array ℕ) (p : Where) (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (run : ℕ → S → Except String (List Claim × S))
    (x : First.Look.Place) (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData) (pw : Where) (b₃ :
      Block S Claim)
    (pq pe : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT)) (ft : ℕ)
    (bs : List (Block S Claim)) (st0 : P → S) (reqW : P → Array UInt32)
    (R : LayersRest2 𝔇 links pl z Rz k m p4 t3 l3 L u ψ nU p d N pb items run x tlD set pp sT
      fd) :
    LinkRest 𝔇 links pl z Rz k m (Phi β) .layers L (phiAll u ψ) (OkLayers p4 nU tlD) nU p pw
      (tmL p4 entUnit tmFour t3) (lenL p4 l3) d N b₃ pb pq pe items u pi8 (4, "K8.equations") run x
        tlD set
      pp sT ft bs st0 fd reqW :=
  have A := layersTake_of (Ok := (fun q => OkLayers p4 nU tlD q ∧ (rowsFit p.rows pi8) q))
    (tlD := tlD) (fun _ h => h.1) R.ties R.hψ R.h4 R.k3 R.k3d
  have hn := moveNum_layers (α := Phi β) u R.seg A R.k3f []
  linkRest_layers 𝔇 links pl z Rz k m p4 tmFour t3 l3 L u ψ nU p d N pb items (4, "K8.equations")
    run x tlD set
    pp sT fd pw b₃ pq pe ft bs st0 reqW
    { seg := R.seg
      ties := R.ties
      hψ := R.hψ
      h4 := R.h4
      k3 := R.k3
      k3d := R.k3d
      k3g := R.k3g
      core := coreRest_of2 𝔇 links pl z Rz k m .layers L u ψ _ nU p _ _ d N pb items _ run x tlD
        set pp
        sT fd (by rw [(order_at R.seg).1]; decide) (R.ties.tEq run R.core.hAt)
        (by funext n q y; simp [tmL, tmFour])
        ⟨R.drawB, R.rows,
          fun _ Rr hf => rel_layers Rr R.seg A fun o ho run hr n e c e₁ hy => by
            obtain ⟨G, rfl⟩ := R.k3p o ho run hr n e c e₁ hy
            exact hf e G,
          ⟨(4, "K8.equations"), by rw [(order_at R.seg).1]; decide, R.ties.tEq⟩,
          (run_layers (rests_fork sizedLS_rests) R.seg A R.k3sL).1,
          (run_layers (rests_fork sized_rests) R.seg A R.k3s).2⟩
        (fun mv hmv => by
          obtain rfl := List.mem_singleton.1 hmv
          exact hn _ (List.mem_append_left _ (List.mem_singleton.2 rfl)))
        (fun mv hmv => by
          obtain rfl := List.mem_singleton.1 hmv
          exact hn _ (List.mem_append_right _ (List.mem_singleton.2 rfl)))
        R.core }

/-- **WHAT IS LEFT AT AN ATTENTION LINK, SECOND FORM.** -/
structure AttRest2 (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard))
    (c : First.Att.P.ParC)
    (t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (l3 : ℕ × String → Phi β × Option Pub9 → ℕ)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β) (nU : Array ℕ) (p : Where) (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (run : ℕ → S → Except String (List Claim × S))
    (x : First.Look.Place) (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData) : Prop where
  seg : SegAt m .attention L
  ties : AttTies L c nU
  hψ : Rests u ψ
  hrd : ∀ e, rd (phiAll u ψ e) = psiAtt e
  h4 : ∀ q front e a c' e₁, Fx9 (phiAll u ψ) (fun q => OkAtt rd c nU tlD q ∧ (rowsFit p.rows pi8) q)
    q e → good9 e → atS.get? e = some a → k8Run.2 front e = .ok (c', e₁) → ∀ t y, laterK atS (O9 (K
    := GE8) (phiAll u ψ) (fun q => OkAtt rd c nU tlD q ∧ (rowsFit p.rows pi8) q) (FullAt nU)) e₁ t →
    (FullAt nU) t → wsumK atS Reading.gl t y (Reading.gl.val a.F.theta) (a.F.nClaim + front)
    (c'.take 4) = termsAt GE8 (tmFour (a.F.nClaim + front) q y) (Reading.gl.val a.F.theta)
  k3 : ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")], ∀ run, At L o run → RunOk
    Reading.gl atS (O9 (phiAll u ψ) (fun q => OkAtt rd c nU tlD q ∧ (rowsFit p.rows pi8) q) (FullAt
    nU)) (Fx9 (phiAll u ψ) (fun q => OkAtt rd c nU tlD q ∧ (rowsFit p.rows pi8) q)) run (t3 o) (l3
    o)
  k3d : ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")], ∀ run, At L o run → ∀ n
    e c' e₁, run n e = .ok (c', e₁) → KeepsDoor atS e e₁
  k3g : ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")], ∀ run, At L o run → ∀ n
    e c e₁, run n e = .ok (c, e₁) → good9 e → good9 e₁
  k3f : ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")], ∀ run, At L o run → ∀ n
    e c e₁, run n e = .ok (c, e₁) → numOf u e₁ = numOf u e
  k3p : ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")], ∀ run, At L o run → ∀ n
    e c e₁, run n e = .ok (c, e₁) → ∃ G, e₁ = e.putFork G
  k3s : ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")], ∀ run, At L o run → ∀ n
    e c e₁, run n e = .ok (c, e₁) → HasFork Sized e → HasFork Sized e₁
  k3sL : ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")], ∀ run, At L o run → ∀ n
    e c e₁, run n e = .ok (c, e₁) → HasFork (fun F => Sized F ∧ F.LS.size = F.ns) e → HasFork (fun F
    => Sized F ∧ F.LS.size = F.ns) e₁
  drawB : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB
  rows : p.rows ≠ 0
  core : CoreRest2 𝔇 links pl z Rz k m .attention L u ψ (OkAtt rd c nU tlD) nU p
    (tmA rd c entUnit tmFour t3) (lenA rd c l3) d N pb items (4, "K8.equations") run x tlD set pp
      sT fd

/-- **LinkRest AT AN ATTENTION LINK, FROM THE SECOND FORM's STRUCTURE.** -/
theorem linkRest_att2 (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard))
    (c : First.Att.P.ParC)
    (t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (l3 : ℕ × String → Phi β × Option Pub9 → ℕ)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β) (nU : Array ℕ) (p : Where) (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (run : ℕ → S → Except String (List Claim × S))
    (x : First.Look.Place) (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData) (pw : Where) (b₃ :
      Block S Claim)
    (pq pe : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT)) (ft : ℕ)
    (bs : List (Block S Claim)) (st0 : P → S) (reqW : P → Array UInt32)
    (R : AttRest2 𝔇 links pl z Rz k m rd c t3 l3 L u ψ nU p d N pb items run x tlD set pp sT
      fd) :
    LinkRest 𝔇 links pl z Rz k m (Phi β) .attention L (phiAll u ψ) (OkAtt rd c nU tlD) nU p pw
      (tmA rd c entUnit tmFour t3) (lenA rd c l3) d N b₃ pb pq pe items u pi8 (4, "K8.equations")
        run x tlD set
      pp sT ft bs st0 fd reqW :=
  have A := attTake_of (Ok := (fun q => OkAtt rd c nU tlD q ∧ (rowsFit p.rows pi8) q))
    (tlD := tlD) (fun _ h => h.1) R.ties R.hψ R.hrd R.h4 R.k3 R.k3d
  have hn := moveNum_attention (α := Phi β) u R.seg A R.k3f []
  linkRest_att 𝔇 links pl z Rz k m rd c tmFour t3 l3 L u ψ nU p d N pb items (4, "K8.equations")
    run x tlD set
    pp sT fd pw b₃ pq pe ft bs st0 reqW
    { seg := R.seg
      ties := R.ties
      hψ := R.hψ
      hrd := R.hrd
      h4 := R.h4
      k3 := R.k3
      k3d := R.k3d
      k3g := R.k3g
      core := coreRest_of2 𝔇 links pl z Rz k m .attention L u ψ _ nU p _ _ d N pb items _ run x
        tlD set pp
        sT fd (by rw [(order_at R.seg).1]; decide) (R.ties.tEq run R.core.hAt)
        (by funext n q y; simp [tmA, tmFour])
        ⟨R.drawB, R.rows,
          fun _ Rr hf => rel_attention Rr R.seg A fun o ho run hr n e c e₁ hy => by
            obtain ⟨G, rfl⟩ := R.k3p o ho run hr n e c e₁ hy
            exact hf e G,
          ⟨(4, "K8.equations"), by rw [(order_at R.seg).1]; decide, R.ties.tEq⟩,
          (run_attention (rests_fork sizedLS_rests) R.seg A R.k3sL).1,
          (run_attention (rests_fork sized_rests) R.seg A R.k3s).2⟩
        (fun mv hmv => by
          obtain rfl := List.mem_singleton.1 hmv
          exact hn _ (List.mem_append_left _ (List.mem_singleton.2 rfl)))
        (fun mv hmv => by
          obtain rfl := List.mem_singleton.1 hmv
          exact hn _ (List.mem_append_right _ (List.mem_singleton.2 rfl)))
        R.core }

/-- **WHAT IS LEFT AT THE HEAD's LINK, SECOND FORM.** -/
structure HeadRest2 (hS : OnBytes.Model.Head.Shape) (iU3 l' piece : ℕ) (p6 : Kinds.Head.Par)
    (kap : Phi β → Option Kinds.Head.Law.Seen)
    (t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (l3 : ℕ × String → Phi β × Option Pub9 → ℕ)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β) (nU : Array ℕ) (p : Where) (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (run : ℕ → S → Except String (List Claim × S))
    (x : First.Look.Place) (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData) : Prop where
  seg : SegAt m .head L
  ties : HeadTies L hS iU3 l' piece p6 nU
  hψ : Rests u ψ
  hkap : ∀ e, kap (phiAll u ψ e) = Kinds.Head.Law.seenOf e
  h4 : ∀ q front e a c e₁, Fx9 (phiAll u ψ) (fun q => OkHead hS iU3 p6 kap nU tlD q ∧ (rowsFit
    p.rows pi8) q) q e → good9 e → atS.get? e = some a → k8Run.2 front e = .ok (c, e₁) → ∀ t y,
    laterK atS (O9 (K := GE8) (phiAll u ψ) (fun q => OkHead hS iU3 p6 kap nU tlD q ∧ (rowsFit p.rows
    pi8) q) (FullAt nU)) e₁ t → (FullAt nU) t → wsumK atS Reading.gl t y (Reading.gl.val a.F.theta)
    (a.F.nClaim + front) (c.take 4) = termsAt GE8 (tmFour (a.F.nClaim + front) q y) (Reading.gl.val
    a.F.theta)
  k3 : ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run → RunOk Reading.gl
    atS (O9 (phiAll u ψ) (fun q => OkHead hS iU3 p6 kap nU tlD q ∧ (rowsFit p.rows pi8) q) (FullAt
    nU)) (Fx9 (phiAll u ψ) (fun q => OkHead hS iU3 p6 kap nU tlD q ∧ (rowsFit p.rows pi8) q)) run
    (t3 o) (l3 o)
  k3d : ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run → ∀ n e c e₁, run n
    e = .ok (c, e₁) → KeepsDoor atS e e₁
  k3g : ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run → ∀ n e c e₁, run n
    e = .ok (c, e₁) → good9 e → good9 e₁
  k3f : ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run → ∀ n e c e₁, run n
    e = .ok (c, e₁) → numOf u e₁ = numOf u e
  k3p : ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run → ∀ n e c e₁, run n
    e = .ok (c, e₁) → ∃ G, e₁ = e.putFork G
  k3s : ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run → ∀ n e c e₁, run n
    e = .ok (c, e₁) → HasFork Sized e → HasFork Sized e₁
  k3sL : ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run → ∀ n e c e₁, run
    n e = .ok (c, e₁) → HasFork (fun F => Sized F ∧ F.LS.size = F.ns) e → HasFork (fun F => Sized F
    ∧ F.LS.size = F.ns) e₁
  drawB : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB
  rows : p.rows ≠ 0
  core : CoreRest2 𝔇 links pl z Rz k m .head L u ψ (OkHead hS iU3 p6 kap nU tlD) nU p
    (tmH hS iU3 p6 kap entUnit tmFour t3) (lenH hS iU3 p6 kap l3) d N pb items (5, "K8.equations")
      run x tlD set pp sT fd

/-- **LinkRest AT THE HEAD's LINK, FROM THE SECOND FORM's STRUCTURE.** -/
theorem linkRest_head2 (hS : OnBytes.Model.Head.Shape) (iU3 l' piece : ℕ) (p6 : Kinds.Head.Par)
    (kap : Phi β → Option Kinds.Head.Law.Seen)
    (t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (l3 : ℕ × String → Phi β × Option Pub9 → ℕ)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β) (nU : Array ℕ) (p : Where) (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (run : ℕ → S → Except String (List Claim × S))
    (x : First.Look.Place) (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData) (pw : Where) (b₃ :
      Block S Claim)
    (pq pe : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT)) (ft : ℕ)
    (bs : List (Block S Claim)) (st0 : P → S) (reqW : P → Array UInt32)
    (R : HeadRest2 𝔇 links pl z Rz k m hS iU3 l' piece p6 kap t3 l3 L u ψ nU p d N pb items run x
      tlD set pp sT
      fd) :
    LinkRest 𝔇 links pl z Rz k m (Phi β) .head L (phiAll u ψ) (OkHead hS iU3 p6 kap nU tlD) nU p pw
      (tmH hS iU3 p6 kap entUnit tmFour t3) (lenH hS iU3 p6 kap l3) d N b₃ pb pq pe items u pi8 (5,
        "K8.equations") run x tlD set
      pp sT ft bs st0 fd reqW :=
  have A := headTake_of (Ok := (fun q => OkHead hS iU3 p6 kap nU tlD q ∧ (rowsFit p.rows pi8) q))
    (tlD := tlD) (fun _ h => h.1) R.ties R.hψ R.hkap R.h4 R.k3 R.k3d
  have hn := moveNum_head (α := Phi β) u R.seg A R.k3f []
  linkRest_head 𝔇 links pl z Rz k m hS iU3 l' piece p6 kap tmFour t3 l3 L u ψ nU p d N pb items
    (5, "K8.equations") run x tlD set
    pp sT fd pw b₃ pq pe ft bs st0 reqW
    { seg := R.seg
      ties := R.ties
      hψ := R.hψ
      hkap := R.hkap
      h4 := R.h4
      k3 := R.k3
      k3d := R.k3d
      k3g := R.k3g
      core := coreRest_of2 𝔇 links pl z Rz k m .head L u ψ _ nU p _ _ d N pb items _ run x tlD set
        pp
        sT fd (by rw [(order_at R.seg).1]; decide) (R.ties.tEq run R.core.hAt)
        (by funext n q y; simp [tmH, tmFour])
        ⟨R.drawB, R.rows,
          fun _ Rr hf => rel_head Rr R.seg A fun o ho run hr n e c e₁ hy => by
            obtain ⟨G, rfl⟩ := R.k3p o ho run hr n e c e₁ hy
            exact hf e G,
          ⟨(5, "K8.equations"), by rw [(order_at R.seg).1]; decide, R.ties.tEq⟩,
          (run_head (rests_fork sizedLS_rests) R.seg A R.k3sL).1,
          (run_head (rests_fork sized_rests) R.seg A R.k3s).2⟩
        (fun mv hmv => by
          obtain rfl := List.mem_singleton.1 hmv
          exact hn _ (List.mem_append_left _ (List.mem_singleton.2 rfl)))
        (fun mv hmv => by
          obtain rfl := List.mem_singleton.1 hmv
          exact hn _ (List.mem_append_right _ (List.mem_singleton.2 rfl)))
        R.core }

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.coreRest_of2
#print axioms VerifiableInference.Desc.LinkJoin.linkRest_layers2
#print axioms VerifiableInference.Desc.LinkJoin.linkRest_att2
#print axioms VerifiableInference.Desc.LinkJoin.linkRest_head2
