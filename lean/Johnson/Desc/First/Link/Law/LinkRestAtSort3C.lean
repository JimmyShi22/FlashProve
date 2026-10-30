-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/LinkRestAtSort3C.lean: ON THE SECOND ROAD (the law's letter C at
`rowsLen`): WHAT IS LEFT AT A LINK OF EACH SORT, AT THE SORT's CHOSEN LETTERS, Kx A FREE LETTER;
AND `LinkRestC` FROM IT. Structures (cut by program out of LinkRestAtSort3.lean, which stands as it
is) and theorems: assemblies. EACH NAME IS THE ELDER NAME WITH "C" AT ITS END.

What turns against the elder text, and nothing else: (1) THE FIELDS h4 AND k3 STAND AT THE BARE
PROMISE fun q => ‹the named Ok› q ∧ Kx q, WITHOUT THE PUBLIC SENTENCE: so they are owed once; the
forms at the promise with C are drawn inside linkRestC_core by monotony · (2) one new field: k3k: a
yes of each of the lookup argument's runs keeps the ledger's map of weights, the plan's number and
the count (kapOf, KapRuns.lean): with the sort's Take it gives the field hk
(keepsKap_layers, keepsKap_attention, keepsKap_head) · (3) core is CoreRest2C
(LinkRestAtSortC.lean).

Limits. BOOK-KEEPING. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkRestAtSortC
import Johnson.Desc.First.Link.Law.LinkRestAtSort3
import Johnson.Desc.First.Link.Law.KapRuns

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

/-- **WHAT IS LEFT AT A LAYERS' LINK, THIRD FORM**: Ok := the sort's named Ok AND Kx. -/
structure LayersRest3C (p4 : OnBytes.Desc.First.K4.Par)
    (Kx : Phi β × Option Pub9 → Prop)
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
  h4 : ∀ q front e a c e₁, Fx9 (phiAll u ψ) (fun q => OkLayers p4 nU tlD q ∧ Kx q) q e → good9 e →
    atS.get? e = some a → k8Run.2 front e = .ok (c, e₁) → ∀
    t y, laterK atS (O9 (K := GE8) (phiAll u ψ) (fun q => OkLayers p4 nU tlD q ∧ Kx q) (FullAt nU))
      e₁ t → (FullAt nU) t → wsumK atS Reading.gl t y
    (Reading.gl.val a.F.theta) (a.F.nClaim + front) (c.take 4) = termsAt GE8 (tmFour (a.F.nClaim +
    front) q y) (Reading.gl.val a.F.theta)
  k3 : ∀ o ∈ [(1, "objects"), (6, "objects")], ∀ run, At L o run → RunOk Reading.gl atS (O9 (phiAll
    u ψ) (fun q => OkLayers p4 nU tlD q ∧ Kx q) (FullAt nU))
    (Fx9 (phiAll u ψ) (fun q => OkLayers p4 nU tlD q ∧ Kx q))
    run (t3 o) (l3 o)
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
  k3k : ∀ o ∈ [(1, "objects"), (6, "objects")], ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c,
    e₁) → kapOf e₁ = kapOf e
  drawB : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB
  rows : p.rows ≠ 0
  core : CoreRest2C 𝔇 links pl z Rz k m .layers L u ψ (fun q => OkLayers p4 nU tlD q ∧ Kx q) nU p
    (tmL p4 entUnit tmFour t3) (lenL p4 l3) d N pb items (4, "K8.equations") run x tlD set pp sT fd

/-- **LinkRestC AT A LAYERS' LINK, AT Ok := THE NAMED Ok AND Kx.** -/
theorem linkRestC_layers3 (p4 : OnBytes.Desc.First.K4.Par)
    (Kx : Phi β × Option Pub9 → Prop)
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
    (R : LayersRest3C 𝔇 links pl z Rz k m p4 Kx t3 l3 L u ψ nU p d N pb items run x tlD set pp
      sT fd) :
    LinkRestC 𝔇 links pl z Rz k m (Phi β) .layers L (phiAll u ψ) (fun q => OkLayers p4 nU tlD q ∧
      Kx q) nU
      p pw (tmL p4 entUnit tmFour t3) (lenL p4 l3) d N b₃ pb pq pe items u pi8 (4, "K8.equations")
        run x
      tlD set pp sT ft bs st0 fd reqW :=
  have A := layersTake_of (Ok := (fun q => OkLayers p4 nU tlD q ∧ Kx q))
    (tlD := tlD) (fun _ h => h.1) R.ties R.hψ R.h4 R.k3 R.k3d
  have hn := moveNum_layers (α := Phi β) u R.seg A R.k3f []
  linkRestC_core 𝔇 links pl z Rz k m .layers L u ψ _ nU p _ _ d N pb items _ run x tlD set pp sT fd
    pw
    b₃ pq pe ft bs st0 reqW (fun _ h => h.1.core) R.hψ (order_at R.seg).1 (runs_layers A)
      (full_layers R.seg A R.k3g)
    (coreRestC_of2 𝔇 links pl z Rz k m .layers L u ψ _ nU p _ _ d N pb items _ run x tlD set pp
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
      (keepsKap_layers R.seg A R.k3k) R.core)

/-- **WHAT IS LEFT AT AN ATTENTION LINK, THIRD FORM**: Ok := the sort's named Ok AND Kx. -/
structure AttRest3C (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard))
    (c : First.Att.P.ParC)
    (Kx : Phi β × Option Pub9 → Prop)
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
  h4 : ∀ q front e a c' e₁, Fx9 (phiAll u ψ) (fun q => OkAtt rd c nU tlD q ∧ Kx q) q e → good9 e →
    atS.get? e = some a → k8Run.2 front e = .ok (c', e₁) → ∀
    t y, laterK atS (O9 (K := GE8) (phiAll u ψ) (fun q => OkAtt rd c nU tlD q ∧ Kx q) (FullAt nU))
      e₁ t → (FullAt nU) t → wsumK atS Reading.gl t y
    (Reading.gl.val a.F.theta) (a.F.nClaim + front) (c'.take 4) = termsAt GE8 (tmFour (a.F.nClaim +
    front) q y) (Reading.gl.val a.F.theta)
  k3 : ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")], ∀ run, At L o run → RunOk
    Reading.gl atS (O9 (phiAll u ψ) (fun q => OkAtt rd c nU tlD q ∧ Kx q) (FullAt nU)) (Fx9 (phiAll
      u ψ) (fun q => OkAtt rd c nU tlD q ∧ Kx q)) run (t3 o) (l3 o)
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
  k3k : ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")], ∀ run, At L o run → ∀ n
    e c' e₁, run n e = .ok (c', e₁) → kapOf e₁ = kapOf e
  drawB : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB
  rows : p.rows ≠ 0
  core : CoreRest2C 𝔇 links pl z Rz k m .attention L u ψ (fun q => OkAtt rd c nU tlD q ∧ Kx q) nU p
    (tmA rd c entUnit tmFour t3) (lenA rd c l3) d N pb items (4, "K8.equations") run x tlD set pp
      sT fd

/-- **LinkRestC AT AN ATTENTION LINK, AT Ok := THE NAMED Ok AND Kx.** -/
theorem linkRestC_att3 (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard))
    (c : First.Att.P.ParC)
    (Kx : Phi β × Option Pub9 → Prop)
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
    (R : AttRest3C 𝔇 links pl z Rz k m rd c Kx t3 l3 L u ψ nU p d N pb items run x tlD set pp
      sT fd) :
    LinkRestC 𝔇 links pl z Rz k m (Phi β) .attention L (phiAll u ψ) (fun q => OkAtt rd c nU tlD q ∧
      Kx q) nU
      p pw (tmA rd c entUnit tmFour t3) (lenA rd c l3) d N b₃ pb pq pe items u pi8 (4,
        "K8.equations") run x
      tlD set pp sT ft bs st0 fd reqW :=
  have A := attTake_of (Ok := (fun q => OkAtt rd c nU tlD q ∧ Kx q))
    (tlD := tlD) (fun _ h => h.1) R.ties R.hψ R.hrd R.h4 R.k3 R.k3d
  have hn := moveNum_attention (α := Phi β) u R.seg A R.k3f []
  linkRestC_core 𝔇 links pl z Rz k m .attention L u ψ _ nU p _ _ d N pb items _ run x tlD set pp sT
    fd pw
    b₃ pq pe ft bs st0 reqW (fun _ h => h.1.core) R.hψ (order_at R.seg).1 (runs_attention A)
      (full_attention R.seg A
      R.k3g)
    (coreRestC_of2 𝔇 links pl z Rz k m .attention L u ψ _ nU p _ _ d N pb items _ run x tlD set pp
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
      (keepsKap_attention R.seg A R.k3k) R.core)

/-- **WHAT IS LEFT AT THE HEAD's LINK, THIRD FORM**: Ok := the sort's named Ok AND Kx. -/
structure HeadRest3C (hS : OnBytes.Model.Head.Shape) (iU3 l' piece : ℕ) (p6 : Kinds.Head.Par)
    (kap : Phi β → Option Kinds.Head.Law.Seen)
    (Kx : Phi β × Option Pub9 → Prop)
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
  h4 : ∀ q front e a c e₁, Fx9 (phiAll u ψ) (fun q => OkHead hS iU3 p6 kap nU tlD q ∧ Kx q) q e →
    good9 e → atS.get? e = some a → k8Run.2 front e = .ok (c,
    e₁) → ∀ t y, laterK atS (O9 (K := GE8) (phiAll u ψ) (fun q => OkHead hS iU3 p6 kap nU tlD q ∧
      Kx q) (FullAt nU)) e₁ t → (FullAt nU) t → wsumK atS
    Reading.gl t y (Reading.gl.val a.F.theta) (a.F.nClaim + front) (c.take 4) = termsAt GE8 (tmFour
    (a.F.nClaim + front) q y) (Reading.gl.val a.F.theta)
  k3 : ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run → RunOk Reading.gl
    atS (O9 (phiAll u ψ) (fun q => OkHead hS iU3 p6 kap nU tlD q ∧ Kx q) (FullAt nU)) (Fx9 (phiAll
      u ψ) (fun q => OkHead hS iU3 p6 kap nU tlD q ∧ Kx q)) run (t3 o) (l3 o)
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
  k3k : ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run → ∀ n e c e₁, run
    n e = .ok (c, e₁) → kapOf e₁ = kapOf e
  drawB : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB
  rows : p.rows ≠ 0
  core : CoreRest2C 𝔇 links pl z Rz k m .head L u ψ (fun q => OkHead hS iU3 p6 kap nU tlD q ∧ Kx q)
    nU p
    (tmH hS iU3 p6 kap entUnit tmFour t3) (lenH hS iU3 p6 kap l3) d N pb items (5, "K8.equations")
      run x tlD set pp sT fd

/-- **LinkRestC AT THE HEAD's LINK, AT Ok := THE NAMED Ok AND Kx.** -/
theorem linkRestC_head3 (hS : OnBytes.Model.Head.Shape) (iU3 l' piece : ℕ) (p6 : Kinds.Head.Par)
    (kap : Phi β → Option Kinds.Head.Law.Seen)
    (Kx : Phi β × Option Pub9 → Prop)
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
    (R : HeadRest3C 𝔇 links pl z Rz k m hS iU3 l' piece p6 kap Kx t3 l3 L u ψ nU p d N pb items run
      x tlD set pp
      sT fd) :
    LinkRestC 𝔇 links pl z Rz k m (Phi β) .head L (phiAll u ψ) (fun q => OkHead hS iU3 p6 kap nU
      tlD q ∧ Kx q) nU
      p pw (tmH hS iU3 p6 kap entUnit tmFour t3) (lenH hS iU3 p6 kap l3) d N b₃ pb pq pe items u
        pi8 (5, "K8.equations") run x
      tlD set pp sT ft bs st0 fd reqW :=
  have A := headTake_of (Ok := (fun q => OkHead hS iU3 p6 kap nU tlD q ∧ Kx q))
    (tlD := tlD) (fun _ h => h.1) R.ties R.hψ R.hkap R.h4 R.k3 R.k3d
  have hn := moveNum_head (α := Phi β) u R.seg A R.k3f []
  linkRestC_core 𝔇 links pl z Rz k m .head L u ψ _ nU p _ _ d N pb items _ run x tlD set pp sT fd pw
    b₃ pq pe ft bs st0 reqW (fun _ h => h.1.core) R.hψ (order_at R.seg).1 (runs_head A) (full_head
      R.seg A R.k3g)
    (coreRestC_of2 𝔇 links pl z Rz k m .head L u ψ _ nU p _ _ d N pb items _ run x tlD set pp
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
      (keepsKap_head R.seg A R.k3k) R.core)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.linkRestC_layers3
#print axioms VerifiableInference.Desc.LinkJoin.linkRestC_att3
#print axioms VerifiableInference.Desc.LinkJoin.linkRestC_head3
