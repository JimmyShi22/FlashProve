-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/LinkRestAtSort4.lean: WHAT IS LEFT OF A LINK's LAW AT EACH SORT OF
LINK, CUT IN TWO: THE SORT's OWN FIELDS (`LayersOwes`, `AttOwes`, `HeadOwes`) AND core. Over
LinkRestAtSort3.lean, which stands as it is. Structures of sentences, and theorems: assemblies.
For joining the sorts at the constant.

Why. Three fields of core (Ahs1, hbook₂, inRun) have payers that spend the runs' share of the link,
or the sort's Take. Both come off the sort's own fields, which in `LayersRest3` .. stand in ONE
structure with core: to pay a field of core one would need the structure that holds core: a circle.
With the own fields in a structure of their own the circle is cut.

On the names. NOT "AttOwn", "HeadOwn": these are structures of the verifier's state
(Johnson/Desc/First/State.lean).

What is said, at each sort.
  `‹Sort›Owes`: `‹Sort›Rest3` less its field core: the same texts (cut by the same program), over
    the letters that they name alone: no 𝔇, no list of places, no public part.
  `take_of_‹sort›Owes`: the sort's Take, at Ok := fun q => (‹the named Ok› q ∧ Kx q) ∧ rowsFit
    p.rows pi8 q.
  `share_of_‹sort›Owes`: LinkShare L p (SortShare.lean).
  `‹sort›Rest3_of_owes`: **`‹Sort›Rest3` from the own fields and core.**

Limits. BOOK-KEEPING. NOTHING IS SHOWN OF ANY STATE OR RUN. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkRestAtSort3
import Johnson.Desc.First.Link.Law.SortShare

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

/-- **A LAYERS' LINK's OWN FIELDS**: `LayersRest3` less its field core. -/
structure LayersOwes (m : ℕ) (p4 : OnBytes.Desc.First.K4.Par)
    (Kx : Phi β × Option Pub9 → Prop)
    (t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (l3 : ℕ × String → Phi β × Option Pub9 → ℕ)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β) (nU : Array ℕ) (p : Where) (tlD : HTailF2) : Prop
      where
  seg : SegAt m .layers L
  ties : LayersTies L p4 nU
  hψ : Rests u ψ
  h4 : ∀ q front e a c e₁, Fx9 (phiAll u ψ) (fun q => (fun q => OkLayers p4 nU tlD q ∧ Kx q) q ∧
    (rowsFit p.rows pi8) q) q e → good9 e → atS.get? e = some a → k8Run.2 front e = .ok (c, e₁) → ∀
    t y, laterK atS (O9 (K := GE8) (phiAll u ψ) (fun q => (fun q => OkLayers p4 nU tlD q ∧ Kx q) q ∧
    (rowsFit p.rows pi8) q) (FullAt nU)) e₁ t → (FullAt nU) t → wsumK atS Reading.gl t y
    (Reading.gl.val a.F.theta) (a.F.nClaim + front) (c.take 4) = termsAt GE8 (tmFour (a.F.nClaim +
    front) q y) (Reading.gl.val a.F.theta)
  k3 : ∀ o ∈ [(1, "objects"), (6, "objects")], ∀ run, At L o run → RunOk Reading.gl atS (O9 (phiAll
    u ψ) (fun q => (fun q => OkLayers p4 nU tlD q ∧ Kx q) q ∧ (rowsFit p.rows pi8) q) (FullAt nU))
    (Fx9 (phiAll u ψ) (fun q => (fun q => OkLayers p4 nU tlD q ∧ Kx q) q ∧ (rowsFit p.rows pi8) q))
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
  drawB : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB
  rows : p.rows ≠ 0

/-- The sort's Take from the own fields. -/
theorem take_of_layersOwes {m : ℕ} {p4 : OnBytes.Desc.First.K4.Par}
    {Kx : Phi β × Option Pub9 → Prop}
    {t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E)}
    {l3 : ℕ × String → Phi β × Option Pub9 → ℕ}
    {L : Link S Claim} {u : HTailF2} {ψ : S → β} {nU : Array ℕ} {p : Where} {tlD : HTailF2}
    (O : LayersOwes m p4 Kx t3 l3 L u ψ nU p tlD) :
    LayersTake L u ψ (fun q => (fun q => OkLayers p4 nU tlD q ∧ Kx q) q ∧ (rowsFit p.rows pi8) q)
      (FullAt nU) p4 nU entUnit tmFour t3 l3 :=
  layersTake_of (tlD := tlD) (fun _ h => h.1.1) O.ties O.hψ O.h4 O.k3 O.k3d

/-- The runs' share of the link from the own fields. -/
theorem share_of_layersOwes {m : ℕ} {p4 : OnBytes.Desc.First.K4.Par}
    {Kx : Phi β × Option Pub9 → Prop}
    {t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E)}
    {l3 : ℕ × String → Phi β × Option Pub9 → ℕ}
    {L : Link S Claim} {u : HTailF2} {ψ : S → β} {nU : Array ℕ} {p : Where} {tlD : HTailF2}
    (O : LayersOwes m p4 Kx t3 l3 L u ψ nU p tlD) : LinkShare L p :=
  linkShare_layers O.seg (take_of_layersOwes O) O.k3p O.k3s O.k3sL p O.drawB O.rows

/-- **`LayersRest3` FROM THE OWN FIELDS AND core.** -/
theorem layersRest3_of_owes (p4 : OnBytes.Desc.First.K4.Par)
    (Kx : Phi β × Option Pub9 → Prop)
    (t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (l3 : ℕ × String → Phi β × Option Pub9 → ℕ)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β) (nU : Array ℕ) (p : Where) (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (run : ℕ → S → Except String (List Claim × S))
    (x : First.Look.Place) (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData)
    (O : LayersOwes m p4 Kx t3 l3 L u ψ nU p tlD)
    (c₂ : CoreRest2 𝔇 links pl z Rz k m .layers L u ψ (fun q => OkLayers p4 nU tlD q ∧ Kx q) nU p
      (tmL p4 entUnit tmFour t3) (lenL p4 l3) d N pb items (4, "K8.equations") run x tlD set pp sT
        fd) :
    LayersRest3 𝔇 links pl z Rz k m p4 Kx t3 l3 L u ψ nU p d N pb items run x tlD set pp sT
      fd where
  seg := O.seg
  ties := O.ties
  hψ := O.hψ
  h4 := O.h4
  k3 := O.k3
  k3d := O.k3d
  k3g := O.k3g
  k3f := O.k3f
  k3p := O.k3p
  k3s := O.k3s
  k3sL := O.k3sL
  drawB := O.drawB
  rows := O.rows
  core := c₂

/-- **AN ATTENTION LINK's OWN FIELDS**: `AttRest3` less its field core. -/
structure AttOwes (m : ℕ) (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard))
    (c : First.Att.P.ParC)
    (Kx : Phi β × Option Pub9 → Prop)
    (t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (l3 : ℕ × String → Phi β × Option Pub9 → ℕ)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β) (nU : Array ℕ) (p : Where) (tlD : HTailF2) : Prop
      where
  seg : SegAt m .attention L
  ties : AttTies L c nU
  hψ : Rests u ψ
  hrd : ∀ e, rd (phiAll u ψ e) = psiAtt e
  h4 : ∀ q front e a c' e₁, Fx9 (phiAll u ψ) (fun q => (fun q => OkAtt rd c nU tlD q ∧ Kx q) q ∧
    (rowsFit p.rows pi8) q) q e → good9 e → atS.get? e = some a → k8Run.2 front e = .ok (c', e₁) → ∀
    t y, laterK atS (O9 (K := GE8) (phiAll u ψ) (fun q => (fun q => OkAtt rd c nU tlD q ∧ Kx q) q ∧
    (rowsFit p.rows pi8) q) (FullAt nU)) e₁ t → (FullAt nU) t → wsumK atS Reading.gl t y
    (Reading.gl.val a.F.theta) (a.F.nClaim + front) (c'.take 4) = termsAt GE8 (tmFour (a.F.nClaim +
    front) q y) (Reading.gl.val a.F.theta)
  k3 : ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")], ∀ run, At L o run → RunOk
    Reading.gl atS (O9 (phiAll u ψ) (fun q => (fun q => OkAtt rd c nU tlD q ∧ Kx q) q ∧ (rowsFit
    p.rows pi8) q) (FullAt nU)) (Fx9 (phiAll u ψ) (fun q => (fun q => OkAtt rd c nU tlD q ∧ Kx q) q
    ∧ (rowsFit p.rows pi8) q)) run (t3 o) (l3 o)
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

/-- The sort's Take from the own fields. -/
theorem take_of_attOwes {m : ℕ} {rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)}
    {c : First.Att.P.ParC}
    {Kx : Phi β × Option Pub9 → Prop}
    {t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E)}
    {l3 : ℕ × String → Phi β × Option Pub9 → ℕ}
    {L : Link S Claim} {u : HTailF2} {ψ : S → β} {nU : Array ℕ} {p : Where} {tlD : HTailF2}
    (O : AttOwes m rd c Kx t3 l3 L u ψ nU p tlD) :
    AttTake L u ψ (fun q => (fun q => OkAtt rd c nU tlD q ∧ Kx q) q ∧ (rowsFit p.rows pi8) q)
      (FullAt nU) rd c nU entUnit tmFour t3 l3 :=
  attTake_of (tlD := tlD) (fun _ h => h.1.1) O.ties O.hψ O.hrd O.h4 O.k3 O.k3d

/-- The runs' share of the link from the own fields. -/
theorem share_of_attOwes {m : ℕ} {rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)}
    {c : First.Att.P.ParC}
    {Kx : Phi β × Option Pub9 → Prop}
    {t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E)}
    {l3 : ℕ × String → Phi β × Option Pub9 → ℕ}
    {L : Link S Claim} {u : HTailF2} {ψ : S → β} {nU : Array ℕ} {p : Where} {tlD : HTailF2}
    (O : AttOwes m rd c Kx t3 l3 L u ψ nU p tlD) : LinkShare L p :=
  linkShare_att O.seg (take_of_attOwes O) O.k3p O.k3s O.k3sL p O.drawB O.rows

/-- **`AttRest3` FROM THE OWN FIELDS AND core.** -/
theorem attRest3_of_owes (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard))
    (c : First.Att.P.ParC)
    (Kx : Phi β × Option Pub9 → Prop)
    (t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (l3 : ℕ × String → Phi β × Option Pub9 → ℕ)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β) (nU : Array ℕ) (p : Where) (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (run : ℕ → S → Except String (List Claim × S))
    (x : First.Look.Place) (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData)
    (O : AttOwes m rd c Kx t3 l3 L u ψ nU p tlD)
    (c₂ : CoreRest2 𝔇 links pl z Rz k m .attention L u ψ (fun q => OkAtt rd c nU tlD q ∧ Kx q) nU p
      (tmA rd c entUnit tmFour t3) (lenA rd c l3) d N pb items (4, "K8.equations") run x tlD set pp
        sT fd) :
    AttRest3 𝔇 links pl z Rz k m rd c Kx t3 l3 L u ψ nU p d N pb items run x tlD set pp sT
      fd where
  seg := O.seg
  ties := O.ties
  hψ := O.hψ
  hrd := O.hrd
  h4 := O.h4
  k3 := O.k3
  k3d := O.k3d
  k3g := O.k3g
  k3f := O.k3f
  k3p := O.k3p
  k3s := O.k3s
  k3sL := O.k3sL
  drawB := O.drawB
  rows := O.rows
  core := c₂

/-- **THE HEAD's LINK's OWN FIELDS**: `HeadRest3` less its field core. -/
structure HeadOwes (m : ℕ) (hS : OnBytes.Model.Head.Shape) (iU3 l' piece : ℕ) (p6 : Kinds.Head.Par)
    (kap : Phi β → Option Kinds.Head.Law.Seen)
    (Kx : Phi β × Option Pub9 → Prop)
    (t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (l3 : ℕ × String → Phi β × Option Pub9 → ℕ)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β) (nU : Array ℕ) (p : Where) (tlD : HTailF2) : Prop
      where
  seg : SegAt m .head L
  ties : HeadTies L hS iU3 l' piece p6 nU
  hψ : Rests u ψ
  hkap : ∀ e, kap (phiAll u ψ e) = Kinds.Head.Law.seenOf e
  h4 : ∀ q front e a c e₁, Fx9 (phiAll u ψ) (fun q => (fun q => OkHead hS iU3 p6 kap nU tlD q ∧ Kx
    q) q ∧ (rowsFit p.rows pi8) q) q e → good9 e → atS.get? e = some a → k8Run.2 front e = .ok (c,
    e₁) → ∀ t y, laterK atS (O9 (K := GE8) (phiAll u ψ) (fun q => (fun q => OkHead hS iU3 p6 kap nU
    tlD q ∧ Kx q) q ∧ (rowsFit p.rows pi8) q) (FullAt nU)) e₁ t → (FullAt nU) t → wsumK atS
    Reading.gl t y (Reading.gl.val a.F.theta) (a.F.nClaim + front) (c.take 4) = termsAt GE8 (tmFour
    (a.F.nClaim + front) q y) (Reading.gl.val a.F.theta)
  k3 : ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run → RunOk Reading.gl
    atS (O9 (phiAll u ψ) (fun q => (fun q => OkHead hS iU3 p6 kap nU tlD q ∧ Kx q) q ∧ (rowsFit
    p.rows pi8) q) (FullAt nU)) (Fx9 (phiAll u ψ) (fun q => (fun q => OkHead hS iU3 p6 kap nU tlD q
    ∧ Kx q) q ∧ (rowsFit p.rows pi8) q)) run (t3 o) (l3 o)
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

/-- The sort's Take from the own fields. -/
theorem take_of_headOwes {m : ℕ} {hS : OnBytes.Model.Head.Shape} {iU3 l' piece : ℕ} {p6 :
    Kinds.Head.Par}
    {kap : Phi β → Option Kinds.Head.Law.Seen}
    {Kx : Phi β × Option Pub9 → Prop}
    {t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E)}
    {l3 : ℕ × String → Phi β × Option Pub9 → ℕ}
    {L : Link S Claim} {u : HTailF2} {ψ : S → β} {nU : Array ℕ} {p : Where} {tlD : HTailF2}
    (O : HeadOwes m hS iU3 l' piece p6 kap Kx t3 l3 L u ψ nU p tlD) :
    HeadTake L u ψ (fun q => (fun q => OkHead hS iU3 p6 kap nU tlD q ∧ Kx q) q ∧ (rowsFit p.rows
      pi8) q)
      (FullAt nU) hS iU3 l' piece p6 kap nU entUnit tmFour t3 l3 :=
  headTake_of (tlD := tlD) (fun _ h => h.1.1) O.ties O.hψ O.hkap O.h4 O.k3 O.k3d

/-- The runs' share of the link from the own fields. -/
theorem share_of_headOwes {m : ℕ} {hS : OnBytes.Model.Head.Shape} {iU3 l' piece : ℕ} {p6 :
    Kinds.Head.Par}
    {kap : Phi β → Option Kinds.Head.Law.Seen}
    {Kx : Phi β × Option Pub9 → Prop}
    {t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E)}
    {l3 : ℕ × String → Phi β × Option Pub9 → ℕ}
    {L : Link S Claim} {u : HTailF2} {ψ : S → β} {nU : Array ℕ} {p : Where} {tlD : HTailF2}
    (O : HeadOwes m hS iU3 l' piece p6 kap Kx t3 l3 L u ψ nU p tlD) : LinkShare L p :=
  linkShare_head O.seg (take_of_headOwes O) O.k3p O.k3s O.k3sL p O.drawB O.rows

/-- **`HeadRest3` FROM THE OWN FIELDS AND core.** -/
theorem headRest3_of_owes (hS : OnBytes.Model.Head.Shape) (iU3 l' piece : ℕ) (p6 : Kinds.Head.Par)
    (kap : Phi β → Option Kinds.Head.Law.Seen)
    (Kx : Phi β × Option Pub9 → Prop)
    (t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (l3 : ℕ × String → Phi β × Option Pub9 → ℕ)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β) (nU : Array ℕ) (p : Where) (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (run : ℕ → S → Except String (List Claim × S))
    (x : First.Look.Place) (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData)
    (O : HeadOwes m hS iU3 l' piece p6 kap Kx t3 l3 L u ψ nU p tlD)
    (c₂ : CoreRest2 𝔇 links pl z Rz k m .head L u ψ (fun q => OkHead hS iU3 p6 kap nU tlD q ∧ Kx
      q) nU p
      (tmH hS iU3 p6 kap entUnit tmFour t3) (lenH hS iU3 p6 kap l3) d N pb items (5,
        "K8.equations") run x tlD set pp sT fd) :
    HeadRest3 𝔇 links pl z Rz k m hS iU3 l' piece p6 kap Kx t3 l3 L u ψ nU p d N pb items run x
      tlD set pp sT
      fd where
  seg := O.seg
  ties := O.ties
  hψ := O.hψ
  hkap := O.hkap
  h4 := O.h4
  k3 := O.k3
  k3d := O.k3d
  k3g := O.k3g
  k3f := O.k3f
  k3p := O.k3p
  k3s := O.k3s
  k3sL := O.k3sL
  drawB := O.drawB
  rows := O.rows
  core := c₂

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.take_of_layersOwes
#print axioms VerifiableInference.Desc.LinkJoin.share_of_layersOwes
#print axioms VerifiableInference.Desc.LinkJoin.layersRest3_of_owes
#print axioms VerifiableInference.Desc.LinkJoin.take_of_attOwes
#print axioms VerifiableInference.Desc.LinkJoin.share_of_attOwes
#print axioms VerifiableInference.Desc.LinkJoin.attRest3_of_owes
#print axioms VerifiableInference.Desc.LinkJoin.take_of_headOwes
#print axioms VerifiableInference.Desc.LinkJoin.share_of_headOwes
#print axioms VerifiableInference.Desc.LinkJoin.headRest3_of_owes
