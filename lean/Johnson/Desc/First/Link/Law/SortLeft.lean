-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/SortLeft.lean: BENEATH THE THREE LISTS OF WHAT IS LEFT OF A
LINK's LAW AT THE SORT's CHOSEN LETTERS (`LayersRest3`, `AttRest3`, `HeadRest3`,
LinkRestAtSort3.lean): EACH CUT IN TWO (`LayersOwes`, `AttOwes`, `HeadOwes`,
LinkRestAtSort4.lean: the sort's own fields), ITS FIELD core (`CoreRest2`) GIVEN WAY TO WHAT IS LEFT
OF IT (`CoreLeft`, CoreLeft.lean). Three definitions and three theorems, written by program from
these lists' own heads.

What is said.
  `LayersLeft …` := `LayersOwes` at the sort's letters AND `CoreLeft` at its core letters.
    `AttLeft`, `HeadLeft`: the like. `layersRest3_of_left`, `attRest3_of_left`, `headRest3_of_left`:
    **the sort's list from it and a road from `CoreLeft` to `CoreRest2` that may spend the runs'
    share of the link** (which comes off the own fields: `share_of_layersOwes` and its like).

Limits. BOOK-KEEPING. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkRestAtSort4
import Johnson.Desc.First.Link.Law.CoreLeft

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

/-- **WHAT IS LEFT AT A LAYERS' LINK**: the sort's own fields, and what is left of the core. -/
def LayersLeft (p4 : OnBytes.Desc.First.K4.Par)
    (Kx : Phi β × Option Pub9 → Prop)
    (t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (l3 : ℕ × String → Phi β × Option Pub9 → ℕ)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β) (nU : Array ℕ) (p : Where) (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (run : ℕ → S → Except String (List Claim × S))
    (x : First.Look.Place) (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData) : Prop :=
  LayersOwes m p4 Kx t3 l3 L u ψ nU p tlD ∧
  CoreLeft 𝔇 links pl z Rz k m .layers L u ψ (fun q => OkLayers p4 nU tlD q ∧ Kx q) nU p (tmL p4
    entUnit tmFour t3) (lenL p4 l3) d N pb items (4, "K8.equations") run x tlD set pp sT fd

theorem layersRest3_of_left (p4 : OnBytes.Desc.First.K4.Par)
    (Kx : Phi β × Option Pub9 → Prop)
    (t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (l3 : ℕ × String → Phi β × Option Pub9 → ℕ)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β) (nU : Array ℕ) (p : Where) (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (run : ℕ → S → Except String (List Claim × S))
    (x : First.Look.Place) (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData)
    (hc : LinkShare L p → CoreLeft 𝔇 links pl z Rz k m .layers L u ψ (fun q => OkLayers p4 nU tlD q
      ∧ Kx q) nU p (tmL p4 entUnit tmFour t3) (lenL p4 l3) d N pb items (4, "K8.equations") run x
      tlD set pp sT fd →
      CoreRest2 𝔇 links pl z Rz k m .layers L u ψ (fun q => OkLayers p4 nU tlD q ∧ Kx q) nU p (tmL
        p4 entUnit tmFour t3) (lenL p4 l3) d N pb items (4, "K8.equations") run x tlD set pp sT fd)
    (H : LayersLeft 𝔇 links pl z Rz k m p4 Kx t3 l3 L u ψ nU p d N pb items run x tlD set pp sT fd)
      :
    LayersRest3 𝔇 links pl z Rz k m p4 Kx t3 l3 L u ψ nU p d N pb items run x tlD set pp sT fd :=
  layersRest3_of_owes 𝔇 links pl z Rz k m p4 Kx t3 l3 L u ψ nU p d N pb items run x tlD set pp sT
    fd H.1
    (hc (share_of_layersOwes H.1) H.2)

/-- **WHAT IS LEFT AT AN ATTENTION LINK**: the sort's own fields, and what is left of the core. -/
def AttLeft (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard))
    (c : First.Att.P.ParC)
    (Kx : Phi β × Option Pub9 → Prop)
    (t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (l3 : ℕ × String → Phi β × Option Pub9 → ℕ)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β) (nU : Array ℕ) (p : Where) (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (run : ℕ → S → Except String (List Claim × S))
    (x : First.Look.Place) (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData) : Prop :=
  AttOwes m rd c Kx t3 l3 L u ψ nU p tlD ∧
  CoreLeft 𝔇 links pl z Rz k m .attention L u ψ (fun q => OkAtt rd c nU tlD q ∧ Kx q) nU p (tmA rd
    c entUnit tmFour t3) (lenA rd c l3) d N pb items (4, "K8.equations") run x tlD set pp sT fd

theorem attRest3_of_left (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard))
    (c : First.Att.P.ParC)
    (Kx : Phi β × Option Pub9 → Prop)
    (t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (l3 : ℕ × String → Phi β × Option Pub9 → ℕ)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β) (nU : Array ℕ) (p : Where) (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (run : ℕ → S → Except String (List Claim × S))
    (x : First.Look.Place) (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData)
    (hc : LinkShare L p → CoreLeft 𝔇 links pl z Rz k m .attention L u ψ (fun q => OkAtt rd c nU tlD
      q ∧ Kx q) nU p (tmA rd c entUnit tmFour t3) (lenA rd c l3) d N pb items (4, "K8.equations")
      run x tlD set pp sT fd →
      CoreRest2 𝔇 links pl z Rz k m .attention L u ψ (fun q => OkAtt rd c nU tlD q ∧ Kx q) nU p
        (tmA rd c entUnit tmFour t3) (lenA rd c l3) d N pb items (4, "K8.equations") run x tlD set
        pp sT fd)
    (H : AttLeft 𝔇 links pl z Rz k m rd c Kx t3 l3 L u ψ nU p d N pb items run x tlD set pp sT fd)
      :
    AttRest3 𝔇 links pl z Rz k m rd c Kx t3 l3 L u ψ nU p d N pb items run x tlD set pp sT fd :=
  attRest3_of_owes 𝔇 links pl z Rz k m rd c Kx t3 l3 L u ψ nU p d N pb items run x tlD set pp sT fd
    H.1
    (hc (share_of_attOwes H.1) H.2)

/-- **WHAT IS LEFT AT THE HEAD'S LINK**: the sort's own fields, and what is left of the core. -/
def HeadLeft (hS : OnBytes.Model.Head.Shape) (iU3 l' piece : ℕ) (p6 : Kinds.Head.Par)
    (kap : Phi β → Option Kinds.Head.Law.Seen)
    (Kx : Phi β × Option Pub9 → Prop)
    (t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (l3 : ℕ × String → Phi β × Option Pub9 → ℕ)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β) (nU : Array ℕ) (p : Where) (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (run : ℕ → S → Except String (List Claim × S))
    (x : First.Look.Place) (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData) : Prop :=
  HeadOwes m hS iU3 l' piece p6 kap Kx t3 l3 L u ψ nU p tlD ∧
  CoreLeft 𝔇 links pl z Rz k m .head L u ψ (fun q => OkHead hS iU3 p6 kap nU tlD q ∧ Kx q) nU p
    (tmH hS iU3 p6 kap entUnit tmFour t3) (lenH hS iU3 p6 kap l3) d N pb items (5, "K8.equations")
    run x tlD set pp sT fd

theorem headRest3_of_left (hS : OnBytes.Model.Head.Shape) (iU3 l' piece : ℕ) (p6 : Kinds.Head.Par)
    (kap : Phi β → Option Kinds.Head.Law.Seen)
    (Kx : Phi β × Option Pub9 → Prop)
    (t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (l3 : ℕ × String → Phi β × Option Pub9 → ℕ)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β) (nU : Array ℕ) (p : Where) (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (run : ℕ → S → Except String (List Claim × S))
    (x : First.Look.Place) (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData)
    (hc : LinkShare L p → CoreLeft 𝔇 links pl z Rz k m .head L u ψ (fun q => OkHead hS iU3 p6 kap
      nU tlD q ∧ Kx q) nU p (tmH hS iU3 p6 kap entUnit tmFour t3) (lenH hS iU3 p6 kap l3) d N pb
      items (5, "K8.equations") run x tlD set pp sT fd →
      CoreRest2 𝔇 links pl z Rz k m .head L u ψ (fun q => OkHead hS iU3 p6 kap nU tlD q ∧ Kx q) nU
        p (tmH hS iU3 p6 kap entUnit tmFour t3) (lenH hS iU3 p6 kap l3) d N pb items (5,
        "K8.equations") run x tlD set pp sT fd)
    (H : HeadLeft 𝔇 links pl z Rz k m hS iU3 l' piece p6 kap Kx t3 l3 L u ψ nU p d N pb items run x
      tlD set pp sT fd) :
    HeadRest3 𝔇 links pl z Rz k m hS iU3 l' piece p6 kap Kx t3 l3 L u ψ nU p d N pb items run x tlD
      set pp sT fd :=
  headRest3_of_owes 𝔇 links pl z Rz k m hS iU3 l' piece p6 kap Kx t3 l3 L u ψ nU p d N pb items run
    x tlD set pp sT fd H.1
    (hc (share_of_headOwes H.1) H.2)
end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.layersRest3_of_left
#print axioms VerifiableInference.Desc.LinkJoin.attRest3_of_left
#print axioms VerifiableInference.Desc.LinkJoin.headRest3_of_left
