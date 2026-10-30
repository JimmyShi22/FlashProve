-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/SortLeftC.lean: ON THE SECOND ROAD: BENEATH THE THREE LISTS OF
WHAT IS LEFT OF A LINK's LAW AT THE SORT's CHOSEN LETTERS (`LayersRest3C`, `AttRest3C`,
`HeadRest3C`, LinkRestAtSort3C.lean): EACH CUT IN TWO (`LayersOwesC`, `AttOwesC`,
`HeadOwesC`, LinkRestAtSort4C.lean: the sort's own fields), ITS FIELD core (`CoreRest2C`) GIVEN WAY
TO WHAT IS LEFT OF IT (`CoreLeftC`, CoreLeftC.lean). Three definitions and three theorems, written
by program from these lists' own heads.

What is said.
  `LayersLeftC …` := `LayersOwesC` at the sort's letters AND `CoreLeftC` at its core letters.
    `AttLeftC`, `HeadLeftC`: the like. `layersRest3C_of_left`, `attRest3C_of_left`,
    `headRest3C_of_left`: **the sort's list from it and a road from `CoreLeftC` to `CoreRest2C` that
    may spend the runs' share of the link** (which comes off the own fields: `share_of_layersOwesC`
    and its like).

Limits. BOOK-KEEPING. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkRestAtSort4C
import Johnson.Desc.First.Link.Law.CoreLeftC

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
def LayersLeftC (p4 : OnBytes.Desc.First.K4.Par)
    (Kx : Phi β × Option Pub9 → Prop)
    (t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (l3 : ℕ × String → Phi β × Option Pub9 → ℕ)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β) (nU : Array ℕ) (p : Where) (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (run : ℕ → S → Except String (List Claim × S))
    (x : First.Look.Place) (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData) : Prop :=
  LayersOwesC m p4 Kx t3 l3 L u ψ nU p tlD ∧
  CoreLeftC 𝔇 links pl z Rz k m .layers L u ψ (fun q => OkLayers p4 nU tlD q ∧ Kx q) nU p (tmL p4
    entUnit tmFour t3) (lenL p4 l3) d N pb items (4, "K8.equations") run x tlD set pp sT fd

theorem layersRest3C_of_left (p4 : OnBytes.Desc.First.K4.Par)
    (Kx : Phi β × Option Pub9 → Prop)
    (t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (l3 : ℕ × String → Phi β × Option Pub9 → ℕ)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β) (nU : Array ℕ) (p : Where) (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (run : ℕ → S → Except String (List Claim × S))
    (x : First.Look.Place) (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData)
    (hc : LinkShare L p → CoreLeftC 𝔇 links pl z Rz k m .layers L u ψ (fun q => OkLayers p4 nU tlD
      q ∧ Kx q) nU p (tmL p4 entUnit tmFour t3) (lenL p4 l3) d N pb items (4, "K8.equations") run x
      tlD set pp sT fd →
      CoreRest2C 𝔇 links pl z Rz k m .layers L u ψ (fun q => OkLayers p4 nU tlD q ∧ Kx q) nU p (tmL
        p4 entUnit tmFour t3) (lenL p4 l3) d N pb items (4, "K8.equations") run x tlD set pp sT fd)
    (H : LayersLeftC 𝔇 links pl z Rz k m p4 Kx t3 l3 L u ψ nU p d N pb items run x tlD set pp sT
      fd) :
    LayersRest3C 𝔇 links pl z Rz k m p4 Kx t3 l3 L u ψ nU p d N pb items run x tlD set pp sT fd :=
  layersRest3C_of_owes 𝔇 links pl z Rz k m p4 Kx t3 l3 L u ψ nU p d N pb items run x tlD set pp sT
    fd H.1
    (hc (share_of_layersOwesC H.1) H.2)

/-- **WHAT IS LEFT AT AN ATTENTION LINK**: the sort's own fields, and what is left of the core. -/
def AttLeftC (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard))
    (c : First.Att.P.ParC)
    (Kx : Phi β × Option Pub9 → Prop)
    (t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (l3 : ℕ × String → Phi β × Option Pub9 → ℕ)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β) (nU : Array ℕ) (p : Where) (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (run : ℕ → S → Except String (List Claim × S))
    (x : First.Look.Place) (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData) : Prop :=
  AttOwesC m rd c Kx t3 l3 L u ψ nU p tlD ∧
  CoreLeftC 𝔇 links pl z Rz k m .attention L u ψ (fun q => OkAtt rd c nU tlD q ∧ Kx q) nU p (tmA rd
    c entUnit tmFour t3) (lenA rd c l3) d N pb items (4, "K8.equations") run x tlD set pp sT fd

theorem attRest3C_of_left (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard))
    (c : First.Att.P.ParC)
    (Kx : Phi β × Option Pub9 → Prop)
    (t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (l3 : ℕ × String → Phi β × Option Pub9 → ℕ)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β) (nU : Array ℕ) (p : Where) (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (run : ℕ → S → Except String (List Claim × S))
    (x : First.Look.Place) (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData)
    (hc : LinkShare L p → CoreLeftC 𝔇 links pl z Rz k m .attention L u ψ (fun q => OkAtt rd c nU
      tlD q ∧ Kx q) nU p (tmA rd c entUnit tmFour t3) (lenA rd c l3) d N pb items (4,
      "K8.equations") run x tlD set pp sT fd →
      CoreRest2C 𝔇 links pl z Rz k m .attention L u ψ (fun q => OkAtt rd c nU tlD q ∧ Kx q) nU p
        (tmA rd c entUnit tmFour t3) (lenA rd c l3) d N pb items (4, "K8.equations") run x tlD set
        pp sT fd)
    (H : AttLeftC 𝔇 links pl z Rz k m rd c Kx t3 l3 L u ψ nU p d N pb items run x tlD set pp sT fd)
      :
    AttRest3C 𝔇 links pl z Rz k m rd c Kx t3 l3 L u ψ nU p d N pb items run x tlD set pp sT fd :=
  attRest3C_of_owes 𝔇 links pl z Rz k m rd c Kx t3 l3 L u ψ nU p d N pb items run x tlD set pp sT
    fd H.1
    (hc (share_of_attOwesC H.1) H.2)

/-- **WHAT IS LEFT AT THE HEAD'S LINK**: the sort's own fields, and what is left of the core. -/
def HeadLeftC (hS : OnBytes.Model.Head.Shape) (iU3 l' piece : ℕ) (p6 : Kinds.Head.Par)
    (kap : Phi β → Option Kinds.Head.Law.Seen)
    (Kx : Phi β × Option Pub9 → Prop)
    (t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (l3 : ℕ × String → Phi β × Option Pub9 → ℕ)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β) (nU : Array ℕ) (p : Where) (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (run : ℕ → S → Except String (List Claim × S))
    (x : First.Look.Place) (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData) : Prop :=
  HeadOwesC m hS iU3 l' piece p6 kap Kx t3 l3 L u ψ nU p tlD ∧
  CoreLeftC 𝔇 links pl z Rz k m .head L u ψ (fun q => OkHead hS iU3 p6 kap nU tlD q ∧ Kx q) nU p
    (tmH hS iU3 p6 kap entUnit tmFour t3) (lenH hS iU3 p6 kap l3) d N pb items (5, "K8.equations")
    run x tlD set pp sT fd

theorem headRest3C_of_left (hS : OnBytes.Model.Head.Shape) (iU3 l' piece : ℕ) (p6 : Kinds.Head.Par)
    (kap : Phi β → Option Kinds.Head.Law.Seen)
    (Kx : Phi β × Option Pub9 → Prop)
    (t3 : ℕ × String → ℕ → Phi β × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (l3 : ℕ × String → Phi β × Option Pub9 → ℕ)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β) (nU : Array ℕ) (p : Where) (d N : ℕ)
    (pb : Piece (ckP .two) F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (items : List (ℕ × String)) (run : ℕ → S → Except String (List Claim × S))
    (x : First.Look.Place) (tlD : HTailF2) (set : Params.Setting) (pp : ℕ)
    (sT : Fin (digList x 𝔇.sent 𝔇.l3.rad).length → ℕ × ℕ) (fd : FoldData)
    (hc : LinkShare L p → CoreLeftC 𝔇 links pl z Rz k m .head L u ψ (fun q => OkHead hS iU3 p6 kap
      nU tlD q ∧ Kx q) nU p (tmH hS iU3 p6 kap entUnit tmFour t3) (lenH hS iU3 p6 kap l3) d N pb
      items (5, "K8.equations") run x tlD set pp sT fd →
      CoreRest2C 𝔇 links pl z Rz k m .head L u ψ (fun q => OkHead hS iU3 p6 kap nU tlD q ∧ Kx q) nU
        p (tmH hS iU3 p6 kap entUnit tmFour t3) (lenH hS iU3 p6 kap l3) d N pb items (5,
        "K8.equations") run x tlD set pp sT fd)
    (H : HeadLeftC 𝔇 links pl z Rz k m hS iU3 l' piece p6 kap Kx t3 l3 L u ψ nU p d N pb items run
      x tlD set pp sT fd) :
    HeadRest3C 𝔇 links pl z Rz k m hS iU3 l' piece p6 kap Kx t3 l3 L u ψ nU p d N pb items run x
      tlD set pp sT fd :=
  headRest3C_of_owes 𝔇 links pl z Rz k m hS iU3 l' piece p6 kap Kx t3 l3 L u ψ nU p d N pb items
    run x tlD set pp sT fd H.1
    (hc (share_of_headOwesC H.1) H.2)
end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.layersRest3C_of_left
#print axioms VerifiableInference.Desc.LinkJoin.attRest3C_of_left
#print axioms VerifiableInference.Desc.LinkJoin.headRest3C_of_left
