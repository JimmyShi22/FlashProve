-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/CarrySProx.lean: how the written rounds of a proximity test are read as the typed
rounds of its blocks, kind by kind, and the whole test as one stretch.

A proximity test is: one round that batches; stages, each a fold and a code switch; a last step. The
typed rounds are those of the blocks' shapes: the batching `[drawRound Ch]`; a fold whose mask was
sent earlier `plainRound GE Ch 0 :: replicate k (sRoundS GE Ch n)` (Cb/Ent/FoldShort.lean); a switch
`[r₁, plainRound (S → GE) C₂ 0]`, r₁ the caller's round that sends the new word; the last step
`[plainRound GE C₁ 0, plainRound MR C₂ z]`. A caller's type of verifier messages enters through a
map ι from the plain reading of what the round draws (OnBytes/Flat/CarrySForms.lean); a caller's
names of answers through a numbering. Definitions and proofs.

Main names:
  `sentT d m i`: element number i that the written prover message m sends, in the field.
  `Maps.bat`, `foldT`, `foldRide`, `cs`, `base`, each with `…_ok`.
  `StageR`: the data of a stage's reading; `StageR.ds`, `sh`, `maps`, `OK`, `maps_ok`.
  `towDs`, `towSh`, `Maps.tower`, `tower_ok`: stages in a row, nested to the right, before a last
    stretch.
  `Maps.test`, `test_ok`: the batching round, then the tower.
Limits: it is not shown that a chain's written rounds send and draw so (`SendsDraws` at a value),
nor that a block's shape is the typed list here. How the new word is read off the written oracles
(the map of prover messages into r₁) and how the last step's message is read are the caller's.
Nothing on what a verifier accepts.
-/
import OnBytes.Flat.CarrySForms
import OnBytes.Slice.CorePeel
import Cb.Ent.FoldShort

set_option autoImplicit false

namespace OnBytes.Flat
open Iop Prob Run OnBytes.Maker OnBytes.Slice Cb Blocks

/-- Element number i that a written prover message sends, in the field; 0 beyond the end. -/
def sentT (d : RDT) (m : (wT d).Msg) (i : ℕ) : GE := (ansOf (toRD d) (msgRD d m)).getD i 0

namespace Maps

section Kinds
variable {Ch : Type} [Fintype Ch] [Nonempty Ch]

/-- The batching round: nothing is sent; one element is drawn. -/
def bat (d : RDT) (ι : GE → Ch) : Maps [d] [IOR.drawRound Ch] :=
  .step (RMap.one (fun _ => ((), ())) ι) .nil

theorem bat_ok (d : RDT) {ι : GE → Ch} (hι : Function.Injective ι) {ns a : ℕ}
    (h : SendsDraws (toRD d) ns 1 0 a) : (bat d ι).OK := ⟨RMap.one_ok _ h hι, trivial⟩

/-- k rounds of the short sumcheck: n coefficients are sent; one element is drawn. -/
def foldT (d : RDT) (n : ℕ) (ι : GE → Ch) :
    (k : ℕ) → Maps (List.replicate k d) (List.replicate k (sRoundS GE Ch n))
  | 0 => .nil
  | k + 1 => .step (RMap.one (fun m => ((), fun t : Fin n => sentT d m t.val)) ι) (foldT d n ι k)

theorem foldT_ok (d : RDT) (n : ℕ) {ι : GE → Ch} (hι : Function.Injective ι) {ns a : ℕ}
    (h : SendsDraws (toRD d) ns 1 0 a) : ∀ k, (foldT d n ι k).OK
  | 0 => trivial
  | k + 1 => ⟨RMap.one_ok _ h hι, foldT_ok d n hι h k⟩

/-- A fold whose mask was sent earlier: the mask's sum and one element; then the k rounds. -/
def foldRide (dE dT : RDT) (n k : ℕ) (ι : GE → Ch) :
    Maps (dE :: List.replicate k dT) (plainRound GE Ch 0 :: List.replicate k (sRoundS GE Ch n)) :=
  .step (RMap.one (fun m => ((), sentT dE m 0)) ι) (foldT dT n ι k)

theorem foldRide_ok (dE dT : RDT) (n k : ℕ) {ι : GE → Ch} (hι : Function.Injective ι)
    {nE aE nT aT : ℕ} (hE : SendsDraws (toRD dE) nE 1 0 aE) (hT : SendsDraws (toRD dT) nT 1 0 aT) :
    (foldRide dE dT n k ι).OK := ⟨RMap.one_ok _ hE hι, foldT_ok dT n hι hT k⟩

end Kinds

/-- A code switch: the new word and the sample's seed; the answers, one element and t positions. -/
noncomputable def cs (dS dC : RDT) (r₁ : Round) (fm₁ : (wT dS).Msg → r₁.Msg) (na : ℕ)
    (ι₁ : (Fin na → GE) × GEˣ → r₁.Chal) {S C₂ : Type} [Fintype C₂] [Nonempty C₂] (ix : S → ℕ)
    (a t : ℕ) (ι₂ : (Fin 1 → GE) × (Fin t → Fin (2 ^ a)) → C₂) :
    Maps [dS, dC] [r₁, plainRound (S → GE) C₂ 0] :=
  .step (RMap.seed fm₁ na ι₁)
    (.step (RMap.mix (fun m => ((), fun s => sentT dC m (ix s))) 1 a t ι₂) .nil)

theorem cs_ok (dS dC : RDT) (r₁ : Round) (fm₁ : (wT dS).Msg → r₁.Msg) (na : ℕ)
    {ι₁ : (Fin na → GE) × GEˣ → r₁.Chal} (h₁ : Function.Injective ι₁) {S C₂ : Type} [Fintype C₂]
    [Nonempty C₂] (ix : S → ℕ) (a t : ℕ) {ι₂ : (Fin 1 → GE) × (Fin t → Fin (2 ^ a)) → C₂}
    (h₂ : Function.Injective ι₂) {nS aS nC : ℕ} (hS : SendsDraws (toRD dS) nS (na + 1) 0 aS)
    (hz : IsNZ (Fmt.dsOf dS.entry dS.kind) na) (hC : SendsDraws (toRD dC) nC 1 t a) :
    (cs dS dC r₁ fm₁ na ι₁ ix a t ι₂).OK :=
  ⟨RMap.seed_ok _ hS.plain hS.els hS.poss hz hS.logN h₁, RMap.mix_ok _ hC h₂, trivial⟩

/-- The last step: one element and one element; the shown message and t positions. -/
def base (dL dB : RDT) {C₁ MR C₂ : Type} [Fintype C₁] [Nonempty C₁] [Fintype C₂] [Nonempty C₂]
    (ι₁ : GE → C₁) (z : MR) (fs : (wT dB).Msg → MR) (a t : ℕ) (ι₂ : (Fin t → Fin (2 ^ a)) → C₂) :
    Maps [dL, dB] [plainRound GE C₁ 0, plainRound MR C₂ z] :=
  .step (RMap.one (fun m => ((), sentT dL m 0)) ι₁)
    (.step (RMap.pos (fun m => ((), fs m)) a t ι₂) .nil)

theorem base_ok (dL dB : RDT) {C₁ MR C₂ : Type} [Fintype C₁] [Nonempty C₁] [Fintype C₂]
    [Nonempty C₂] {ι₁ : GE → C₁} (h₁ : Function.Injective ι₁) (z : MR) (fs : (wT dB).Msg → MR)
    (a t : ℕ) {ι₂ : (Fin t → Fin (2 ^ a)) → C₂} (h₂ : Function.Injective ι₂) {nL aL nB : ℕ}
    (hL : SendsDraws (toRD dL) nL 1 0 aL) (hB : SendsDraws (toRD dB) nB 0 t a) :
    (base dL dB ι₁ z fs a t ι₂).OK := ⟨RMap.one_ok _ hL h₁, RMap.pos_ok _ hB h₂, trivial⟩

end Maps

/-- The data of a stage's reading. -/
structure StageR : Type 1 where
  dE : RDT
  dT : RDT
  dS : RDT
  dC : RDT
  n : ℕ
  k : ℕ
  na : ℕ
  a : ℕ
  t : ℕ
  Ch : Type
  [finCh : Fintype Ch]
  [neCh : Nonempty Ch]
  ι : GE → Ch
  r₁ : Round
  fm₁ : (wT dS).Msg → r₁.Msg
  ι₁ : (Fin na → GE) × GEˣ → r₁.Chal
  S : Type
  C₂ : Type
  [finC₂ : Fintype C₂]
  [neC₂ : Nonempty C₂]
  ix : S → ℕ
  ι₂ : (Fin 1 → GE) × (Fin t → Fin (2 ^ a)) → C₂

attribute [instance] StageR.finCh StageR.neCh StageR.finC₂ StageR.neC₂

namespace StageR
variable (s : StageR)

/-- The stage's written rounds. -/
def ds : List RDT := (s.dE :: List.replicate s.k s.dT) ++ [s.dS, s.dC]

/-- Its typed rounds. -/
def sh : Shape :=
  (plainRound GE s.Ch 0 :: List.replicate s.k (sRoundS GE s.Ch s.n)) ++
    [s.r₁, plainRound (s.S → GE) s.C₂ 0]

/-- The reading. -/
noncomputable def maps : Maps s.ds s.sh :=
  (Maps.foldRide s.dE s.dT s.n s.k s.ι).app
    (Maps.cs s.dS s.dC s.r₁ s.fm₁ s.na s.ι₁ s.ix s.a s.t s.ι₂)

/-- What is asked: the three maps are one-to-one; the four rounds send and draw as a stage's. -/
structure OK : Prop where
  ι : Function.Injective s.ι
  ι₁ : Function.Injective s.ι₁
  ι₂ : Function.Injective s.ι₂
  eps : ∃ ns a, SendsDraws (toRD s.dE) ns 1 0 a
  two : ∃ ns a, SendsDraws (toRD s.dT) ns 1 0 a
  seed : ∃ ns a, SendsDraws (toRD s.dS) ns (s.na + 1) 0 a
  nz : IsNZ (Fmt.dsOf s.dS.entry s.dS.kind) s.na
  cs : ∃ ns, SendsDraws (toRD s.dC) ns 1 s.t s.a

theorem maps_ok (h : s.OK) : s.maps.OK := by
  obtain ⟨_, _, hE⟩ := h.eps
  obtain ⟨_, _, hT⟩ := h.two
  obtain ⟨_, _, hS⟩ := h.seed
  obtain ⟨_, hC⟩ := h.cs
  exact Maps.OK.app (Maps.foldRide_ok _ _ _ _ h.ι hE hT)
    (Maps.cs_ok _ _ _ _ _ h.ι₁ _ _ _ h.ι₂ hS h.nz hC)

end StageR

/-- The written rounds of stages in a row, before the rounds b. -/
def towDs : List StageR → List RDT → List RDT
  | [], b => b
  | s :: l, b => s.ds ++ towDs l b

/-- Their typed rounds, nested to the right, before the rounds b. -/
def towSh : List StageR → Shape → Shape
  | [], b => b
  | s :: l, b => s.sh ++ towSh l b

namespace Maps

/-- Stages in a row, then a last stretch. -/
noncomputable def tower {bd : List RDT} {bs : Shape} (B : Maps bd bs) :
    (l : List StageR) → Maps (towDs l bd) (towSh l bs)
  | [] => B
  | s :: l => s.maps.app (tower B l)

theorem tower_ok {bd : List RDT} {bs : Shape} {B : Maps bd bs} (hB : B.OK) :
    ∀ l : List StageR, (∀ s ∈ l, s.OK) → (tower B l).OK
  | [], _ => hB
  | s :: l, h => OK.app (s.maps_ok (h s List.mem_cons_self))
      (tower_ok hB l fun s' hs' => h s' (List.mem_cons_of_mem _ hs'))

/-- A whole test: the batching round, then the tower. -/
noncomputable def test {Ch : Type} [Fintype Ch] [Nonempty Ch] (d : RDT) (ι : GE → Ch)
    {bd : List RDT} {bs : Shape} (B : Maps bd bs) (l : List StageR) :
    Maps ([d] ++ towDs l bd) ([IOR.drawRound Ch] ++ towSh l bs) :=
  (bat d ι).app (tower B l)

theorem test_ok {Ch : Type} [Fintype Ch] [Nonempty Ch] (d : RDT) {ι : GE → Ch}
    (hι : Function.Injective ι) {ns a : ℕ} (h : SendsDraws (toRD d) ns 1 0 a) {bd : List RDT}
    {bs : Shape} {B : Maps bd bs} (hB : B.OK) (l : List StageR) (hl : ∀ s ∈ l, s.OK) :
    (test d ι B l).OK := OK.app (bat_ok d hι h) (tower_ok hB l hl)

end Maps

end OnBytes.Flat

#print axioms OnBytes.Flat.Maps.cs_ok
#print axioms OnBytes.Flat.Maps.base_ok
#print axioms OnBytes.Flat.StageR.maps_ok
#print axioms OnBytes.Flat.Maps.test_ok
