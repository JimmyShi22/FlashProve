-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/KindsBattSend.lean: two kinds of block of a key file's chains, the short batching and
the sending of a family of oracle messages: how their written rounds are read as their typed rounds.



A reading of a file is laid a kind of block at a time, general in the block's caller (`Maps`,
OnBytes/Flat/CarrySMaps.lean). Here, for two of the library's blocks, the list of maps is put
together from one map a round, in the brackets of the block's own list of rounds. That each
definition is accepted by Lean shows that the block's rounds are as many, and of the types, as the
maps say.

Main names:
  `Maps.castT h M`: M with the typed list of rounds replaced along an equation; `ok_castT`,
    `err_castT`, `held_castT`, `heldN_castT`, `view_castT`, `pass_castT`.
  `shortMaps f mk ds`: one short round of a sumcheck for each written round of ds.
  `battMaps B Ex mZ m0 mk ds hk`: the short batching (`Cb.Pv.BattShort.R`): the draw of the
    coefficients' seed, the round of the hiding polynomial's sum, and B.k short rounds; hk: ds has
    B.k rounds. `battMaps_ok`.
  `sendMaps s X E₀ mS mA`: a sending (`Cb.Pv.Send.R`): the words with the joint seed; the answers.
    `sendMaps_ok`.

Limits: the maps of the single rounds are the caller's, and so is that they are as asked. Nothing on
the counts. The sending whose first message bears a rider is not here.
Terms: lean/GLOSSARY.md.
-/
import OnBytes.Flat.CarrySNum
import Cb.Pv.BattShort
import Cb.Pv.Send

set_option autoImplicit false

namespace OnBytes.Flat
open Iop IOR Prob Run OnBytes.Maker OnBytes.Slice Cb Johnson.L5.Layers
open scoped ENNReal

namespace Maps

/-- The maps, with the typed list of rounds replaced along an equation. -/
def castT {ds : List RDT} {s' t' : Shape} (h : s' = t') (M : Maps ds s') : Maps ds t' := h ▸ M

theorem ok_castT {ds : List RDT} {s' t' : Shape} (h : s' = t') {M : Maps ds s'} (hM : M.OK) :
    (M.castT h).OK := by
  subst h
  exact hM

/-- The written counts: those of M at the typed counts carried back. -/
theorem err_castT {ds : List RDT} {s' t' : Shape} (h : s' = t') (M : Maps ds s') (δ : Err t') :
    (M.castT h).err δ = M.err (h ▸ δ) := by
  subst h
  rfl

theorem held_castT {ds : List RDT} {s' t' : Shape} (h : s' = t') {M : Maps ds s'} {δ : Err t'}
    {εs : ℝ≥0∞} (hM : M.Held εs (h ▸ δ)) : (M.castT h).Held εs δ := by
  subst h
  exact hM

theorem heldN_castT {ds : List RDT} {s' t' : Shape} (h : s' = t') {M : Maps ds s'} {δ : Err t'}
    {k : ℕ} (hM : M.HeldN k (h ▸ δ)) : (M.castT h).HeldN k δ := by
  subst h
  exact hM

/-- The image: that of M, carried along. -/
theorem view_castT {ds : List RDT} {s' t' : Shape} (h : s' = t') (M : Maps ds s')
    (τ : Tr (uLT (ckP .two) ds)) : (M.castT h).view τ = h ▸ M.view τ := by
  subst h
  rfl

theorem pass_castT {ds : List RDT} {s' t' : Shape} (h : s' = t') (M : Maps ds s')
    (τ : Tr (uLT (ckP .two) ds)) : (M.castT h).pass τ = M.pass τ := by
  subst h
  rfl

end Maps

section Batt
variable {E : Type} [Field E] [Fintype E]

/-- One short round of a sumcheck for each written round. -/
def shortMaps (f : PFmt E) (mk : ∀ d : RDT, RMap d (sRound f)) :
    (ds : List RDT) → Maps ds (sRounds (List.replicate ds.length f))
  | [] => .nil
  | d :: ds => .step (mk d) (shortMaps f mk ds)

omit [Fintype E] in
theorem shortMaps_ok (f : PFmt E) (mk : ∀ d : RDT, RMap d (sRound f)) :
    ∀ ds : List RDT, (∀ d ∈ ds, (mk d).OK) → (shortMaps f mk ds).OK
  | [], _ => trivial
  | d :: ds, h =>
      ⟨h d List.mem_cons_self, shortMaps_ok f mk ds fun d' hd' => h d' (List.mem_cons_of_mem _ hd')⟩

variable (B : BattPar E) (Ex : ExtSpec) {dZ d0 : RDT} (mZ : RMap dZ (drawRound B.Z.D))
  (m0 : RMap d0 (pRound0 E)) (mk : ∀ d : RDT, RMap d (sRound (pfCube E B.n)))

/-- The block's rounds, where ds has as many rounds as the sumcheck has variables. -/
theorem batt_shape (ds : List RDT) (hk : ds.length = B.k) :
    [drawRound B.Z.D] ++ (pRound0 E :: sRounds (List.replicate ds.length (pfCube E B.n))) =
      (Cb.Pv.BattShort.R B Ex).shape := by
  rw [hk]
  rfl

/-- **The short batching.** -/
noncomputable def battMaps (ds : List RDT) (hk : ds.length = B.k) :
    Maps (dZ :: d0 :: ds) (Cb.Pv.BattShort.R B Ex).shape :=
  Maps.castT (batt_shape B Ex ds hk) (.step mZ (.step m0 (shortMaps (pfCube E B.n) mk ds)))

theorem battMaps_ok (ds : List RDT) (hk : ds.length = B.k) (hZ : mZ.OK) (h0 : m0.OK)
    (h : ∀ d ∈ ds, (mk d).OK) : (battMaps B Ex mZ m0 mk ds hk).OK :=
  Maps.ok_castT _ ⟨hZ, h0, shortMaps_ok _ mk ds h⟩

end Batt

section Send
variable {E : Type} [Field E] (s : Cb.Pv.Send.Size E) (X : Type) (E₀ : ExtSpec) {dS dA : RDT}
  (mS : RMap dS (s.N.sendRound s.Sd)) (mA : RMap dA (Blocks.plainRound s.N.Answ Unit 0))

/-- **A sending**: the words with the joint seed; the answers. -/
noncomputable def sendMaps : Maps [dS, dA] (Cb.Pv.Send.R s X E₀).shape := .step mS (.step mA .nil)

theorem sendMaps_ok (hS : mS.OK) (hA : mA.OK) : (sendMaps s X E₀ mS mA).OK := ⟨hS, hA, trivial⟩

end Send

end OnBytes.Flat
