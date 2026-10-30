-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/LookupCRModel.lean: three callers with riders of the lookup inside a sub-proof: a
layer group's with identity j10, attention's with identity at3, the head's with the two clauses on a
position's cost.

Definitions, statements and proofs. A caller with riders (`LookupCRCaller`,
Johnson/Top/H/LookupCRide.lean) has a family of arrays, each member's cube and each member's choice
of places of the key point. The kind `kLookupCR` states its two joints by `src` ("every array is 0
on its cube") and `tgt` ("the extension of every array is 0 at the chosen places"). This file fills
the family from the model's field relation and restates `src` and `tgt` in that relation's names, so
that the blocks before and behind can meet the joints.
Main names:
  `crHot c D cells`, `crDen c D C cells`, `crLines c lt cells req`: the three callers over a caller
    c. `cells` and `req` are free letters: how the cells, and what the head reads of the request and
    the policy, are read off the state and the committed messages of c.
  `crHot_src`, `crDen_src`, `crLines_src`: `src` is the clause of the relation at every valid index.
  `crHot_tgt`, `crDen_tgt`, `crLines_tgt`: `tgt` is the equation at the key point.
  `crHot_sel`, `crDen_sel`, `crLines_sel`: the choices are lawful: what `SelLookupCR` asks.
  `lookupCR_three`: at a list of the three callers, every block of the kind has `KnowAt`
    (`lookupCR_knowAt`), from the test `FoNums.ok` at the three records and the three conditions on
    sizes.
Limits: c, its joint R0, `cells` and `req` are free. If R0 gives the clause, the statements on
`kLookupCR` at these callers say nothing of the choice (`Cb.Rider.forB_hollow`): R0 has to be
without it. No caller is given whose data are a sub-proof's own. Nothing on whether the programs
test these equations, on whether a later block takes them up, or on an honest prover.
-/
import Johnson.Top.H.LookupCRide
import OnBytes.Tie.Pv.Lookup.Rider.Model.OneHot
import OnBytes.Tie.Pv.Lookup.Rider.Model.Denom
import OnBytes.Tie.Pv.Lookup.Rider.Model.TwoLines

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open Cb Blocks Cb.LdLkp Cb.LdLkp.Kn Cb.Fo Cb.Rider Inst.Model

/-! ### a layer group's lookup with j10 -/

section Hot
variable [scl : Scl] (c : LookupCCaller) (D : FFSeg.Dim)
  (cells : c.St₀ → c.Sg.Msg → FFSeg.Cell → Cb.Gl.E)

/-- The caller c with j10, tested at the last D.lT places of the first part of the key point. -/
def crHot : LookupCRCaller :=
  ⟨c, Fin D.ne, fun _ => D.lT, fun _ t => c.h.dT - D.lT + t, hotFam D cells⟩

theorem crHot_sel (hlt : D.lT ≤ c.h.dT) :
    SelIn (FoNums.v' c.h) (crHot c D cells).g (crHot c D cells).sel := selIn_last c.h hlt

theorem crHot_src (m : c.Sg.Msg) (a : c.St₀ × c.Ex.Str) :
    (crHot c D cells).src m a ↔
      ∀ (emb : ℕ → ℕ → Cb.Gl.E) (tok : ℕ → ℕ) (first : Bool) (l i : ℕ),
        (FFSeg.Idn.j10 l i).Valid D first →
          FFSeg.idnVal D (cells a.1 m) emb tok (.j10 l i) = 0 :=
  hot_source D cells a.1 m

theorem crHot_tgt (hlt : D.lT ≤ c.h.dT) (m : c.Sg.Msg)
    (b : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) × c.Ex.Str) :
    (crHot c D cells).tgt m b ↔
      ∀ l, l < D.ne →
        ext D.lT
          (fun i => FFSeg.idnVal D (cells b.1.1.1 m) (fun _ _ => 0) (fun _ => 0) (.j10 l i))
          (ofList (outZt c.h D.lT b.1)) = 0 :=
  hot_target_zt c.h D hlt cells b.1.1.1 b.1 m

end Hot

/-! ### attention's lookup with at3 -/

section Den
variable (c : LookupCCaller) (D : AttSeg.Dim) (C : AttSeg.Calls)
  (cells : c.St₀ → c.Sg.Msg → AttSeg.Raw → Cb.Gl.E)

/-- The caller c with at3, tested at the pick of the key point of call 2. -/
def crDen : LookupCRCaller :=
  ⟨c, Unit, fun _ => C.a 2 - D.lW + D.lg + D.lT,
    fun _ => selAtt C.Dk C.sg (C.e 2) (C.a 2 - D.lW), denFam D cells⟩

theorem crDen_sel (F : AttFits c.h D C) :
    SelIn (FoNums.v' c.h) (crDen c D C cells).g (crDen c D C cells).sel := den_sel F

theorem crDen_src (F : AttFits c.h D C) (m : c.Sg.Msg) (a : c.St₀ × c.Ex.Str) :
    (crDen c D C cells).src m a ↔
      ∀ b g i, AttSeg.Idn.Valid D (.at3 b g i) →
        AttSeg.idnVal D (cells a.1 m) (.at3 b g i) = 0 :=
  den_source D cells F.nb a.1 m

theorem crDen_tgt (F : AttFits c.h D C) (m : c.Sg.Msg)
    (b : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) × c.Ex.Str) :
    (crDen c D C cells).tgt m b ↔ Cb.Pv.Att.denOut D C b.1.2.1.pt (cells b.1.1.1 m) = 0 :=
  den_target_out F.e2 F.nb cells b.1.1.1 b.1.2.1.pt m

end Den

/-! ### the head's lookup with the two clauses on a position's cost -/

section Lines
variable (c : LookupCCaller) (lt : ℕ) (cells : c.St₀ → c.Sg.Msg → Head.Cells Cb.Gl.E)
  (req : c.St₀ → Head.Req)

/-- The caller c with the two clauses, tested at the last lt places of the first part of the key
point. -/
def crLines : LookupCRCaller :=
  ⟨c, Fin 2, fun _ => lt, fun _ t => c.h.dT - lt + t, twoFam cells req⟩

theorem crLines_sel (hlt : lt ≤ c.h.dT) :
    SelIn (FoNums.v' c.h) (crLines c lt cells req).g (crLines c lt cells req).sel :=
  selIn_last c.h hlt

theorem crLines_src (m : c.Sg.Msg) (a : c.St₀ × c.Ex.Str) :
    (crLines c lt cells req).src m a ↔ Cb.Pv.Head.LinesAll (cells a.1 m) (req a.1) lt :=
  two_source cells req lt a.1 m

theorem crLines_tgt (hlt : lt ≤ c.h.dT) (m : c.Sg.Msg)
    (b : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) × c.Ex.Str) :
    (crLines c lt cells req).tgt m b ↔
      Cb.Pv.Head.LinesAtPt (cells b.1.1.1 m) (req b.1.1.1) lt (ofList (outZt c.h lt b.1)) :=
  two_target_zt c.h hlt cells req b.1.1.1 b.1 m

end Lines

/-! ### the three together -/

/-- All four facts of a block, at a list of the three callers: from the test on the three records of
public numbers and the three conditions on sizes. -/
theorem lookupCR_three [scl : Scl] (c₁ c₂ c₃ : LookupCCaller) (D₁ : FFSeg.Dim)
    (cells₁ : c₁.St₀ → c₁.Sg.Msg → FFSeg.Cell → Cb.Gl.E) (D₂ : AttSeg.Dim) (C₂ : AttSeg.Calls)
    (cells₂ : c₂.St₀ → c₂.Sg.Msg → AttSeg.Raw → Cb.Gl.E) (lt : ℕ)
    (cells₃ : c₃.St₀ → c₃.Sg.Msg → Head.Cells Cb.Gl.E) (req₃ : c₃.St₀ → Head.Req)
    (o₁ : FoNums.ok c₁.h = true) (o₂ : FoNums.ok c₂.h = true) (o₃ : FoNums.ok c₃.h = true)
    (h₁ : D₁.lT ≤ c₁.h.dT) (F : AttFits c₂.h D₂ C₂) (h₃ : lt ≤ c₃.h.dT) :
    (kLookupCR
      [crHot c₁ D₁ cells₁, crDen c₂ D₂ C₂ cells₂, crLines c₃ lt cells₃ req₃]).KnowAtAll := by
  refine lookupCR_knowAt _ ?_ ?_
  · intro c hc
    simp only [callersCR, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact o₁
    · exact o₂
    · exact o₃
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact crHot_sel c₁ D₁ cells₁ h₁
    · exact crDen_sel c₂ D₂ C₂ cells₂ F
    · exact crLines_sel c₃ lt cells₃ req₃ h₃

#print axioms VerifiableInference.OnPublicFiles.lookupCR_three
#print axioms VerifiableInference.OnPublicFiles.crHot_src
#print axioms VerifiableInference.OnPublicFiles.crHot_tgt
#print axioms VerifiableInference.OnPublicFiles.crDen_src
#print axioms VerifiableInference.OnPublicFiles.crDen_tgt
#print axioms VerifiableInference.OnPublicFiles.crLines_src
#print axioms VerifiableInference.OnPublicFiles.crLines_tgt

end VerifiableInference.OnPublicFiles
