-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/E/KObj/Obj.lean: an object made of four typed lists of bare blocks and one batch test, and
the five knowledge-soundness items of its sub-protocols from the blocks' properties.

The lists stand between the joints that the five items of `SubsR.HypK` name (Hiop/RecSubs.lean,
Hiop/RecBuild.lean): weights-formedness, the test at one instance, the link, a request. The test at
N instances is one letter (a `BIOP`). The honest sides are letters of which nothing is asked
(`SubsR` holds them as data). Definitions and proofs. No library file turns.
Main names:
  `LK.HandsL`, `LK.hands`: along a list each block hands a record and an encoded index on.
  `jWf`, `jLin`, `jLink`, `jReq`, `jEnd`: the joints.
  `Obj`: the object: a configuration, what the two preambles leave, the number of slots, the four
    lists, the batch test with its errors. `Obj.Hon`: the honest sides.
  `Obj.S`, `Obj.P`: the five sub-protocols and their numbers in which the object ends.
  `Obj.Blocks`: the hypotheses: every block of the four lists has its property; the batch test has
    its item, is local and coherent; the request's blocks hand record and encoded index on.
  `Obj.hypK`: `Obj.Blocks` ⇒ `(O.S H).HypK (O.P H)`. `Obj.passes`, `Obj.copy`, `Obj.locals`,
    `Obj.points`: the other facts on the verifiers.
Limits: nothing here says that `Obj.Blocks` holds of any object, or that an object is the protocol
that any program runs. Nothing on completeness or on zero knowledge.

-/
import Johnson.E.KObj.Blocks
import Hiop.RecBuild

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj
open Iop Prob Hiop
open scoped ENNReal

/-! ### what is handed on along a list -/

/-- along a list: at every joint between two blocks there is a reading, and each block hands both
parts on -/
def LK.HandsL {T U : Type} : {A B : JK} → LK A B → Rd T U A → Rd T U B → Prop
  | _, _, .one b, ρ, θ => b.Hands ρ θ
  | _, _, .snoc l b, ρ, θ => ∃ σ, l.HandsL ρ σ ∧ b.Hands σ θ

theorem LK.hands {T U : Type} {A B : JK} (l : LK A B) (d : A.W) (ρ : Rd T U A) :
    ∀ θ : Rd T U B, l.HandsL ρ θ → (l.blk d).Hands ρ θ := by
  induction l with
  | one b =>
    intro θ h
    rw [LK.blk_one]
    rw [LK.HandsL] at h
    exact h
  | snoc l b ih =>
    intro θ h
    rw [LK.blk_snoc]
    rw [LK.HandsL] at h
    obtain ⟨σ, h1, h2⟩ := h
    exact BK.hands_seq _ b d ρ σ θ (ih σ h1) h2

/-! ### the joints that the five items name -/

section
variable (C : ConfigurationWithOutOfDomainSample)

/-- before weights-formedness: a record and an encoded index without a collision; relaxed: the
index decodes -/
@[reducible] def jWf : JK := ⟨C.Rec, C.E0, Unit, C.free, C.RwfR⟩
/-- what a preamble leaves: the constraint relation's relaxation, on collision-free statements -/
@[reducible] def jLin (S : C.Left) : JK := ⟨S.Xl × C.Rec, S.El, S.AMsg, S.cond, S.RlinR⟩
/-- two encoded indices -/
@[reducible] def jLink : JK := ⟨C.Rec × C.Rec, twoExternalStrings C.n C.Sg, Unit, C.onEq, C.ReqR⟩
/-- a request: on statements whose index decoder answers; relaxed: the cells -/
@[reducible] def jReq : JK :=
  ⟨C.X × C.Rec, C.E0, C.Cells, fun a => (C.D a.2 a.1.2).isSome, C.RreqR⟩
end

/-- the end: nothing is left -/
@[reducible] def jEnd : JK := ⟨Unit, extNone, Unit, fun _ => True, fun _ _ => True⟩

/-- THE OBJECT AT LETTERS: the verifier's side -/
structure Obj : Type 1 where
  C      : ConfigurationWithOutOfDomainSample
  off    : C.Left
  on     : C.Left
  N      : ℕ
  wf     : LK (jWf C) (jLin C off)
  linOff : LK (jLin C off) jEnd
  link   : LK (jLink C) jEnd
  req    : LK (jReq C) (jLin C on)
  linOn  : BIOP (on.Xl × C.Rec) on.El
  errOn  : Err linOn.ior.shape
  dOff   : off.AMsg
  dOn    : on.AMsg

namespace Obj
variable (O : Obj)

/-- the four lists' one block each -/
noncomputable abbrev bWf := O.wf.blk ()
noncomputable abbrev bLinOff := O.linOff.blk O.dOff
noncomputable abbrev bLink := O.link.blk ()
noncomputable abbrev bReq := O.req.blk O.C.cells0

/-- the honest sides: letters of which nothing is asked -/
structure Hon where
  hWf     : O.bWf.R.Honest O.C.PIdx (O.C.PIdx × O.off.WAux)
  hLinOff : O.bLinOff.R.Honest (O.C.PIdx × O.off.WAux) Unit
  hLink   : O.bLink.R.Honest (O.C.PIdx × O.C.PIdx) Unit
  hReq    : O.bReq.R.Honest (O.C.PIdx × O.C.Cells) (O.C.PIdx × O.on.WAux)
  hLinOn  : O.linOn.Honest O.C.PIdx O.on.WAux

/-- THE FIVE SUB-PROTOCOLS -/
@[reducible] noncomputable def S (H : O.Hon) : SubsR O.C where
  off := O.off
  on := O.on
  N := O.N
  wf := O.bWf.R
  linOff := O.bLinOff.R
  link := O.bLink.R
  req := O.bReq.R
  linOn := O.linOn
  cellsOf := O.bReq.ext
  hWf := H.hWf
  hLinOff := H.hLinOff
  hLink := H.hLink
  hReq := H.hReq
  hLinOn := H.hLinOn
  dOff := O.dOff
  dOn := O.dOn

/-- THE NUMBERS: the lists' errors in a row; the honest side's numbers: idle -/
@[reducible] noncomputable def P (H : O.Hon) : (O.S H).Nums where
  wf := ⟨O.bWf.err, 0, 0, fun _ _ => True⟩
  linOff := ⟨O.bLinOff.err, 0, 0, fun _ _ => True⟩
  link := ⟨O.bLink.err, 0, 0, 0, fun _ _ => True⟩
  req := ⟨O.bReq.err, 0, 0, fun _ _ => True⟩
  linOn := ⟨O.errOn, 0, 0, fun _ _ _ => True⟩

/-- THE NAMED HYPOTHESES: every block of the four lists has its property; the batch test has its
item, is local, coherent -/
structure Blocks : Prop where
  wf      : O.wf.Each PG
  linOff  : O.linOff.Each PG
  link    : O.link.Each PG
  req     : O.req.Each PG
  linOn   : LinBKnowR O.on O.linOn O.N O.dOn O.errOn
  localOn : O.linOn.ior.IsLocal
  cohOn   : O.linOn.ann.Coherent
  /-- the request's blocks hand the record and the encoded index on -/
  hands   : O.req.HandsL (T := O.C.Rec) (U := O.C.E0.Str) ⟨Prod.snd, id⟩ ⟨Prod.snd, Prod.fst⟩

variable {O}

/-- (8) THE FIVE ITEMS -/
theorem hypK (H : O.Hon) (h : O.Blocks) : (O.S H).HypK (O.P H) where
  wf := (O.wf.good () h.wf).know
  linOff := by
    have g := (know_of_knowInto _ _ _ _ _ _ _ _ _ _).1 (O.linOff.good O.dOff h.linOff).know
    refine know_of_det _ _ _ _ _ _ _ _ _ _ (fun a => O.off.decA O.dOff a.1.1 a.2.2) ?_ g
    rintro a w - ⟨U, -, h2, -⟩
    show w = (O.off.adec a.1.1 a.2.2).getD O.dOff
    rw [h2]
    rfl
  link := (know_of_knowInto _ _ _ _ _ _ _ _ _ _).1 (O.link.good () h.link).know
  req := (O.req.good O.C.cells0 h.req).know
  linOn := h.linOn

theorem passes (H : O.Hon) (h : O.Blocks) :
    ∀ x y τ b, (O.S H).req.out x y τ = some b → b.2 = x.2 :=
  (O.req.hands O.C.cells0 _ _ h.hands).passes

theorem copy (H : O.Hon) (h : O.Blocks) : ∀ y τ, ((O.S H).req.imp y τ).1 = y :=
  (O.req.hands O.C.cells0 _ _ h.hands).copy

theorem locals (H : O.Hon) (h : O.Blocks) :
    (O.S H).wf.IsLocal ∧ (O.S H).linOff.IsLocal ∧ (O.S H).link.IsLocal ∧ (O.S H).req.IsLocal ∧
      (O.S H).linOn.ior.IsLocal ∧ (O.S H).linOn.ann.Coherent :=
  ⟨(O.wf.good () h.wf).isLocal, (O.linOff.good O.dOff h.linOff).isLocal,
    (O.link.good () h.link).isLocal, (O.req.good O.C.cells0 h.req).isLocal, h.localOn, h.cohOn⟩

theorem points (H : O.Hon) (h : O.Blocks) :
    Nonempty (O.S H).wf.shape.IsPoint ∧ Nonempty (O.S H).linOff.shape.IsPoint ∧
      Nonempty (O.S H).link.shape.IsPoint ∧ Nonempty (O.S H).req.shape.IsPoint :=
  ⟨(O.wf.good () h.wf).point, (O.linOff.good O.dOff h.linOff).point,
    (O.link.good () h.link).point, (O.req.good O.C.cells0 h.req).point⟩

end Obj

#print axioms KObj.LK.hands
#print axioms KObj.Obj.hypK
#print axioms KObj.Obj.passes
#print axioms KObj.Obj.copy
#print axioms KObj.Obj.locals
#print axioms KObj.Obj.points

end KObj
