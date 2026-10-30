-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/PointLift.lean: WHAT A YES OF "LIN point" GIVES, AT THE BLOCK LIFTED TO A WIDER
RECORD: a pair of what was handed to the chain (P₁: any type) and the chain's own record: the form
in which a table of joints lays the shared chain's blocks (Block.lift Prod.snd,
Johnson/Desc/Block.lean).

  lift_ok         a yes of a lifted block is a yes of the block at the chain's own record; what was
                  handed stays.
  liftedPiece     the piece that holds the lifted block at one written round: ANY extractor, ANY
                  errors.
  point_yesL      **point_yes (Johnson/Desc/K14/Law/PointCounts.lean) at the lifted piece**, with
                  what stays said beside it: what was handed; the stored table's columns; the key;
                  and the book-keeping's first test in front gives the second behind.

What is not claimed. As in PointCounts.lean: these are the parts of a law for a batch, not the law.
BadKey, Dec, Tab are letters that read the chain's own record and the oracle string; hgood is a
premise (paid in PointKey2.lean). g and wv are letters: that they are read off what was handed is
the caller's. Kin, not read: other files' lemmas that carry a yes under a lift (liftOut, under_out:
LiftRule.lean, LiftBelow.lean): lift_ok is said of the decision alone. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.PointCounts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Grows Block noDigest)
open VerifiableInference.Desc.Sound (Frame Piece)
open Iop.IOR (drawRound)

/-- A yes of a lifted block is a yes of the block at the chain's own record; what was handed
stays. -/
theorem lift_ok {P₁ S Cl : Type} (b : Block S Cl) (t t' : P₁ × S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (b.lift Prod.snd fun (t : P₁ × S) s => (t.1, s)).decide t rs gs = .ok t') :
    b.decide t.2 rs gs = .ok t'.2 ∧ t'.1 = t.1 := by
  have h' : (b.decide t.2 rs gs).map (fun s => (t.1, s)) = .ok t' := h
  cases hd : b.decide t.2 rs gs with
  | error e => rw [hd] at h'; cases h'
  | ok s =>
    rw [hd] at h'
    have e : (t.1, s) = t' := Except.ok.inj h'
    subst e
    exact ⟨rfl, rfl⟩

variable {W P₁ : Type} {F : Frame}

/-- The piece that holds the lifted block at one written round. -/
def liftedPiece (b : Block St Unit) (base : Nat) (d : RDT)
    (ext : (P₁ × St) × F.E.Str → Tr (uLT (ckP .two) [d]) → W → W)
    (err : Err (uLT (ckP .two) [d])) : Piece (ckP .two) F (P₁ × St) Unit W :=
  ⟨b.lift Prod.snd fun t s => (t.1, s), base, [d], [], ext, err⟩

/-- **What a yes of the chain's own first block gives, at the lifted piece.** -/
theorem point_yesL (rg : W → Words GE) (wv : W → Nat → GE) (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (g : Nat → GE) (e' : Nat)
    (base : Nat) (d : RDT) {ns a0 : Nat} (hd : SendsDraws (toRD d) ns P.par.S.kCol 0 a0)
    (ext : (P₁ × St) × F.E.Str → Tr (uLT (ckP .two) [d]) → W → W)
    (err : Err (uLT (ckP .two) [d]))
    (BadKey : St × F.E.Str → (Fin P.par.S.fold.index.v → GE) → Prop)
    (Tab : St × F.E.Str → Nat → Nat → GE) (Dec : St × F.E.Str → Prop)
    (a : (P₁ × St) × F.E.Str)
    (hgood : ∀ (x : St) (m : Words GE) (gam : Fin P.par.S.fold.index.v → GE),
      ¬ BadKey (a.1.2, a.2) gam →
      (gamma P.par.S x.loc).map OnBytes.Model.Reading.gl.val = List.ofFn gam →
      x.loc.key = a.1.2.loc.key → x.st.codes = a.1.2.st.codes →
      NearAt OnBytes.Model.Reading.gl P.par x m (tabOf a.2) e' →
      RecAll OnBytes.Model.Reading.gl P.par x m →
      Dec (a.1.2, a.2) ∧ UIsFold P.par.S.matrixRows P.par.S.kLo P.par.S.fold.index.v
        (Tab (a.1.2, a.2)) (List.ofFn gam) (uOf x.loc m))
    (τ : Tr (uLT (ckP .two) (liftedPiece (W := W) (F := F) (P₁ := P₁) b1 base d ext err).ds))
    (b : (P₁ × St) × F.E.Str)
    (hout : (liftedPiece (W := W) (F := F) b1 base d ext err).ior.red.out a τ = some b) :
    ∃ τ' : Tr [drawRound (Fin P.par.S.kCol → GE)],
      (vecMaps d P.par.S.kCol).carry.tr τ = some τ' ∧
      b.1.1 = a.1.1 ∧ tabOf b.2 = tabOf a.2 ∧ b.1.2.loc.key = a.1.2.loc.key ∧
      (∃ rs, linPoint P.par a.1.2 rs = some b.1.2) ∧
      b.1.2.loc.psiSh.map OnBytes.Model.Reading.gl.val = List.ofFn τ'.2.1 ∧
      (shape1 P.par a.1.2 = true → shape2 P.par b.1.2 = true) ∧
      ∀ w, ¬ BadKey (a.1.2, a.2) (gamOf P.par.S.kLo P.par.S.fold.index.v τ'.2.1) →
        NearAt OnBytes.Model.Reading.gl P.par (withNext P.par b.1.2) (rg w) (tabOf b.2) e' →
        RecAll OnBytes.Model.Reading.gl P.par (withNext P.par b.1.2) (rg w) →
        DotUAt P.par.S g (withNext P.par b.1.2).loc (rg w) (wv w) →
        Dec (a.1.2, a.2) ∧ DotTrue P.par.S g (Tab (a.1.2, a.2)) (wv w) τ'.2.1 := by
  obtain ⟨hy, gs, hdc0⟩ := piece_yes (liftedPiece (W := W) (F := F) b1 base d ext err) a τ b hout
  obtain ⟨hdc, hh⟩ := lift_ok b1 a.1 b.1 _ gs hdc0
  have k1 := point_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl _ _ gs _ hdc
  obtain ⟨r, hr, hpsi, hkeyE, hor, hco⟩ := linPoint_inv _ _ _ _ k1
  have ht := piece_tests (liftedPiece (W := W) (F := F) b1 base d ext err) a τ b hout
  simp only [sTests, Bool.and_eq_true] at ht
  have hp : (vecMaps d P.par.S.kCol).pass τ = true := (vecMaps_pass d _ τ).trans ht.1.1
  obtain ⟨m, c, ⟨⟩⟩ := τ
  have hr' : [noDigest (shownAt d m c)] = [r] := hr
  obtain rfl := (List.cons.inj hr').1
  have hsh := drawn_shown hd m c
  have e1 : (withNext P.par b.1.2).loc.psiSh.map OnBytes.Model.Reading.gl.val =
      List.ofFn (gVec P.par.S.kCol _ (valsOf (toRD d) c)) := by
    show b.1.2.loc.psiSh.map _ = _
    rw [hpsi]
    exact hsh
  have htab : tabOf b.2 = tabOf a.2 := by rw [hy, tabOf_imp]
  refine ⟨_, (vecMaps d P.par.S.kCol).tr_of_pass (m, c, ()) hp, hh, htab, hkeyE, ⟨_, k1⟩, e1,
    fun h1 => ?_, fun w hnb hnear hrec hdot => ?_⟩
  · have hl := congrArg List.length e1
    rw [List.length_map, List.length_ofFn] at hl
    have hl' : b.1.2.loc.psiSh.length = P.par.S.kCol := hl
    unfold shape2 shape1 at *
    rw [hkeyE, h1, hl']
    simp
  have eg : (gamma P.par.S (withNext P.par b.1.2).loc).map OnBytes.Model.Reading.gl.val =
      List.ofFn (gamOf P.par.S.kLo P.par.S.fold.index.v
        (gVec P.par.S.kCol _ (valsOf (toRD d) c))) := by
    unfold gamma
    rw [List.map_drop, e1]
    exact drop_ofFn P.par.S.kLo P.par.S.fold.index.v _
  have et : ((withNext P.par b.1.2).loc.psiSh.take P.par.S.kLo).map
      OnBytes.Model.Reading.gl.val = List.ofFn (loOf P.par.S.kLo P.par.S.fold.index.v
        (gVec P.par.S.kCol _ (valsOf (toRD d) c))) := by
    rw [List.map_take, e1]
    exact take_ofFn P.par.S.kLo P.par.S.fold.index.v _
  have eapp : List.ofFn (loOf P.par.S.kLo P.par.S.fold.index.v
        (gVec P.par.S.kCol _ (valsOf (toRD d) c))) ++
      List.ofFn (gamOf P.par.S.kLo P.par.S.fold.index.v
        (gVec P.par.S.kCol _ (valsOf (toRD d) c))) =
      List.ofFn (gVec P.par.S.kCol _ (valsOf (toRD d) c)) := by
    rw [← take_ofFn, ← drop_ofFn]
    exact List.take_append_drop _ _
  rw [htab] at hnear
  have hnb' : ¬ BadKey (a.1.2, a.2) (gamOf P.par.S.kLo P.par.S.fold.index.v
      (gVec P.par.S.kCol _ (valsOf (toRD d) c))) := hnb
  obtain ⟨hdec, hU⟩ := hgood (withNext P.par b.1.2) (rg w) _ hnb' eg hkeyE hco hnear hrec
  unfold DotUAt at hdot
  rw [et, e1, ← eapp] at hdot
  have hfin := dotTrue_of P.par.S.matrixRows P.par.S.kLo P.par.S.fold.index.v
    (Tab (a.1.2, a.2)) _ _ g (uOf (withNext P.par b.1.2).loc (rg w)) (wv w) (by simp) hU hdot
  rw [eapp] at hfin
  exact ⟨hdec, hfin⟩

end Desc.K14.Law
