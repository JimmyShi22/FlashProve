-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectPartBat.lean: for toys: the fifth part of the object (the test for linear constraints
at N instances) with standard parts: its data, and its bundle of hypotheses from the premises of
`Spec.std2B_part`: conditions on codes, places and numbers.

The object (`LdObj`, Cb/Obj/LdObject.lean) is one record with a configuration and, over it, the
sub-protocols of the proof system, as five terms. The test for linear constraints is the proximity
test with claims that follows a preamble.
Definitions, statements (`Cb.Spec.std2B_on`, `Cb.Spec.std2B_part`) and proofs. A tool for guards
against empty theorems; no parameter of a protocol.
Cb/Obj/LdObjectParts.lean cuts the record `LdObjP` (Cb/Obj/LdObjectPlan.lean), from which an object
is made, and its hypotheses into five parts; the fifth is `PBat Cf on` with `Bt.Hyp`, over what the
request's preamble leaves ("on"). Here, for `D : StdLn2 Cf P` (Cb/Obj/LdObjectLinStd2.lean: the
standard test over a preamble that leaves a family `D.Sa`):

Main names:
  `D.on`: `D.on.ol` is `D.O` by definition (`Spec.std2B_on`).
  `D.partB ..`: the part. Its regime (`onB`) is that in which the index decodes with its record (if
    the index code has its distance and e' + eM is below it, no point is bad for the fold). It has
    the standard senders (`SnB`), the bound "at most ba a long positions of the member a" on the
    oracles left (`qaB`), and the standard plan and tests (`pB`, `TB`); its third test in every slot
    closes what is left.
  `Spec.std2B_part`: for non-empty `Fin Cf.C₀.n` and P: the index code has its distance, e' + eM is
    below it, the places are distinct, 1 ≤ N, `D.HypB N ..` ⇒ `(D.partB ..).Hyp`.

Limits: this file does not say that `D.HypB` can be met. It does not say that a given request ends
at `D.on`.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectParts
import Cb.Obj.LdObjectOnBStd2
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace StdLn2
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] {Cf : LdCf F E}
  [Nonempty (Fin Cf.C₀.n)] {P : Type} [Fintype P] [Nonempty P] (D : StdLn2 Cf P)

/-- What the preamble leaves, and the data of the test after it. -/
@[reducible] def on : LdOLd Cf where
  S := D.O.S
  Cl := D.O.Cl
  Y := D.O.Y
  klo := D.O.klo
  l := D.O.l
  lay := D.O.lay
  py := D.O.py
  g := D.O.g
  ψ := D.O.ψ
  τ := D.O.τ
  restM := D.O.restM
  more := D.O.more
  e' := D.O.e'
  t := D.O.t
  NW := D.O.NW
  SdW := D.O.SdW
  iW := D.O.iW
  lW := D.O.lW
  NU := D.O.NU
  SdU := D.O.SdU
  iU := D.O.iU
  lU := D.O.lU
  NO := D.O.NO
  SdO := D.O.SdO
  iO := D.O.iO
  lO := D.O.lO

/-- The part. -/
@[reducible] def partB (N L tW tU tO : ℕ) (ba : D.Sa.O → ℕ) (x₀ : D.T.St₁ × D.C.S.Smp)
    (y₀ : (D.C.E₀.prod D.C.S.ext).Str) (d : D.C.P.W0) (d₀ : D.O.P.W0) (ya : D.C.P.Ea.Str) :
    PBat Cf D.on where
  N := N
  onB := D.O.onDec
  SnB := D.Sn L tW tU tO
  qaB := D.Sa.qFam (E₀ := extNone) (fun _ => True) ba
  εfB := 0
  dB := d
  dB₀ := d₀
  yB := ya
  pB := D.pl
  TB := D.T
  q₀B := fun _ => True
  bB' := D.b₃ N
  baB := ba
  tie' := fun _ _ _ _ => True
  cA' := D.rest3.cA
  same' := D.rest3.same
  x₀ := x₀
  y₀ := y₀
  QV' := D.QV3 N

end StdLn2

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def std2B_on : Prop := ∀ (Cf : LdCf F E) (P : Type) [Fintype P] (D : StdLn2 Cf P), D.on.ol = D.O

/-- The bundle of hypotheses of the fifth part. -/
def std2B_part : Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (P : Type) [Fintype P] [Nonempty P] (D : StdLn2 Cf P)
      (N L tW tU tO : ℕ) (ba : D.Sa.O → ℕ) (x₀ : D.T.St₁ × D.C.S.Smp)
      (y₀ : (D.C.E₀.prod D.C.S.ext).Str) (d : D.C.P.W0) (d₀ : D.O.P.W0) (ya : D.C.P.Ea.Str),
    HasDist Cf.C₀.G Cf.C₀.d → D.e' + Cf.eM < Cf.C₀.d → Function.Injective D.py → 1 ≤ N →
    D.HypB N L tW tU tO ba → (D.partB N L tW tU tO ba x₀ y₀ d d₀ ya).Hyp

end
end Spec

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

omit [Fintype F] in
theorem std2B_on : Spec.std2B_on F E := fun _ _ _ _ => rfl

/-- With one slot or more, a test in every slot needs no less than one test. -/
theorem need_le_needV {E : Type} [Field E] [Fintype E] {S : Sig E} (D : LdRunD S) (N : ℕ)
    (hN : 1 ≤ N) (sh : S.O → Prop) [DecidablePred sh] (b' : (S.sub D.kp).O → ℕ) (o : S.O) :
    D.need b' o ≤ D.needV N sh b' o := by
  unfold LdRunD.need LdRunD.needV
  refine Nat.add_le_add_right ?_ _
  split_ifs
  · exact Nat.le_mul_of_pos_left _ hN
  · exact le_refl _
  · exact le_refl _

omit [Fintype F] in
theorem std2B_part : Spec.std2B_part F E := by
  intro Cf _ P _ _ D N L tW tU tO ba x₀ y₀ d d₀ ya hd he hpy hN h
  exact
    { sndB := std2_snd D h.hyp.okW h.hyp.okU h.hyp.okO
      apartB := std2B_apart F E Cf P D L tW tU tO
      fitsB := (ldOB_fits F E D.O).1
      foldB := ldOB_foldErr F E D.O hd he
      pyInjB := hpy
      monoB := std2B_mono E D.Sa extNone ba
      shared := std2B_shared F E Cf P D
      restB := std2_rest
      saysAB := std2_saysA
      leftB := std2_q' h.hyp
      leftQB := fun V hV => by
        have h1 := ldDemand_cons E _ _ _ D.D₃ _ _ _ (fun _ => True) (fun _ => 0)
          (ldDemand_nil E _ _ _ _ (fun _ => True) _ trivial) V hV
        exact ⟨trivial,
          fun a =>
            (h1.2 a).trans
              (show D.D₃.need (fun _ => 0) a ≤ D.b₃ N a
                from need_le_needV D.D₃ N hN (fun a => D.C.isSh a.1.1) (fun _ => 0) a)⟩
      leftKB := ldPlanB_cons_local E _ _ _ D.D₃ D.nil3 _ _ N (ldKeyU _) (ldKeyU _) id
        (std2_d3 h.hyp) (ldPlanB_nil E _ _ _ _ N _) fun _ _ _ _ => rfl
      leftV := std2B_rest F E Cf P D L tW tU tO N ba h.hyp
      tieC := fun _ _ _ _ => trivial
      qaOK := fun _ hW => hW
      oneN := hN
      needNA := fun a => le_of_eq_of_le (std2B_needA N a) (h.hyp.posA a)
      needNW := fun _ => le_of_eq_of_le (std2B_needW N) h.hyp.posW
      needNU := fun _ => le_of_eq_of_le (std2B_needU N) h.hyp.posU
      needNO := fun _ => le_of_eq_of_le (std2B_needO N) h.posO
      test₁B := std2_d1 h.hyp
      test₂B := std2_d2 h.hyp }

end
end Cb
