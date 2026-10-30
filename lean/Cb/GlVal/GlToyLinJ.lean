-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/GlVal/GlToyLinJ.lean: a toy of the test for linear constraints on the encoded index
(Cb/Ld/LdLin.lean), at one instance, over what the toy of weights-formedness at the radius 3 leaves.
Of its conditions that do not speak of agreement, those that `sndJ`, `codesJ`, `grpJ`, `needJ` state
are proved for it, nothing assumed beyond the hypotheses of the statements and whatever the
arguments hold as proofs.
The groups' joint radius and the messages' own radius are 3 (2 · 3 = 6: not within half the
distance; lists `LJ` = listMax 8 6 3). This guard shows no value with 2 e above d.

For the guard below the Johnson radius, over p = 2^64 - 2^32 + 1, with two different fields.
Definitions, statements are the theorems' own texts, proofs. A guard against empty theorems; no
parameter of a protocol. Cb/GlVal/GlToyLin.lean again, with the families and the groups at the
radius 3. Cb/Gl/GlSendersToyJ.lean [not in this library] takes its three oracle messages (`mW`, `mU`, `mO`) from here.
The preamble's data are those of Cb/GlVal/GlToyWfJ.lean (`Wf8J.W3 Ln`: the code on the subgroup of
order 8, distance 6, read at the radius 3: 16 < 25: below the Johnson radius, beyond a third, not
below half the distance). The encoded index stays within a third: `toyCf8 ToyMo8.two`: eM = 1; the
fold is tested at the radius e' = 1; its sample map is `Sample.nil`.

Main names:
  `toyStd83`: the standard oracle message at the eight positions at the radius 3, the pad's
    coefficient drawn among all values other than 0 (`Wf8J.Bq`). `toyStd83_ok`: for an injective
    placement: `(toyStd83 Dt μ plc).OK LJ 2` (lists by the Johnson bound `LJ` = listMax 8 6 3),
    distance 6, transparent.
  `LnJ`: one location; W, G_u, Ω: three such messages, at the radius 3, with 2, 3, 1 data and one
    pad each; independent seeds.
  `SnJ`: the three senders; bound on lists `LJ`; each encoding hides 2 long positions.
  `sndJ`: `SnJ.John 6 6 6` (Cb/Obj/LdObjectJohnTests.lean): what the three sendings ask without the
    clauses on lists.
  `DJ b`: the standard plan over `(W3 LnJ).O` (Cb/Obj/LdObjectPartLin.lean): joint radius 3, three
    base cases, each drawing one position, distance 6, bound on lists `LJ`; b, the number of
    exceptional coefficients of a complex at the radius 3, is a letter: no bound on agreement is
    proved in this file.
  `codesJ`: every oracle message at the end of the test, as read: laws, distance 6, transparent, "3
    implies its own radius". `glcJ`: it is a code of the closure of Cb/Gl/GlLd.lean, at distance 6,
    hiding 2 positions. `grpJ b`: the plan's three groups meet `G.John 6`.
  `needJ b`: what the three tests need of an oracle message: those that the preamble left: 1 + 1; W:
    1; G_u: 1; Ω: 1 + 1: each at most 2.

Limits: agreement of the three tests' complexes at the radius 3 (the letter b), and with it `D.PreJ`
(Cb/Obj/LdObjectTowerJohn.lean), is left for these tests. It is not shown here. (Under the statement
on codes, by name: in the larger library; the guard's file is not in this library.)
No clause here needs F = E.

Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyLin
import Cb.GlVal.GlToyWfJ

set_option autoImplicit false

namespace Cb.Gl
namespace Off8J
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.LdLkp Wf8 Wf8J

noncomputable section

/-- The standard oracle message at the eight positions, radius 3. -/
@[reducible] def toyStd83 (Dt μ : Type) [Fintype Dt] [DecidableEq Dt] [Fintype μ]
    [DecidableEq μ] (plc : Dt → μ → Bool) : StdM E P8 where
  Cm := toyLd8 (Dt ⊕ Unit)
  Dt := Dt
  place := toyPlace8 (Dt ⊕ Unit)
  μ := μ
  plc := plc
  B := Bq
  b := Bq.val
  e := 3

/-- lists by the Johnson bound; the rest as at the radius 1 -/
theorem toyStd83_ok (Dt μ : Type) [Fintype Dt] [DecidableEq Dt] [Fintype μ] [DecidableEq μ]
    (plc : Dt → μ → Bool) (hp : Function.Injective plc) :
    (toyStd83 Dt μ plc).OK LJ 2 ∧
    (toyStd83 Dt μ plc).Cm.Dist 6 ∧
    (toyStd83 Dt μ plc).Cm.Transparent := by
  have h := toyStd8_third Dt μ plc hp
  exact ⟨⟨h.laws, ld_list_johnson E P8 _ 6 3 h.laws h.dist inJ8, h.zk, hp, Bq.val_inj, Bq.val_ne⟩,
    h.dist, h.tr⟩

/-- the three standard oracle messages, at the radius 3 -/
@[reducible] def mW : StdM E P8 :=
  toyStd83 ((Fin Wf8.Cf.X.v ⊕ Fin 0) → Bool) (Fin Wf8.Cf.X.v ⊕ Fin 0) id
@[reducible] def mU : StdM E P8 := toyStd83 (Fin Wf8.Cf.C₀.k) (Fin 2) plcK8
@[reducible] def mO : StdM E P8 := toyStd83 Unit Empty fun _ e => e.elim

theorem mWJ : mW.OK LJ 2 ∧ mW.Cm.Dist 6 ∧ mW.Cm.Transparent := toyStd83_ok _ _ _ fun _ _ h => h
theorem mUJ : mU.OK LJ 2 ∧ mU.Cm.Dist 6 ∧ mU.Cm.Transparent := toyStd83_ok _ _ _ plcK8_inj
theorem mOJ : mO.OK LJ 2 ∧ mO.Cm.Dist 6 ∧ mO.Cm.Transparent := toyStd83_ok _ _ _ fun _ _ _ => rfl

/-- What the test needs beside the preamble's data (`ToyLn`). -/
@[reducible] def LnJ : ToyLn where
  l := 0
  py := fun _ i => i.elim0
  e' := 1
  t := 1
  NW := Sig.one mW.om
  SdW := Sig.Seeds.indep _
  iW := ()
  lW := fun c => mW.place (Sum.inl c)
  NU := Sig.one mU.om
  SdU := Sig.Seeds.indep _
  iU := ()
  lU := fun k => mU.place (Sum.inl k)
  NO := Sig.one mO.om
  SdO := Sig.Seeds.indep _
  iO := ()
  lO := fun y => mO.place (Sum.inl y)

/-- how the two oracle messages that the preamble left are read -/
def posF3 : ∀ a : Fm3.sig.O, P8 → (Fm3.sig.om a).P
  | false => id
  | true => id

/-- the data of the test's chain -/
abbrev PP : LdLinP E (Fin Wf8.Cf.C₀.n) (Fin Wf8.Cf.C₀.k) Wf8.Cf.J Unit := (W3 LnJ).O.toC.P

/-- fixed witnesses -/
def w0 : PP.W0 := (fun _ _ => 0, (fun _ => (fun _ => 0, fun _ => 0), ()))
def w1 : PP.W1 := (fun _ => (fun _ => 0, fun _ => 0), w0)
def w3 : PP.W3 := (fun _ => (fun _ => 0, fun _ => 0), w1)

/-- the data of the three messages: the entries of w, of u, of ω -/
def datW (w : PP.WA) : mW.Dt → E := fun i => w.1 i
def datU (w : PP.W2) : mU.Dt → E := fun i => w.1 i
def datO (w : PP.W4) : mO.Dt → E := fun i => w.1 i

@[reducible] def memW : ∀ a, (PP.NW.om a).Sender PP.WA Unit := fun _ => mW.snd datW (fun _ => 0, w0)
@[reducible] def memU : ∀ a, (PP.NU.om a).Sender PP.W2 Unit := fun _ => mU.snd datU (fun _ => 0, w1)
@[reducible] def memO : ∀ a, (PP.NO.om a).Sender PP.W4 Unit := fun _ => mO.snd datO (fun _ => 0, w3)

/-- The three senders. -/
@[reducible] def SnJ : PP.Snd where
  dW := Sig.Sender.ofMem memW (fun w => w.2) (fun _ => 0, w0)
  dU := Sig.Sender.ofMem memU (fun w => w.2) (fun _ => 0, w1)
  dO := Sig.Sender.ofMem memO (fun w => w.2) (fun _ => 0, w3)
  LW := fun _ => LJ
  LU := fun _ => LJ
  LO := fun _ => LJ
  tW := fun _ => 2
  tU := fun _ => 2
  tO := fun _ => 2

/-- What the three sendings ask, without the clauses on lists: below the Johnson radius. -/
theorem sndJ : SnJ.John (fun _ => 6) (fun _ => 6) (fun _ => 6) := by
  have hW := mWJ.1
  have hU := mUJ.1
  have hO := mOJ.1
  exact
    { lawsW := fun _ => hW.laws, distW := fun _ => mWJ.2.1,
      inJW := fun _ => inJ8, isLW := fun _ => rfl
      fairW := (ldSendFam_fair_indep E _).1
      evW := fun _ => stdM_evades mW hW
      sndW := ldSendMem_laws E _ _ _ memW (fun w => w.2) _ PP.backW (fun _ m r => stdM_enc mW _ _ m r) (by
        intro w k
        refine Prod.ext (funext fun c => ?_) rfl
        exact stdM_put mW datW (fun _ => 0, w0) w (k ()) c)
      blW := ldSendMem_blind E _ _ _ memW (fun w => w.2) _ _ fun _ => stdM_blind mW hW _ _
      hidW :=
        ldSendMem_hides E _ _ _ memW (fun w => w.2) _ (fun _ => 2) fun _ => stdM_hides mW hW _ _
      lawsU := fun _ =>
        hU.laws, distU := fun _ => mUJ.2.1, inJU := fun _ => inJ8, isLU := fun _ => rfl
      fairU := (ldSendFam_fair_indep E _).1
      evU := fun _ => stdM_evades mU hU
      sndU := ldSendMem_laws E _ _ _ memU (fun w => w.2) _ PP.backU (fun _ m r => stdM_enc mU _ _ m r) (by
        intro w k
        refine Prod.ext (funext fun c => ?_) rfl
        exact stdM_put mU datU (fun _ => 0, w1) w (k ()) c)
      blU := ldSendMem_blind E _ _ _ memU (fun w => w.2) _ _ fun _ => stdM_blind mU hU _ _
      hidU :=
        ldSendMem_hides E _ _ _ memU (fun w => w.2) _ (fun _ => 2) fun _ => stdM_hides mU hU _ _
      lawsO := fun _ =>
        hO.laws, distO := fun _ => mOJ.2.1, inJO := fun _ => inJ8, isLO := fun _ => rfl
      fairO := (ldSendFam_fair_indep E _).1
      evO := fun _ => stdM_evades mO hO
      sndO := ldSendMem_laws E _ _ _ memO (fun w => w.2) _ PP.backO (fun _ m r => stdM_enc mO _ _ m r) (by
        intro w k
        refine Prod.ext (funext fun c => ?_) rfl
        exact stdM_put mO datO (fun _ => 0, w3) w (k ()) c)
      blO := ldSendMem_blind E _ _ _ memO (fun w => w.2) _ _ fun _ => stdM_blind mO hO _ _
      hidO :=
        ldSendMem_hides E _ _ _ memO (fun w => w.2) _ (fun _ => 2) fun _ => stdM_hides mO hO _ _ }

/-- every oracle message at the end of the test is read at the eight positions, as it stands -/
def posJ : ∀ o : (W3 LnJ).O.toC.S.O, P8 → ((W3 LnJ).O.toC.S.om o).P
  | .inl (.inl (.inl a)) => posF3 a
  | .inl (.inl (.inr _)) => id
  | .inl (.inr _) => id
  | .inr _ => id

/-- The standard plan; b: the number of exceptional coefficients, a letter. -/
@[reducible] def DJ (b : ℕ) : StdPO (W3 LnJ).O P8 := (W3 LnJ).stdPO nAt3 posJ 3 1 1 1 6 b LJ LJ

/-- Every oracle message at the end of the test, as read. -/
theorem codesJ :
    (∀ o, (((W3 LnJ).O.toC.S.om o).C.atPos (posJ o)).Laws) ∧
    (∀ o, (((W3 LnJ).O.toC.S.om o).C.atPos (posJ o)).Dist 6) ∧
    (∀ o, (((W3 LnJ).O.toC.S.om o).C.atPos (posJ o)).Transparent) ∧
    ∀ o (f g : ((W3 LnJ).O.toC.S.om o).C.Word),
      (((W3 LnJ).O.toC.S.om o).C.atPos (posJ o)).Near 3 f g →
      ((W3 LnJ).O.toC.S.om o).C.Near ((W3 LnJ).O.toC.S.om o).e f g := by
  obtain ⟨-, a1, a2, a3, -, -, -, -, -⟩ := gl_toy8 (Ix ⊕ Unit)
  obtain ⟨-, b1, b2, b3, -, -, -, -, -⟩ := gl_toy8 (Im ⊕ Unit)
  refine ⟨fun o => ?_, fun o => ?_, fun o => ?_, fun o => ?_⟩
  · exact match o with
      | .inl (.inl (.inl false)) => a1
      | .inl (.inl (.inl true)) => b1
      | .inl (.inl (.inr _)) => mWJ.1.laws
      | .inl (.inr _) => mUJ.1.laws
      | .inr _ => mOJ.1.laws
  · exact match o with
      | .inl (.inl (.inl false)) => a2
      | .inl (.inl (.inl true)) => b2
      | .inl (.inl (.inr _)) => mWJ.2.1
      | .inl (.inr _) => mUJ.2.1
      | .inr _ => mOJ.2.1
  · exact match o with
      | .inl (.inl (.inl false)) => a3
      | .inl (.inl (.inl true)) => b3
      | .inl (.inl (.inr _)) => mWJ.2.2
      | .inl (.inr _) => mUJ.2.2
      | .inr _ => mOJ.2.2
  · exact match o with
      | .inl (.inl (.inl false)) => fun _ _ hn =>  hn
      | .inl (.inl (.inl true)) => fun _ _ hn =>  hn
      | .inl (.inl (.inr _)) => fun _ _ hn =>  hn
      | .inl (.inr _) => fun _ _ hn =>  hn
      | .inr _ => fun _ _ hn =>  hn

theorem glcJ : ∀ o, GlC (((W3 LnJ).O.toC.S.om o).C.atPos (posJ o)) 6 2
  | .inl (.inl (.inl false)) => glC8 _
  | .inl (.inl (.inl true)) => glC8 _
  | .inl (.inl (.inr _)) => glC8 _
  | .inl (.inr _) => glC8 _
  | .inr _ => glC8 _

/-- The plan's three groups lie below the Johnson radius. -/
theorem grpJ (b : ℕ) : (DJ b).pl.G₁.John 6 ∧ (DJ b).pl.G₂.John 6 ∧ (DJ b).G₃.John 6 := by
  obtain ⟨h1, h2, h3, h4⟩ := codesJ
  exact ⟨⟨fun a => h1 a.1, fun a => h2 a.1, fun a => h3 a.1, inJ8, fun a f g hn => h4 a.1 f g hn⟩,
    ⟨fun a => h1 a.1.1, fun a => h2 a.1.1, fun a => h3 a.1.1,
      inJ8, fun a f g hn => h4 a.1.1 f g hn⟩,
    ⟨fun a => h1 a.1.1.1, fun a => h2 a.1.1.1, fun a => h3 a.1.1.1,
      inJ8, fun a f g hn => h4 a.1.1.1 f g hn⟩⟩

/-- what the three tests need of each oracle message is at most what its encoding bears -/
theorem needJ (b : ℕ) :
    (∀ a, (DJ b).T.D₁.need ((DJ b).T.D₂.need fun _ => (DJ b).tb₃) (.inl (.inl (.inl a))) ≤
      (ZJ LnJ).t a) ∧
    (∀ a,
      (DJ b).T.D₁.need ((DJ b).T.D₂.need fun _ => (DJ b).tb₃) (.inl (.inl (.inr a))) ≤ SnJ.tW a) ∧
    (∀ a, (DJ b).T.D₁.need ((DJ b).T.D₂.need fun _ => (DJ b).tb₃) (.inl (.inr a)) ≤ SnJ.tU a) ∧
    ∀ a, (DJ b).T.D₁.need ((DJ b).T.D₂.need fun _ => (DJ b).tb₃) (.inr a) ≤ SnJ.tO a :=
  ⟨fun a => le_of_eq_of_le (stdPO_needA a) (by cases a <;> exact le_refl 2),
    fun a => le_of_eq_of_le (stdPO_needW a) (by norm_num : 1 ≤ 2),
    fun a => le_of_eq_of_le (stdPO_needU a) (by norm_num : 1 ≤ 2),
    fun a => le_of_eq_of_le (stdPO_needO a) (le_refl 2)⟩

end

end Off8J
end Cb.Gl
