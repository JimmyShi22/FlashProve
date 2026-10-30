-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/GlVal/GlToyLin.lean: a toy of the test for linear constraints on the encoded index
(Cb/Ld/LdLin.lean), at one instance, over what the toy of weights-formedness leaves. Of its
conditions "within a third", those that `snd1`, `d1` state are proved for it, nothing assumed.

For the guard on the offline phase within a third, over p = 2^64 - 2^32 + 1, with two different
fields. (In the larger library; the guard's file is not in this library.) Definitions, statements
are the theorems' own texts, proofs. A guard against empty theorems; no parameter of a protocol.
The preamble's data are those of Cb/GlVal/GlToyWf.lean (`Wf8.W Ln`: the code on the subgroup of
order 8, distance 6, read at the radius 1: 3 · 1 < 6; configuration `toyCf8 ToyMo8.two`: eM = 1,
Z = `Sample.nil`; index messages over F, all that is read over E); its parameter Ln is chosen here.

Main names:
  `Ln1`: one location, the fold tested at the radius 1; the index matrix has one row; W, G_u, Ω:
    three standard oracle messages at the eight positions at the radius 1 (Cb/GlVal/GlToyMsg.lean),
    with 2, 3, 1 data and one pad each; independent seeds.
  `Sn1`: the three senders: each message := the entries of the vector (w; the folded full message u;
    ω) as data, the pad from the sender's coin (Cb/Obj/LdObjectToyKit.lean: `M.snd`;
    Cb/Ld/LdSendMem.lean); bound on lists 1; each encoding hides 2 long positions.
  `snd1`: `Sn1.Third 6 6 6`: what the three sendings ask without the clauses on lists
    (Cb/Obj/LdObjectThirdTests.lean).
  `D1 nAt`: the standard plan over `(Wf8.W Ln1).O` (Cb/Obj/LdObjectPartLin.lean), for any places nAt
    of the named entries: joint radius 1, three base cases, each drawing one position, distance 6, 1
    + 1 exceptional coefficients, lists of at most 1.
  `d1 nAt`: `(D1 nAt).Third` (Cb/Obj/LdObjectThirdStd.lean): so its three tests are within a third
    (`ldStd3_plan`).
  `glc1`: every oracle message at the end of the test, as read, is a code of the closure of
    Cb/Gl/GlLd.lean, at distance 6, hiding 2 positions.

Why: the senders are written at this test's own types, since over these fields Lean does not get
through the comparison of types by which a toy over 101 elements carries them over from another test
with the same families.
No clause here needs F = E: senders, families, plan and tests live over E alone; F enters through
the types of the configuration only (the number of entries of a full message, the row variables).

Limits: this file says nothing on the other clauses of the offline phase's conditions, and on their
assembly. It says nothing on security.

Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyMsg
import Cb.GlVal.GlToyWf
import Cb.Obj.LdObjectPartLin

set_option autoImplicit false

namespace Cb.Gl
namespace Off8
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.LdLkp Wf8

noncomputable section

/-- the three standard oracle messages, at the radius 1 -/
@[reducible] def mW : StdM E P8 :=
  toyStd8 ((Fin Wf8.Cf.X.v ⊕ Fin 0) → Bool) (Fin Wf8.Cf.X.v ⊕ Fin 0) id
@[reducible] def mU : StdM E P8 := toyStd8 (Fin Wf8.Cf.C₀.k) (Fin 2) plcK8
@[reducible] def mO : StdM E P8 := toyStd8 Unit Empty fun _ e => e.elim

theorem mW3 : mW.Third 6 2 := toyStd8_third _ _ _ fun _ _ h => h
theorem mU3 : mU.Third 6 2 := toyStd8_third _ _ _ plcK8_inj
theorem mO3 : mO.Third 6 2 := toyStd8_third _ _ _ fun _ _ _ => rfl

/-- What the test needs beside the preamble's data (`ToyLn`). -/
@[reducible] def Ln1 : ToyLn where
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
def posF1 : ∀ a : Fm.sig.O, P8 → (Fm.sig.om a).P
  | false => id
  | true => id

/-- the data of the test's chain -/
abbrev PP : LdLinP E (Fin Wf8.Cf.C₀.n) (Fin Wf8.Cf.C₀.k) Wf8.Cf.J Unit := (W Ln1).O.toC.P

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
@[reducible] def Sn1 : PP.Snd where
  dW := Sig.Sender.ofMem memW (fun w => w.2) (fun _ => 0, w0)
  dU := Sig.Sender.ofMem memU (fun w => w.2) (fun _ => 0, w1)
  dO := Sig.Sender.ofMem memO (fun w => w.2) (fun _ => 0, w3)
  LW := fun _ => 1
  LU := fun _ => 1
  LO := fun _ => 1
  tW := fun _ => 2
  tU := fun _ => 2
  tO := fun _ => 2

/-- What the three sendings ask, without the clauses on lists. -/
theorem snd1 : Sn1.Third (fun _ => 6) (fun _ => 6) (fun _ => 6) := by
  have hW := ldStd3_msg E P8 mW 6 2 mW3
  have hU := ldStd3_msg E P8 mU 6 2 mU3
  have hO := ldStd3_msg E P8 mO 6 2 mO3
  exact
    { lawsW := fun _ => hW.laws, distW := fun _ => mW3.dist,
      ltW := fun _ => (by norm_num : 2 * 1 < 6), oneW := fun _ => rfl
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
        hU.laws, distU := fun _ =>
              mU3.dist, ltU := fun _ => (by norm_num : 2 * 1 < 6), oneU := fun _ => rfl
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
        hO.laws, distO := fun _ =>
              mO3.dist, ltO := fun _ => (by norm_num : 2 * 1 < 6), oneO := fun _ => rfl
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
def pos1 : ∀ o : (W Ln1).O.toC.S.O, P8 → ((W Ln1).O.toC.S.om o).P
  | .inl (.inl (.inl a)) => posF1 a
  | .inl (.inl (.inr _)) => id
  | .inl (.inr _) => id
  | .inr _ => id

/-- The standard plan, for any places of the named entries. -/
@[reducible] def D1 (nAt : Nm → Fm.sig.Ent) : StdPO (W Ln1).O P8 :=
  (W Ln1).stdPO nAt pos1 1 1 1 1 6 2 1 1

/-- The plan is within a third. -/
theorem d1 (nAt : Nm → Fm.sig.Ent) : (D1 nAt).Third := by
  obtain ⟨-, a1, a2, a3, -, -, -, -, -⟩ := gl_toy8 (Ix ⊕ Unit)
  obtain ⟨-, b1, b2, b3, -, -, -, -, -⟩ := gl_toy8 (Im ⊕ Unit)
  exact
    { laws := fun o => match o with
        | .inl (.inl (.inl false)) => a1
        | .inl (.inl (.inl true)) => b1
        | .inl (.inl (.inr _)) => mW3.laws
        | .inl (.inr _) => mU3.laws
        | .inr _ => mO3.laws
      dist := fun o => match o with
        | .inl (.inl (.inl false)) => a2
        | .inl (.inl (.inl true)) => b2
        | .inl (.inl (.inr _)) => mW3.dist
        | .inl (.inr _) => mU3.dist
        | .inr _ => mO3.dist
      tr := fun o => match o with
        | .inl (.inl (.inl false)) => a3
        | .inl (.inl (.inl true)) => b3
        | .inl (.inl (.inr _)) => mW3.tr
        | .inl (.inr _) => mU3.tr
        | .inr _ => mO3.tr
      fits := fun o => match o with
        | .inl (.inl (.inl false)) => fun _ _ hn => hn
        | .inl (.inl (.inl true)) => fun _ _ hn => hn
        | .inl (.inl (.inr _)) => fun _ _ hn => hn
        | .inl (.inr _) => fun _ _ hn => hn
        | .inr _ => fun _ _ hn => hn
      lt := (by norm_num : 3 * 1 < 6), bad := rfl, l2 := rfl, lc := rfl }

/-- every oracle message at the end of the test, as it is read, is a code of the closure `GlC`:
distance 6, hides 2 positions (Cb/Gl/GlLd.lean) -/
theorem glc1 : ∀ o, GlC (((W Ln1).O.toC.S.om o).C.atPos (pos1 o)) 6 2
  | .inl (.inl (.inl false)) => glC8 _
  | .inl (.inl (.inl true)) => glC8 _
  | .inl (.inl (.inr _)) => glC8 _
  | .inl (.inr _) => glC8 _
  | .inr _ => glC8 _

end

end Off8
end Cb.Gl
