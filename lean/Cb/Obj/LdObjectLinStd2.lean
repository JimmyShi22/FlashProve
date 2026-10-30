-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectLinStd2.lean: for toys: the test for linear constraints on the encoded index with
standard parts, over a preamble that leaves a family of oracle messages and rows on them.

The test for linear constraints is the interactive oracle proof of proximity (IOPP) for the
constraint relation; it follows a preamble (Hiop/RecSubs.lean, Hiop/RecBuild.lean). This file has
the data of a second filling of the test's open parameters (senders, plan, tests on groups) with
standard parts: here the preamble leaves oracle messages and linear claims on them, which the test's
last part has to test too.

Definitions and one lemma (`kA`); the statements and proofs are in
Cb/Obj/LdObjectLinStd2Proofs.lean. A tool for guards against empty theorems; no parameter of a
protocol. The analogue of Cb/Obj/LdObjectLinStd.lean, in which the preamble leaves nothing.

Why: a preamble leaves something: its first sending holds the message of index masks, its last
closings leave oracle messages, its lookups file rows. So the test's plan has to close also what the
preamble leaves, and the tensor row's "rest" reads a mask of that family.

Main names:
  `StdLn2 Cf P`: the data. Those of Cb/Obj/LdObjectLinStd.lean (claims with the tensor row; layout;
    e', t; three standard oracle messages MW, MU, MO (below: W, G_u, Ω) for w, the folded full
    message u, ω; joint radius er; numbers), and what the preamble leaves:
    Sa, posA: any family of oracle messages, each read at the common positions P. (The test does
      not send them: nothing is asked of their senders.)
    iM, cM: the message of index masks, and the coefficients of "rest": a linear form on its
      message.
    BM, SbM, slM, xM: finitely many rows on all entries of the family, with states (the rows that
      the preamble filed); targets and states are read off the claim. "more" := these rows hold.
      (No row: more is true.)
    tb₃: the number of positions that the third base case draws.
  `D.pl`, `D.T`: the plan (Cb/Ld/LdLinClosePlan.lean, without a splitting), three whole tests:
    first group: G_u and Ω: the record's rows, the columns, the fold's row. Kept: all but G_u.
    second group: Ω, W and the message of index masks: the evaluation, the inner product. Kept: the
      whole family Sa (the message of index masks too: a row that the preamble filed may read it).
    third group: the whole family Sa: the rows that the preamble filed. Nothing is kept.
    Bridges with independent coefficients; each whole test is the base case on the complex.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectLinFullProofs
import Cb.Ld.LdLinCloseDemandProofs
import Cb.Obj.LdObjectToyKit
import Cb.Ld.LdTowerMain
import Cb.Gen.BatEvaderProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The test with standard parts, over a preamble that leaves a family: the data. -/
structure StdLn2 {F E : Type} [Field F] [Field E] [Algebra F E] (Cf : LdCf F E)
    (P : Type) [Fintype P] where
  Cl  : Type
  Y   : Type
  [finY : Fintype Y]
  klo : ℕ
  l   : ℕ
  lay : Y × (Fin klo → Bool) → Cf.J₀
  py  : Y → Fin l → Bool
  g   : Cl → Y → E
  ψ   : Cl → (Fin Cf.X.v → E) × (Fin klo → E)
  τ   : Cl → E
  e'  : ℕ
  t   : ℕ
  MW  : StdM E P
  MU  : StdM E P
  MO  : StdM E P
  dW  : ((Fin Cf.X.v ⊕ Fin klo) → Bool) ≃ MW.Dt
  dU  : Fin Cf.C₀.k ≃ MU.Dt
  dO  : Y ≃ MO.Dt
  /-- what the preamble leaves: a family, read at the common positions; the message of index masks
  and the coefficients of "rest"; the rows that it filed -/
  Sa   : Sig E
  posA : ∀ a, P → (Sa.om a).P
  iM   : Sa.O
  cM   : Cl → (Sa.om iM).C.J → E
  BM   : Type
  [finBM : Fintype BM]
  SbM  : BM → Type
  slM  : ∀ b, Slf E (SbM b) Sa.Ent
  xM   : Cl → (BM → E) × (∀ b, SbM b)
  er  : ℕ
  tb₁ : ℕ
  tb₂ : ℕ
  tb₃ : ℕ
  d   : ℕ
  bad : ℕ
  L2  : ℕ
  Lc  : ℕ

attribute [instance] StdLn2.finY StdLn2.finBM

namespace StdLn2
variable {F E : Type} [Field F] [Field E] [Fintype E] [Algebra F E] {Cf : LdCf F E} {P : Type}
  [Fintype P] (D : StdLn2 Cf P)

/-- The test over the configuration. -/
@[reducible] def O : LdOL F E where
  Cf := Cf
  S := D.Sa
  Cl := D.Cl
  Y := D.Y
  klo := D.klo
  l := D.l
  lay := D.lay
  py := D.py
  g := D.g
  ψ := D.ψ
  τ := D.τ
  restM := fun cl m => ∑ j, D.cM cl j * m D.iM j
  more := fun cl m => Slf.All D.slM (D.xM cl) (D.Sa.ents m)
  e' := D.e'
  t := D.t
  NW := Sig.one D.MW.om
  SdW := Sig.Seeds.indep _
  iW := ()
  lW := fun c => D.MW.place (Sum.inl (D.dW c))
  NU := Sig.one D.MU.om
  SdU := Sig.Seeds.indep _
  iU := ()
  lU := fun k => D.MU.place (Sum.inl (D.dU k))
  NO := Sig.one D.MO.om
  SdO := Sig.Seeds.indep _
  iO := ()
  lO := fun y => D.MO.place (Sum.inl (D.dO y))

/-- the same, over a signature -/
@[reducible] def C : LdLinC E (Fin Cf.C₀.n) (Fin Cf.C₀.k) Cf.J D.Y := D.O.toC

/-- fixed witnesses (`w0`, `w1`, `w3`) -/
def w0 : D.C.P.W0 := (fun _ _ => 0, (fun _ => (fun _ => 0, fun _ => 0), ()))
def w1 : D.C.P.W1 := (fun _ => (fun _ => 0, fun _ => 0), D.w0)
def w3 : D.C.P.W3 := (fun _ => (fun _ => 0, fun _ => 0), D.w1)

/-- the data of the three messages: the entries of w, of u, of ω (`datW`, `datU`, `datO`) -/
def datW (w : D.C.P.WA) : D.MW.Dt → E := fun i => w.1 (D.dW.symm i)
def datU (w : D.C.P.W2) : D.MU.Dt → E := fun i => w.1 (D.dU.symm i)
def datO (w : D.C.P.W4) : D.MO.Dt → E := fun i => w.1 (D.dO.symm i)

@[reducible] def memW : ∀ a, (D.C.NW.om a).Sender D.C.P.WA Unit := fun _ =>
  D.MW.snd D.datW (fun _ => 0, D.w0)
@[reducible] def memU : ∀ a, (D.C.NU.om a).Sender D.C.P.W2 Unit := fun _ =>
  D.MU.snd D.datU (fun _ => 0, D.w1)
@[reducible] def memO : ∀ a, (D.C.NO.om a).Sender D.C.P.W4 Unit := fun _ =>
  D.MO.snd D.datO (fun _ => 0, D.w3)

/-- The three senders. -/
@[reducible] def Sn (L tW tU tO : ℕ) : D.C.P.Snd where
  dW := Sig.Sender.ofMem D.memW (fun w => w.2) (fun _ => 0, D.w0)
  dU := Sig.Sender.ofMem D.memU (fun w => w.2) (fun _ => 0, D.w1)
  dO := Sig.Sender.ofMem D.memO (fun w => w.2) (fun _ => 0, D.w3)
  LW := fun _ => L
  LU := fun _ => L
  LO := fun _ => L
  tW := fun _ => tW
  tU := fun _ => tU
  tO := fun _ => tO

/-- every oracle message at the end of the test is read at the positions P -/
def posAll : ∀ o : D.C.S.O, P → (D.C.S.om o).P
  | .inl (.inl (.inl a)) => D.posA a
  | .inl (.inl (.inr _)) => id
  | .inl (.inr _) => id
  | .inr _ => id

/-- the names of what the preamble left (`isA`, `nA`); of the message of index masks (`nM`) -/
def isA : D.C.S.O → Prop
  | .inl (.inl (.inl _)) => True
  | _ => False

instance : DecidablePred D.isA
  | .inl (.inl (.inl _)) => isTrue trivial
  | .inl (.inl (.inr _)) => isFalse id
  | .inl (.inr _) => isFalse id
  | .inr _ => isFalse id

abbrev nA (a : D.Sa.O) : D.C.S.O := .inl (.inl (.inl a))
abbrev nM : D.C.S.O := D.nA D.iM

/-- what is kept at the first bridge: all but G_u -/
abbrev kp₁ : D.C.S.O → Prop := fun o => o ≠ D.C.nU

theorem kA (a : D.Sa.O) : D.kp₁ (D.nA a) := by simp

/-- the two groups of the plan (`G₁`, `G₂`) -/
@[reducible] def G₁ : Grp D.C.S :=
  { P := P, mem := fun o => o = D.C.nU ∨ o = D.C.nO, pos := fun a => D.posAll a.1, e := D.er }
@[reducible] def G₂ : Grp (D.C.S.sub D.kp₁) :=
  { P := P, mem := fun a => a.1 = D.C.nW ∨ a.1 = D.C.nO ∨ a.1 = D.nM,
    pos := fun a => D.posAll a.1.1, e := D.er }

/-- The plan. -/
@[reducible] def pl : LdLinPl D.C where
  G₁ := D.G₁
  hU := Or.inl rfl
  hO := Or.inr rfl
  kp₁ := D.kp₁
  kW := by simp
  kO := by simp
  G₂ := D.G₂
  hW₂ := Or.inl rfl
  hO₂ := Or.inr (Or.inl rfl)
  kp₂ := fun a => D.isA a.1
  restG := D.G₂.onMem ⟨D.nM, D.kA D.iM⟩ (Or.inr (Or.inr rfl)) D.cM

/-- the third group: all that is left -/
@[reducible] def G₃ : Grp D.pl.S₂ :=
  { P := P, mem := fun _ => True, pos := fun a => D.posAll a.1.1.1, e := D.er }

/-- an entry of the family, as an entry of the message of the third group's complex -/
def φ₃ (n : D.Sa.Ent) : D.G₃.C.J := ⟨⟨⟨⟨D.nA n.1, D.kA n.1⟩, trivial⟩, trivial⟩, n.2⟩

variable [Nonempty P]

/-- The third test: the rows that the preamble filed, on the whole family. -/
@[reducible] def D₃ : LdRunD D.pl.S₂ where
  G := D.G₃
  neP := inferInstanceAs (Nonempty P)
  kp := fun _ => False
  decKp := fun _ => instDecidableFalse
  hc := fun _ => Or.inl trivial
  B := D.BM
  Sb := D.SbM
  sl := fun b => @Slf.push E (D.SbM b) D.Sa.Ent D.G₃.C.J _ _ (Classical.decEq _) D.φ₃ (D.slM b)
  Z := @Evader.indep E (D.G₃.Row D.BM) _ _ _ (Classical.decEq _)
  T := ldBaseEnd _ D.tb₃ (fun _ => Classical.arbitrary P) D.d D.bad D.L2
  L := D.Lc
  t := D.tb₃

/-- The tests. -/
@[reducible] def T : LdLinPlT D.pl where
  ne₁ := inferInstanceAs (Nonempty P)
  hc₁ := fun o => by
    by_cases h : o = D.C.nU
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
  Z₁ := @Evader.indep E (D.pl.G₁.Row D.C.B₁) _ _ _ (Classical.decEq _)
  T₁ := ldBaseEnd _ D.tb₁ (fun _ => Classical.arbitrary P) D.d D.bad D.L2
  L₁ := D.Lc
  t₁ := D.tb₁
  ne₂ := inferInstanceAs (Nonempty P)
  hc₂ := fun a => by
    rcases a with ⟨((a | w) | u) | o, h⟩
    · exact Or.inr trivial
    · exact Or.inl (Or.inl rfl)
    · exact absurd rfl h
    · exact Or.inl (Or.inr (Or.inl rfl))
  Z₂ := @Evader.indep E (D.pl.G₂.Row LinB₂) _ _ _ (Classical.decEq _)
  T₂ := ldBaseEnd _ D.tb₂ (fun _ => Classical.arbitrary P) D.d D.bad D.L2
  L₂ := D.Lc
  t₂ := D.tb₂
  Q' := LdTc.cons D.D₃ (LdTc.nil _ _ _ (fun a => a.2.elim, ()))
    (fun _ => (fun _ => 0, fun _ => 0), ()) ((fun _ => 0, fun _ => 0), (fun a => a.2.elim, ()))
  fa := fun cl => (D.xM cl, ())
  d₁ := (fun _ => (fun _ => 0, fun _ => 0), ())
  d₁' := ((fun _ => 0, fun _ => 0), (fun _ => (fun _ => 0, fun _ => 0), ()))
  d₂ := (fun _ => (fun _ => 0, fun _ => 0), ())
  d₂' := ((fun _ => 0, fun _ => 0), (fun _ => (fun _ => 0, fun _ => 0), ()))

end StdLn2
end Cb
