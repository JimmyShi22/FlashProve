-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectPpStdQ.lean: assembly of the holographic IOP from its sub-protocols: the plan of a
write-up of ours (lean/CREDITS.md) for the linear test with standard groups, each of the
four groups with its own set of long positions, its own readings and its own radius; the four whole
tests are parameters (no value is fixed).

Definitions, theorems and proofs. Generic in the test `O : LdOL F E`. A tool: for guards against
empty theorems, and for whoever puts towers with stages at these groups.
Why: In the write-up the two shared groups have two lengths, and the splitting's one mask
row is read in both.
A plan (`LdLinPp`, Cb/Ld/LdLinClosePlanP.lean) fixes how the rows that the test for linear
constraints leaves are closed. A group (`Grp`, Cb/Ld/LdBatSig.lean) is a set of whole oracle
messages, read at common long positions, with one joint radius.
W, G_u, Ω are the oracle messages `O.toC.nW`, `nU`, `nO` (Cb/Ld/LdLinClosePre.lean); s° is `D.sO`.

Main names:
  `StdPq O`: n₀ (the mask entry), neO, four (the families are {W}, {G_u}, {Ω, s°}), slR, the rows
    rowsA with targets tgA, inG, kpA, cov; PU, PO, PC, P4: the four sets of long positions; posU,
    posO, posC, pos4: how every oracle message is read at each; eU, eO, eC, e4: the four radii.
  `D.pl : LdLinPp O.toC`: GU := {G_u, s°} at PU; GO := {Ω, s°} at PO; the splitting's entry n₀ in
    s°; kept at the first bridge: all but G_u, at the second: all but s°; Gc := {Ω, W, the messages
    in inG} at PC; kept after it: the messages in kpA. `D.G₄`: all that is left, at P4.
  `stdPq_plain`, `stdPq_kept`, `stdPq_shared`, `stdPq_mask`, `stdPq_k12`: `D.pl.Plain`, `Kept`,
    `Shared`; at standard senders with `Ts.Places` and n₀ a free entry: kIs, noPad; a message that
    the preamble left is kept at both shared bridges.
  `stdPq_needOff`, `stdPq_needN`: for every `T : LdLinPpT D.pl` (and every fourth test on `D.G₄`
    that keeps nothing): the four families of inequalities of `R.HypPl`
    (Cb/Obj/LdObjectPpRows.lean) from five inequalities in T.t₁, T.t₂, T.t₃, t₄: what is left:
    [inG] t₃ + [kpA] t₄; W: t₃; G_u: t₁; Ω: t₂ + t₃ (N instances: t₂ + N · t₃); s°: t₁ + t₂.
    `stdPq_needN` also assumes that the configuration's code has a position
    (`Nonempty (Fin O.Cf.C₀.n)`).

Notation: `T.D₁.need` .. (`LdRunD.need`, Cb/Ld/LdLinCloseDemand.lean): the bound after one more
test.

Limits: this file says nothing on the four whole tests but the number `need` for each oracle
message, in `T.t₁`, `T.t₂`, `T.t₃`, t₄ (`stdPq_needAt`, `stdPq_needOff`, `stdPq_needN`,
`stdPq_bOne`): the tests are parameters here (T₁ .. T₄ : `LdEnd`, in `D.mkT`, `D.mkX`), and
`LdRunD.OK` (Cb/Ld/LdLinCloseRuns.lean) is neither asked nor concluded here.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Obj.LdObjectPpData
import Cb.Ld.LdLinStdSpV
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The data. -/
structure StdPq {F E : Type} [Field F] [Field E] [Algebra F E] (O : LdOL F E) where
  n₀ : O.toC.NO.Ent
  neO : n₀.1 ≠ O.toC.iO
  four : ∀ o : O.toC.S.O,
    (∃ a, o = .inl (.inl (.inl a))) ∨ o = O.toC.nU ∨ o = O.toC.nO ∨ o = O.toC.nW ∨ o = .inr n₀.1
  slR    : Slf E O.Cl O.S.Ent
  BM     : Type
  [finBM : Fintype BM]
  rowsA  : BM → Slf E O.Cl O.S.Ent
  tgA    : O.Cl → BM → E
  inG    : O.S.O → Prop
  [dInG  : DecidablePred inG]
  kpA    : O.S.O → Prop
  [dKpA  : DecidablePred kpA]
  cov    : ∀ a, inG a ∨ kpA a
  /-- the four sets of long positions -/
  PU : Type
  [finPU : Fintype PU]
  [nePU : Nonempty PU]
  PO : Type
  [finPO : Fintype PO]
  [nePO : Nonempty PO]
  PC : Type
  [finPC : Fintype PC]
  [nePC : Nonempty PC]
  P4 : Type
  [finP4 : Fintype P4]
  [neP4 : Nonempty P4]
  posU : ∀ o : O.toC.S.O, PU → (O.toC.S.om o).P
  posO : ∀ o : O.toC.S.O, PO → (O.toC.S.om o).P
  posC : ∀ o : O.toC.S.O, PC → (O.toC.S.om o).P
  pos4 : ∀ o : O.toC.S.O, P4 → (O.toC.S.om o).P
  eU : ℕ
  eO : ℕ
  eC : ℕ
  e4 : ℕ

attribute [instance] StdPq.finBM StdPq.dInG StdPq.dKpA StdPq.finPU StdPq.nePU StdPq.finPO StdPq.nePO
  StdPq.finPC StdPq.nePC StdPq.finP4 StdPq.neP4

namespace StdPq
variable {F E : Type} [Field F] [Field E] [Algebra F E] {O : LdOL F E} (D : StdPq O)

/-- the shared mask holder -/
abbrev sO : O.toC.S.O := .inr D.n₀.1

abbrev k₁ : O.toC.S.O → Prop := fun o => o ≠ O.toC.nU
abbrev k₂ : (O.toC.S.sub (k₁ (O := O))).O → Prop := fun a => a.1 ≠ D.sO

/-- what is left after the two shared tests -/
abbrev ST₂ : Sig E := (O.toC.S.sub (k₁ (O := O))).sub D.k₂

/-- the members of the instance's group; what is kept after its test -/
def memC : O.toC.S.O → Prop
  | .inl (.inl (.inl x)) => D.inG x
  | _ => True
def kpC : O.toC.S.O → Prop
  | .inl (.inl (.inl x)) => D.kpA x
  | _ => False

instance : DecidablePred D.memC := fun o => match o with
  | .inl (.inl (.inl x)) => inferInstanceAs (Decidable (D.inG x))
  | .inl (.inl (.inr _)) => isTrue trivial
  | .inl (.inr _) => isTrue trivial
  | .inr _ => isTrue trivial
instance : DecidablePred D.kpC := fun o => match o with
  | .inl (.inl (.inl x)) => inferInstanceAs (Decidable (D.kpA x))
  | .inl (.inl (.inr _)) => isFalse fun h => h
  | .inl (.inr _) => isFalse fun h => h
  | .inr _ => isFalse fun h => h

/-- the instance's group -/
@[reducible] def Gc : Grp D.ST₂ :=
  { P := D.PC, mem := fun a => D.memC a.1.1, pos := fun a => D.posC a.1.1.1, e := D.eC }

/-- The plan. -/
@[reducible] def pl : LdLinPp O.toC where
  GU :=
    { P := D.PU, mem := fun o => o = O.toC.nU ∨ o = D.sO, pos := fun a => D.posU a.1, e := D.eU }
  GO :=
    { P := D.PO, mem := fun o => o = O.toC.nO ∨ o = D.sO, pos := fun a => D.posO a.1, e := D.eO }
  hU := Or.inl rfl
  hO := Or.inl rfl
  k₀ := ⟨D.sO, Or.inr rfl, Or.inr rfl, D.n₀.2⟩
  Rs₀ := fun n =>
    (∃ y, n = ⟨O.toC.nO, O.toC.lO y⟩) ∨ (∃ k, n = ⟨O.toC.nU, O.toC.lU k⟩) ∨ n = O.toC.eO D.n₀
  dRs₀ := Classical.decPred _
  kp₁ := k₁
  kp₂ := D.k₂
  kO₁ := by simp
  kO₂ := fun e => D.neO (Sum.inr.inj e).symm
  kW₁ := by simp
  kW₂ := by simp
  Gc := D.Gc
  hcO := trivial
  hcW := trivial
  kp₃ := fun a => D.kpC a.1.1
  dKp₃ := fun a => inferInstanceAs (Decidable (D.kpC a.1.1))
  restG := (((O.toC.upA D.slR).onSub k₁).onSub D.k₂).onG D.Gc

/-- the fourth group: all that is left -/
@[reducible] def G₄ : Grp D.pl.S₃ :=
  { P := D.P4, mem := fun _ => True, pos := fun a => D.pos4 a.1.1.1.1, e := D.e4 }

theorem hc₁ : ∀ o, D.pl.GU.mem o ∨ D.pl.kp₁ o := fun o => by
  by_cases h : o = O.toC.nU
  · exact Or.inl (Or.inl h)
  · exact Or.inr h

theorem hc₂ : ∀ o, D.pl.G₂.mem o ∨ D.pl.kp₂ o := fun a => by
  by_cases h : a.1 = D.sO
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

theorem hc₃ : ∀ o, D.pl.Gc.mem o ∨ D.pl.kp₃ o := fun a => by
  obtain ⟨⟨((x | x) | x) | x, h₁⟩, h₂⟩ := a
  · exact (D.cov x).imp id id
  · exact Or.inl trivial
  · exact Or.inl trivial
  · exact Or.inl trivial

variable [Fintype E]

/-- The fourth test, its evader and its whole test parameters. -/
@[reducible] def mkX (Z₄ : Evader E (D.G₄.Row {_b : D.BM // True}))
    (T₄ : LdEnd
      (D.G₄.joint (fun _ => O.Cl)
        (fun b : {_b : D.BM // True} => (D.pl.rowsL D.rowsA b.1).onG D.G₄) Z₄)) (L₄ t₄ : ℕ) :
    LdRowsD D.pl.S₃ O.toC.E₀ O.toC.Wpa (D.pl.rowsL D.rowsA) where
  G := D.G₄
  neP := D.neP4
  kp := fun _ => False
  decKp := fun _ => instDecidableFalse
  hc := fun _ => Or.inl trivial
  now := fun _ => True
  decNow := fun _ => instDecidableTrue
  Z := Z₄
  T := T₄
  L := L₄
  t := t₄
  d := (fun _ => (fun _ => 0, fun _ => 0), ())
  d' := ((fun _ => 0, fun _ => 0), (fun a => a.2.elim, ()))

/-- The three tests, their evaders and whole tests parameters; after them a closing X of the
preamble's rows. -/
@[reducible] def mkT (Z₁ : Evader E (D.pl.GU.Row (O.toC.Brc ⊕ Unit)))
    (T₁ : LdEnd (D.pl.GU.joint (fun _ => O.toC.Sh6) D.pl.r₁ Z₁)) (L₁ t₁ : ℕ)
    (Z₂ : Evader E (D.pl.G₂.Row Unit)) (T₂ : LdEnd (D.pl.G₂.joint (fun _ => O.toC.Sh6) D.pl.r₂ Z₂))
    (L₂ t₂ : ℕ) (Z₃ : Evader E (D.pl.Gc.Row LinB₂))
    (T₃ : LdEnd (D.pl.Gc.joint (fun _ => O.toC.St6) D.pl.r₃ Z₃)) (L₃ t₃ : ℕ)
    (X : LdRowsD D.pl.S₃ O.toC.E₀ O.toC.Wpa (D.pl.rowsL D.rowsA))
    (wX : (D.pl.S₃.sub X.kp).Wit × O.toC.Wpa) : LdLinPpT D.pl where
  ne₁ := D.nePU
  hc₁ := D.hc₁
  Z₁ := Z₁
  T₁ := T₁
  L₁ := L₁
  t₁ := t₁
  ne₂ := D.nePO
  hc₂ := D.hc₂
  Z₂ := Z₂
  T₂ := T₂
  L₂ := L₂
  t₂ := t₂
  ne₃ := D.nePC
  hc₃ := D.hc₃
  Z₃ := Z₃
  T₃ := T₃
  L₃ := L₃
  t₃ := t₃
  Q' := (X.one D.tgA wX).Q
  fa := (X.one D.tgA wX).fx
  d₁ := (fun _ => (fun _ => 0, fun _ => 0), ())
  d₁' := ((fun _ => 0, fun _ => 0), (fun _ => (fun _ => 0, fun _ => 0), ()))
  d₂ := (fun _ => (fun _ => 0, fun _ => 0), ())
  d₂' := ((fun _ => 0, fun _ => 0), (fun _ => (fun _ => 0, fun _ => 0), ()))
  d₃ := (fun _ => (fun _ => 0, fun _ => 0), ())
  d₃' := ((fun _ => 0, fun _ => 0), (fun _ => (fun _ => 0, fun _ => 0), ()))

end StdPq

section
variable {F E : Type} [Field F] [Field E] [Algebra F E] {O : LdOL F E} (D : StdPq O)

theorem stdPq_plain : D.pl.Plain where
  ne₀O := fun e => D.neO (Sum.inr.inj e)
  ne₀U := by simp
  rs₀O := fun y => Or.inl ⟨y, rfl⟩
  rs₀U := fun k => Or.inr (Or.inl ⟨k, rfl⟩)
  rs₀K := Or.inr (Or.inr rfl)
  rsSh := by
    rintro n (⟨y, rfl⟩ | ⟨k, rfl⟩ | rfl) <;> trivial

theorem stdPq_kept : D.pl.Kept where
  o₁ := by rintro o (rfl | rfl) <;> simp

theorem stdPq_shared : D.pl.Shared := by
  rintro o ((rfl | rfl) | (rfl | rfl)) <;> trivial

/-- a message that the preamble left is kept at both shared bridges -/
theorem stdPq_k12 (a : O.toC.Sa.O) :
    ∃ (h₁ : D.pl.kp₁ (.inl (.inl (.inl a)))) (_ : D.pl.kp₂ ⟨_, h₁⟩), True :=
  ⟨by simp, by simp, trivial⟩

/-- The mask, at standard senders. -/
theorem stdPq_mask [Fintype E] {Fp : Type} [Field Fp] [Fintype Fp] [Algebra Fp E]
    (Ts : O.toC.P.Std Fp) (n₀ : Σ a, Ts.YO.Fr a) (hPl : Ts.Places) (hn : D.n₀ = Ts.YO.entF n₀) :
    (⟨D.pl.k₀.o, D.pl.k₀.j⟩ : O.toC.S.Ent) = O.toC.eO (Ts.YO.entF n₀) ∧
    ∀ n, D.pl.Rs₀ (O.toC.eO n) → Ts.YO.NoPad n := by
  have inj : ∀ n n' : O.toC.NO.Ent, O.toC.eO n = O.toC.eO n' → n = n' := by
    rintro ⟨a, j⟩ ⟨a', j'⟩ e
    obtain ⟨e1, e2⟩ := Sigma.mk.inj_iff.1 e
    obtain rfl : a = a' := Sum.inr.inj e1
    have e3 : j = j' := eq_of_heq e2
    rw [e3]
  refine ⟨congrArg O.toC.eO hn, ?_⟩
  rintro n (⟨y, e⟩ | ⟨k, e⟩ | e)
  · rw [inj n ⟨O.toC.iO, O.toC.lO y⟩ e]
    exact ⟨Sum.inl (Ts.qO y), hPl.lO y⟩
  · exact absurd (congrArg Sigma.fst e) (by simp [LdLinC.eO])
  · rw [inj n D.n₀ e, hn]
    exact ⟨Sum.inr n₀.2, rfl⟩

end

section
variable {F E : Type} [Field F] [Field E] [Fintype E] [Algebra F E] {O : LdOL F E}
  (D : StdPq O) (T : LdLinPpT D.pl)

/-- What Ω and the splitting's message bear: equations, for every datum of the three tests. -/
theorem stdPq_needAt (N t₄ : ℕ) :
    T.D₁.need (T.D₂.need (T.D₃.need fun _ => t₄)) (.inr O.toC.iO) = T.t₂ + T.t₃ ∧
    T.D₁.need (T.D₂.need (T.D₃.need fun _ => t₄)) (.inr D.n₀.1) = T.t₁ + T.t₂ ∧
    T.D₁.need (T.D₂.need (T.D₃.needV N (fun a => O.toC.isSh a.1.1) fun _ => t₄)) (.inr O.toC.iO) =
      T.t₂ + N * T.t₃ ∧
    T.D₁.need (T.D₂.need (T.D₃.needV N (fun a => O.toC.isSh a.1.1) fun _ => t₄)) (.inr D.n₀.1) =
      T.t₁ + T.t₂ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show T.D₁.need (T.D₂.need (T.D₃.need fun _ => t₄)) O.toC.nO = T.t₂ + T.t₃
    simp [LdRunD.need, StdPq.memC, StdPq.kpC, D.neO.symm]
  · simp [LdRunD.need, D.neO]
  · show T.D₁.need (T.D₂.need (T.D₃.needV N (fun a => O.toC.isSh a.1.1) fun _ => t₄)) O.toC.nO =
      T.t₂ + N * T.t₃
    simp [LdRunD.need, LdRunD.needV, LdLinC.isSh, StdPq.memC, StdPq.kpC, D.neO.symm]
  · simp [LdRunD.need, D.neO]

/-- The four families of inequalities for one instance. -/
theorem stdPq_needOff (t₄ : ℕ) (ba : O.toC.Sa.O → ℕ) (tW : O.toC.P.NW.O → ℕ)
    (tU : O.toC.P.NU.O → ℕ) (tO : O.toC.P.NO.O → ℕ)
    (iA : ∀ a, (if D.inG a then T.t₃ else 0) + (if D.kpA a then t₄ else 0) ≤ ba a)
    (iW : T.t₃ ≤ tW O.toC.iW) (iU : T.t₁ ≤ tU O.toC.iU)
    (iO : T.t₂ + T.t₃ ≤ tO O.toC.iO) (iS : T.t₁ + T.t₂ ≤ tO D.n₀.1) :
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need fun _ => t₄)) (.inl (.inl (.inl a))) ≤ ba a) ∧
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need fun _ => t₄)) (.inl (.inl (.inr a))) ≤ tW a) ∧
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need fun _ => t₄)) (.inl (.inr a)) ≤ tU a) ∧
    ∀ a, T.D₁.need (T.D₂.need (T.D₃.need fun _ => t₄)) (.inr a) ≤ tO a := by
  have nA : ∀ a, T.D₁.need (T.D₂.need (T.D₃.need fun _ => t₄)) (.inl (.inl (.inl a))) =
      (if D.inG a then T.t₃ else 0) + (if D.kpA a then t₄ else 0) := fun a => by
    simp [LdRunD.need, StdPq.memC, StdPq.kpC]
  have nW : T.D₁.need (T.D₂.need (T.D₃.need fun _ => t₄)) O.toC.nW = T.t₃ := by
    simp [LdRunD.need, StdPq.memC, StdPq.kpC]
  have nU : T.D₁.need (T.D₂.need (T.D₃.need fun _ => t₄)) O.toC.nU = T.t₁ := by simp [LdRunD.need]
  obtain ⟨nO, nS, -, -⟩ := stdPq_needAt D T 0 t₄
  refine ⟨fun a => (nA a).le.trans (iA a), fun a => ?_, fun a => ?_, fun a => ?_⟩
  · rcases D.four (.inl (.inl (.inr a))) with ⟨x, e⟩ | e | e | e | e
    · simp at e
    · simp at e
    · simp at e
    · obtain rfl : a = O.toC.iW := Sum.inr.inj (Sum.inl.inj (Sum.inl.inj e))
      exact nW.le.trans iW
    · simp at e
  · rcases D.four (.inl (.inr a)) with ⟨x, e⟩ | e | e | e | e
    · simp at e
    · obtain rfl : a = O.toC.iU := Sum.inr.inj (Sum.inl.inj e)
      exact nU.le.trans iU
    all_goals simp at e
  · rcases D.four (.inr a) with ⟨x, e⟩ | e | e | e | e
    · simp at e
    · simp at e
    · obtain rfl : a = O.toC.iO := Sum.inr.inj e
      exact nO.le.trans iO
    · simp at e
    · obtain rfl : a = D.n₀.1 := Sum.inr.inj e
      exact nS.le.trans iS

/-- Under the hypotheses below, what is left behind the three tests is a slot's own: the fourth
test's positions are not multiplied -/
theorem stdPq_bOne [Nonempty (Fin O.Cf.C₀.n)]
    (X : LdRowsD D.pl.S₃ O.toC.E₀ O.toC.Wpa (D.pl.rowsL D.rowsA)) (hG : ∀ o, X.G.mem o)
    (hk : ∀ o, ¬ X.kp o) (N : ℕ) (a : D.pl.S₃.O) : X.bOneP N a = X.t := by
  obtain ⟨⟨⟨((a | a) | a) | a, h1⟩, h2⟩, h3⟩ := a
  · simp [LdRunD.needV, LdLinC.isSh, LdRowsD.bOneP, hG, hk]
  · exact h3.elim
  · exact h3.elim
  · exact h3.elim

/-- The four families of inequalities for N instances. -/
theorem stdPq_needN [Nonempty (Fin O.Cf.C₀.n)]
    (X : LdRowsD D.pl.S₃ O.toC.E₀ O.toC.Wpa (D.pl.rowsL D.rowsA)) (hG : ∀ o, X.G.mem o)
    (hk : ∀ o, ¬ X.kp o) (N : ℕ) (ba : O.toC.Sa.O → ℕ) (tW : O.toC.P.NW.O → ℕ)
    (tU : O.toC.P.NU.O → ℕ) (tO : O.toC.P.NO.O → ℕ)
    (iA : ∀ a, (if D.inG a then T.t₃ else 0) + (if D.kpA a then X.t else 0) ≤ ba a)
    (iW : T.t₃ ≤ tW O.toC.iW) (iU : T.t₁ ≤ tU O.toC.iU)
    (iO : T.t₂ + N * T.t₃ ≤ tO O.toC.iO) (iS : T.t₁ + T.t₂ ≤ tO D.n₀.1) :
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.needV N (fun a => O.toC.isSh a.1.1) (X.bOneP N)))
        (.inl (.inl (.inl a))) ≤ ba a) ∧
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.needV N (fun a => O.toC.isSh a.1.1) (X.bOneP N)))
        (.inl (.inl (.inr a))) ≤ tW a) ∧
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.needV N (fun a => O.toC.isSh a.1.1) (X.bOneP N)))
        (.inl (.inr a)) ≤ tU a) ∧
    ∀ a, T.D₁.need (T.D₂.need (T.D₃.needV N (fun a => O.toC.isSh a.1.1) (X.bOneP N))) (.inr a) ≤
      tO a := by
  have hb : X.bOneP N = fun _ => X.t := funext (stdPq_bOne D X hG hk N)
  rw [hb]
  have nA : ∀ a,
      T.D₁.need (T.D₂.need (T.D₃.needV N (fun a => O.toC.isSh a.1.1) fun _ => X.t))
          (.inl (.inl (.inl a))) =
        (if D.inG a then T.t₃ else 0) + (if D.kpA a then X.t else 0) := fun a => by
    simp [LdRunD.need, LdRunD.needV, LdLinC.isSh, StdPq.memC, StdPq.kpC]
  have nW : T.D₁.need (T.D₂.need (T.D₃.needV N (fun a => O.toC.isSh a.1.1) fun _ => X.t)) O.toC.nW =
      T.t₃ := by
    simp [LdRunD.need, LdRunD.needV, LdLinC.isSh, StdPq.memC, StdPq.kpC]
  have nU : T.D₁.need (T.D₂.need (T.D₃.needV N (fun a => O.toC.isSh a.1.1) fun _ => X.t)) O.toC.nU =
      T.t₁ := by
    simp [LdRunD.need]
  obtain ⟨-, -, nO, nS⟩ := stdPq_needAt D T N X.t
  refine ⟨fun a => (nA a).le.trans (iA a), fun a => ?_, fun a => ?_, fun a => ?_⟩
  · rcases D.four (.inl (.inl (.inr a))) with ⟨x, e⟩ | e | e | e | e
    · simp at e
    · simp at e
    · simp at e
    · obtain rfl : a = O.toC.iW := Sum.inr.inj (Sum.inl.inj (Sum.inl.inj e))
      exact nW.le.trans iW
    · simp at e
  · rcases D.four (.inl (.inr a)) with ⟨x, e⟩ | e | e | e | e
    · simp at e
    · obtain rfl : a = O.toC.iU := Sum.inr.inj (Sum.inl.inj e)
      exact nU.le.trans iU
    all_goals simp at e
  · rcases D.four (.inr a) with ⟨x, e⟩ | e | e | e | e
    · simp at e
    · simp at e
    · obtain rfl : a = O.toC.iO := Sum.inr.inj e
      exact nO.le.trans iO
    · simp at e
    · obtain rfl : a = D.n₀.1 := Sum.inr.inj e
      exact nS.le.trans iS

end

/-- Under the hypotheses below, `R.PlacesOKP D.pl plR` holds: the conditions on places at the end of
a request. -/
theorem stdPq_places {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    {Kc : Type} (R : LdORE F E Kc) (D : StdPq R.O.d.ol) (plR : R.Bn → R.S.Ent → Prop)
    (own : ∀ i, D.inG (R.wAt i).1) (laid : ∀ a, D.inG (R.μAt a).1)
    (off : ∀ b x n, ¬ plR b n → R.sl b x n = 0) (kept : ∀ b n, plR b n → D.kpA n.1) :
    R.PlacesOKP D.pl plR :=
  { own := fun i => ⟨(stdPq_k12 D _).1, (stdPq_k12 D _).2.1, own i⟩
    laid := fun a => ⟨(stdPq_k12 D _).1, (stdPq_k12 D _).2.1, laid a⟩
    off := off
    kept := fun b n h => ⟨(stdPq_k12 D _).1, (stdPq_k12 D _).2.1, kept b n h⟩ }

end Cb
