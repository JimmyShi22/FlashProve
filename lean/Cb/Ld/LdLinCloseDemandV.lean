-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinCloseDemandV.lean: what the tests of a closing need of the oracle messages in a batch: a
slot's own oracle message bears what its slot reads; a shared one bears the union over the slots.

Definitions, and statements (each statement a `Prop` in `Cb.Spec`); the proofs are in
Cb/Ld/LdLinCloseDemandVProofs.lean.
It uses Ior/LinkVBears.lean, Ior/LinkVBearsMore.lean (demands on families of sets of positions, one
set for each slot: `QFam`; "kept by subsets of the set of slots": `Her`; the half of "bears what
follows" without a budget: `IOR.NeedsV`), Cb/Ld/LdLinCloseChain.lean (one whole test on a group as a
link: `D.link`), Cb/Ld/LdLinCloseDemand.lean (the same question for one instance),
Cb/Ld/LdLinBHon.lean (the demands of the test for linear constraints for a batch: `qv5`).
In standard terms: a batch runs up to N instances (slots) of the protocol together; some oracle
messages are shared by all slots, the others are a slot's own. `R.NeedsV A qi qo`: whenever the
family (U_j) of sets of positions of R's output oracles is within qo, the family of what R needs of
its input oracles is within qi.

Main names:
  `S.qV sh q₀ b`: a demand on families (U_j) of sets of positions of (further oracles, the words of
    the signature S). sh: which oracle messages are shared by all slots. Of the further oracles: q₀
    of the family of the left parts; of an oracle message o that is a slot's own: each U_j holds at
    most b o of its long positions; of a shared o: the union of the U_j holds at most b o.
  `Spec.ldDemandV_her`, `Spec.ldDemandV_empty`: `S.qV` is kept by subsets of the set of slots, and
    holds of the empty family, if q₀ is and does.
The rules, for one whole test D on a group beside what is carried, under `D.OK`:
  `Spec.ldDemandV_need`: for one slot, as sets: what is needed of the statement's oracles, if what
    follows needs U, are the sources of (at most `D.t` common long positions of the group, and U).
  `Spec.ldDemandV_shared`: the test is run once, by the shared part (all slots see the same verifier
    messages): every member bears `D.t` more, shared or not: the bound `D.need b'` of one instance.
  `Spec.ldDemandV_local`: the test is run in every slot (any annotation): a slot's own member bears
    `D.t` more; a shared member bears N · D.t more: the bound `D.needV N sh b'`.
For the test for linear constraints:
  `Spec.ldDemandV_step`: the re-bracketing of Cb/Ld/LdLinClosePre.lean, at any annotation: if b is
    at most the senders' numbers on the three families and at most ba on what the preamble left, and
    qa allows what q₀ and ba allow, then through it `C.S.qV C.isSh` (each q₀) b is within the
    batch's demand `qv5` (`NeedsV`).
  `Spec.ldDemandV_plan`: the plan without a splitting in a batch (first test once, second test in
    every slot), all members of the first group shared (`p.Shared`), in plain numbers: of an oracle
    message of which the closing of what is left needs at most c: a slot's own (W's family, what the
    preamble left): t₂ + c; a shared one (G_u's family, Ω's): t₁ + N · t₂ + c. So Ω's sender has to
    bear t₁ + N · t₂. This bound is stated for all members of the two shared families, since the
    second group may hold any of them: it is wider than needed for one that is no member of the
    second group:
  `Spec.ldDemandV_plan_first`: an oracle message that is no member of the second group (G_u, in a
    write-up of ours (lean/CREDITS.md)), and of which the closing of what is left needs at
    most c, bears t₁ + c alone.

Limits: this file says nothing on a budget, an honest side or soundness: those are other files'. It
says nothing on plans with a splitting.
The rule on unions of positions follows this protocol's technical report, which follows a proof of
the paper that this protocol builds on; the numbers asked of the senders follow that report's
theorem on linear constraints, which follows Brakedown (GLSTW23), TensorSwitch (BFRW25) and that
paper (lean/CREDITS.md).
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdLinCloseDemandProofs
import Cb.Ld.LdLinBHon
import Ior.LinkVBearsMore

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The demand for families of slots. -/
def Sig.qV {E : Type} (S : Sig E) {E₀ : ExtSpec} {N : ℕ} (sh : S.O → Prop)
    (q₀ : QFam E₀ N) (b : S.O → ℕ) :
    QFam (E₀.prod S.ext) N := fun J Us =>
  q₀ J (fun j => (Us j).toLeft) ∧
  (∀ o,
    ¬ sh o → ∀ j, cnt (fun x : (S.om o).P => (Sum.inr ⟨o, x⟩ : (E₀.prod S.ext).Pos) ∈ Us j) ≤ b o) ∧
  ∀ o, sh o → cnt (fun x : (S.om o).P => ∃ j, (Sum.inr ⟨o, x⟩ : (E₀.prod S.ext).Pos) ∈ Us j) ≤ b o

/-- The bound after one more test that is run in every slot. -/
def LdRunD.needV {E : Type} [Field E] [Fintype E] {S : Sig E} (D : LdRunD S) (N : ℕ)
    (sh : S.O → Prop) [DecidablePred sh] (b' : (S.sub D.kp).O → ℕ) : S.O → ℕ :=
  fun o =>
    (if D.G.mem o then (if sh o then N * D.t else D.t) else 0) +
      (if h : D.kp o then b' ⟨o, h⟩ else 0)

/-- the shared oracle messages at the end of the test for linear constraints: those sent with G_u
and with Ω -/
def LdLinC.isSh {E ι κ J Y : Type} [Field E] (C : LdLinC E ι κ J Y) : C.S.O → Prop
  | .inl (.inl _) => False
  | _ => True

instance {E ι κ J Y : Type} [Field E] (C : LdLinC E ι κ J Y) :
    DecidablePred C.isSh := fun o => match o with
  | .inl (.inl _) => isFalse fun h => h
  | .inl (.inr _) => isTrue trivial
  | .inr _ => isTrue trivial

namespace Spec

def ldDemandV_her : Prop :=
  ∀ (E : Type) (S : Sig E) (E₀ : ExtSpec) (N : ℕ) (sh : S.O → Prop) (q₀ : QFam E₀ N) (b : S.O → ℕ),
    q₀.Her → (S.qV sh q₀ b).Her

def ldDemandV_empty : Prop :=
  ∀ (E : Type) (S : Sig E) (E₀ : ExtSpec) (N : ℕ) (sh : S.O → Prop) (q₀ : QFam E₀ N) (b : S.O → ℕ),
    (∀ J, q₀ J fun _ => ∅) → ∀ J, S.qV sh q₀ b J fun _ => ∅

open Classical in
/-- What one slot needs, as sets. -/
def ldDemandV_need : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (D : LdRunD S) (St₀ Wp : Type) (E₀ : ExtSpec)
      (A₀ : IOR.Rels Unit St₀ E₀ ((S.sub D.kp).Msg × Wp)) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp),
    D.OK → ∀ (ρ : Rho (D.link A₀ d d').R.shape) (U : Finset (LdCarE D.kp E₀).Pos),
      ∃ U' : Finset (LdBrE D.G D.kp E₀).Pos,
        U'.toLeft.card ≤ D.t ∧
        U'.toRight = U ∧
        (D.link A₀ d d').R.need ρ U = U'.biUnion (ldBrG D.G D.kp E₀).src

/-- The test is run once, by the shared part. -/
def ldDemandV_shared : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (D : LdRunD S) (St₀ Wp : Type) (E₀ : ExtSpec)
      (A₀ : IOR.Rels Unit St₀ E₀ ((S.sub D.kp).Msg × Wp)) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp)
      (N : ℕ) (sh : S.O → Prop) (q₀ : QFam E₀ N) (b' : (S.sub D.kp).O → ℕ),
    D.OK → (D.link A₀ d d').R.NeedsV (RoundSplits.const (RAnn.ofShared .sh) _) (S.qV sh q₀ (D.need b'))
      ((S.sub D.kp).qV (fun a => sh a.1) q₀ b')

/-- The test is run in every slot. -/
def ldDemandV_local : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (D : LdRunD S) (St₀ Wp : Type) (E₀ : ExtSpec)
      (A₀ : IOR.Rels Unit St₀ E₀ ((S.sub D.kp).Msg × Wp)) (d : S.Wit × Wp)
      (d' : LdBrW D.G D.kp Wp) (N : ℕ) (sh : S.O → Prop) [DecidablePred sh] (q₀ : QFam E₀ N)
      (b' : (S.sub D.kp).O → ℕ) (A : RoundSplits (D.link A₀ d d').R.shape),
    D.OK → (D.link A₀ d d').R.NeedsV
      A (S.qV sh q₀ (D.needV N sh b')) ((S.sub D.kp).qV (fun a => sh a.1) q₀ b')

section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

/-- Through the re-bracketing. -/
def ldDemandV_step : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (Stq : Type) (Bq : IOR.Rels Unit Stq C.E₀ (C.S.Msg × C.Wpa))
      (fq : C.St6 → Stq) (Sn : C.P.Snd) (qa : Finset C.P.Ea.Pos → Prop) (N : ℕ)
      (q₀ : Finset C.E₀.Pos → Prop) (ba : C.Sa.O → ℕ) (b : C.S.O → ℕ)
      (A : RoundSplits (C.link fq Bq).R.shape),
    (∀ W, C.Sa.qFam q₀ ba W → qa W) → (∀ a, b (.inl (.inl (.inl a))) ≤ ba a) →
    (∀ a, b (.inl (.inl (.inr a))) ≤ Sn.tW a) → (∀ a, b (.inl (.inr a)) ≤ Sn.tU a) →
    (∀ a, b (.inr a) ≤ Sn.tO a) →
    (C.link fq Bq).R.NeedsV A (C.P.qv5 Sn qa N) (C.S.qV C.isSh (QFam.each q₀) b)

/-- The plan in a batch, in plain numbers. -/
def ldDemandV_plan : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPl C) (T : LdLinPlT p) (N : ℕ)
      (b' : p.S₂.O → ℕ) (o : C.S.O) (c : ℕ),
    p.Shared → (∀ h₁ h₂, b' ⟨⟨o, h₁⟩, h₂⟩ ≤ c) →
    T.D₁.need (T.D₂.needV N (fun a => C.isSh a.1) b') o ≤
      (if C.isSh o then T.t₁ + N * T.t₂ else T.t₂) + c

/-- An oracle message that is no member of the second group, and of which the closing of what is
left needs at most c, bears the first test alone: t₁ + c. -/
def ldDemandV_plan_first : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPl C) (T : LdLinPlT p) (N : ℕ)
      (b' : p.S₂.O → ℕ) (o : C.S.O) (c : ℕ),
    (∀ h₁, ¬ p.G₂.mem ⟨o, h₁⟩) → (∀ h₁ h₂, b' ⟨⟨o, h₁⟩, h₂⟩ ≤ c) →
    T.D₁.need (T.D₂.needV N (fun a => C.isSh a.1) b') o ≤ T.t₁ + c

end
end Spec
end Cb
