-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdPsc.lean: the zero-knowledge sumcheck for a polynomial summand, as an interactive oracle
reduction (this file does not say zero knowledge: see Limits).

This file defines a sumcheck protocol for the sum of a polynomial in several maps, and states, each
under the hypotheses of its statement, its completeness and its round-by-round knowledge soundness
on the statements with the condition.
It holds the protocol as a term, its honest side, the relations, the numbers, and the statements
(each a `Prop` in `Cb.Spec`). The proofs are in Cb/Ld/LdPscProofs.lean, Cb/Ld/LdPscProofsIor.lean
and Cb/Ld/LdPscProofsOur.lean.

The claim: the oracles of the statement hold messages; m : J → E are all their entries, masks
included. The claim of the input statement (target τ, state st) is
    (sum over all variables, each with its own functional) of S(st; X, F_1(X), .., F_a(X))
      + < sl_s(st), m > = τ,    τ public,
where the F_j are polynomial functions of the point X that are computed from (st, m) (extensions of
vector maps: linear in m or not), S is a polynomial in them with public coefficients, and
< sl_s(st), m > is a linear form that reads masks left over from an earlier block.

The protocol: the prover sends no oracle and the verifier reads none: the block's own masks are
entries of m, sent and sampled before the block.
  Round 0: the prover sends μ', the sum of one hiding polynomial U (Cb/Ld/LdHide.lean) whose
    coefficients are own mask entries; then the verifier sends a coefficient ε from all of E.
  Round j (one for each variable): plain sumcheck on
      H = U + ε ( S(st; X, masked maps) + < sl_s(st), m > ψ_1(X_1) .. ψ_k(X_k) ):
    the prover sends the n_j + 1 coefficients of a round polynomial, the verifier a challenge.
  Last round: the prover sends, in the clear, the values v_a of the masked maps a ∈ A (the revealed
    maps) at the point of challenges; the verifier's message is empty.
  Checks, all in the clear: the first round polynomial sums to μ' + ε τ, each later one to the value
    of the one before at its challenge. No product check, no quadratic predicate, no hidden target.
  Output, claims with public targets on the same oracles:
    the row on the hiding polynomial's coefficients (`UHolds`):
      U(γ) + ε ψ(γ) < sl_s(st), m > + ε ∑_b S1_b(st; γ, v) G_b(γ)
        = (last round polynomial at the last challenge) - ε S0(st; γ, v);
    the row on a revealed map's value (`EHolds`), one for each: (masked map a at γ) = v_a.
  The maps that are not revealed (b ∈ B; G_b: `PscPar.Gb`): the summand is affine in them once the
    revealed ones are fixed. Here that is so by form:
      S = S0(st; X, values of A) + ∑_b S1_b(st; X, values of A) · (value of b).
    They stay as terms of the first row.

Inner masks, two layers:
  `PscPar`: the abstract layer. All proofs on the block (completeness, knowledge soundness) are at
    this layer. At this layer the input claim is the sum of the masked summand. That inner masks do
    not change the sum, whatever their values, is a condition on an instance and is not named here;
    for our instance it is `Spec.psc_our_sum`.
  `PscOur`: the instance that we use: k variables and one dummy last variable Y with the functional
    g ↦ g(0), ψ = 1, degree DY, challenge β from E without 0; masked map: F_a(X) + c_a Y, with
    c_a = m (cAt a) one own mask entry for each revealed map. `Spec.psc_our_next`: if F_a at the
    point is itself a sum (a map that is never sent), the row on its value (`Spec.psc_our_val`) is
    the input claim of a next block, with the incoming form β at the entry c_a and the target v_a.
  With no revealed map there is no dummy variable and no last round: that block is `PscPar.core`
    alone, at A = Empty; its output claim, the end claim (`MidHolds`), is then the first row
    (`Spec.psc_mid_empty`).

The block is `core`, then `ends` (`IOR.seq`): core = round 0 and the rounds of the variables, to the
end claim: H(γ) = last value; ends = the last round.
A variable is split in its format (`PFmt`: degree, node set, challenge set with its map to E), which
the shape of the protocol reads, and its data (`PDat`: nodes, weights, ψ), which may depend on the
state: equality weights at a point that an earlier verifier message fixed.
The order of the coefficient ε holds by the form of the term: state, target and functionals stand in
the input statement; the oracles that hold the masks are in the input statement with their samples
(this of the joint that is plugged in, not of the term: see Limits); μ' and ε are a round of their
own, μ' first. Nothing is merged.

The oracles: the block is told nothing of codes. The term `Y.psc Ex` has the claim as its explicit
part and copies oracles of any kind Ex; a carried part Cr of the explicit part (the samples) and
further oracles are copied by `IOR.keep` (Ior/Frame.lean). Of the statement, verifier and prover
read the claim only; the prover also reads its witness's entries (`msg w`).
  `PscBase` (its fields: see the record; `on`: a condition on statements). Whatever else is claimed
    of state, oracles and witness is a part of its relations: it rides along.
  `PscBase.Det`: on the statements with the condition the relaxed relation determines the entries (a
    relaxation by decoding with a sample, on collision-free statements). It is a hypothesis of
    knowledge soundness, and the reason why no list size enters an error.
  At the base (no carried part; in `Spec.psc_know_at` the witness is (messages, further part);
    `baseIn`, `baseOut` over any joint A0 that rides along): `Spec.psc_acc_base`,
    `Spec.psc_carry_base`, `Spec.psc_keeps`, and `Spec.psc_know_at`: knowledge soundness for each
    fixed tuple of messages, the form that the lifting rule of Cb/Ld/LdSigLift.lean takes.

Numbers, under the hypotheses of the statements below. Rounds: 2 + number of variables (`PscOur`:
k + 3), the last with an empty verifier message.
Errors, as counts: 1 of |E|; n_j of the j-th challenge set; (`PscOur`: DY of |E| - 1;) 0. No query.
Extractor: the identity. Completeness is perfect.

Main names, each under the hypotheses of its statement:
  `Spec.psc_acc`: completeness.
  `Spec.psc_sound_at` (the main step, for each fixed tuple of entries), `Spec.psc_know`:
    round-by-round knowledge soundness on the statements with the condition; `Spec.psc_carry`: the
    condition is carried.
  `Spec.psc_core_acc`, `Spec.psc_core_sound_at`, `Spec.psc_core_know`, `Spec.psc_core_acc_base`,
    `Spec.psc_core_know_at`: the same for `core` alone.
  `Spec.psc_our_sum` to `Spec.psc_our_card`: the instance.

Limits: between joints that leave the entries free the block is not knowledge sound: the bad
challenges depend on the entries.
That ε comes after the samples of the oracles that hold the masks is true of the joint that is
plugged in (samples in the carried part of the input statement), not of the term alone.
Declared differences to the text that we follow.
  (a) A functional is a weighted sum of values at nodes (Cb/Ld/LdHide.lean), not any linear
      functional.
  (b) All n_j + 1 coefficients of a round polynomial are sent; the text's count of scalars leaves
      out the one that the check fixes.
  (c) S, F are functions with a degree bound in each variable (`PscPar.DegOK`), not syntactic
      polynomials.
  (d) The honest prover's coefficients of the summand's round polynomials are taken by choice
      (`hCo`); if E has more elements than the degree they are unique.
  (e) One witness type for relation and relaxation (`Iop.IOR.Rels`).
This file does not say zero knowledge: with its masks in the input the block is not zero knowledge
for a worst-case witness; its item "masked messages" is in Cb/Ld/LdPscMask.lean, Cb/Ld/LdPscZk.lean.
So the record `IOR.GoodT` is not claimed. This file says nothing on where masks lie in rows and
groups; nothing on running times or on succinct forms.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdHide
import Cb.Ld.LdRel
import Ior.KnowCollGood

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

noncomputable section

/-! ## 1. Any summand: degrees by variable, round polynomials -/

section Summand
variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

/-- The summand has the degrees of the variables: in each variable, all others fixed, it is a
polynomial with the n + 1 coefficients of that variable. -/
def HDeg : (l : List (HVar R)) → (HPt l → M) → Prop
  | [], _ => True
  | v :: l, f =>
    (∀ xs : HPt l, ∃ c : Fin (v.n + 1) → M, ∀ x : R, f (x, xs) = hev c x) ∧
    ∀ x : R, HDeg l fun xs => f (x, xs)

open Classical in
/-- coefficients of a function that is a polynomial with n + 1 coefficients (0 if it is none) -/
def hCo (n : ℕ) (g : R → M) : Fin (n + 1) → M :=
  if h : ∃ c : Fin (n + 1) → M, ∀ x, g x = hev c x then h.choose else 0

/-- The round polynomials of a summand at the challenges γ: earlier variables at the challenges,
later ones summed. -/
def hTrOf : (l : List (HVar R)) → (HPt l → M) → HPt l → RIdx l → M
  | [], _, _, i => i.elim
  | v :: l, f, _, .inl t => hCo v.n (fun x => hSumAll l fun xs => f (x, xs)) t
  | _ :: l, f, γ, .inr i => hTrOf l (fun xs => f (γ.1, xs)) γ.2 i

/-- the point 0 -/
def hZero : (l : List (HVar R)) → HPt l
  | [] => ()
  | _ :: l => (0, hZero l)

end Summand

/-! ## 2. Variables: format and data -/

/-- The format of a variable: what the shape of the protocol reads. -/
structure PFmt (E : Type) where
  /-- the largest degree of a round polynomial -/
  n : ℕ
  /-- the names of the nodes of the functional -/
  S : Type
  [finS : Fintype S]
  /-- the challenge set -/
  Ch : Type
  [finCh : Fintype Ch]
  [neCh : Nonempty Ch]
  val : Ch → E

attribute [instance] PFmt.finS PFmt.finCh PFmt.neCh

/-- The data of a variable: nodes and weights of the functional, and ψ. They may depend on the
state. -/
structure PDat (E : Type) (f : PFmt E) where
  node : f.S → E
  wt : f.S → E
  psi : Fin (f.n + 1) → E

section Fmt
variable {E : Type}

/-- the variable, as an `HVar` of Cb/Ld/LdHide.lean -/
@[reducible] def PFmt.var (f : PFmt E) (d : PDat E f) : HVar E :=
  { n := f.n, S := f.S, node := d.node, wt := d.wt, psi := d.psi }

def PDats : List (PFmt E) → Type
  | [] => Unit
  | f :: l => PDat E f × PDats l

def pVars : (l : List (PFmt E)) → PDats l → List (HVar E)
  | [], _ => []
  | f :: l, d => f.var d.1 :: pVars l d.2

/-- names of the coefficients of the hiding polynomial, and points, without the data -/
def PIdx : List (PFmt E) → Type
  | [] => Unit
  | f :: l => Fin f.n ⊕ PIdx l
def PPt : List (PFmt E) → Type
  | [] => Unit
  | _ :: l => E × PPt l

def pIx : (l : List (PFmt E)) → (d : PDats l) → HIdx (pVars l d) ≃ PIdx l
  | [], _ => Equiv.refl Unit
  | _ :: l, d => Equiv.sumCongr (Equiv.refl _) (pIx l d.2)
def pH : (l : List (PFmt E)) → (d : PDats l) → PPt l → HPt (pVars l d)
  | [], _, _ => ()
  | _ :: l, d, γ => (γ.1, pH l d.2 γ.2)

variable [Field E]

/-- a round of the sumcheck: n + 1 coefficients in the clear, a challenge -/
@[reducible] def pRound (f : PFmt E) : Round :=
  { Orc := Unit, Pos := Empty, Sym := fun _ => Unit, rd := fun _ p => p.elim,
    Plain := Fin (f.n + 1) → E, Chal := f.Ch, dOrc := (), dPlain := 0 }
abbrev pRounds (l : List (PFmt E)) : Shape := l.map pRound

/-- the point of challenges; the round polynomials, named as in Cb/Ld/LdHide.lean (`RIdx`); the
errors -/
def pG : (l : List (PFmt E)) → Rho (pRounds l) → PPt l
  | [], _ => ()
  | f :: l, ρ => (f.val ρ.1, pG l ρ.2)
def pQ : (l : List (PFmt E)) → (d : PDats l) → Plains (pRounds l) → RIdx (pVars l d) → E
  | [], _, _, i => i.elim
  | _ :: _, _, pl, .inl t => pl.1 t
  | _ :: l, d, pl, .inr i => pQ l d.2 pl.2 i
def pErr : (l : List (PFmt E)) → Err (pRounds l)
  | [] => ()
  | f :: l => (f.n, pErr l)

/-- A prover from its messages in closed form: q γ holds all round polynomials at the challenges γ;
in each round the prover sends its part of q at the challenges so far (this and the later ones set
to 0: for the q that are meant, the part does not depend on them). -/
def pStrat {β : Type} :
    (l : List (PFmt E)) → (d : PDats l) → (HPt (pVars l d) → RIdx (pVars l d) → E) →
    (PPt l → β) → Strat (pRounds l) β
  | [], _, _, res => res ()
  | f :: l, d, q, res =>
    (((), fun t => q (0, hZero (pVars l d.2)) (.inl t)),
      fun c => pStrat l d.2 (fun γ i => q (f.val c, γ) (.inr i)) fun γ => res (f.val c, γ))

/-- Round 0: a scalar, the coefficient from all of E. The last round: the values, no verifier
message. -/
@[reducible] def pRound0 (E : Type) [Field E] [Fintype E] : Round :=
  { Orc := Unit, Pos := Empty, Sym := fun _ => Unit, rd := fun _ p => p.elim, Plain := E, Chal := E,
    dOrc := (), dPlain := 0 }
@[reducible] def pRoundV (E A : Type) [Field E] : Round :=
  { Orc := Unit, Pos := Empty, Sym := fun _ => Unit, rd := fun _ p => p.elim, Plain := A → E,
    Chal := Unit, dOrc := (), dPlain := 0 }

end Fmt

/-! ## 3. The parameters (abstract inner masks), the claims -/

/-- The parameters of the block. -/
structure PscPar (E : Type) [Field E] where
  /-- states: all that is public and that functionals, summand, maps and forms read -/
  St : Type
  /-- the entries of all messages of the statement's oracles, masks included -/
  J : Type
  [finJ : Fintype J]
  /-- all variables of the sumcheck -/
  fmt : List (PFmt E)
  dat : St → PDats fmt
  /-- the maps whose values are revealed, and the others -/
  A : Type
  [finA : Fintype A]
  B : Type
  [finB : Fintype B]
  /-- the maps, with their inner masks, as functions of state, entries and point -/
  G : (st : St) → (J → E) → A → HPt (pVars fmt (dat st)) → E
  Gb : (st : St) → (J → E) → B → HPt (pVars fmt (dat st)) → E
  /-- the summand: S0 + ∑ b, S1 b · (value of the map b); S0, S1 read the point and the values of
  the revealed maps -/
  S0 : (st : St) → HPt (pVars fmt (dat st)) → (A → E) → E
  S1 : (st : St) → HPt (pVars fmt (dat st)) → (A → E) → B → E
  /-- the form of the masks that come in with the claim -/
  slS : Slf E St J
  /-- at which entries the coefficients of the hiding polynomial lie -/
  wAt : PIdx fmt → J

attribute [instance] PscPar.finJ PscPar.finA PscPar.finB

namespace PscPar
variable {E : Type} [Field E] (Y : PscPar E)

abbrev vars (st : Y.St) : List (HVar E) := pVars Y.fmt (Y.dat st)
/-- a point, as an `HPt` of Cb/Ld/LdHide.lean -/
abbrev hp (st : Y.St) (γ : PPt Y.fmt) : HPt (Y.vars st) := pH Y.fmt (Y.dat st) γ

/-- the coefficients of the hiding polynomial; the value of the incoming masks' form -/
def W (st : Y.St) (m : Y.J → E) : HIdx (Y.vars st) → E := fun i =>
  m (Y.wAt (pIx Y.fmt (Y.dat st) i))
def inc (st : Y.St) (m : Y.J → E) : E := ∑ j, Y.slS st j * m j

/-- The summand, and the polynomial H of the sumcheck. -/
def sum (st : Y.St) (m : Y.J → E) (X : HPt (Y.vars st)) : E :=
  Y.S0 st X (fun a => Y.G st m a X) + ∑ b, Y.S1 st X (fun a => Y.G st m a X) b * Y.Gb st m b X
def whole (st : Y.St) (m : Y.J → E) (ε : E) (X : HPt (Y.vars st)) : E :=
  hU (Y.vars st) (Y.W st m) X + ε * (hPsi (Y.vars st) X * Y.inc st m + Y.sum st m X)

/-- The conditions on the parameters: φ(ψ) = 1 for every variable; the summand has the degrees of
the variables; different challenges have different values. -/
def VarsOK : Prop := ∀ st, ∀ v ∈ Y.vars st, v.OK
def DegOK : Prop := ∀ st m, HDeg (Y.vars st) (Y.sum st m)
def ValInj : Prop := ∀ f ∈ Y.fmt, Function.Injective f.val

/-- The claim of the input statement x = (target, state). -/
def SumHolds (x : E × Y.St) (m : Y.J → E) : Prop :=
  hSumAll (Y.vars x.2) (Y.sum x.2 m) + Y.inc x.2 m = x.1

/-- the claim after the rounds of the variables: state, coefficient, point, last value -/
structure Mid where
  st : Y.St
  eps : E
  pt : PPt Y.fmt
  fin : E
/-- the claim of the output statement: also the values -/
structure Out where
  st : Y.St
  eps : E
  pt : PPt Y.fmt
  fin : E
  vals : Y.A → E

/-- The end claim: H at the point is the last value. -/
def MidHolds (z : Y.Mid) (m : Y.J → E) : Prop := Y.whole z.st m z.eps (Y.hp z.st z.pt) = z.fin

/-- The row on the hiding polynomial's coefficients. -/
def UHolds (o : Y.Out) (m : Y.J → E) : Prop :=
  hU (Y.vars o.st) (Y.W o.st m) (Y.hp o.st o.pt) +
      o.eps * hPsi (Y.vars o.st) (Y.hp o.st o.pt) * Y.inc o.st m +
      o.eps * ∑ b, Y.S1 o.st (Y.hp o.st o.pt) o.vals b * Y.Gb o.st m b (Y.hp o.st o.pt) =
    o.fin - o.eps * Y.S0 o.st (Y.hp o.st o.pt) o.vals
/-- The row on a revealed map's value. -/
def EHolds (o : Y.Out) (m : Y.J → E) (a : Y.A) : Prop := Y.G o.st m a (Y.hp o.st o.pt) = o.vals a
def OutHolds (o : Y.Out) (m : Y.J → E) : Prop := Y.UHolds o m ∧ ∀ a, Y.EHolds o m a

/-! ### The output claims as linear rows -/

/-- the maps are linear in the entries, with these rows -/
def LinA (rowA : (st : Y.St) → Y.A → HPt (Y.vars st) → Y.J → E) : Prop :=
  ∀ st m a X, Y.G st m a X = ∑ j, rowA st a X j * m j
def LinB (rowB : (st : Y.St) → Y.B → HPt (Y.vars st) → Y.J → E) : Prop :=
  ∀ st m b X, Y.Gb st m b X = ∑ j, rowB st b X j * m j

open Classical in
/-- the first row as a linear form, and its public target -/
def slU (rowB : (st : Y.St) → Y.B → HPt (Y.vars st) → Y.J → E) : Slf E Y.Out Y.J := fun o j =>
  (∑ i, if Y.wAt (pIx Y.fmt (Y.dat o.st) i) = j then hSl (Y.vars o.st) (Y.hp o.st o.pt) i else 0) +
    o.eps * hPsi (Y.vars o.st) (Y.hp o.st o.pt) * Y.slS o.st j +
    o.eps * ∑ b, Y.S1 o.st (Y.hp o.st o.pt) o.vals b * rowB o.st b (Y.hp o.st o.pt) j
def tU (o : Y.Out) : E := o.fin - o.eps * Y.S0 o.st (Y.hp o.st o.pt) o.vals
/-- the row on the value of the map a as a linear form; its target is o.vals a -/
def slE (rowA : (st : Y.St) → Y.A → HPt (Y.vars st) → Y.J → E) (a : Y.A) : Slf E Y.Out Y.J :=
  fun o => rowA o.st a (Y.hp o.st o.pt)

/-! ### The term -/

variable [Fintype E]

abbrev shapeC : Shape := pRound0 E :: pRounds Y.fmt

/-- what the verifier reads off a transcript -/
def mu (τ : Tr Y.shapeC) : E := τ.plains.1
def eps (τ : Tr Y.shapeC) : E := τ.rho.1
def pt (τ : Tr Y.shapeC) : PPt Y.fmt := pG Y.fmt τ.rho.2
def qs (st : Y.St) (τ : Tr Y.shapeC) : RIdx (Y.vars st) → E := pQ Y.fmt (Y.dat st) τ.plains.2

open Classical in
/-- The verifier: the checks of the sumcheck for the claimed sum μ' + ε τ; the last value is the
last round polynomial at the last challenge. -/
def outC (x : E × Y.St) (τ : Tr Y.shapeC) : Option Y.Mid :=
  if HCons (Y.vars x.2) (Y.mu τ + Y.eps τ * x.1) (Y.qs x.2 τ) (Y.hp x.2 (Y.pt τ)) then
    some ⟨x.2, Y.eps τ, Y.pt τ,
      hFin (Y.vars x.2) (Y.mu τ + Y.eps τ * x.1) (Y.qs x.2 τ) (Y.hp x.2 (Y.pt τ))⟩
  else none

variable (Ex : ExtSpec)

/-- Round 0 and the rounds of the variables. The oracles, of any kind Ex, are copied. -/
def core : IOR (E × Y.St) Ex Y.Mid Ex where
  shape := Y.shapeC
  blinded := fun _ => true
  extReads := fun _ => ∅
  reads := fun _ => ∅
  out := fun x _ τ => Y.outC x τ
  imp := fun y _ => y
  srcE := fun _ q => {q}
  srcO := fun _ _ => ∅
  tie := fun _ _ => ∅

/-- The last round: the values of the revealed maps, in the clear; nothing is checked. -/
def ends : IOR Y.Mid Ex Y.Out Ex where
  shape := [pRoundV E Y.A]
  blinded := fun _ => true
  extReads := fun _ => ∅
  reads := fun _ => ∅
  out := fun z _ τ => some ⟨z.st, z.eps, z.pt, z.fin, τ.plains.1⟩
  imp := fun y _ => y
  srcE := fun _ q => {q}
  srcO := fun _ _ => ∅
  tie := fun _ _ => ∅

/-- The block. -/
def psc : IOR (E × Y.St) Ex Y.Out Ex := (Y.core Ex).seq (Y.ends Ex)

/-- The errors, as counts of challenges. -/
def errC : Err (Y.core Ex).shape := (1, pErr Y.fmt)
def err : Err (Y.psc Ex).shape := Err.app (Y.errC Ex) ((0, ()) : Err (Y.ends Ex).shape)

/-! ### The honest side -/

/-- The honest round polynomials: those of U, and ε times those of the rest. -/
def honQ (st : Y.St) (m : Y.J → E) (ε : E) (γ : HPt (Y.vars st)) : RIdx (Y.vars st) → E :=
  fun i =>
    hTr (Y.vars st) 0 (Y.W st m) γ i +
      ε * (hTr (Y.vars st) (Y.inc st m) 0 γ i + hTrOf (Y.vars st) (Y.sum st m) γ i)

/-- with what the honest prover ends -/
def honMid (st : Y.St) (m : Y.J → E) (ε : E) (γ : PPt Y.fmt) : Y.Mid :=
  ⟨st, ε, γ, Y.whole st m ε (Y.hp st γ)⟩
def honOut (z : Y.Mid) (m : Y.J → E) : Y.Out :=
  ⟨z.st, z.eps, z.pt, z.fin, fun a => Y.G z.st m a (Y.hp z.st z.pt)⟩

variable {Wt : Type} (msg : Wt → Y.J → E)

/-- The honest side. No coins; nothing is withheld; the witness stays. -/
def honC : (Y.core Ex).Honest Wt Wt where
  Coin := Unit
  strat := fun w x _ =>
    (((), hMu (Y.vars x.2) (Y.W x.2 (msg w))),
      fun ε =>
        pStrat Y.fmt (Y.dat x.2) (Y.honQ x.2 (msg w) ε) fun γ => (Y.honMid x.2 (msg w) ε γ, w))
  Bad := ∅
  Hid := fun _ _ => ∅
def honE : (Y.ends Ex).Honest Wt Wt where
  Coin := Unit
  strat := fun w z _ => (((), (Y.honOut z (msg w)).vals), fun _ => (Y.honOut z (msg w), w))
  Bad := ∅
  Hid := fun _ _ => ∅
def hon : (Y.psc Ex).Honest Wt Wt := (Y.honC Ex msg).seq (Y.honE Ex msg)

end PscPar

/-! ## 4. The oracles, as the block sees them; the joints -/

/-- What the block is told of the oracles, and all that rides along. St: the states of the claims;
Cr: the carried part of the explicit part (the samples). -/
structure PscBase (E J St Cr : Type) (Ex : ExtSpec) (Wt : Type) where
  /-- the entries of a witness's messages -/
  msg : Wt → J → E
  /-- the exact and the relaxed relation between state, carried part, oracles and witness -/
  rel : St × Cr → Ex.Str → Wt → Prop
  relR : (St × Cr) × Ex.Str → Wt → Prop
  /-- the statements of which knowledge soundness speaks -/
  on : (St × Cr) × Ex.Str → Prop

namespace PscBase
variable {E J St Cr : Type} {Ex : ExtSpec} {Wt : Type} (Bs : PscBase E J St Cr Ex Wt)

/-- On the statements with the condition, the relaxed relation determines the entries. -/
def Det : Prop := ∀ a w w', Bs.on a → Bs.relR a w → Bs.relR a w' → Bs.msg w = Bs.msg w'

/-- A joint: the base, at the state of the claim, and the claim Φ on the entries. -/
def rels {Kc X : Type} (stOf : X → St) (Φ : X → (J → E) → Prop) (core : Wt → Kc) :
    IOR.Rels Kc (X × Cr) Ex Wt where
  rel := fun x y w => Bs.rel (stOf x.1, x.2) y w ∧ Φ x.1 (Bs.msg w)
  relR := fun a w => Bs.relR ((stOf a.1.1, a.1.2), a.2) w ∧ Φ a.1.1 (Bs.msg w)
  on := fun a => Bs.on ((stOf a.1.1, a.1.2), a.2)
  core := core

end PscBase

namespace PscPar
variable {E : Type} [Field E] (Y : PscPar E) {Cr : Type} {Ex : ExtSpec} {Wt Kc : Type}
  (Bs : PscBase E Y.J Y.St Cr Ex Wt) (kc : Wt → Kc)

/-- The three joints: the sum claim; the end claim; the output rows. -/
def relsIn : IOR.Rels Kc ((E × Y.St) × Cr) Ex Wt := Bs.rels Prod.snd Y.SumHolds kc
def relsMid : IOR.Rels Kc (Y.Mid × Cr) Ex Wt := Bs.rels Mid.st Y.MidHolds kc
def relsOut : IOR.Rels Kc (Y.Out × Cr) Ex Wt := Bs.rels Out.st Y.OutHolds kc

/-- A joint at the base: no carried part; A0, a joint on (state, oracles, witness), rides along. -/
def baseRels {X : Type} (A0 : IOR.Rels Kc Y.St Ex Wt) (msg : Wt → Y.J → E)
    (stOf : X → Y.St) (Φ : X → (Y.J → E) → Prop) : IOR.Rels Kc X Ex Wt where
  rel := fun x y w => A0.rel (stOf x) y w ∧ Φ x (msg w)
  relR := fun a w => A0.relR (stOf a.1, a.2) w ∧ Φ a.1 (msg w)
  on := fun a => A0.on (stOf a.1, a.2)
  core := A0.core
def baseIn (A0 : IOR.Rels Kc Y.St Ex Wt) (msg : Wt → Y.J → E) : IOR.Rels Kc (E × Y.St) Ex Wt :=
  Y.baseRels A0 msg Prod.snd Y.SumHolds
def baseMid (A0 : IOR.Rels Kc Y.St Ex Wt) (msg : Wt → Y.J → E) : IOR.Rels Kc Y.Mid Ex Wt :=
  Y.baseRels A0 msg Mid.st Y.MidHolds
def baseOut (A0 : IOR.Rels Kc Y.St Ex Wt) (msg : Wt → Y.J → E) : IOR.Rels Kc Y.Out Ex Wt :=
  Y.baseRels A0 msg Out.st Y.OutHolds

end PscPar

/-! ## 5. The instance: one dummy last variable -/

section Snoc
variable {E : Type}

/-- data, with those of one more variable at the end; a point without its last coordinate; the last
coordinate -/
def PDats.snoc : (l : List (PFmt E)) → PDats l → (f : PFmt E) → PDat E f → PDats (l ++ [f])
  | [], _, _, e => (e, ())
  | _ :: l, d, f, e => (d.1, PDats.snoc l d.2 f e)
def hInit :
    (l : List (PFmt E)) → (d : PDats l) → (f : PFmt E) → (e : PDat E f) →
    HPt (pVars (l ++ [f]) (PDats.snoc l d f e)) → HPt (pVars l d)
  | [], _, _, _, _ => ()
  | _ :: l, d, f, e, X => (X.1, hInit l d.2 f e X.2)
def hLast :
    (l : List (PFmt E)) → (d : PDats l) → (f : PFmt E) → (e : PDat E f) →
    HPt (pVars (l ++ [f]) (PDats.snoc l d f e)) → E
  | [], _, _, _, X => X.1
  | _ :: l, d, f, e, X => hLast l d.2 f e X.2

variable [Field E] [Fintype E]

open Classical in
/-- The dummy variable: the functional is the value at 0, ψ = 1, the challenge is not 0. -/
def pDummy (E : Type) [Field E] [Fintype E] (D : ℕ) : PFmt E :=
  { n := D, S := Unit, Ch := {x : E // x ≠ 0}, neCh := ⟨⟨1, one_ne_zero⟩⟩, val := Subtype.val }
def pDummyD (E : Type) [Field E] [Fintype E] (D : ℕ) : PDat E (pDummy E D) :=
  { node := fun _ => 0, wt := fun _ => 1, psi := fun t => if t = 0 then 1 else 0 }

end Snoc

/-- The parameters of the instance. -/
structure PscOur (E : Type) [Field E] [Fintype E] where
  St : Type
  J : Type
  [finJ : Fintype J]
  /-- the k variables of the sum -/
  fmt : List (PFmt E)
  dat : St → PDats fmt
  /-- the maps whose values are revealed, and the others -/
  A : Type
  [finA : Fintype A]
  B : Type
  [finB : Fintype B]
  /-- the maps, without masks -/
  F : (st : St) → (J → E) → A → HPt (pVars fmt (dat st)) → E
  Fb : (st : St) → (J → E) → B → HPt (pVars fmt (dat st)) → E
  S0 : (st : St) → HPt (pVars fmt (dat st)) → (A → E) → E
  S1 : (st : St) → HPt (pVars fmt (dat st)) → (A → E) → B → E
  /-- the degree of the summand in the revealed maps -/
  DY : ℕ
  slS : Slf E St J
  /-- own masks: the coefficients of the hiding polynomial in k + 1 variables; one entry for each
  revealed map -/
  wAt : PIdx (fmt ++ [pDummy E DY]) → J
  cAt : A → J

attribute [instance] PscOur.finJ PscOur.finA PscOur.finB

namespace PscOur
variable {E : Type} [Field E] [Fintype E] (T : PscOur E)

abbrev vars (st : T.St) : List (HVar E) := pVars T.fmt (T.dat st)
abbrev datD (st : T.St) : PDats (T.fmt ++ [pDummy E T.DY]) :=
  PDats.snoc T.fmt (T.dat st) (pDummy E T.DY) (pDummyD E T.DY)
/-- the first k coordinates of a point, and the last -/
abbrev ini (st : T.St) (X : HPt (pVars (T.fmt ++ [pDummy E T.DY]) (T.datD st))) : HPt (T.vars st) :=
  hInit T.fmt (T.dat st) (pDummy E T.DY) (pDummyD E T.DY) X
abbrev lst (st : T.St) (X : HPt (pVars (T.fmt ++ [pDummy E T.DY]) (T.datD st))) : E :=
  hLast T.fmt (T.dat st) (pDummy E T.DY) (pDummyD E T.DY) X

/-- The instance as parameters of the block: masked map a = F_a(X) + c_a Y. -/
def par : PscPar E where
  St := T.St
  J := T.J
  fmt := T.fmt ++ [pDummy E T.DY]
  dat := T.datD
  A := T.A
  B := T.B
  G := fun st m a X => T.F st m a (T.ini st X) + m (T.cAt a) * T.lst st X
  Gb := fun st m b X => T.Fb st m b (T.ini st X)
  S0 := fun st X v => T.S0 st (T.ini st X) v
  S1 := fun st X v b => T.S1 st (T.ini st X) v b
  slS := T.slS
  wAt := T.wAt

/-- the true summand, in k variables -/
def sum (st : T.St) (m : T.J → E) (X : HPt (T.vars st)) : E :=
  T.S0 st X (fun a => T.F st m a X) + ∑ b, T.S1 st X (fun a => T.F st m a X) b * T.Fb st m b X

/-- The claim of the input statement, in k variables, without inner masks. -/
def SumHolds (x : E × T.St) (m : T.J → E) : Prop :=
  hSumAll (T.vars x.2) (T.sum x.2 m) + ∑ j, T.slS x.2 j * m j = x.1

def VarsOK : Prop := ∀ st, ∀ v ∈ T.vars st, v.OK
def ValInj : Prop := ∀ f ∈ T.fmt, Function.Injective f.val

/-- The degrees of the summand. In the k variables: those of the formats, whatever constants are
added to the values of the revealed maps. In the values of the revealed maps: DY, along every line.
-/
def DegX : Prop :=
  ∀ st m (u : T.A → E), HDeg (T.vars st) fun X =>
    T.S0 st X (fun a => T.F st m a X + u a) +
      ∑ b, T.S1 st X (fun a => T.F st m a X + u a) b * T.Fb st m b X
def DegY : Prop :=
  ∀ st (X : HPt (T.vars st)) (v u : T.A → E) (r : T.B → E), ∃ c : Fin (T.DY + 1) → E, ∀ y : E,
    T.S0 st X (fun a => v a + u a * y) + ∑ b, T.S1 st X (fun a => v a + u a * y) b * r b = hev c y

end PscOur

/-! ## The statements -/

namespace Spec

section
variable (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M]

/-- States: the round polynomials (`hTrOf`) of a summand with degrees (`HDeg`) are what their name
says (`HRounds`). -/
def psc_trOf : Prop :=
  ∀ (l : List (HVar R)) (f : HPt l → M) (γ : HPt l), HDeg l f → HRounds l f (hTrOf l f γ) γ

/-- States: round polynomials of a summand (`HRounds`) pass the checks for its sum, and end with its
value at the challenges. -/
def psc_cons : Prop :=
  ∀ (l : List (HVar R)) (f : HPt l → M) (q : RIdx l → M) (γ : HPt l),
    HRounds l f q γ → HCons l (hSumAll l f) q γ ∧ hFin l (hSumAll l f) q γ = f γ

end

section
variable (E : Type) [Field E]

/-- These state: the output claims are linear rows with public targets, where the maps are linear
in the entries (`LinB`, `LinA`). -/
def psc_row_U : Prop :=
  ∀ (Y : PscPar E) (rowB : (st : Y.St) → Y.B → HPt (Y.vars st) → Y.J → E),
    Y.LinB rowB → ∀ (o : Y.Out) (m : Y.J → E), Y.UHolds o m ↔ (Y.slU rowB).Holds (Y.tU o, o) m
def psc_row_E : Prop :=
  ∀ (Y : PscPar E) (rowA : (st : Y.St) → Y.A → HPt (Y.vars st) → Y.J → E), Y.LinA rowA →
    ∀ (o : Y.Out) (m : Y.J → E) (a : Y.A), Y.EHolds o m a ↔ (Y.slE rowA a).Holds (o.vals a, o) m

/-- These state: the output rows together say the end claim; given the rows on the values, the
first row is the end claim. -/
def psc_out_mid : Prop :=
  ∀ (Y : PscPar E) (o : Y.Out) (m : Y.J → E),
    Y.OutHolds o m → Y.MidHolds ⟨o.st, o.eps, o.pt, o.fin⟩ m
def psc_out_iff : Prop :=
  ∀ (Y : PscPar E) (o : Y.Out) (m : Y.J → E),
    Y.OutHolds o m ↔ Y.MidHolds ⟨o.st, o.eps, o.pt, o.fin⟩ m ∧ ∀ a, Y.EHolds o m a
/-- States: with no revealed map the end claim is the first row. -/
def psc_mid_empty : Prop :=
  ∀ (Y : PscPar E) (_ : IsEmpty Y.A) (z : Y.Mid) (m : Y.J → E),
    Y.MidHolds z m ↔ Y.UHolds ⟨z.st, z.eps, z.pt, z.fin, isEmptyElim⟩ m

variable [Fintype E]

/-- States, under `Y.VarsOK` and `Y.DegOK`: the honest prover is the sumcheck prover of H. Its first
scalar is the sum of the hiding polynomial, its round polynomials are those of
H = U + ε (summand + incoming masks · ψ_1 .. ψ_k). -/
def psc_rounds : Prop :=
  ∀ Y : PscPar E, Y.VarsOK → Y.DegOK →
    ∀ (st : Y.St) (m : Y.J → E) (ε : E) (γ : HPt (Y.vars st)),
      hSumAll (Y.vars st) (hU (Y.vars st) (Y.W st m)) = hMu (Y.vars st) (Y.W st m) ∧
      HRounds (Y.vars st) (Y.whole st m ε) (Y.honQ st m ε γ) γ

/-- States: what the honest prover sends in a run is its closed form at the run's challenges. -/
def psc_run : Prop :=
  ∀ (Y : PscPar E) (Ex : ExtSpec) (Wt : Type) (msg : Wt → Y.J → E) (w : Wt)
      (x : E × Y.St) (ρ : Rho (Y.core Ex).shape),
    Y.mu (((Y.honC Ex msg).strat w x ()).run ρ).1 = hMu (Y.vars x.2) (Y.W x.2 (msg w)) ∧
    Y.qs x.2 (((Y.honC Ex msg).strat w x ()).run ρ).1 =
      Y.honQ x.2 (msg w) ρ.1 (Y.hp x.2 (pG Y.fmt ρ.2)) ∧
    (((Y.honC Ex msg).strat w x ()).run ρ).1.rho = ρ ∧
    (((Y.honC Ex msg).strat w x ()).run ρ).2 = (Y.honMid x.2 (msg w) ρ.1 (pG Y.fmt ρ.2), w)

/-- These state: all rounds are point rounds (`Shape.IsPoint`); verifier and new oracles read what
the term declares (`IOR.IsLocal`). That no oracle is sent holds by definition: `Pos := Empty` in
`pRound0`, `pRound`, `pRoundV`. -/
def psc_point : Prop := ∀ (Y : PscPar E) (Ex : ExtSpec), Nonempty (Y.psc Ex).shape.IsPoint
def psc_local : Prop := ∀ (Y : PscPar E) (Ex : ExtSpec), (Y.psc Ex).IsLocal

/-- States the number of rounds: two more than there are variables. -/
def psc_len : Prop := ∀ (Y : PscPar E) (Ex : ExtSpec), (Y.psc Ex).shape.length = Y.fmt.length + 2

/-- States, under `Y.VarsOK` and `Y.DegOK`: perfect completeness, the carried part and further
oracles F being copied (`IOR.keep`). -/
def psc_acc : Prop :=
  ∀ (Y : PscPar E) (Cr : Type) (E₀ F : ExtSpec) (Wt : Type)
      (Bs : PscBase E Y.J Y.St Cr (E₀.prod F) Wt),
    Y.VarsOK → Y.DegOK →
    ((Y.hon E₀ Bs.msg).keep Cr F).Acc (Y.relsIn Bs fun _ => ()).rel (Y.relsOut Bs fun _ => ()).rel

/-- States: the condition on statements is carried: state, carried part and oracles are copied. -/
def psc_carry : Prop :=
  ∀ (Y : PscPar E) (Cr : Type) (E₀ F : ExtSpec) (Wt : Type)
      (Bs : PscBase E Y.J Y.St Cr (E₀.prod F) Wt) a τ b,
    (Y.relsIn Bs fun _ => ()).on a →
    ((Y.psc E₀).keep Cr F).red.out a τ = some b → (Y.relsOut Bs fun _ => ()).on b

/-- States the main step, for each fixed tuple of entries m, under `Y.VarsOK`, `Y.DegOK` and
`Y.ValInj`: if the sum claim is false of m, the prover has lost (`Doomed`), with the errors 1, the
degrees, 0, towards the goal that whatever the verifier outputs is false of m. -/
def psc_sound_at : Prop :=
  ∀ (Y : PscPar E) (Ex : ExtSpec), Y.VarsOK → Y.DegOK → Y.ValInj →
    ∀ (x : E × Y.St) (y : Ex.Str) (m : Y.J → E), ¬ Y.SumHolds x m →
      Doomed (Y.psc Ex).shape (Y.err Ex) fun τ =>
        ∀ o, (Y.psc Ex).out x y τ = some o → ¬ Y.OutHolds o m

/-- States, under `Y.VarsOK`, `Y.DegOK`, `Y.ValInj` and `Bs.Det`: round-by-round knowledge soundness
of the block, on the statements with the condition. Errors 1, the degrees, 0; no list size; the
extractor is the identity. -/
def psc_know : Prop :=
  ∀ (Y : PscPar E) (Cr : Type) (E₀ F : ExtSpec) (Wt : Type)
      (Bs : PscBase E Y.J Y.St Cr (E₀.prod F) Wt),
    Y.VarsOK → Y.DegOK → Y.ValInj → Bs.Det →
    ((Y.psc E₀).keep Cr F).red.Know (Y.relsIn Bs fun _ => ()).on (Y.relsIn Bs fun _ => ()).relR
      (Y.relsOut Bs fun _ => ()).relR (fun _ _ w => w) (Y.err E₀)

/-! ### At the base: no carried part, the messages a part of the witness -/

/-- These state: perfect completeness at the base, under `Y.VarsOK` and `Y.DegOK`; the honest
prover hands its witness on; the condition is carried. -/
def psc_acc_base : Prop :=
  ∀ (Y : PscPar E) (Ex : ExtSpec) (Wt Kc : Type) (A0 : IOR.Rels Kc Y.St Ex Wt) (msg : Wt → Y.J → E),
    Y.VarsOK → Y.DegOK → (Y.hon Ex msg).Acc (Y.baseIn A0 msg).rel (Y.baseOut A0 msg).rel
def psc_keeps : Prop :=
  ∀ (Y : PscPar E) (Ex : ExtSpec) (Wt : Type) (msg : Wt → Y.J → E) w x c ρ,
    (((Y.hon Ex msg).strat w x c).run ρ).2.2 = w
def psc_carry_base : Prop :=
  ∀ (Y : PscPar E) (Ex : ExtSpec) (Wt Kc : Type)
      (A0 : IOR.Rels Kc Y.St Ex Wt) (msg : Wt → Y.J → E) a τ b,
    (Y.baseIn A0 msg).on a → (Y.psc Ex).red.out a τ = some b → (Y.baseOut A0 msg).on b

/-- States, under `Y.VarsOK`, `Y.DegOK` and `Y.ValInj`: knowledge soundness for each fixed tuple of
messages. The witness is (messages, further part); the messages are fixed, the extractor hands the
further part back. -/
def psc_know_at : Prop :=
  ∀ (Y : PscPar E) (Ex : ExtSpec) (M Wp Kc : Type)
      (A0 : IOR.Rels Kc Y.St Ex (M × Wp)) (msg : M → Y.J → E),
    Y.VarsOK → Y.DegOK → Y.ValInj →
    ∀ m : M, (Y.psc Ex).red.Know (Y.baseIn A0 fun w => msg w.1).on
      (fun a wp => (Y.baseIn A0 fun w => msg w.1).relR a (m, wp))
      (fun b wp => (Y.baseOut A0 fun w => msg w.1).relR b (m, wp)) (fun _ _ wp => wp) (Y.err Ex)

/-- These state, each under the hypotheses of its statement: completeness at the base and knowledge
soundness for each fixed tuple of messages, for `core` alone. -/
def psc_core_acc_base : Prop :=
  ∀ (Y : PscPar E) (Ex : ExtSpec) (Wt Kc : Type) (A0 : IOR.Rels Kc Y.St Ex Wt) (msg : Wt → Y.J → E),
    Y.VarsOK → Y.DegOK → (Y.honC Ex msg).Acc (Y.baseIn A0 msg).rel (Y.baseMid A0 msg).rel
def psc_core_know_at : Prop :=
  ∀ (Y : PscPar E) (Ex : ExtSpec) (M Wp Kc : Type)
      (A0 : IOR.Rels Kc Y.St Ex (M × Wp)) (msg : M → Y.J → E),
    Y.VarsOK → Y.DegOK → Y.ValInj →
    ∀ m : M, (Y.core Ex).red.Know (Y.baseIn A0 fun w => msg w.1).on
      (fun a wp => (Y.baseIn A0 fun w => msg w.1).relR a (m, wp))
      (fun b wp => (Y.baseMid A0 fun w => msg w.1).relR b (m, wp)) (fun _ _ wp => wp) (Y.errC Ex)

/-! ### `core` alone (round 0 and the rounds of the variables), with a carried part -/

/-- These state, each under the hypotheses of its statement: completeness, the main step and
knowledge soundness on the statements with the condition, to the end claim, for `core` alone
(the whole block where no map is revealed). -/
def psc_core_acc : Prop :=
  ∀ (Y : PscPar E) (Cr : Type) (E₀ F : ExtSpec) (Wt : Type)
      (Bs : PscBase E Y.J Y.St Cr (E₀.prod F) Wt),
    Y.VarsOK → Y.DegOK →
    ((Y.honC E₀ Bs.msg).keep Cr F).Acc (Y.relsIn Bs fun _ => ()).rel (Y.relsMid Bs fun _ => ()).rel
def psc_core_sound_at : Prop :=
  ∀ (Y : PscPar E) (Ex : ExtSpec), Y.VarsOK → Y.DegOK → Y.ValInj →
    ∀ (x : E × Y.St) (m : Y.J → E), ¬ Y.SumHolds x m →
      Doomed (Y.core Ex).shape (Y.errC Ex) fun τ => ∀ z, Y.outC x τ = some z → ¬ Y.MidHolds z m
def psc_core_know : Prop :=
  ∀ (Y : PscPar E) (Cr : Type) (E₀ F : ExtSpec) (Wt : Type)
      (Bs : PscBase E Y.J Y.St Cr (E₀.prod F) Wt),
    Y.VarsOK → Y.DegOK → Y.ValInj → Bs.Det →
    ((Y.core E₀).keep Cr F).red.Know (Y.relsIn Bs fun _ => ()).on (Y.relsIn Bs fun _ => ()).relR
      (Y.relsMid Bs fun _ => ()).relR (fun _ _ w => w) (Y.errC E₀)

/-! ### The instance with the dummy variable -/

/-- States: the dummy variable and the inner masks do not change the sum. -/
def psc_our_sum : Prop :=
  ∀ (T : PscOur E) (x : E × T.St) (m : T.J → E), T.par.SumHolds x m ↔ T.SumHolds x m

/-- States: the conditions on the variables pass to the k + 1 variables. -/
def psc_our_ok : Prop := ∀ T : PscOur E, (T.VarsOK → T.par.VarsOK) ∧ (T.ValInj → T.par.ValInj)

/-- States the degrees of the masked summand in the k + 1 variables, from the conditions on S and F
(`DegX`, `DegY`). -/
def psc_our_deg : Prop := ∀ T : PscOur E, T.DegX → T.DegY → T.par.DegOK

open Classical in
/-- States, of a revealed map that is never sent: if its value at the point is a sum (the summand of
T' (whose entries are those of T, renamed by ι) at the state st'), and T' has as incoming form β at
the entry c_a, then the row on its value is the input claim of T', with the target v_a. -/
def psc_our_next : Prop :=
  ∀ (T T' : PscOur E) (ι : T'.J ≃ T.J) (o : T.par.Out) (m : T.J → E) (a : T.A) (st' : T'.St),
    T.F o.st m a (T.ini o.st (T.par.hp o.st o.pt)) =
      hSumAll (T'.vars st') (T'.sum st' fun j => m (ι j)) →
    (∀ j, T'.slS st' j = if ι j = T.cAt a then T.lst o.st (T.par.hp o.st o.pt) else 0) →
    (T.par.EHolds o m a ↔ T'.SumHolds (o.vals a, st') fun j => m (ι j))

/-- States the row on a revealed map's value, in the instance: F_a(γ) + β c_a = v_a. -/
def psc_our_val : Prop :=
  ∀ (T : PscOur E) (o : T.par.Out) (m : T.J → E) (a : T.A),
    T.par.EHolds o m a ↔
    T.F o.st m a (T.ini o.st (T.par.hp o.st o.pt)) + m (T.cAt a) * T.lst o.st (T.par.hp o.st o.pt) =
      o.vals a

/-- States: the last coordinate of the verifier's point is not 0. -/
def psc_our_nz : Prop :=
  ∀ (T : PscOur E) (x : E × T.St) (τ : Tr T.par.shapeC) (z : T.par.Mid),
    T.par.outC x τ = some z → T.lst z.st (T.par.hp z.st z.pt) ≠ 0

/-- These state the degrees of the instance (the errors of its rounds of variables): those of the k
variables, then DY. The rounds: k + 3. -/
def psc_our_degs : Prop := ∀ T : PscOur E, T.par.fmt.map PFmt.n = T.fmt.map PFmt.n ++ [T.DY]
def psc_our_len : Prop :=
  ∀ (T : PscOur E) (Ex : ExtSpec), (T.par.psc Ex).shape.length = T.fmt.length + 3
/-- States: the last challenge set has |E| - 1 elements. -/
def psc_our_card : Prop := ∀ D : ℕ, Fintype.card (pDummy E D).Ch = Fintype.card E - 1

end
end Spec
end
end Cb
