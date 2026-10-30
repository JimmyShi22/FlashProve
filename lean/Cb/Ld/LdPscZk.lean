-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdPscZk.lean: the zero-knowledge item of the sumcheck for a polynomial summand: "masked
messages".

Definitions and statements (each a `Prop` in `Cb.Spec`); the proofs are in Cb/Ld/LdPscZkProofs.lean
and, for the two on the instance, in Cb/Ld/LdPscZkOur.lean.

The block (Cb/Ld/LdPsc.lean) sends no oracle; its masks are entries of messages that were sent, and
sampled, before it. With its masks in the input it is not zero knowledge for a worst-case witness
(Ior/Masked.lean: `Spec.masked_not_exact`). Its item is "masked messages" (`Iop.IOR.Honest.MM`),
which it has under `Y.VarsOK`, `Y.DegOK` and `Y.OwnOK O` (`Spec.psc_mm`): under `Cl` (here
`Y.SumHolds`), over its own mask entries, uniform, everything else of the witness fixed, all that it
sends has exactly the law of a simulator.
`H.MM D` asks five things: the block sends no oracle; `H.withheld w x` is always empty; the honest
prover's plain parts are `D.msg` at `D.kc w`, `D.pub x` and ρ; `D.Cl` is kept under `D.put`; and
where `D.Cl xp k` holds, `D.msg (D.put M k) xp ρ` over uniform M has the distribution `D.sim xp ρ`.
`GoodM` is `GoodB` (`GoodT` without the clause `exact`) with `H.MM D`, and the clause that every (x,
y, w) in the honest relation meets `D.Cl (D.pub x) (D.kc w)`. In this file's statements `MM` stands
as a conclusion (`Spec.psc_mm`, `Spec.psc_core_mm`, `Spec.psc_our_mm`, `Spec.psc_mm_keep`); `GoodM`
stands in none of them (Limits).
What the simulator is given: the explicit part of the claim, x = (target τ, state st), and the
verifier's messages (the coefficient ε, the challenges). Nothing else: no entry of a message, no
symbol of an oracle, no answer to a sample (these are not even in x: they ride in a carried part,
Ior/MaskedFrame.lean).
What it writes (Cb/Ld/LdPscMask.lean: `pscSim`): values of the revealed maps, uniform; under
`Y.VarsOK`, the sum of a hiding polynomial and round polynomials, uniform among those that pass the
verifier's checks for the claim (sum + ε τ). So, under `Cl` and the hypotheses of `Spec.psc_mm`,
over the own mask entries, uniform, all else fixed (field `law` of the item), all that is shown in
the clear, the values at the last point too, is simulated from τ, the functionals of st, ε and the
challenges (exactly: the field `sim` of `Y.maskData`). The targets
of the output claims are functions of x, of the verifier's messages and of these plain parts
(they are what the verifier outputs), so nothing more is shown by them.
The own entries (`PscPar.Own`, data): the coefficients of the hiding polynomial lie at `Y.wAt`; the
inner masks, named by Cx, at cAt. "Rd": the entries that the block reads at all.

`Y.OwnOK O`, the conditions, all on the parameters:
  inj: different own entries lie at different places.
  own, rdG, rdGb, rdS: the block reads the entries in Rd only, the own ones among them. (What is
    outside Rd is forgotten by what the item reads of a witness: kc sets it to 0.)
  wG, wGb: the maps do not read the coefficients of the hiding polynomial.
  sS: the form of the incoming masks reads no own entry.
  sum: the inner masks do not change the sum of the summand.
  val: at every point of challenges, uniform inner masks give uniform values of the revealed maps.

Main names:
  `Spec.psc_mm`: under `Y.VarsOK`, `Y.DegOK` and `Y.OwnOK O`, the block has the item, with the
    fields `Y.maskData`.
  `Spec.psc_core_mm`: `Y.core` alone (round 0 and the rounds of the variables; the whole block where
    no map is revealed): own entries = the coefficients of the hiding polynomial; conditions
    `Y.OwnW`, with `Y.VarsOK` and `Y.DegOK`.
  `Spec.psc_hands`: under `Y.OwnOK O`, the witness is handed on unchanged, and the explicit part
    with which the prover ends is a function of x, the entries read and ρ.
  `Spec.psc_our_own`, `Spec.psc_our_mm`: the instance with the dummy last variable: one inner mask
    c_a for each revealed map; conditions `T.OwnOur`: places differ; the block reads the entries in
    Rd only, the own ones among them; maps and incoming form read no own entry; for the item also
    `T.VarsOK` and `T.par.DegOK`. The challenge of the dummy variable is not 0 by the type of its
    challenge set: at 0 the values would be bare.
  `Spec.psc_mm_keep`: under the hypotheses of `Spec.psc_mm`, the same with a carried part of the
    explicit part and further oracles (`IOR.keep`): same simulator.
  `Spec.psc_own_card`, `Spec.psc_own_card_all`, `Spec.psc_no_coins`: the prover's randomness that
    the block uses up: 1 + the sum of the degrees of all variables (coefficients of the hiding
    polynomial), and one entry for each inner mask (in the instance these are named by the revealed
    maps: `T.own`). The honest prover has no coins. (It sends no oracle: field noOrc of the item; so
    no encoding randomness and no entry that blinds a sample is spent in the block.)

Limits: where the own entries lie in rows is not said and not needed: J names all entries of all
messages of the statement, so an own entry may lie in any row of any number of mask rows, packed or
not.
That the entry which blinds the answer to a sample lies outside Rd is not asked here: whoever puts
the block into a chain has to show it (no own entry is such an entry, and such an entry is read by
nothing else that is shown); with it inside Rd the chain's condition on the rounds before the block
fails (exactly: `Honest.Fresh`, Ior/KnowCollRulesMask.lean).
That no earlier message but the oracle that holds them, and the answer to its sample, depends on the
own entries is a condition on the chain, not on the block: it is not here.
This file does not say zero knowledge of a chain that holds the block. It does not say the bundle
`GoodM` of the block: Cb/Ld/LdPscGood.lean. It says nothing on running times.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdPsc
import Cb.Ld.LdPscMask
import Ior.MaskedFrame

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

noncomputable section

/-! ## Names of coefficients without the data: finitely many -/

section Fmt
variable {E : Type}

instance PIdx.fintype : (l : List (PFmt E)) → Fintype (PIdx l)
  | [] => inferInstanceAs (Fintype Unit)
  | f :: l => haveI := PIdx.fintype l; inferInstanceAs (Fintype (Fin f.n ⊕ PIdx l))
instance PIdx.decEq : (l : List (PFmt E)) → DecidableEq (PIdx l)
  | [] => inferInstanceAs (DecidableEq Unit)
  | f :: l => haveI := PIdx.decEq l; inferInstanceAs (DecidableEq (Fin f.n ⊕ PIdx l))

variable [Field E]

/-- round polynomials as the plain parts of the rounds of the variables -/
def pPl : (l : List (PFmt E)) → (d : PDats l) → (RIdx (pVars l d) → E) → Plains (pRounds l)
  | [], _, _ => ()
  | _ :: l, d, q => ((fun t => q (.inl t)), pPl l d.2 fun i => q (.inr i))

end Fmt

namespace PscPar
variable {E : Type} [Field E] [Fintype E] (Y : PscPar E)

/-- The own entries of the block, and the entries that it reads: data. -/
structure Own where
  /-- the names of the inner masks, and where they lie -/
  Cx : Type
  [finCx : Fintype Cx]
  [decCx : DecidableEq Cx]
  cAt : Cx → Y.J
  /-- the entries that the block reads -/
  Rd : Y.J → Prop

attribute [instance] Own.finCx Own.decCx

variable {Y}

/-- where the own entries lie -/
def Own.at (O : Y.Own) : PIdx Y.fmt ⊕ O.Cx → Y.J := Sum.elim Y.wAt O.cAt

/-- the values of the own entries -/
abbrev Own.Mk (O : Y.Own) : Type := (PIdx Y.fmt → E) × (O.Cx → E)

/-- the entries, the own ones overwritten -/
def Own.put (O : Y.Own) (M : O.Mk) (m : Y.J → E) : Y.J → E :=
  Function.extend O.at (Sum.elim M.1 M.2) m

open Classical in
/-- the entries that the block reads; all others set to 0 -/
def Own.cut (O : Y.Own) (m : Y.J → E) : Y.J → E := fun j => if O.Rd j then m j else 0

variable (Y)

/-- The conditions for the coefficients of the hiding polynomial. -/
structure OwnW (Rd : Y.J → Prop) : Prop where
  inj  : Function.Injective Y.wAt
  own  : ∀ i, Rd (Y.wAt i)
  rdG  : ∀ st m m', (∀ j, Rd j → m j = m' j) → Y.G st m = Y.G st m'
  rdGb : ∀ st m m', (∀ j, Rd j → m j = m' j) → Y.Gb st m = Y.Gb st m'
  rdS  : ∀ st j, ¬ Rd j → Y.slS st j = 0
  wG   : ∀ st m m', (∀ j, (∀ i, j ≠ Y.wAt i) → m j = m' j) → Y.G st m = Y.G st m'
  wGb  : ∀ st m m', (∀ j, (∀ i, j ≠ Y.wAt i) → m j = m' j) → Y.Gb st m = Y.Gb st m'
  wS   : ∀ st i, Y.slS st (Y.wAt i) = 0

open Classical in
/-- The conditions on the own entries. -/
structure OwnOK (O : Y.Own) : Prop where
  inj  : Function.Injective O.at
  own  : ∀ i, O.Rd (O.at i)
  rdG  : ∀ st m m', (∀ j, O.Rd j → m j = m' j) → Y.G st m = Y.G st m'
  rdGb : ∀ st m m', (∀ j, O.Rd j → m j = m' j) → Y.Gb st m = Y.Gb st m'
  rdS  : ∀ st j, ¬ O.Rd j → Y.slS st j = 0
  wG   : ∀ st m m', (∀ j, (∀ i, j ≠ Y.wAt i) → m j = m' j) → Y.G st m = Y.G st m'
  wGb  : ∀ st m m', (∀ j, (∀ i, j ≠ Y.wAt i) → m j = m' j) → Y.Gb st m = Y.Gb st m'
  sS   : ∀ st i, Y.slS st (O.at i) = 0
  sum  : ∀ st m m', (∀ j, (∀ i, j ≠ O.at i) → m j = m' j) →
    hSumAll (Y.vars st) (Y.sum st m) = hSumAll (Y.vars st) (Y.sum st m')
  val  : ∀ st m (ρ : Rho (pRounds Y.fmt)),
    (unif (O.Cx → E)).map (fun c a => Y.G st (Function.extend O.cAt c m) a (Y.hp st (pG Y.fmt ρ))) =
      unif (Y.A → E)

variable (Ex : ExtSpec)

/-- the coefficient and the point of challenges, read off the verifier's messages of the whole
block -/
def zEps (ρ : Rho (Y.psc Ex).shape) : E := (Rho.fst (s := Y.shapeC) (t := [pRoundV E Y.A]) ρ).1
def zPt (ρ : Rho (Y.psc Ex).shape) : PPt Y.fmt :=
  pG Y.fmt (Rho.fst (s := Y.shapeC) (t := [pRoundV E Y.A]) ρ).2

/-- (sum, round polynomials), and (sum, round polynomials, values), as plain parts -/
def packC (st : Y.St) (p : E × (RIdx (Y.vars st) → E)) : Plains (Y.core Ex).shape :=
  (p.1, pPl Y.fmt (Y.dat st) p.2)
def pack (st : Y.St) (p : PMsg (Y.vars st) Y.A) : Plains (Y.psc Ex).shape :=
  Plains.app (s := Y.shapeC) (t := [pRoundV E Y.A]) (p.1, pPl Y.fmt (Y.dat st) p.2.1) (p.2.2, ())

/-- All that the honest prover sends, in closed form, from the entries m. -/
def sent (st : Y.St) (m : Y.J → E) (ε : E) (γ : PPt Y.fmt) : PMsg (Y.vars st) Y.A :=
  (hMu (Y.vars st) (Y.W st m), Y.honQ st m ε (Y.hp st γ), fun a => Y.G st m a (Y.hp st γ))

variable {Wt : Type} (msg : Wt → Y.J → E)

open Classical in
/-- The fields of the item (`IOR.MaskData`) for the block. -/
def maskData (O : Y.Own) : IOR.MaskData (Y.psc Ex) Wt where
  Kc  := Y.J → E
  kc  := fun w => O.cut (msg w)
  Xp  := E × Y.St
  pub := fun x => x
  Mk  := O.Mk
  put := O.put
  Cl  := Y.SumHolds
  msg := fun m x ρ => Y.pack Ex x.2 (Y.sent x.2 m (Y.zEps Ex ρ) (Y.zPt Ex ρ))
  sim := fun x ρ =>
    (pscSim (Y.vars x.2) Y.A (Y.hp x.2 (Y.zPt Ex ρ)) (Y.zEps Ex ρ) x.1).map (Y.pack Ex x.2)

open Classical in
/-- the fields for `Y.core` alone (round 0 and the rounds of the variables): own entries = the
coefficients of the hiding polynomial -/
def maskDataC (Rd : Y.J → Prop) : IOR.MaskData (Y.core Ex) Wt where
  Kc  := Y.J → E
  kc  := fun w j => if Rd j then msg w j else 0
  Xp  := E × Y.St
  pub := fun x => x
  Mk  := PIdx Y.fmt → E
  put := fun M m => Function.extend Y.wAt M m
  Cl  := Y.SumHolds
  msg := fun m x ρ =>
    Y.packC Ex x.2 (hMu (Y.vars x.2) (Y.W x.2 m), Y.honQ x.2 m ρ.1 (Y.hp x.2 (pG Y.fmt ρ.2)))
  sim := fun x ρ =>
    ((unif (HIdx (Y.vars x.2) → E)).map fun W =>
        (hMu (Y.vars x.2) W, hTr (Y.vars x.2) (ρ.1 * x.1) W (Y.hp x.2 (pG Y.fmt ρ.2)))).map
      (Y.packC Ex x.2)

end PscPar

namespace PscOur
variable {E : Type} [Field E] [Fintype E] (T : PscOur E)

open Classical in
/-- the own entries of the instance: one inner mask for each revealed map -/
def own (Rd : T.J → Prop) : T.par.Own := { Cx := T.A, cAt := T.cAt, Rd := Rd }

/-- The conditions in the instance. -/
structure OwnOur (Rd : T.J → Prop) : Prop where
  inj  : Function.Injective (Sum.elim T.wAt T.cAt)
  own  : ∀ i, Rd (Sum.elim T.wAt T.cAt i)
  rdF  : ∀ st m m', (∀ j, Rd j → m j = m' j) → T.F st m = T.F st m'
  rdFb : ∀ st m m', (∀ j, Rd j → m j = m' j) → T.Fb st m = T.Fb st m'
  rdS  : ∀ st j, ¬ Rd j → T.slS st j = 0
  /-- the maps, without their masks, and the incoming form read no own entry -/
  oF   : ∀ st m m', (∀ j, (∀ i, j ≠ Sum.elim T.wAt T.cAt i) → m j = m' j) → T.F st m = T.F st m'
  oFb  : ∀ st m m', (∀ j, (∀ i, j ≠ Sum.elim T.wAt T.cAt i) → m j = m' j) → T.Fb st m = T.Fb st m'
  oS   : ∀ st i, T.slS st (Sum.elim T.wAt T.cAt i) = 0

end PscOur

/-! ## The statements -/

namespace Spec
open IOR
variable (E : Type) [Field E] [Fintype E]

/-- States, under the hypotheses below: the block has the item "masked messages". -/
def psc_mm : Prop :=
  ∀ (Y : PscPar E) (Ex : ExtSpec) (Wt : Type) (msg : Wt → Y.J → E) (O : Y.Own),
    Y.VarsOK → Y.DegOK → Y.OwnOK O → (Y.hon Ex msg).MM (Y.maskData Ex msg O)

/-- `Y.core` alone (round 0 and the rounds of the variables). -/
def psc_core_mm : Prop :=
  ∀ (Y : PscPar E) (Ex : ExtSpec) (Wt : Type) (msg : Wt → Y.J → E) (Rd : Y.J → Prop),
    Y.VarsOK → Y.DegOK → Y.OwnW Rd → (Y.honC Ex msg).MM (Y.maskDataC Ex msg Rd)

/-- States, under `Y.OwnOK O`: the witness is handed on unchanged; the explicit part with which the
prover ends is a function of x, of the entries read and of ρ. -/
def psc_hands : Prop :=
  ∀ (Y : PscPar E) (Ex : ExtSpec) (Wt : Type) (msg : Wt → Y.J → E) (O : Y.Own), Y.OwnOK O →
    ∀ (w : Wt) (x : E × Y.St) (c : (Y.hon Ex msg).Coin) (ρ : Rho (Y.psc Ex).shape),
      (((Y.hon Ex msg).strat w x c).run ρ).2 =
        (Y.honOut (Y.honMid x.2 (O.cut (msg w)) (Y.zEps Ex ρ) (Y.zPt Ex ρ)) (O.cut (msg w)), w)

/-- States: the conditions of the instance give the conditions of the block. -/
def psc_our_own : Prop := ∀ (T : PscOur E) (Rd : T.J → Prop), T.OwnOur Rd → T.par.OwnOK (T.own Rd)

/-- States, under the hypotheses below: the instance with the dummy variable has the item. -/
def psc_our_mm : Prop :=
  ∀ (T : PscOur E) (Ex : ExtSpec) (Wt : Type) (msg : Wt → T.J → E) (Rd : T.J → Prop),
    T.VarsOK → T.par.DegOK → T.OwnOur Rd → (T.par.hon Ex msg).MM (T.par.maskData Ex msg (T.own Rd))

/-- These state the number of own mask entries: the coefficients of the hiding polynomial;
`psc_own_card_all`: with the inner masks. -/
def psc_own_card : Prop := ∀ l : List (PFmt E), Fintype.card (PIdx l) = 1 + (l.map PFmt.n).sum
def psc_own_card_all : Prop :=
  ∀ (Y : PscPar E) (O : Y.Own),
    Fintype.card (PIdx Y.fmt ⊕ O.Cx) = 1 + (Y.fmt.map PFmt.n).sum + Fintype.card O.Cx
/-- The honest prover has no coins. -/
def psc_no_coins : Prop :=
  ∀ (Y : PscPar E) (Ex : ExtSpec) (Wt : Type) (msg : Wt → Y.J → E), Subsingleton (Y.hon Ex msg).Coin

/-- With a carried part of the explicit part and further oracles: the same simulator; it does not
read the carried part. -/
def psc_mm_keep : Prop :=
  ∀ (Y : PscPar E) (Ex F : ExtSpec) (Cr Wt : Type) (msg : Wt → Y.J → E) (O : Y.Own),
    Y.VarsOK → Y.DegOK → Y.OwnOK O → ((Y.hon Ex msg).keep Cr F).MM ((Y.maskData Ex msg O).keep Cr F)

end Spec
end
end Cb
