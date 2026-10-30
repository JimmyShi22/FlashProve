-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/Grind.lean: proof-of-work bits ("grinding") in the rounds of an interactive oracle proof.

The file has definitions and two statements, for ordinary interactive oracle proofs (IOPs; `InteractiveOracleProof`,
Iop/InteractiveOracleProof.lean). The proofs are in Iop/GrindProofs.lean, the form for protocols with slots in
Iop/BatchGrind.lean. In the next paragraph "test bits" are proof-of-work bits.

What it is. StarkWare, "ethSTARK Documentation", version 1.2, section 6.3, calls it the grinded IOP:
in a round with b test bits the prover sends, after its message, one more piece (the nonce), and the
verifier sends, with its message c, b more uniform bits z; at the end the verifier accepts if the
old verifier accepts and every z is 0. Here that is a step on protocols, along a list g of numbers,
one for each round (Iop/GBits.lean).

`InteractiveOracleProof.grind W Q g` is this protocol; W is the type of nonces, a parameter with a fixed element
(`default`); of W nothing else is used. The interactive verifier does not read the nonce: it is
there so that the round's Fiat-Shamir query contains it, and a new nonce gives a new query and a new
answer (c, z). `Err.grind` keeps the error counts, which are now out of |C| · 2^b challenge values.

Stated and proved in Iop/GrindProofs.lean:
  InteractiveOracleProof.Sound.grind       round-by-round soundness is kept with the errors Err.grind g ε (ethSTARK
      Theorem 6: ε_i becomes ε_i 2^-b_i). No hypothesis on g.
  `Err.below_grind_iff`   all new errors, as probabilities, are at most c if and only if e_i ≤ c ·
      2^b_i · |C_i| in every round (`Err.BelowG`).
  `Honest.Acc.grind`      if the old honest prover is complete (`Honest.Acc`), then for valid inputs
      the verifier accepts the new one, with any rule for the nonces, outside the abort set
      (`withheld` in Lean names) and where all proof-of-work bits are 0.

What "128 BITS" means after this step. Round i of the new interactive protocol has the error e_i /
(|C_i| · 2^b_i). This is small only because the honest interactive prover fails too: all its
proof-of-work bits are 0 with probability 2^-(sum of the b_i). So the step is of use only under a
compiler in which a prover may repeat an attempt. There the honest prover makes about 2^b_i queries
in round i and a cheating prover one query for each attempt, and the bound is (number of queries) ·
(largest round error) + a collision term. If a list of positions is shortened so that a round's
error grows by 2^b, then with b proof-of-work bits the error is what it was: in the query model
nothing is gained or lost, and the gain is bytes. The model does not show that (a) without the proof
of work the protocol has rounds of error up to 2^-(128 - b); (b) at those rounds b of the 128 bits
are the cheating prover's work, counted at one query for each attempt; (c) a query costs 1 whatever
it is: the model never showed what a new attempt cost before (a new tree only where the last message
before the challenge is a root), nor that it now costs one hash. As a Lean term the bound of 128
bits after this step is `Err.Below (Err.grind g ε) 2^-128`: `Err.grind g ε` has the numbers of the
list ε unchanged, one beside each new round, and `Err.Below` says of each of them that it is at most
2^-128 times the number of values of its new round's challenge.

Limits:
* This file proves that bound for no protocol. It has no statement on a compiled scheme, and none of
  the form "work over probability".
* The new interactive protocol is not complete. Strategies, abort sets, positions read, views and
  simulators are the old ones and ignore the proof-of-work bits. A bit that is 1 does not put the
  randomness into the abort set and gives no notice: the honest prover goes on, and the verifier
  rejects. So completeness as `BatchProtocol.Props` states it fails as soon as a round has a
  proof-of-work bit and some verifier randomness of some valid input is outside the abort set (this
  is not proved), and `BatchProtocol.Props` of a record with such a protocol then holds for no
  numbers. The other clauses hold with the old numbers under uniform (c, z). The compiler runs the
  honest prover under another distribution of z (0 except with small probability); there c is still
  uniform and no set that the other clauses measure depends on z, so their numbers hold.
* The clause on hiding (`Spec.grindSim`) is about honest provers that send a nonce given in advance
  (with slots: one list for all slots). The compiled prover sends a nonce that it has found by
  search, which depends on the oracle's answers. For it the compiler has `InteractiveOracleProof.dview_grind` (the
  disclosed view (`DView`, Iop/InteractiveOracleProof.lean) of any new transcript is the disclosed view of the
  stripped transcript with that transcript's nonces put in) and must itself say how a simulator
  makes the nonces. Nothing here says what a nonce shows.
* The implementation stops publicly when it finds no nonce within its cap; here the prover goes on
  and is rejected. That stop is not modelled.
* The collision term of a compiler's bound gets no factor, and a round without proof of work must be
  below the bound c by itself.
* Nothing is said on how a nonce is found, on the number of attempts, or on queries. This file fixes
  neither W nor the length of a nonce (Iop/GrindCap.lean has the search data `cap64` at W = Fin
  (2^64)).
* At g = 0 the new list of rounds is the old one: by definition for a list that is written out, by
  the proved equation `Shape.grind_zero` for a variable list. That the protocol and the honest
  prover are then the old ones is not stated.
* The step on a record of protocols: `BatchProtocol`, Iop/BatchGrind.lean.

This transformer is applied last, after rounds are split and merged (Iop/Recut.lean) and after
challenges are derived from hash blocks (`BatchProtocol.draws`). Iop/GrindRecut.lean and Iop/GrindPull.lean
carry the list g through these steps, the second also the error lists.

The construction and Theorem 6 are ethSTARK's; the proof (Iop/GrindProofs.lean) is for this
library's recursion Doomed.

Notation: `Bad : Set (Rho Q.shape)`, `Hid : Wt → X → Set (Rho Q.shape)`: fields of `Honest`;
`Honest.withheld H w x` is `H.Bad ∪ H.Hid w x` (Iop/InteractiveOracleProof.lean); the two statements:
`Spec.grindSim`, `Spec.grindUnif : Prop`; `Doomed : (s : Shape) → Err s → (Tr s → Prop) → Prop`
(Iop/Rbr.lean): the recursion on the rounds by which `InteractiveOracleProof.Sound` is written.
The errors of this head are the numbers of a list ε (`Err s`, Iop/Rbr.lean): `Err.Below`
(Iop/InteractiveOracleProof.lean) and `Err.BelowG` bound such a list, whichever it is, and that a protocol is sound
at the numbers of the list is no statement of this file; that tie is `InteractiveOracleProof.Sound.grind`
(Iop/GrindProofs.lean), if the old protocol is sound at ε, and, with the bound, for records with
slots `grindSoundB` (Iop/BatchGrindProofs.lean), if the old record is sound at its lists
(`BatchProtocol.SoundAt`, Iop/SoundAt.lean).
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Iop.GBits
import Iop.InteractiveOracleProof
noncomputable section -- Lean tags what it cannot compile

namespace Iop
open Prob
open scoped ENNReal

/-! ## 1. One round -/

/-- The plain part (what a prover message sends in the clear, not as an oracle) in a round with b
proof-of-work bits: the old plain part and the nonce. At b = 0: the old plain part. -/
def GPlain (W : Type) : ℕ → Type → Type
  | 0, P => P
  | _ + 1, P => P × W

/-- The challenge of a round with b proof-of-work bits: the old challenge and these bits. At b = 0:
the old challenge. -/
def GChal : ℕ → Type → Type
  | 0, C => C
  | b + 1, C => C × (Fin (b + 1) → Bool)

namespace GPlain
variable {W P : Type}

/-- the old plain part -/
def old : {b : ℕ} → GPlain W b P → P
  | 0, p => p
  | _ + 1, (p, _) => p

/-- the nonce; the fixed element of W in a round with b = 0 -/
def nonce [Inhabited W] : {b : ℕ} → GPlain W b P → W
  | 0, _ => default
  | _ + 1, (_, ν) => ν

/-- put a nonce in; in a round with b = 0 it is dropped -/
def mk : (b : ℕ) → P → W → GPlain W b P
  | 0, p, _ => p
  | _ + 1, p, ν => (p, ν)

/-- the image of the old plain part under a function; the nonce is unchanged -/
def map {P' : Type} (f : P → P') : {b : ℕ} → GPlain W b P → GPlain W b P'
  | 0, p => f p
  | _ + 1, (p, ν) => (f p, ν)

end GPlain

namespace GChal
variable {C : Type}

/-- the old challenge -/
def old : {b : ℕ} → GChal b C → C
  | 0, c => c
  | _ + 1, (c, _) => c

/-- the proof-of-work bits -/
def test : {b : ℕ} → GChal b C → Fin b → Bool
  | 0, _ => fun i => i.elim0
  | _ + 1, (_, z) => z

def mk : (b : ℕ) → C → (Fin b → Bool) → GChal b C
  | 0, c, _ => c
  | _ + 1, c, z => (c, z)

/-- The proof-of-work check: every proof-of-work bit is 0. (Always true in a round with b = 0.) -/
def pass {b : ℕ} (c : GChal b C) : Bool := decide (∀ i, c.test i = false)

/-- the old challenge with proof-of-work bits 0 -/
def zero (b : ℕ) (c : C) : GChal b C := mk b c fun _ => false

instance instFintype : ∀ (b : ℕ) (C : Type) [Fintype C], Fintype (GChal b C)
  | 0, _, i => i
  | b + 1, C, _ => inferInstanceAs (Fintype (C × (Fin (b + 1) → Bool)))

instance instNonempty : ∀ (b : ℕ) (C : Type) [Nonempty C], Nonempty (GChal b C)
  | 0, _, i => i
  | b + 1, C, _ => inferInstanceAs (Nonempty (C × (Fin (b + 1) → Bool)))

end GChal

variable {W : Type} [Inhabited W]

/-- The round with b proof-of-work bits. The fixed substitute message has the fixed nonce (the
element `default` of W). -/
def Round.grind (W : Type) [Inhabited W] (r : Round) (b : ℕ) : Round where
  Orc := r.Orc
  Pos := r.Pos
  Sym := r.Sym
  rd := r.rd
  Plain := GPlain W b r.Plain
  Chal := GChal b r.Chal
  dOrc := r.dOrc
  dPlain := GPlain.mk b r.dPlain default

/-- At b = 0 the round is the round itself, by definition. -/
theorem Round.grind_zero (r : Round) : r.grind W 0 = r := rfl

/-- the old prover message -/
def Round.stripMsg {r : Round} {b : ℕ} (m : (r.grind W b).Msg) : r.Msg := (m.1, GPlain.old m.2)

/-- the prover message with a nonce -/
def Round.fillMsg {r : Round} (b : ℕ) (m : r.Msg) (ν : W) : (r.grind W b).Msg :=
  (m.1, GPlain.mk b m.2 ν)

/-! ## 2. Lists of rounds, and the maps from the new list to the old one -/

/-- The new list of rounds. -/
def Shape.grind (W : Type) [Inhabited W] : (s : Shape) → GBits s → Shape
  | [], _ => []
  | r :: s, (b, g) => r.grind W b :: Shape.grind W s g

/-- The stripped transcript, of the old list of rounds: nonces and proof-of-work bits are dropped.
-/
def Tr.strip : {s : Shape} → (g : GBits s) → Tr (s.grind W g) → Tr s
  | [], _, _ => ()
  | _ :: _, (_, g), (m, c, τ) => (Round.stripMsg m, GChal.old c, Tr.strip g τ)

/-- The stripped verifier randomness, of the old list of rounds. -/
def Rho.strip : {s : Shape} → (g : GBits s) → Rho (s.grind W g) → Rho s
  | [], _, _ => ()
  | _ :: _, (_, g), (c, ρ) => (GChal.old c, Rho.strip g ρ)

/-- All proof-of-work bits are 0. -/
def Rho.pass : {s : Shape} → (g : GBits s) → Rho (s.grind W g) → Bool
  | [], _, _ => true
  | _ :: _, (_, g), (c, ρ) => GChal.pass c && Rho.pass g ρ

/-- A right inverse of `Rho.strip`: all proof-of-work bits are 0. -/
def Rho.fill : {s : Shape} → (g : GBits s) → Rho s → Rho (s.grind W g)
  | [], _, _ => ()
  | _ :: _, (b, g), (c, ρ) => (GChal.zero b c, Rho.fill g ρ)

/-- The plain parts of the old list of rounds. -/
def Plains.strip : {s : Shape} → (g : GBits s) → Plains (s.grind W g) → Plains s
  | [], _, _ => ()
  | _ :: _, (_, g), (p, pl) => (GPlain.old p, Plains.strip g pl)

/-- A nonce for each round. That of a round with b = 0 is not used. -/
def GNon (W : Type) : Shape → Type
  | [] => Unit
  | _ :: s => W × GNon W s

/-- the fixed nonce in every round -/
def GNon.nil (W : Type) [Inhabited W] : (s : Shape) → GNon W s
  | [] => ()
  | _ :: s => (default, GNon.nil W s)

/-- The nonces among the plain parts. -/
def Plains.nonces : {s : Shape} → (g : GBits s) → Plains (s.grind W g) → GNon W s
  | [], _, _ => ()
  | _ :: _, (_, g), (p, pl) => (GPlain.nonce p, Plains.nonces g pl)

/-- A right inverse of `Plains.strip`: the nonces are put in. -/
def Plains.fill : {s : Shape} → (g : GBits s) → Plains s → GNon W s → Plains (s.grind W g)
  | [], _, _, _ => ()
  | _ :: _, (b, g), (p, pl), (ν, νs) => (GPlain.mk b p ν, Plains.fill g pl νs)

/-- The positions of the new list of rounds are those of the old one. -/
def OPos.stripE : {s : Shape} → (g : GBits s) → OPos (s.grind W g) ≃ OPos s
  | [], _ => Equiv.refl Empty
  | r :: _, (_, g) => Equiv.sumCongr (Equiv.refl r.Pos) (OPos.stripE g)

/-- The alphabet at a position does not change. -/
def OSym.strip :
    {s : Shape} → (g : GBits s) → (p : OPos (s.grind W g)) →
    OSym (s.grind W g) p → OSym s (OPos.stripE g p)
  | _ :: _, (_, _), .inl _ => fun a => a
  | _ :: _, (_, g), .inr q => fun a => OSym.strip g q a

/-- The map back from `OSym.strip`. -/
def OSym.fill :
    {s : Shape} → (g : GBits s) → (p : OPos (s.grind W g)) →
    OSym s (OPos.stripE g p) → OSym (s.grind W g) p
  | _ :: _, (_, _), .inl _ => fun a => a
  | _ :: _, (_, g), .inr q => fun a => OSym.fill g q a

/-! ## 3. From the old list of rounds to the new one -/

/-- A rule for the nonces: in each round a nonce, which may depend on all earlier challenges of the
new list of rounds, proof-of-work bits included. -/
def NStrat (W : Type) [Inhabited W] : (s : Shape) → GBits s → Type
  | [], _ => Unit
  | r :: s, (b, g) => W × ((r.grind W b).Chal → NStrat W s g)

/-- the rule that sends nonces given in advance -/
def NStrat.const : {s : Shape} → (g : GBits s) → GNon W s → NStrat W s g
  | [], _, _ => ()
  | _ :: _, (_, g), (ν, νs) => (ν, fun _ => NStrat.const g νs)

/-- A strategy of the old list of rounds with a rule for the nonces. The old messages do not depend
on the proof-of-work bits; the nonces may, through the rule. -/
def Strat.grind :
    {s : Shape} → {β : Type} → (g : GBits s) → Strat s β → NStrat W s g → Strat (s.grind W g) β
  | [], _, _, b, _ => b
  | _ :: _, _, (b, g), (m, k), (ν, n) =>
    (Round.fillMsg b m ν, fun c => Strat.grind g (k (GChal.old c)) (n c))

/-- The errors: the same counts, now out of card C * 2^b values. -/
def Err.grind : {s : Shape} → (g : GBits s) → Err s → Err (s.grind W g)
  | [], _, _ => ()
  | _ :: _, (_, g), (e, ε) => (e, Err.grind g ε)

/-- Every error of the list, as a probability, is at most c * 2^b, with b the number of
proof-of-work bits of its round. -/
def Err.BelowG : {s : Shape} → GBits s → Err s → ℝ≥0∞ → Prop
  | [], _, _, _ => True
  | r :: _, (b, g), (e, ε), c =>
    (e : ℝ≥0∞) ≤ c * ((2 : ℝ≥0∞) ^ b * (Fintype.card r.Chal : ℝ≥0∞)) ∧ Err.BelowG g ε c

variable {X : Type} {E : ExtSpec}

/-- The protocol with proof-of-work bits. The verifier reads the same positions as before, and
accepts if all these bits are 0 and the old verifier accepts the stripped transcript. -/
def InteractiveOracleProof.grind (W : Type) [Inhabited W] (Q : InteractiveOracleProof X E) (g : GBits Q.shape) : InteractiveOracleProof X E where
  shape    := Q.shape.grind W g
  blinded  := fun p => Q.blinded (OPos.stripE g p)
  extReads := fun x ρ => Q.extReads x (Rho.strip g ρ)
  reads    := fun x ρ pl =>
    (Q.reads x (Rho.strip g ρ) (Plains.strip g pl)).map (OPos.stripE g).symm.toEmbedding
  accept   := fun x y τ => Rho.pass g τ.rho && Q.accept x y (Tr.strip g τ)

/-- The honest prover: the same coins and the same external string; the nonces are ν, given in
advance. A value of the verifier randomness is in the abort set if its stripped value is. A
proof-of-work bit that is 1 does not put it there: nothing here looks at these bits. -/
def Honest.grind {Q : InteractiveOracleProof X E} {Wt : Type} (H : Honest Q Wt)
    (g : GBits Q.shape) (ν : GNon W Q.shape) : Honest (Q.grind W g) Wt where
  Coin  := H.Coin
  ext   := H.ext
  strat := fun w x c => Strat.grind g (H.strat w x c) (NStrat.const g ν)
  Bad   := {ρ | Rho.strip g ρ ∈ H.Bad}
  Hid   := fun w x => {ρ | Rho.strip g ρ ∈ H.Hid w x}

/-- The disclosed view with the nonces put in. -/
def DView.fill {Q : InteractiveOracleProof X E} (g : GBits Q.shape) (ν : GNon W Q.shape) (v : DView Q) :
    DView (Q.grind W g) where
  plains := Plains.fill g v.plains ν
  ext := v.ext
  orc := fun p => (v.orc (OPos.stripE g p)).map (OSym.fill g p)

/-- The simulator: the old simulator at the stripped randomness, with the nonces ν put in. -/
def simGrind {Q : InteractiveOracleProof X E} (g : GBits Q.shape) (ν : GNon W Q.shape)
    (Sim : X → (ρ : Rho Q.shape) → (E.Pos → Option E.Sym) → PMF (Option (DView Q))) :
    X → (ρ : Rho (Q.grind W g).shape) → (E.Pos → Option E.Sym) →
    PMF (Option (DView (Q.grind W g))) :=
  fun x ρ a => (Sim x (Rho.strip g ρ) a).map (Option.map (DView.fill g ν))


/-! ## 4. The statements -/

namespace Spec





/-- The simulator is exact wherever the old one is exact at the stripped randomness, whatever the
proof-of-work bits are; and the answers of the external strings that it is given are those that the
old one is given. -/
def grindSim : Prop :=
  ∀ (W : Type) [Inhabited W] (X : Type) (E : ExtSpec) (Q : InteractiveOracleProof X E) (Wt : Type) (H : Honest Q Wt)
      (g : GBits Q.shape) (ν : GNon W Q.shape)
      (Sim : X → (ρ : Rho Q.shape) → (E.Pos → Option E.Sym) → PMF (Option (DView Q))) (w : Wt)
      (x : X) (ρ : Rho (Q.shape.grind W g)),
    (Q.grind W g).extAns x ρ (H.ext w) = Q.extAns x (Rho.strip g ρ) (H.ext w) ∧
    (H.output w x (Rho.strip g ρ) = Sim x (Rho.strip g ρ) (Q.extAns x (Rho.strip g ρ) (H.ext w)) →
      (H.grind g ν).output w x ρ = simGrind g ν Sim x ρ ((Q.grind W g).extAns x ρ (H.ext w)))


/-- If the new verifier randomness is uniform, the stripped randomness is uniform. -/
def grindUnif : Prop :=
  ∀ (W : Type) [Inhabited W] (s : Shape) (g : GBits s) (S : Set (Rho s)),
    prRho {ρ : Rho (s.grind W g) | Rho.strip g ρ ∈ S} = prRho S

end Spec

end Iop
