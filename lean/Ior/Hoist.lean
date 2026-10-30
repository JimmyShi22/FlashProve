-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/Hoist.lean: a transformation of interactive oracle reductions (IORs): messages that the prover
can fix early are sent in one first message.

Definitions, statements, and one theorem with its proof (`Marks.old_injective`); the proofs of the
statements are in Ior/HoistProofs.lean.
An IOR (`IOR`, Ior/Ior.lean) is an interactive oracle reduction: a protocol after whose rounds the
verifier rejects or outputs a new statement.

Why: a chain of blocks lets each block send its own mask oracle, in a round of its own whose
verifier message has one value. A print of this protocol's technical report
(lean/CREDITS.md) sends all mask oracles of a sub-protocol together, in its first message. Here: the
passage from the one to the other, for any interactive
oracle reduction (Ior/Ior.lean), all such rounds at once.

Main names:
  `Marks`: a marking μ of a shape (by recursion on the list of rounds, as all that depends on a
    shape): each round is kept, or marked, with a value u of its verifier message. `μ.OK`: u is the
    only value.
  `μ.rest`: the shape without the marked rounds.
  `μ.shape`: `μ.front :: μ.rest`, the new shape.
  `μ.tr`, `μ.rho`, `μ.plains`, `μ.old`, `μ.symOld`, `μ.orcs`: from the new shape back to the old:
    transcripts, verifier randomness, plain parts, positions, symbols, oracles. `μ.symNew`, `μ.plM`,
    `μ.plR`, `μ.rhoR`: the maps from the old shape to the new.
  `Strat.drop`, `Strat.masksAt`, `Strat.hoist`: a strategy of the old shape plays the kept rounds;
    its marked messages along given verifier messages; the strategy of the new shape. `Err.rest`,
    `Err.ZeroAt`: the error list without the marked rounds; the errors of the marked rounds are 0.
  `R.hoist μ`, `H.hoist μ ρ₀`, `P.hoist μ`: the reduction, its honest side, its numbers. ρ₀:
    verifier messages of the kept rounds along which the honest prover's marked messages are read:
    an argument, so that the first message is a closed term; under `Early` it does not matter which.
  `Early`, the one condition on the honest side: its marked messages do not depend on the verifier
    messages of the kept rounds. They may depend on coins, witness and instance. `Free`: they depend
    on the coins alone (compared along the verifier messages of the kept rounds: ρ, ρ' :
    `Rho μ.rest`); this is what is kept when protocols are put in a row (`Spec.free_seq`), and it
    gives `Early`.
  `Spec.doomed_hoist`: if the prover has lost in the old shape, with errors 0 in the marked rounds,
    it has lost in the new one, towards the same goal read back, with the error 0 for the first
    message and the old errors for the kept rounds.
  `Spec.know_hoist`: so, under the hypotheses of its statement, round-by-round knowledge soundness
    is kept: same relations, same extractor (it reads the oracles back), same errors without the
    marked rounds. Beyond `ε.ZeroAt μ` nothing is asked of the marking: not even that u is the only
    value.
  `Spec.isLocal_hoist`, `Spec.point_hoist`, `Spec.acc_hoist`, `Spec.exact_hoist`,
    `Spec.prRho_hoist`: locality; strings; completeness and honest-verifier exact zero knowledge
    (`Early`), with the simulator of R up to the renaming of positions and the same budget read
    back; probabilities of sets of verifier randomness (`μ.OK`).
  `Spec.good_hoist`: under `μ.OK`, `P.err.ZeroAt μ` and `H.Early μ`, the bundle of Ior/Chain.lean is
    kept.

Limits: the oracles of the first message stay separate oracles: that they form one interleaved word
under one code (other alphabet, other budget, a smaller relaxation by joint decoding) is not said
here. That the first message joins the next prover message is not said here (the joined round alone:
`Round.joinMsg`, Iop/Join.lean; on IOPs, as a definition: `InteractiveOracleProof.recut` at `XPlan.msg`,
Iop/Recut.lean). This file says nothing on numbers of queries: the verifier reads the same symbols
as before.
Terms: lean/GLOSSARY.md.
-/
import Ior.Chain
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

/-- A marking of a shape: each round is kept (none) or marked, with a value of its verifier
message. -/
def Marks : Shape → Type
  | [] => Unit
  | r :: s => Option r.Chal × Marks s

namespace Marks

/-- The value is the only value of the verifier message of a marked round. -/
def OK : {s : Shape} → Marks s → Prop
  | [], _ => True
  | _ :: _, (none, μ) => OK μ
  | r :: _, (some u, μ) => (∀ c : r.Chal, c = u) ∧ OK μ

/-- Nothing is marked. -/
def keep : (s : Shape) → Marks s
  | [] => ()
  | _ :: s => (none, keep s)

/-- Two shapes in a row. -/
def app : {s t : Shape} → Marks s → Marks t → Marks (s ++ t)
  | [], _, _, ν => ν
  | _ :: _, _, (o, μ), ν => (o, app μ ν)

/-- The shape without the marked rounds. -/
def rest : {s : Shape} → Marks s → Shape
  | [], _ => []
  | r :: _, (none, μ) => r :: rest μ
  | _ :: _, (some _, μ) => rest μ

/-- The oracle parts, the positions, the plain parts of the marked rounds. -/
def Orc : {s : Shape} → Marks s → Type
  | [], _ => Unit
  | _ :: _, (none, μ) => Orc μ
  | r :: _, (some _, μ) => r.Orc × Orc μ

def Pos : {s : Shape} → Marks s → Type
  | [], _ => Empty
  | _ :: _, (none, μ) => Pos μ
  | r :: _, (some _, μ) => r.Pos ⊕ Pos μ

def Plain : {s : Shape} → Marks s → Type
  | [], _ => Unit
  | _ :: _, (none, μ) => Plain μ
  | r :: _, (some _, μ) => r.Plain × Plain μ

def Sym : {s : Shape} → (μ : Marks s) → Pos μ → Type
  | _ :: _, (none, μ), p => Sym μ p
  | r :: _, (some _, _), .inl p => r.Sym p
  | _ :: _, (some _, μ), .inr p => Sym μ p

def rd : {s : Shape} → (μ : Marks s) → Orc μ → (p : Pos μ) → Sym μ p
  | _ :: _, (none, μ), o, p => rd μ o p
  | r :: _, (some _, _), o, .inl p => r.rd o.1 p
  | _ :: _, (some _, μ), o, .inr p => rd μ o.2 p

def dOrc : {s : Shape} → (μ : Marks s) → Orc μ
  | [], _ => ()
  | _ :: _, (none, μ) => dOrc μ
  | r :: _, (some _, μ) => (r.dOrc, dOrc μ)

def dPlain : {s : Shape} → (μ : Marks s) → Plain μ
  | [], _ => ()
  | _ :: _, (none, μ) => dPlain μ
  | r :: _, (some _, μ) => (r.dPlain, dPlain μ)

variable {s : Shape}

/-- The first message: all marked messages, as separate oracles and plain parts of one message. -/
@[reducible] def front (μ : Marks s) : Round where
  Orc := μ.Orc
  Pos := μ.Pos
  Sym := μ.Sym
  rd := μ.rd
  Plain := μ.Plain
  Chal := Unit
  dOrc := μ.dOrc
  dPlain := μ.dPlain

/-- The new shape. -/
abbrev shape (μ : Marks s) : Shape := μ.front :: μ.rest

/-! ### Back to the old shape -/

/-- A transcript of the old shape, from the marked messages and a transcript of the kept rounds. -/
def tr : {s : Shape} → (μ : Marks s) → μ.Orc × μ.Plain → Tr μ.rest → Tr s
  | [], _, _, _ => ()
  | _ :: _, (none, μ), M, (m, c, τ) => (m, c, tr μ M τ)
  | _ :: _, (some u, μ), M, τ => ((M.1.1, M.2.1), u, tr μ (M.1.2, M.2.2) τ)

def rho : {s : Shape} → (μ : Marks s) → Rho μ.rest → Rho s
  | [], _, _ => ()
  | _ :: _, (none, μ), (c, ρ) => (c, rho μ ρ)
  | _ :: _, (some u, μ), ρ => (u, rho μ ρ)

def rhoR : {s : Shape} → (μ : Marks s) → Rho s → Rho μ.rest
  | [], _, _ => ()
  | _ :: _, (none, μ), (c, ρ) => (c, rhoR μ ρ)
  | _ :: _, (some _, μ), (_, ρ) => rhoR μ ρ

def plains : {s : Shape} → (μ : Marks s) → μ.Plain → Plains μ.rest → Plains s
  | [], _, _, _ => ()
  | _ :: _, (none, μ), P, (a, π) => (a, plains μ P π)
  | _ :: _, (some _, μ), P, π => (P.1, plains μ P.2 π)

def plM : {s : Shape} → (μ : Marks s) → Plains s → μ.Plain
  | [], _, _ => ()
  | _ :: _, (none, μ), (_, π) => plM μ π
  | _ :: _, (some _, μ), (a, π) => (a, plM μ π)

def plR : {s : Shape} → (μ : Marks s) → Plains s → Plains μ.rest
  | [], _, _ => ()
  | _ :: _, (none, μ), (a, π) => (a, plR μ π)
  | _ :: _, (some _, μ), (_, π) => plR μ π

/-- The old position of a position of the new shape. -/
def old : {s : Shape} → (μ : Marks s) → OPos μ.shape → OPos s
  | _ :: _, (none, μ), .inl p => .inr (old μ (.inl p))
  | _ :: _, (none, _), .inr (.inl p) => .inl p
  | _ :: _, (none, μ), .inr (.inr p) => .inr (old μ (.inr p))
  | _ :: _, (some _, _), .inl (.inl p) => .inl p
  | _ :: _, (some _, μ), .inl (.inr p) => .inr (old μ (.inl p))
  | _ :: _, (some _, μ), .inr p => .inr (old μ (.inr p))

/-- Different positions have different old positions. (Proved here: the definition of `R.hoist` uses
it.) -/
theorem old_injective : ∀ {s : Shape} (μ : Marks s), Function.Injective μ.old
  | [], _ => fun q => by rcases q with p | p <;> exact p.elim
  | _ :: _, (none, μ) => by
      have ih := old_injective μ
      rintro (p | p | p) (p' | p' | p') h
      · exact congrArg Sum.inl (Sum.inl.inj (ih (Sum.inr.inj h)))
      · exact (Sum.inr_ne_inl h).elim
      · exact (Sum.inl_ne_inr (ih (Sum.inr.inj h))).elim
      · exact (Sum.inl_ne_inr h).elim
      · exact congrArg (fun x => Sum.inr (Sum.inl x)) (Sum.inl.inj h)
      · exact (Sum.inl_ne_inr h).elim
      · exact (Sum.inr_ne_inl (ih (Sum.inr.inj h))).elim
      · exact (Sum.inr_ne_inl h).elim
      · exact congrArg (fun x => Sum.inr (Sum.inr x)) (Sum.inr.inj (ih (Sum.inr.inj h)))
  | _ :: _, (some _, μ) => by
      have ih := old_injective μ
      rintro ((p | p) | p) ((p' | p') | p') h
      · exact congrArg (fun x => Sum.inl (Sum.inl x)) (Sum.inl.inj h)
      · exact (Sum.inl_ne_inr h).elim
      · exact (Sum.inl_ne_inr h).elim
      · exact (Sum.inr_ne_inl h).elim
      · exact congrArg (fun x => Sum.inl (Sum.inr x)) (Sum.inl.inj (ih (Sum.inr.inj h)))
      · exact (Sum.inl_ne_inr (ih (Sum.inr.inj h))).elim
      · exact (Sum.inr_ne_inl h).elim
      · exact (Sum.inr_ne_inl (ih (Sum.inr.inj h))).elim
      · exact congrArg Sum.inr (Sum.inr.inj (ih (Sum.inr.inj h)))

/-- A symbol at a position of the new shape is a symbol at its old position, and back. -/
def symOld : {s : Shape} → (μ : Marks s) → (q : OPos μ.shape) → OSym μ.shape q → OSym s (μ.old q)
  | _ :: _, (none, μ), .inl p, x => symOld μ (.inl p) x
  | _ :: _, (none, _), .inr (.inl _), x => x
  | _ :: _, (none, μ), .inr (.inr p), x => symOld μ (.inr p) x
  | _ :: _, (some _, _), .inl (.inl _), x => x
  | _ :: _, (some _, μ), .inl (.inr p), x => symOld μ (.inl p) x
  | _ :: _, (some _, μ), .inr p, x => symOld μ (.inr p) x

def symNew : {s : Shape} → (μ : Marks s) → (q : OPos μ.shape) → OSym s (μ.old q) → OSym μ.shape q
  | _ :: _, (none, μ), .inl p, x => symNew μ (.inl p) x
  | _ :: _, (none, _), .inr (.inl _), x => x
  | _ :: _, (none, μ), .inr (.inr p), x => symNew μ (.inr p) x
  | _ :: _, (some _, _), .inl (.inl _), x => x
  | _ :: _, (some _, μ), .inl (.inr p), x => symNew μ (.inl p) x
  | _ :: _, (some _, μ), .inr p, x => symNew μ (.inr p) x

/-- The oracles of the old shape, from those of the marked and of the kept rounds. -/
def orcs : {s : Shape} → (μ : Marks s) → ((p : μ.Pos) → μ.Sym p) → Orcs μ.rest → Orcs s
  | [], _, _, _ => fun p => p.elim
  | _ :: _, (none, μ), oM, o => fun p => match p with
    | .inl p => o (.inl p)
    | .inr p => orcs μ oM (fun q => o (.inr q)) p
  | _ :: _, (some _, μ), oM, o => fun p => match p with
    | .inl p => oM (.inl p)
    | .inr p => orcs μ (fun q => oM (.inr q)) o p

/-- The same on whole objects of the new shape. -/
def trOld (μ : Marks s) (τ : Tr μ.shape) : Tr s := μ.tr τ.1 τ.2.2
def rhoOld (μ : Marks s) (ρ : Rho μ.shape) : Rho s := μ.rho ρ.2
def orcsOld (μ : Marks s) (o : Orcs μ.shape) : Orcs s :=
  μ.orcs (fun p => o (.inl p)) fun p => o (.inr p)

end Marks

/-! ### Strategies and errors -/

namespace Strat

/-- The strategy plays the kept rounds; in a marked round it is told the value u. -/
def drop : {s : Shape} → (μ : Marks s) → {β : Type} → Strat s β → Strat μ.rest β
  | [], _, _, b => b
  | _ :: _, (none, μ), _, (m, k) => (m, fun c => drop μ (k c))
  | _ :: _, (some u, μ), _, (_, k) => drop μ (k u)

/-- Its marked messages, along given verifier messages. -/
def masksAt : {s : Shape} → (μ : Marks s) → {β : Type} → Strat s β → Rho μ.rest → μ.Orc × μ.Plain
  | [], _, _, _, _ => ((), ())
  | _ :: _, (none, μ), _, (_, k), (c, ρ) => masksAt μ (k c) ρ
  | _ :: _, (some u, μ), _, (m, k), ρ =>
    ((m.1, (masksAt μ (k u) ρ).1), (m.2, (masksAt μ (k u) ρ).2))

/-- The marked messages do not depend on the verifier messages of the kept rounds. -/
def Early {s : Shape} (μ : Marks s) {β : Type} (σ : Strat s β) : Prop :=
  ∀ ρ ρ', masksAt μ σ ρ = masksAt μ σ ρ'

/-- The strategy of the new shape: first all marked messages, read along the verifier messages ρ₀
(an argument: nothing is picked; for a strategy with `Early` the value does not depend on it), then
the kept rounds. -/
def hoist {s : Shape} (μ : Marks s) (ρ₀ : Rho μ.rest) {β : Type} (σ : Strat s β) :
    Strat μ.shape β :=
  (masksAt μ σ ρ₀, fun _ => drop μ σ)

end Strat

namespace Err

/-- The error list without the marked rounds. -/
def rest : {s : Shape} → (μ : Marks s) → Err s → Err μ.rest
  | [], _, _ => ()
  | _ :: _, (none, μ), (e, ε) => (e, rest μ ε)
  | _ :: _, (some _, μ), (_, ε) => rest μ ε

/-- The errors of the marked rounds are 0. -/
def ZeroAt : {s : Shape} → (μ : Marks s) → Err s → Prop
  | [], _, _ => True
  | _ :: _, (none, μ), (_, ε) => ZeroAt μ ε
  | _ :: _, (some _, μ), (e, ε) => e = 0 ∧ ZeroAt μ ε

/-- The error list of the new shape. -/
def hoist {s : Shape} (μ : Marks s) (ε : Err s) : Err μ.shape := (0, rest μ ε)

end Err

/-! ### The reduction -/

namespace IOR
variable {K Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type}

/-- R with its marked messages sent first. The verifier does what it did, on the transcript read
back. -/
def hoist (R : IOR Xi Ei Xo Eo) (μ : Marks R.shape) : IOR Xi Ei Xo Eo where
  shape := μ.shape
  blinded q := R.blinded (μ.old q)
  extReads ρ := R.extReads (μ.rhoOld ρ)
  reads ρ := (R.reads (μ.rhoOld ρ)).preimage μ.old μ.old_injective.injOn
  out x y τ := R.out x y (μ.trOld τ)
  imp y τ := R.imp y (μ.trOld τ)
  srcE ρ q := R.srcE (μ.rhoOld ρ) q
  srcO ρ q := (R.srcO (μ.rhoOld ρ) q).preimage μ.old μ.old_injective.injOn
  tie ρ p := R.tie (μ.rhoOld ρ) (μ.old p)

/-- Its honest side: same coins; the withheld sets are those of H, read back. -/
def Honest.hoist
    {R : IOR Xi Ei Xo Eo} (H : R.Honest Wi Wo) (μ : Marks R.shape) (ρ₀ : Rho μ.rest) :
    (R.hoist μ).Honest Wi Wo where
  Coin := H.Coin
  strat w x c := (H.strat w x c).hoist μ ρ₀
  Bad := {ρ | μ.rhoOld ρ ∈ H.Bad}
  Hid w x := {ρ | μ.rhoOld ρ ∈ H.Hid w x}

/-- The honest prover's marked messages do not depend on the verifier messages of the kept
rounds. -/
def Honest.Early {R : IOR Xi Ei Xo Eo} (H : R.Honest Wi Wo) (μ : Marks R.shape) : Prop :=
  ∀ w x c, (H.strat w x c).Early μ

/-- They depend on the coins alone (compared along the verifier messages of the kept rounds: ρ, ρ' :
`Rho μ.rest`). -/
def Honest.Free {R : IOR Xi Ei Xo Eo} (H : R.Honest Wi Wo) (μ : Marks R.shape) : Prop :=
  ∀ w x w' x' c ρ ρ', (H.strat w x c).masksAt μ ρ = (H.strat w' x' c).masksAt μ ρ'

open Classical in
/-- Its numbers: the error 0 for the first message, the old errors for the kept rounds; the same
probabilities; budget and cover read back. -/
def Nums.hoist {R : IOR Xi Ei Xo Eo} (P : Nums K R) (μ : Marks R.shape) :
    Nums K (R.hoist μ) where
  err  := P.err.hoist μ
  pBad := P.pBad
  pHid := P.pHid
  bud  := fun ρ T => P.bud (μ.rhoOld ρ) (T.image μ.old)
  cov  := fun k => {ρ | μ.rhoOld ρ ∈ P.cov k}

/-- What a run of R shows, written for the new shape. -/
def View.hoist {R : IOR Xi Ei Xo Eo} (μ : Marks R.shape) (V : View R) : View (R.hoist μ) where
  plains := (μ.plM V.plains, μ.plR V.plains)
  orc := fun q => (V.orc (μ.old q)).map (μ.symNew q)

open Classical in
/-- The simulator: that of R, on the verifier's randomness and the further positions read back; its
output written for the new shape. -/
def simHoist {R : IOR Xi Ei Xo Eo} (μ : Marks R.shape) (S : Honest.Sim R) :
    Honest.Sim (R.hoist μ) :=
  fun x ρ T a => (S x (μ.rhoOld ρ) (T.image μ.old) a).map (Option.map (View.hoist μ))

end IOR

namespace Spec
open IOR

/-- Under the hypotheses below, if the prover has lost in the old shape it has lost in the new one,
towards the same goal read back (a prover that fixes later messages early is a special prover). -/
def doomed_hoist : Prop :=
  ∀ (s : Shape) (μ : Marks s) (ε : Err s) (bad : Tr s → Prop),
    ε.ZeroAt μ → Doomed s ε bad → Doomed μ.shape (ε.hoist μ) fun τ => bad (μ.trOld τ)

/-- Under the hypotheses below, round-by-round knowledge soundness is kept. -/
def know_hoist : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (μ : Marks R.shape) (Wi Wo : Type)
      (on : Xi × Ei.Str → Prop) (RA : Xi × Ei.Str → Wi → Prop) (RB : Xo × Eo.Str → Wo → Prop)
      (ext : Ei.Str → Orcs R.shape → Wo → Wi) (ε : Err R.shape),
    ε.ZeroAt μ → R.red.Know on RA RB (fun a τ w => ext a.2 τ.read w) ε →
    (R.hoist μ).red.Know on RA RB (fun a τ w => ext a.2 (μ.orcsOld τ.read) w) (ε.hoist μ)

def isLocal_hoist : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (μ : Marks R.shape),
    R.IsLocal → (R.hoist μ).IsLocal

/-- If all oracles are strings, so are those of the new shape. -/
def point_hoist : Prop := ∀ (s : Shape) (μ : Marks s), Nonempty s.IsPoint → Nonempty μ.shape.IsPoint

/-- Under `μ.OK`, a set of values of the verifier's randomness has the same probability read
back. -/
def prRho_hoist : Prop :=
  ∀ (s : Shape) (μ : Marks s) (S : Set (Rho s)),
    μ.OK → prRho {ρ : Rho μ.shape | μ.rhoOld ρ ∈ S} = prRho S

def acc_hoist : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (μ : Marks R.shape)
      (ρ₀ : Rho μ.rest) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (Ri : Xi → Ei.Str → Wi → Prop) (Ro : Xo → Eo.Str → Wo → Prop),
    H.Early μ → H.Acc Ri Ro → (H.hoist μ ρ₀).Acc Ri Ro

open Classical in
/-- Under the hypotheses below, honest-verifier exact zero knowledge is kept, with the simulator
named. -/
def exact_hoist : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (μ : Marks R.shape) (ρ₀ : Rho μ.rest)
      (Wi Wo : Type) (H : R.Honest Wi Wo) (Ri : Xi → Ei.Str → Wi → Prop)
      (bud : Rho R.shape → Finset (OPos R.shape) → Prop) (S : Honest.Sim R),
    H.Early μ → H.ExactWith Ri bud S →
    (H.hoist μ ρ₀).ExactWith Ri (fun ρ T => bud (μ.rhoOld ρ) (T.image μ.old)) (simHoist μ S)

/-- Under the hypotheses below, the bundle is kept. -/
def good_hoist : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (μ : Marks R.shape) (ρ₀ : Rho μ.rest)
      (Wi Wo : Type) (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
      (ext : Ei.Str → Orcs R.shape → Wo → Wi) (P : Nums K R),
    μ.OK → P.err.ZeroAt μ → H.Early μ → Good R H A B ext P →
    Good (R.hoist μ) (H.hoist μ ρ₀) A B (fun y o w => ext y (μ.orcsOld o) w) (P.hoist μ)

/-- "The coins alone" (`H.Free μ`) gives "not the verifier messages of the kept rounds". -/
def early_of_free : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (μ : Marks R.shape)
      (Wi Wo : Type) (H : R.Honest Wi Wo),
    H.Free μ → H.Early μ

/-- Along a chain: if the marked messages of both provers depend on their coins alone
(`Honest.Free`), so do those of the composed prover. -/
def free_seq : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (μ₁ : Marks R₁.shape) (μ₂ : Marks R₂.shape) (W₁ W₂ W₃ : Type)
      (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃),
    H₁.Free μ₁ → H₂.Free μ₂ → (H₁.seq H₂).Free (μ₁.app μ₂)

def ok_app : Prop := ∀ (s t : Shape) (μ : Marks s) (ν : Marks t), μ.OK → ν.OK → (μ.app ν).OK

def zeroAt_app : Prop :=
  ∀ (s t : Shape) (μ : Marks s) (ν : Marks t) (ε : Err s) (ε' : Err t),
    ε.ZeroAt μ → ε'.ZeroAt ν → (Err.app ε ε').ZeroAt (μ.app ν)

end Spec
end Iop
