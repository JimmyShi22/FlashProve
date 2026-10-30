-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdFront.lean: the front of a closing: steps without rounds, batchings and any number of
splittings over one signature, behind a chain that has sent the splittings' masks.

lean/GLOSSARY.md on "front": In `Cb/Ld/` and `Cb/Obj/`, the front of a closing is its first part,
before its tests: a list of steps without rounds, batchings and splits over one signature (`Front`,
Cb/Ld/LdFront.lean).

Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdFrontProofs.lean. This file
builds on Cb/Req1/LdSeg.lean, Cb/Req1/LdReq.lean (stages, moves, lists of moves; what zero knowledge
asks of a list, beside its hypotheses), Cb/Req1/LdSegCarry.lean (which facts on fresh masks a move
carries), Ior/KnowCollPiece.lean (a chain that stands behind another: `OkFrom`) and
Cb/Ld/LdTowerKitChain.lean (the budgets' halves).

In standard terms: a batching replaces many linear claims on the oracle messages by one, their
combination with coefficients from the verifier's seed; a splitting replaces one linear claim on the
messages of two groups by one claim on each, after the prover has said one scalar
(Cb/Ld/LdSplit.lean).

Why: before the tests on groups a closing brings its rows into the form "each row on one group":
many rows into one, a row on two groups into a row on each. A splitting is a masked block
(Cb/Ld/LdSplit.lean): its one mask entry κ stands in an oracle message that was sent some rounds
before the closing. So the closing is not zero knowledge by itself; it has to stand behind the
rounds before it (`c.OkFrom c₀`): each splitting's κ must be fresh after all that comes before it
(`Chain.FreshFor`, Ior/KnowCollRulesChain.lean). Here that is reduced, for any number of splittings,
to plain conditions.

Definitions. S, E₀, Wp are fixed: no move of a front sends, drops or tests an oracle message, and in
a batching and a splitting the honest prover hands its witness on (of a step `p.Quiet` asks it).
  `FSt S E₀ Wp Kc`: what changes along a front: the explicit part beside the samples, and the base
    joint. `x.stage`: the stage `⟨S, x.St, E₀, Wp, x.A⟩` (Cb/Req1/LdSegKit.lean). A stage
    (`LdStage`) is the data of a joint over oracle messages that are sent and sampled: their
    signature (`Sig`), the explicit statement without the samples, further oracles, a further
    witness, and what is claimed of the messages (a `Rels`).
  `Front x y`: a list of moves: nil; step (any step without rounds between two such stages); bat
    (many rows into one); split (a row on two groups into a row on each). `p.prog`: the list of
    moves of Cb/Req1/LdSeg.lean; its links after a chain c: `p.prog.onto c`.
  `p.Quiet Rd own`: no move of p looks at the entries "own": a step hands the witness on, and its
    new explicit part does not read the witness; a splitting reads entries in Rd only, its first row
    reads no own entry, its κ is not own. (A batching: nothing is asked.)
  `p.ZkOK Rd Rr base`: for every splitting of p, with p' the moves before it: p' is Quiet for {κ};
    what the splitting reads lies in Rd; the wide fact for κ (Cb/Req1/LdSegCarry.lean: entries in
    Rd, encoding randomness at Rr, the whole further witness; own = {κ}) is in "base": fresh at the
    start of the front.
  `p.Sd q`: every step's link has the budgets' half from q to q (`IOR.SideC`,
    Cb/Ld/LdTowerKitChain.lean). (Under their own hypotheses batchings and splittings have it for
    every q: the proof of `front_sides`.)

Main names:
  `Spec.front_carry`: under the moves' own hypotheses (`p.prog.Hyp`), Mk nonempty, a Quiet front
    carries the wide fact.
  `Spec.front_zk`: under `p.prog.Hyp`, `p.ZkOK` gives what zero knowledge asks of the list, beside
    its hypotheses (Cb/Req1/LdReq.lean: `p.prog.Zk base`), if "base" is closed under reading less.
  `Spec.front_okFrom`: the front stands behind c₀, that is `(p.prog.onto c).OkFrom c₀`, if: `c₀.Ok`;
    `c.OkFrom c₀` (c: say, one step without rounds); the moves' own hypotheses; `p.ZkOK` at base :=
    "fresh after c₀.append c".
  `Spec.front_sides`: `(p.prog.onto c).SidesC qa q` from `c.SidesC qa q`, `p.Sd q` and the moves'
    hypotheses.

The wide fact (`LdStage.wideFact`) is a `MaskFact` (Cb/Req1/LdSegFresh.lean), and "base" (in
`p.ZkOK Rd Rr base`) is a predicate on these. A `MaskFact W` is a reading `kc` of witnesses of type
W into a type `Kc`, a finite, non-empty type `Mk`, and a map `put : Mk → Kc → Kc`. (`MaskFact.Kc` is
a field of that record, not this file's parameter `Kc`, which is the first argument of `IOR.Rels`,
Ior/Chain.lean.)

Limits: this file does not say that the wide fact for a κ is fresh after a given chain (for the test
for linear constraints: Cb/Ld/LdLinCloseSplit.lean). The moves' own hypotheses (`p.prog.Hyp`) are
those of the files that define the blocks (`LdMv.Hyp`, Cb/Req1/LdSeg.lean). This file says nothing
on tests.
That all splittings of a closing come before its tests, and that their masks were sent earlier, is
this protocol's technical report (lean/CREDITS.md); the bookkeeping is ours.

Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegCarry
import Cb.Req1.LdReqProofs
import Cb.Ld.LdTowerKitChain
import Ior.KnowCollPiece

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood IOR

section
variable {E : Type} [Field E] [Fintype E]

/-- What changes along a front: the explicit part beside the samples, and the base joint. -/
structure FSt (S : Sig E) (E₀ : ExtSpec) (Wp Kc : Type) : Type 1 where
  St : Type
  A  : IOR.Rels Kc St E₀ (S.Msg × Wp)

variable {S : Sig E} {E₀ : ExtSpec} {Wp Kc : Type}

@[reducible] def FSt.stage (x : FSt S E₀ Wp Kc) : LdStage E Kc := ⟨S, x.St, E₀, Wp, x.A⟩

/-- The front of a closing: a list of moves over one signature. -/
inductive Front : FSt S E₀ Wp Kc → FSt S E₀ Wp Kc → Type 1
  | nil (x : FSt S E₀ Wp Kc) : Front x x
  | step {x y : FSt S E₀ Wp Kc} (p : Front x y) (z : FSt S E₀ Wp Kc)
      (f : y.stage.X → Option z.stage.X) (g : ExtMap y.stage.Ex z.stage.Ex)
      (m : y.stage.X × y.stage.W → z.stage.X × z.stage.W)
      (back : y.stage.X × y.stage.Ex.Str → z.stage.W → y.stage.W) : Front x z
  | bat {x : FSt S E₀ Wp Kc} (B : Type) (iB : Fintype B)
      (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) S.Ent) (Z : Evader E B)
      (St₀ : Type) (A₀ : IOR.Rels Kc St₀ E₀ (S.Msg × Wp))
      (p : Front x
        ⟨((B → E) × (∀ b, Sb b)) × St₀, claimRels (fun x m => Slf.All sl x (S.ents m)) A₀⟩) :
      Front x ⟨(E × ((∀ b, Sb b) × Z.D)) × St₀,
          claimRels (fun x m => (Slf.bat Z.ze sl).Holds x (S.ents m)) A₀⟩
  | split {x : FSt S E₀ Wp Kc} (G₁ G₂ : Grp S) (k : SplitAt G₁ G₂) (St₁ St₂ : Type)
      (sl₁ : Slf E St₁ G₁.C.J) (sl₂ : Slf E St₂ G₂.C.J) (St₀ : Type)
      (A₀ : IOR.Rels Kc St₀ E₀ (S.Msg × Wp)) (Rs : S.Ent → Prop) (dRs : DecidablePred Rs)
      (p : Front x ⟨(E × (St₁ × St₂)) × St₀, claimRels (splitIn sl₁ sl₂) A₀⟩) :
      Front x ⟨((E × St₁) × (E × St₂)) × St₀, claimRels (splitOut k sl₁ sl₂) A₀⟩

namespace Front

/-- The list of moves. -/
def prog : {x y : FSt S E₀ Wp Kc} → Front x y → LdProg x.stage y.stage
  | _, _, .nil x => .nil x.stage
  | _, _, .step p z f g m back => .snoc p.prog (.step _ z.stage f g m back)
  | _, _, .bat B _ Sb sl Z St₀ A₀ p => .snoc p.prog (.bat ⟨S, B, Sb, sl, Z, St₀, Wp, E₀, A₀⟩)
  | _, _, .split G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs _ p =>
    .snoc p.prog (.split ⟨S, G₁, G₂, k, St₁, St₂, sl₁, sl₂, St₀, Wp, E₀, A₀, Rs⟩)

/-- No move looks at the entries "own". -/
def Quiet (Rd own : S.Ent → Prop) : {x y : FSt S E₀ Wp Kc} → Front x y → Prop
  | _, _, .nil _ => True
  | _, _, .step p _ _ _ m _ =>
    p.Quiet Rd own ∧ (∀ a w, (m (a, w)).2 = w) ∧ ∀ a w w', (m (a, w')).1 = (m (a, w)).1
  | _, _, .bat _ _ _ _ _ _ _ p => p.Quiet Rd own
  | _, _, .split G₁ _ k _ _ sl₁ _ _ _ Rs _ p =>
    p.Quiet Rd own ∧ (∀ n, Rs n → Rd n) ∧ (∀ st n, own (G₁.ent n) → sl₁ st n = 0) ∧ ¬ own ⟨k.o, k.j⟩

/-- What is asked for the splittings. -/
def ZkOK (Rd : S.Ent → Prop) (Rr : S.O → Prop) :
    {x y : FSt S E₀ Wp Kc} → Front x y → (MaskFact x.stage.J.W → Prop) → Prop
  | _, _, .nil _, _ => True
  | _, _, .step p _ _ _ _ _, base => p.ZkOK Rd Rr base
  | _, _, .bat _ _ _ _ _ _ _ p, base => p.ZkOK Rd Rr base
  | x, _, .split _ _ k _ _ _ _ _ _ Rs _ p, base =>
      p.ZkOK Rd Rr base ∧
      p.Quiet Rd (fun n => n = ⟨k.o, k.j⟩) ∧
      (∀ n, Rs n → Rd n) ∧
      base (x.stage.wideFact Rd Rr (fun n => n = ⟨k.o, k.j⟩) E fun u _ => u)

/-- every step's link has the budgets' half from q to q -/
def Sd (q : Finset (E₀.prod S.ext).Pos → Prop) : {x y : FSt S E₀ Wp Kc} → Front x y → Prop
  | _, _, .nil _ => True
  | _, _, .step (y := y) p z f g m _ =>
    p.Sd q ∧ IOR.SideC (IOR.pure f g) (IOR.Honest.pure f g m) (IOR.Nums.pure Kc f g).bud q q
  | _, _, .bat _ _ _ _ _ _ _ p => p.Sd q
  | _, _, .split _ _ _ _ _ _ _ _ _ _ _ p => p.Sd q

end Front
end

namespace Spec
open IOR

/-- brackets: `append` is associative -/
def chain_append_assoc : Prop :=
  ∀ (K : Type) (A B C D : Joint K) (c₁ : Chain K A B) (c₂ : Chain K B C) (c₃ : Chain K C D),
    (c₁.append c₂).append c₃ = c₁.append (c₂.append c₃)

section
variable (E Kc : Type) [Field E] [Fintype E]

def prog_onto_append : Prop :=
  ∀ (Z A : Joint Kc) (a b : LdStage E Kc) (c₀ : Chain Kc Z A) (c : Chain Kc A a.J) (p : LdProg a b),
    p.onto (c₀.append c) = c₀.append (p.onto c)

/-- A list of moves after a chain c that stands behind c₀.
(not all hypotheses are named here: see the statement below) -/
def prog_okFrom : Prop :=
  ∀ (Z A : Joint Kc) (a b : LdStage E Kc) (c₀ : Chain Kc Z A) (c : Chain Kc A a.J)
      (p : LdProg a b) (base : MaskFact a.J.W → Prop),
    c₀.Ok → c.OkFrom c₀ → (∀ g, base g → (c₀.append c).FreshFor g.kc g.Mk g.put) →
    p.Hyp → p.Zk base → (p.onto c).OkFrom c₀

/-- States: under `p.prog.Hyp`, Mk nonempty, a front that does not look carries the wide fact. -/
def front_carry : Prop :=
  ∀ (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (x y : FSt S E₀ Wp Kc) (p : Front x y)
      (base : MaskFact x.stage.J.W → Prop) (Rd : S.Ent → Prop) (Rr : S.O → Prop)
      (own : S.Ent → Prop) (Mk : Type) [Fintype Mk] [Nonempty Mk] (val : Mk → S.Ent → E),
    p.prog.Hyp → p.Quiet Rd own → base (x.stage.wideFact Rd Rr own Mk val) →
    p.prog.After base (y.stage.wideFact Rd Rr own Mk val)

/-- What zero knowledge asks of the list, beside its hypotheses, if "base" is closed under reading
less.
(not all hypotheses are named here: see the statement below) -/
def front_zk : Prop :=
  ∀ (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (x y : FSt S E₀ Wp Kc) (p : Front x y)
      (base : MaskFact x.stage.J.W → Prop) (Rd : S.Ent → Prop) (Rr : S.O → Prop),
    (∀ (Rd' own : S.Ent → Prop) (Mk : Type) [Fintype Mk] [Nonempty Mk] (val : Mk → S.Ent → E),
      (∀ n, Rd' n → Rd n) → (∀ n, own n → Rd' n) →
      base (x.stage.wideFact Rd Rr own Mk val) → base (x.stage.entFact Rd' own Mk val)) →
    p.prog.Hyp → p.ZkOK Rd Rr base → p.prog.Zk base

/-- States: under the hypotheses below, the front stands behind c₀. -/
def front_okFrom : Prop :=
  ∀ (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (x y : FSt S E₀ Wp Kc) (p : Front x y) (Z A : Joint Kc)
      (c₀ : Chain Kc Z A) (c : Chain Kc A x.stage.J) (Rd : S.Ent → Prop) (Rr : S.O → Prop),
    c₀.Ok → c.OkFrom c₀ → p.prog.Hyp →
    p.ZkOK Rd Rr (fun g => (c₀.append c).FreshFor g.kc g.Mk g.put) → (p.prog.onto c).OkFrom c₀

/-- The budgets' halves. -/
def front_sides : Prop :=
  ∀ (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (x y : FSt S E₀ Wp Kc) (p : Front x y) (A : Joint Kc)
      (c : Chain Kc A x.stage.J) (qa : Finset A.E.Pos → Prop)
      (q : Finset (E₀.prod S.ext).Pos → Prop),
    c.SidesC qa q → p.prog.Hyp → p.Sd q → (p.prog.onto c).SidesC qa q

end
end Spec
end Cb
