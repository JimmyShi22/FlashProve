-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectLink.lean: the sub-protocol that tests that two encodings hold the same index: its
data over the configuration, and the statement that, under `Cf.OK L`, every reduction for it with
the properties `K.TailOK`, with a step without rounds in front of it, has the two lists that the
holographic IOP requires of this sub-protocol (`LinkListR`, `LinkKnowR`, Hiop/RecSubs.lean).

Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Obj/LdObjectLinkProofs.lean.

The link is the sub-protocol for the equality relation on two encoded indices (`ConfigurationWithOutOfDomainSample.Req`,
Hiop/RecConf.lean: they hold the same index); its relaxed relation (`ConfigurationWithOutOfDomainSample.ReqR`) says that the
index decoder gives the same result on both.
A joint (`IOR.Rels`; with its types, `IOR.Joint`) consists of, for one kind of statement and of
witness: the honest relation; a second relation, called relaxed, of which round-by-round knowledge
soundness speaks; the set of statements of which that soundness speaks; and a map from a witness to
its core.
`TailTr`, a tail of a chain, asks of a reduction from a joint to a joint whose statements have no
oracles the bundle `IOR.GoodT` and three further clauses, `noHid`, `tied` and `bears`, which
Cb/Ld/LdTowerKit.lean states (through `IOR.Tied`, Ior/Batch.lean, and `IOR.Bears`, Ior/Bears.lean).

Hiop/RecSubs.lean requires of a link over a configuration C with a record: an interactive oracle
reduction Q from ((rec, rec'), the two encoded indices) to the trivial statement, an honest side on
two prover encoded indices, knowledge soundness (`LinkKnowR`) and a list of further items
(`LinkListR`).
Cb/Ld/LdLink.lean has the first joint of the link (`j0`), in the terms of the index format, and one
chain from it. Cb/Obj/LdObjectTail.lean (`Spec.ldObj_link`) leads from any tail of a chain and
four bridging facts to the two lists. Here the three are joined, over C = `Cf.conf`
(Cb/Obj/LdObjectConf.lean).
The statements hold of any tail T from `j0` to the trivial statement (`K.Tail`: the data;
`K.TailOK`: it is a tail, within t₀ and t₁ positions).

Main names, definitions:
  `Cf.LinkPar`: the cube for φ, the two radii, the two numbers of locations, the family of oracle
    messages with its two named members and where the folded full messages are in them.
  `K.enter`: a step without rounds in front of the tail. The object reads two words of one alphabet
    (`Iop.twoExternalStrings`), the chain two oracles side by side (symbols tagged left or right).
  `K.link T`: the step, then the tail. `K.hLink T`: its honest side on two prover encoded indices:
    these (message, randomness, record) are first turned into the tables of the rows' full messages
    (`K.fi`).
Main names, statements:
  `Spec.ldOl_enter`, `Spec.ldOl_tail`: the step is a piece of a chain; the step, then any tail, is a
    tail.
  `Spec.ldOl_bridge`: the four bridging facts, from `Cf.OK L`:
    (a) the object's equality relation gives the exact relation of `j0` at `K.fi`;
    (b) the object's condition gives both conditions of `j0` (no collision at either record's seed);
    (c) on these statements the relaxed relation of `j0` gives the object's relaxed relation;
    (d) a set within the tail's bound has at most t₀ positions on the left and t₁ on the right.
  `Spec.ldOl_object`, `Spec.ldOl_chain`: the two main statements (hypotheses and conclusions: their
    doc comments).

Where the three laws of the configuration enter: an index decoder that answers excludes a collision;
an honest word is the table of the codewords of the rows' full messages, whose message part is the
message; agreement on the layout is "the same index" (`Cb.ldCf_held_same`).

Limits: no tail is given but that of `Spec.ldOl_chain`, whose closing is a parameter.
Honest-verifier zero knowledge is that of the verifier's view (budget of further reads: none). This
file says nothing on the value of any number.
Declared: the equality row reads the layout only (`K.P` takes `Cf.lay`). A write-up of ours
(lean/CREDITS.md) compares all entries of the message outside the pad, and asks for completeness
that the two prover encoded indices hold the same index and zeros outside layout and pad. The row
here is sound, complete without that law of the committer, and reads less (sound and complete:
`Spec.ldOl_object`, under `Cf.OK L` and `K.TailOK T`). The write-up's form is an instance,
without a new definition or proof (by reading of the definitions; no such instance with pads has
been compiled):
a configuration with Lay := J₀, lay := the identity
(Cb/Obj/LdObjectConf.lean: both are fields). There an honest message is "body i" at all of J₀ and
free on the pads alone, so two prover encoded indices of one index agree outside the pads by
definition: the committer's law is built in ("zeros" are whatever body i says there); `Cf.OK`'s
clause "heldB reads the layout only" and the clauses "a layout lands in Cf.lay" are then trivial;
its price in numbers: `K.pl` has to place all of J₀ on the cube for φ, so that cube has at least log
|J₀| variables, and φ's error l·q^(l-1) grows with it. All theorems here hold of every
configuration, so of that one (under their premises, `Cf.OK L` among them).

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Obj.LdObjectConf
import Cb.Ld.LdLink
import Cb.Obj.LdObjectTail
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood

/-- What the link needs beside the configuration. -/
structure LdCf.LinkPar {F E : Type} [Field F] [Field E] [Algebra F E] (Cf : LdCf F E) where
  l  : ℕ
  pl : Cf.Lay → Fin l → Bool
  e₀ : ℕ
  e₁ : ℕ
  t₀ : ℕ
  t₁ : ℕ
  N  : Sig E
  i₀ : N.O
  l₀ : Fin Cf.C₀.k → (N.om i₀).C.J
  i₁ : N.O
  l₁ : Fin Cf.C₀.k → (N.om i₁).C.J

namespace LdCf.LinkPar
variable {F E : Type} [Field F] [Field E] [Algebra F E] {Cf : LdCf F E} (K : Cf.LinkPar)

/-- The data of the chain. -/
def P : LdLkP E (Fin Cf.C₀.n) (Fin Cf.C₀.k) Cf.J Cf.Lay where
  D := ⟨Cf.X, fun a => .inl (Cf.lay a), K.l, K.pl⟩
  Sy := Cf.Sg
  up := fun s r => algebraMap F E (s r)
  e₀ := K.e₀
  e₁ := K.e₁
  t₀ := K.t₀
  t₁ := K.t₁
  N := K.N
  i₀ := K.i₀
  l₀ := K.l₀
  i₁ := K.i₁
  l₁ := K.l₁

/-- two words of one alphabet, as two oracles side by side -/
def two : ExtMap (twoExternalStrings Cf.C₀.n Cf.Sg) K.P.E0 where
  map y := y
  src q := {q}

/-- the table of the rows' full messages, over E -/
def tabW (w : (Cf.Msg × Cf.Rnd) × Cf.X.Rec) : K.P.IxW := fun r =>
  Code.liftWord E (Cf.full w.1.1 w.1.2 r)

/-- the condition of the chain on each index: no collision at the record's seed -/
def free : (K.P.D.X.Row → Fin Cf.C₀.n → E) → K.P.D.X.Rec → Prop := fun f rec =>
  ¬ K.P.D.X.Coll f rec.1

/-- The first joint of the link, read on two words of one alphabet. -/
def jIn : IOR.Rels Unit K.P.X0 (twoExternalStrings Cf.C₀.n Cf.Sg) K.P.W0 where
  rel  := fun x y w => (K.P.j0 K.free K.free).rel x y w
  relR := fun a w => (K.P.j0 K.free K.free).relR a w
  on   := fun a => (K.P.j0 K.free K.free).on a
  core := fun _ => ()

/-- The step in front of the tail. -/
def enter : IOR K.P.X0 (twoExternalStrings Cf.C₀.n Cf.Sg) K.P.X0 K.P.E0 := IOR.pure some K.two
def hEnter : K.enter.Honest K.P.W0 K.P.W0 := IOR.Honest.pure some K.two fun a => a

/-- Any tail from the first joint: the data. -/
structure Tail where
  Q   : IOR K.P.X0 K.P.E0 Unit extNone
  H   : Q.Honest K.P.W0 Unit
  ext : K.P.X0 × K.P.E0.Str → Tr Q.shape → Unit → K.P.W0
  N   : IOR.Nums Unit Q

def TailOK (T : K.Tail) : Prop :=
  IOR.TailTr T.Q T.H (K.P.j0 K.free K.free) trivRels T.ext T.N K.P.q0

variable (T : K.Tail)

def link0 : IOR K.P.X0 (twoExternalStrings Cf.C₀.n Cf.Sg) Unit extNone := K.enter.seq T.Q
def hLink0 : (K.link0 T).Honest K.P.W0 Unit := K.hEnter.seq T.H
def numsT : IOR.Nums Unit (K.link0 T) := (IOR.Nums.pure Unit some K.two).seq T.N
def extT (d : K.P.W0) :
    K.P.X0 × (twoExternalStrings Cf.C₀.n Cf.Sg).Str → Tr (K.link0 T).shape → Unit → K.P.W0 :=
  IOR.extSeq K.enter T.Q (fun _ _ w => w) T.ext d

variable [Fintype F]

/-- from two prover encoded indices to the two tables -/
def fi (w : Cf.conf.PIdx × Cf.conf.PIdx) : K.P.W0 := (K.tabW w.1, K.tabW w.2)

/-- The link over the configuration, its honest side, its numbers. -/
def link : IOR (Cf.conf.Rec × Cf.conf.Rec) (twoExternalStrings Cf.conf.n Cf.conf.Sg) Unit extNone :=
  K.link0 T
def hLink : (K.link T).Honest (Cf.conf.PIdx × Cf.conf.PIdx) Unit :=
  IOR.Honest.mapW (K.hLink0 T) K.fi fun _ u => u
def nums : LinkNums (K.link T).shape :=
  ⟨(K.numsT T).err, (K.numsT T).pBad, K.t₀, K.t₁, fun _ T' => T' = ∅⟩

variable [Fintype E] [Nonempty (Fin Cf.C₀.n)]

/-- the chain of Cb/Ld/LdLink.lean with a closing, as a tail -/
def ofChain (S : K.P.Snd) (Z : K.P.Closing)
    (ε₀ ε₁ : ℕ) (d : K.P.W0 × K.P.W1 × K.P.W2) : K.Tail :=
  ⟨K.P.link S Z, K.P.hLink S Z, K.P.extLink S Z d, K.P.numsLink S Z ε₀ ε₁⟩

end LdCf.LinkPar

namespace Spec
open IOR
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def ldOl_enter : Prop :=
  ∀ (Cf : LdCf F E) (K : Cf.LinkPar),
    PieceTr K.enter K.hEnter K.jIn (K.P.j0 K.free K.free) (fun _ _ w => w)
      (Nums.pure Unit some K.two) K.P.q0 K.P.q0

def ldOl_tail : Prop :=
  ∀ (Cf : LdCf F E) (K : Cf.LinkPar) (T : K.Tail) (d : K.P.W0),
    K.TailOK T → TailTr (K.link0 T) (K.hLink0 T) K.jIn trivRels (K.extT T d) (K.numsT T) K.P.q0

open Classical in
/-- The four bridging facts, from `Cf.OK L`. -/
def ldOl_bridge : Prop :=
  ∀ (Cf : LdCf F E) (K : Cf.LinkPar) (L : ℕ), Cf.OK L →
    (∀ x y w, Cf.conf.Req x y w → K.jIn.rel x y (K.fi w)) ∧
    (∀ a, Cf.conf.onEq a → K.jIn.on a) ∧
    (∀ a w, Cf.conf.onEq a → K.jIn.relR a w → Cf.conf.ReqR a ()) ∧
    ∀ U : Finset (twoExternalStrings Cf.conf.n Cf.conf.Sg).Pos, K.P.q0 U →
      (U.filter fun p => p.isLeft).card ≤ K.t₀ ∧ (U.filter fun p => p.isRight).card ≤ K.t₁

/-- Every tail from the first joint is a link of the object: under `Cf.OK L` and `K.TailOK T`,
`K.link T` (the step, then the tail T) has `LinkListR` and `LinkKnowR`. -/
def ldOl_object : Prop :=
  ∀ (Cf : LdCf F E) (K : Cf.LinkPar) (T : K.Tail) (L : ℕ), Cf.OK L → K.TailOK T →
    LinkListR (C := Cf.conf) (K.link T) (K.hLink T) (K.nums T) ∧
    LinkKnowR (C := Cf.conf) (K.link T) (K.nums T).err

/-- The chain of Cb/Ld/LdLink.lean, with a closing that is a tail by itself: `LinkListR` and
`LinkKnowR`, under the hypotheses below. -/
def ldOl_chain : Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (K : Cf.LinkPar) (S : K.P.Snd) (Z : K.P.Closing)
      (L ε₀ ε₁ : ℕ) (d : K.P.W0 × K.P.W1 × K.P.W2),
    Cf.OK L → K.P.FoldErr K.free K.free ε₀ ε₁ → Function.Injective K.pl → S.OK →
    TailTr Z.T Z.H K.P.j4.cf trivRels Z.ext Z.N (K.P.q3 S) →
    LinkListR (C := Cf.conf) (K.link (K.ofChain S Z ε₀ ε₁ d))
      (K.hLink (K.ofChain S Z ε₀ ε₁ d)) (K.nums (K.ofChain S Z ε₀ ε₁ d)) ∧
    LinkKnowR (C := Cf.conf) (K.link (K.ofChain S Z ε₀ ε₁ d)) (K.nums (K.ofChain S Z ε₀ ε₁ d)).err

end
end Spec
end Cb
