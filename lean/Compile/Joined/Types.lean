-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Joined/Types.lean: what a file with three joined hash chains is to the compiler: the types
of its typed description. Definitions, and the first laws of the cuts.

A twin beside the library's construction: a form of the compiler's verifier side, beside the
library's own. It is made for a key file's and a proof file's three hash chains,
joined by seals; that it writes what is hashed as the prover's files have it is not shown in this
folder.

A key file and a proof file each hold three chains of rounds. The chains are not independent: the
first ends in a seal, the seal goes into a leaf of a binding tree, the root of that tree starts the
second chain, and the third chain starts from both seals; a later chain may open a tree whose root
an earlier chain sent. Here the three chains are ONE batch protocol of the library (Iop/Batch.lean),
so that one compiled verifier and one soundness theorem speak of the whole file:

  the front round | chain 1 | the joining round | chain 2 | the seam | chain 3
  local           | local   | shared (it joins) | shared  | local    | local

How the compiled verifier's queries (the head of Compile/Batch/Oracles.lean) fall on the chains:
  front: (F1), chain 1's first call. Chain 1's rounds: (F2).
  The joining round: (G), whose answer is the slot's value: SEAL 1. The slot's value, with the
    slot's salt, is a leaf of the request tree, the binding tree; its root is the binding root. Then
    (F4), which holds the binding root: chain 2's first call.
  Chain 2's rounds: (F5). The chaining value behind its last round is SEAL 2.
  The seam: (F3), which holds SEAL 2 and the slot's value: chain 3's first call.
  Chain 3's rounds: (F2).
What a chain's first call holds beyond these fields rides in the plain part of its round: the
answers of the record over the three chains and the run's value of chain 2 in the joining round's,
the run's value of chain 3 in the seam's (`JoinMsg`, `plainRound`). The front is any round too: what
chain 1's first call holds beyond (F1)'s own fields (the record's answers; in a proof file the
number of the stored copy) rides in its plain part, which stands in (F1), before any verifier
message. `JoinMsg` is one form of a plain part, no law. A run's value is a hash value that the
programs compute (chain 2's from the binding root, chain 3's from 32 random bytes of its own). Here
it is free data of the prover that is hashed: nothing typed ties it to what it is computed from. The
seeds of the record, a further hash value, stand in no round and have no type here: what fixes them,
and when, is for the statement that uses these types to say.

A tree that a later chain takes over needs no field: all three chains' oracles are oracles of the
one protocol, so its verifier may read a position of chain 1's oracle on behalf of chain 3, and may
read one tree for two lists of positions (`Desc.reads` is one finite set). `TreeRef` names a tree by
the round that sent it.

Main names:
  `Chains`             the rounds `rF`, `s₁`, `rJ`, `s₂`, `r3`, `s₃`; the joining round's annotation
  `Chains.sh`, `.ann`   the shape and the annotation of the whole; `.nJ`, `.n3`: the numbers of the
                       joining round and of the seam in it
  `Chains.c₁` ... `c₃`, `A₁` ... `A₃`, `sh_eq`, `ann_eq`   each chain with its first round: the
                       whole is c₁ ++ (c₂ ++ c₃), by unfolding
  `Chains.tr₁` ... `tr₃`, `msgF`, `msgJ`, `msg3`   the parts of a transcript; `rho₁` ..., `pl₁` ...
  `Chains.i₁` ... `i₃`, `iF`, `iJ`, `i3'`            a part's position as a position of the whole
  `Desc`, `Desc.proto`, `Desc.batch`                 the verifier of a file, and its batch protocol
  `Desc.Answers`       the decision compares the record's answers, said in two first calls, with the
                       instance's
  `TreeRef`, `Chains.chainOf`                        a tree by its sender's round; a round's chain
  `plainRound`, `JoinMsg`, `IsSeam`, `Chains.Seams`   rounds that send a plain part alone

Limits: definitions only; nothing on soundness. The wire records, and the list of a file's trees,
are in OnBytes/TypedOracleCompiler/Joined/Wire.lean. Nothing here says that a file's bytes are such a protocol.
`Chains` holds rounds and shapes as data, and a round holds, as data, that its verifier messages are
finitely many: a function with such a parameter is fit for a theorem's statement; that it can be
evaluated at the size of a real file is not claimed.
"With the slot's salt" (above, at the joining round) is so at the twin's verifier alone
(`reqCheck`, OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean: the slot's value with the string `rsalt`
behind it); the library's own `reqCheck` (Compile/Batch/Verifier.lean) hashes the bare slot value,
and its proof string has no such field.

Terms: lean/GLOSSARY.md.

-/
import Iop.ShapeKit
import Iop.Batch

set_option autoImplicit false

namespace Compile.Joined
open Iop

/-! ## Rounds that send a plain part alone -/

/-- The round that sends a plain part in T and nothing else, and has one verifier message. t is the
fixed message of the right format that every round has to name. -/
@[reducible] def plainRound (T : Type) (t : T) : Round where
  Orc := Unit
  Pos := Empty
  Sym := fun _ => Unit
  rd := fun _ p => p.elim
  Plain := T
  Chal := Unit
  dOrc := ()
  dPlain := t

/-- What the joining round sends in the clear: the answers of the one record over the three chains,
and the run's value of chain 2. Both are free data of the prover. -/
structure JoinMsg (Ans Run : Type) where
  answers : Ans
  run : Run

/-- A round that sends a plain part alone: its oracle part has one value and no position, and it has
one verifier message. -/
structure IsSeam (r : Round) : Prop where
  noOrc : Subsingleton r.Orc
  noPos : IsEmpty r.Pos
  one : Subsingleton r.Chal

theorem plainRound_isSeam (T : Type) (t : T) : IsSeam (plainRound T t) where
  noOrc := inferInstanceAs (Subsingleton Unit)
  noPos := inferInstanceAs (IsEmpty Empty)
  one := inferInstanceAs (Subsingleton Unit)

/-! ## The rounds of a file -/

/-- The rounds of a file with three joined chains. -/
structure Chains where
  /-- the front round: chain 1's first call -/
  rF : Round
  /-- the rounds of chain 1 behind its first call, without its last, the seal -/
  s₁ : Shape
  /-- the joining round: SEAL 1, the binding tree, and chain 2's first call -/
  rJ : Round
  /-- the rounds of chain 2 behind its first call. The last of them is SEAL 2's: a round of its own,
  unlike chain 1's seal, whose call is the joining round's query (G). The chaining value behind it
  is SEAL 2. (In the programs: the round named SEAL with which the shared chain's block closes:
  `sharedBlock`, OnBytes/Proof/Tail.lean.) -/
  s₂ : Shape
  /-- the seam: chain 3's first call -/
  r3 : Round
  /-- the rounds of chain 3 behind its first call -/
  s₃ : Shape
  /-- the joining round's annotation -/
  aJ : RAnn rJ

/-- The laws of the joining round's annotation: it is a shared round (else the first round of chain
2 would become the joining round), and its data fit together. -/
structure Chains.Laws (G : Chains) : Prop where
  kindJ : G.aJ.kind = Kind.sh
  cohJ : G.aJ.Coherent

/-- The front, the joining round and the seam send a plain part alone. (No definition here needs it.
In the byte format only the chaining value of the answers to their queries is a hash call's
value.) -/
structure Chains.Seams (G : Chains) : Prop where
  seamF : IsSeam G.rF
  seamJ : IsSeam G.rJ
  seam3 : IsSeam G.r3

namespace Chains
variable (G : Chains)

/-- the seam and chain 3 -/
abbrev sh₃ : Shape := G.r3 :: G.s₃
/-- the joining round, chain 2, and what follows -/
abbrev shJ : Shape := G.rJ :: (G.s₂ ++ G.sh₃)
/-- The shape of the whole: front, chain 1, joining round, chain 2, seam, chain 3. -/
abbrev sh : Shape := G.rF :: (G.s₁ ++ G.shJ)

/-- the number of the joining round in the whole (the front has the number 0) -/
def nJ : ℕ := G.s₁.length + 1
/-- the number of the seam in the whole -/
def n3 : ℕ := G.s₁.length + G.s₂.length + 2
/-- the chain of round number i of the whole, each chain with its first round: 0, 1 or 2; none
beyond the last round -/
def chainOf (i : ℕ) : Option (Fin 3) :=
  if i < G.nJ then some 0 else if i < G.n3 then some 1 else if i < G.sh.length then some 2 else none

/-- the seam and chain 3 are local -/
def ann₃ : RoundSplits G.sh₃ := RoundSplits.allLocal G.sh₃
/-- the joining round; chain 2 is shared: only the shared part is sent -/
def annJ : RoundSplits G.shJ := (G.aJ, RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) G.s₂) G.ann₃)
/-- The annotation of the whole: the front and chain 1 are local. -/
def ann : RoundSplits G.sh := (RAnn.allLocal G.rF, RoundSplits.app (RoundSplits.allLocal G.s₁) G.annJ)

/-- chain 1 with its first round, the front -/
abbrev c₁ : Shape := G.rF :: G.s₁
/-- chain 2 with its first round, the joining round -/
abbrev c₂ : Shape := G.rJ :: G.s₂
/-- chain 3 with its first round, the seam -/
abbrev c₃ : Shape := G.r3 :: G.s₃
/-- chain 1 is local -/
def A₁ : RoundSplits G.c₁ := RoundSplits.allLocal G.c₁
/-- the joining round, and chain 2's shared rounds -/
def A₂ : RoundSplits G.c₂ := (G.aJ, RoundSplits.const (RAnn.ofShared .sh) G.s₂)
/-- chain 3 is local -/
def A₃ : RoundSplits G.c₃ := RoundSplits.allLocal G.c₃

/-- the whole is the three chains in a row, by unfolding -/
theorem sh_eq : G.sh = G.c₁ ++ (G.c₂ ++ G.c₃) := rfl
theorem ann_eq : G.ann = RoundSplits.app G.A₁ (RoundSplits.app G.A₂ G.A₃) := rfl

/-! ### The parts of a transcript -/

/-- the front's prover message -/
def msgF (τ : Tr G.sh) : G.rF.Msg := τ.1
/-- chain 1's part of a transcript -/
def tr₁ (τ : Tr G.sh) : Tr G.s₁ := Tr.fst τ.2.2
/-- from the joining round on -/
def trJ (τ : Tr G.sh) : Tr G.shJ := Tr.snd (s := G.s₁) τ.2.2
/-- the joining round's prover message -/
def msgJ (τ : Tr G.sh) : G.rJ.Msg := (G.trJ τ).1
/-- chain 2's part -/
def tr₂ (τ : Tr G.sh) : Tr G.s₂ := Tr.fst (G.trJ τ).2.2
/-- the seam's prover message -/
def msg3 (τ : Tr G.sh) : G.r3.Msg := (Tr.snd (s := G.s₂) (G.trJ τ).2.2).1
/-- chain 3's part -/
def tr₃ (τ : Tr G.sh) : Tr G.s₃ := (Tr.snd (s := G.s₂) (G.trJ τ).2.2).2.2

/-- the verifier messages of chain 1 -/
def rho₁ (ρ : Rho G.sh) : Rho G.s₁ := Rho.fst ρ.2
/-- from the joining round on -/
def rhoJ (ρ : Rho G.sh) : Rho G.shJ := Rho.snd (s := G.s₁) ρ.2
/-- the verifier messages of chain 2 -/
def rho₂ (ρ : Rho G.sh) : Rho G.s₂ := Rho.fst (G.rhoJ ρ).2
/-- the verifier messages of chain 3 -/
def rho₃ (ρ : Rho G.sh) : Rho G.s₃ := (Rho.snd (s := G.s₂) (G.rhoJ ρ).2).2

/-- the front's plain part -/
def plF (π : Plains G.sh) : G.rF.Plain := π.1
/-- the plain parts of chain 1 -/
def pl₁ (π : Plains G.sh) : Plains G.s₁ := Plains.fst π.2
/-- from the joining round on -/
def plJ' (π : Plains G.sh) : Plains G.shJ := Plains.snd (s := G.s₁) π.2
/-- the joining round's plain part -/
def plJ (π : Plains G.sh) : G.rJ.Plain := (G.plJ' π).1
/-- the plain parts of chain 2 -/
def pl₂ (π : Plains G.sh) : Plains G.s₂ := Plains.fst (G.plJ' π).2
/-- the seam's plain part -/
def pl3 (π : Plains G.sh) : G.r3.Plain := (Plains.snd (s := G.s₂) (G.plJ' π).2).1
/-- the plain parts of chain 3 -/
def pl₃ (π : Plains G.sh) : Plains G.s₃ := (Plains.snd (s := G.s₂) (G.plJ' π).2).2

theorem rho_tr₁ (τ : Tr G.sh) : (G.tr₁ τ).rho = G.rho₁ τ.rho := Tr.rho_fst τ.2.2
theorem rho_trJ (τ : Tr G.sh) : (G.trJ τ).rho = G.rhoJ τ.rho := Tr.rho_snd τ.2.2
theorem rho_tr₂ (τ : Tr G.sh) : (G.tr₂ τ).rho = G.rho₂ τ.rho := by
  unfold tr₂ rho₂
  rw [Tr.rho_fst, ← G.rho_trJ]
  rfl
theorem rho_tr₃ (τ : Tr G.sh) : (G.tr₃ τ).rho = G.rho₃ τ.rho := by
  unfold tr₃ rho₃
  rw [← G.rho_trJ]
  exact congrArg Prod.snd (Tr.rho_snd (s := G.s₂) (G.trJ τ).2.2)

/-! ### A part's position as a position of the whole -/

/-- a position of the front's oracle -/
def iF (p : G.rF.Pos) : OPos G.sh := .inl p
/-- a position of chain 1's oracles -/
def i₁ (p : OPos G.s₁) : OPos G.sh := .inr (OPos.left p)
/-- a position from the joining round on -/
def iJ' (p : OPos G.shJ) : OPos G.sh := .inr (OPos.right (s := G.s₁) p)
/-- a position of the joining round's oracle -/
def iJ (p : G.rJ.Pos) : OPos G.sh := G.iJ' (.inl p)
/-- a position of chain 2's oracles -/
def i₂ (p : OPos G.s₂) : OPos G.sh := G.iJ' (.inr (OPos.left p))
/-- a position of the seam's oracle -/
def i3' (p : G.r3.Pos) : OPos G.sh := G.iJ' (.inr (OPos.right (s := G.s₂) (.inl p)))
/-- a position of chain 3's oracles -/
def i₃ (p : OPos G.s₃) : OPos G.sh := G.iJ' (.inr (OPos.right (s := G.s₂) (.inr p)))

end Chains

/-! ## The verifier of a file -/

/-- The verifier of a file, over the rounds G: instances in X, the external strings E (a stored
table). It sees the whole: what it reads for one chain may lie in an oracle that another chain
sent. -/
structure Desc (G : Chains) (X : Type) (E : ExtSpec) where
  /-- is the oracle at this position hashed with a salt -/
  blinded : OPos G.sh → Bool
  /-- the positions of the external strings that are read -/
  extReads : X → Rho G.sh → Finset E.Pos
  /-- the positions of the prover's oracles that are read, for all three chains together -/
  reads : X → Rho G.sh → Plains G.sh → Finset (OPos G.sh)
  /-- the decision -/
  accept : X → E.Str → Tr G.sh → Bool

/-- the file's protocol -/
@[reducible] def Desc.proto {G : Chains} {X : Type} {E : ExtSpec} (D : Desc G X E) : InteractiveOracleProof X E where
  shape := G.sh
  blinded := D.blinded
  extReads := D.extReads
  reads := D.reads
  accept := D.accept

/-- The file's batch protocol: what the compiler takes. -/
@[reducible] def Desc.batch {G : Chains} {X : Type} {E : ExtSpec} (D : Desc G X E) :
    BatchInteractiveOracleProof X E := ⟨D.proto, G.ann⟩

/-- The decision holds the prover to the record's answers. `ans x`: the answers as the instance has
them; `atF`, `atJ`: where they stand in the plain parts of the front and of the joining round, which
chain 1's and chain 2's first calls hold. Wherever the decision says yes, both are the instance's. A
property of a description: nothing here shows it of any. In a description that never looks at these
two plain parts (a silent round: CompileK/Joined/Silent.lean) the verifier's yes does not depend on
what stands there: so it need not have this property, and it takes the answers from the instance
alone. -/
structure Desc.Answers {G : Chains} {X : Type} {E : ExtSpec} {A : Type} (D : Desc G X E)
    (ans : X → A) (atF : G.rF.Plain → A) (atJ : G.rJ.Plain → A) : Prop where
  front : ∀ x y τ, D.accept x y τ = true → atF (G.msgF τ).2 = ans x
  join : ∀ x y τ, D.accept x y τ = true → atJ (G.msgJ τ).2 = ans x

/-! ## Trees, named by the round that sent them -/

/-- A tree of a file: the number in the whole of the round that sent its root, whether it lies over
the slot's component of that round or over the shared one, and its number among the trees of that
component, in the order of their roots. -/
structure TreeRef where
  round : ℕ
  own : Bool
  tree : ℕ
  deriving DecidableEq

end Compile.Joined
