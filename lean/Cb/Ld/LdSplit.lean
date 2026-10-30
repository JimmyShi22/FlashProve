-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSplit.lean: a sub-protocol with one prover message, before the proximity tests: a linear
claim on the messages of two groups of oracles is turned into one linear claim on each group, by one
mask entry that both groups hold.

Definitions and statements (each a `Prop` in `Cb.Spec`); the proofs are in Cb/Ld/LdSplitProofs.lean.
The file uses Cb/Ld/LdSig.lean (oracle messages, signatures, the joint `S.over A`),
Cb/Ld/LdBatSig.lean (groups, `claimRels`) and Ior/Masked.lean (the bundle of a block whose masks
were sent in advance).

Why: a proximity test closes one group, and takes in rows on the message of that group alone. A row
that reads the messages of two groups must first become two rows. The value of the first part must
not be shown: it is a linear functional of hidden messages.

The protocol. The claim: (a₁ at the message of G₁) + (a₂ at the message of G₂) = τ (in Lean: a₁, a₂
are `sl₁`, `sl₂` at their states; τ' is the value said). κ is one entry of an oracle message o° that
is a member of both groups, sent (and sampled) earlier, and read by nothing else.
  One round: the prover sends one scalar τ' in the clear; the verifier sends nothing. No query; the
  verifier never rejects.
  The new claims: (a₁ at the message of G₁) + κ = τ', a row on G₁;
    (a₂ at the message of G₂) - κ = τ - τ', a row on G₂.
  The honest prover sends τ' := (a₁ at the message of G₁) + κ. It has no coins.

Main names:
  `sayRound`, `ldSay`: the simplest piece with a prover message: the prover says a value in the
    clear, the explicit part changes with it, oracles and witness stay. `Spec.ldSpl_say`: what makes
    it lead from a joint to a joint (all of the bundle but zero knowledge), with the error 0.
  `SplitAt G₁ G₂`: where κ stands.
  `Rd`, `S.cut Rd m`: the entries that the block reads (a parameter: a set of entries that holds κ
    and outside which a₁ and a₂ vanish), and the messages with all other entries set to 0: what the
    item "masked messages" reads of a witness. So a pad of o°, or any entry that a sample's answer
    has told something about, can be kept out of view.
  `Spec.ldSpl_sum`: for every τ', both new claims hold of m only if the old claim does; and with the
    honest τ' the old claim gives both.
  `Spec.ldSpl_good`: under the hypotheses of its statement, the block is `IOR.GoodM`: from S.over
    (the row on two groups, beside any base joint A₀) to S.over (the two rows, beside A₀), both
    relaxed by decoding with a sample:
      strings (`point`), local (`isLocal`), perfectly complete, nothing withheld;
      knowledge sound, on the statements with the joint's condition, with the identity as extractor
      and the error 0;
      and the item "masked messages": if neither a₁ nor a₂ ever reads κ, then the claim does not
      read κ, and for all messages for which the claim holds, all else fixed, over a uniform κ the
      scalar τ' is uniform: the simulator draws it, and reads nothing.
    `GoodM` is `GoodB` (`GoodT` without the clause `exact`) with `H.MM D`, and the clause that every
    (x, y, w) in the honest relation meets `D.Cl (D.pub x) (D.kc w)`. Here `GoodM` is the conclusion
    of `Spec.ldSpl_good`.
    `H.MM D` asks five things: the block sends no oracle; `H.withheld w x` is always empty; the
      honest prover's plain parts are `D.msg` at `D.kc w`, `D.pub x` and ρ; `D.Cl` is kept under
      `D.put`; and where `D.Cl xp k` holds, `D.msg (D.put M k) xp ρ` over uniform M has the
      distribution `D.sim xp ρ`. Here `H.MM D` is a clause of that conclusion.

Why not `IOR.GoodT`: κ stands in the input witness and the prover has no coins, so τ' is a function
of the witness, and our exact zero knowledge (for every witness, over the block's own coins)
fails: header of Ior/Masked.lean. [In words; no statement here.]
Why the error is 0: both sides are relaxed by decoding with a sample: the messages, κ among them,
are a function of words and samples, which are fixed before τ' is sent. The prover's τ' moves a
quantity from one row to the other and cannot change their sum. In the tests that follow, that both
groups speak of one κ is the work of the bridge (Cb/Ld/LdBatSig.lean): each test takes in the sample
rows of o°.

Notation: `S`: a signature (`Sig`, Cb/Ld/LdSig.lean); `G₁`, `G₂`: groups of `S` (`Grp`,
Cb/Ld/LdBatSig.lean); `k`: a `SplitAt G₁ G₂`; `St₁`, `St₂`: the types of the states of `sl₁`, `sl₂`;
`St₀`, `E₀`, `Wp`, `Kc`: the types of A₀: explicit part, external oracles, further witness, core; in
`Spec.ldSpl_say`: `Pl`: the type of the value said; `d`: a value of `Pl`, an argument of `sayRound`;
`nx`: the new explicit part, from the old one and the value said; `val`: the value said, from
witness and explicit part.

Limits:
Declared differences to a write-up of ours (lean/CREDITS.md).
 (a) A write-up of ours asks that o° hold masks only, with a sample and a pad of its own: a
     group holds whole oracle messages under one base code, so a message with main rows cannot be a
     member of a second group. Here a group is any family of whole oracle messages
     (Cb/Ld/LdBatSig.lean (a)), so "member of both groups" is all that is asked; main rows and mask
     rows are not told apart by type.
 (b) "Read by nothing else" is here: a₁ and a₂ never read κ. That no other block reads κ, that all
     splits of a closing step come before its tests, that the encoding of o° bears the queries of
     both tests: conditions of the lemma on whole chains, not of this block.
This file says nothing on zero knowledge of a chain that holds this block. It says nothing on
running times.

The block follows this protocol's technical report (lean/CREDITS.md).

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdBatSig
import Ior.Masked
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood

/-! ## 1. The prover says a value -/

/-- the one round: a plain part, an empty verifier message -/
abbrev sayRound (Pl : Type) (d : Pl) : Round := Blocks.plainRound Pl Unit d

/-- the value said -/
def said {Pl : Type} {d : Pl} (τ : Tr [sayRound Pl d]) : Pl :=
  (show (Unit × Pl) × Unit × Unit from τ).1.2

section
variable {K X X' W Pl : Type} (d : Pl) (nx : X → Pl → X') (Ex : ExtSpec)

/-- The prover says a; the explicit part becomes nx x a. -/
def ldSay : IOR X Ex X' Ex where
  shape := [sayRound Pl d]
  blinded _ := true
  extReads _ := ∅
  reads _ := ∅
  out x _ τ := some (nx x (said τ))
  imp y _ := y
  srcE _ q := {q}
  srcO _ _ := ∅
  tie _ _ := ∅

/-- Its honest side: the value is a function of witness and explicit part; no coins; nothing is
withheld; the witness stays. -/
def ldSayH (val : W → X → Pl) : (ldSay d nx Ex).Honest W W where
  Coin := Unit
  strat w x _ := ((((), val w x), fun _ => (nx x (val w x), w)) : Strat [sayRound Pl d] (X' × W))
  Bad := ∅
  Hid _ _ := ∅

/-- Its numbers: the error 0; nothing is withheld; every budget. -/
def ldSayN (K : Type) : IOR.Nums K (ldSay d nx Ex) :=
  ⟨((0, ()) : ℕ × Unit), 0, 0, fun _ _ => True, fun _ => ∅⟩

end

/-! ## 2. The split -/

/-- the form sl with c added to its coefficient at the entry κ -/
def Slf.addAt {E St J : Type} [Add E] [Zero E] [DecidableEq J] (sl : Slf E St J) (c : E) (κ : J) :
    Slf E St J :=
  fun st j => sl st j + if j = κ then c else 0

/-- an entry of the message of a group, as an entry of the messages of the signature -/
def Grp.ent {E : Type} {S : Sig E} (G : Grp S) (n : G.C.J) : S.Ent := ⟨n.1.1, n.2⟩

/-- the messages with all entries outside Rd set to 0 -/
def Sig.cut {E : Type} [Zero E] (S : Sig E) (Rd : S.Ent → Prop) [DecidablePred Rd] (m : S.Msg) :
    S.Msg :=
  fun a j => if Rd ⟨a, j⟩ then m a j else 0

/-- Where the mask entry stands: an entry of an oracle message that is a member of both groups. -/
structure SplitAt {E : Type} {S : Sig E} (G₁ G₂ : Grp S) where
  o  : S.O
  h₁ : G₁.mem o
  h₂ : G₂.mem o
  j  : (S.om o).C.J

namespace SplitAt
variable {E : Type} {S : Sig E} {G₁ G₂ : Grp S} (k : SplitAt G₁ G₂)

/-- the entry, in the message of the first group and in that of the second -/
def e₁ : G₁.C.J := ⟨⟨k.o, k.h₁⟩, k.j⟩
def e₂ : G₂.C.J := ⟨⟨k.o, k.h₂⟩, k.j⟩
/-- its value -/
def val (m : S.Msg) : E := m k.o k.j
/-- the messages with the entry overwritten -/
def put (u : E) (m : S.Msg) : S.Msg := Function.update m k.o (Function.update (m k.o) k.j u)

end SplitAt

section
variable {E : Type} [Field E] [Fintype E] {S : Sig E} {G₁ G₂ : Grp S} {St₁ St₂ : Type}

/-- The row on two groups: x = (target, (state of the first part, state of the second)). -/
def splitIn (sl₁ : Slf E St₁ G₁.C.J) (sl₂ : Slf E St₂ G₂.C.J) : E × (St₁ × St₂) → S.Msg → Prop :=
  fun x m => sl₁.val x.2.1 (G₁.msg m) + sl₂.val x.2.2 (G₂.msg m) = x.1

/-- The two rows: x = ((target, state), (target, state)). -/
def splitOut (k : SplitAt G₁ G₂) (sl₁ : Slf E St₁ G₁.C.J) (sl₂ : Slf E St₂ G₂.C.J) :
    (E × St₁) × (E × St₂) → S.Msg → Prop :=
  fun x m => (sl₁.addAt 1 k.e₁).Holds x.1 (G₁.msg m) ∧ (sl₂.addAt (-1) k.e₂).Holds x.2 (G₂.msg m)

/-- the new explicit part -/
def splitNx (S : Sig E) (St₁ St₂ St₀ : Type) :
    ((E × (St₁ × St₂)) × St₀) × S.Smp → E → (((E × St₁) × (E × St₂)) × St₀) × S.Smp :=
  fun x t => ((((t, x.1.1.2.1), (x.1.1.1 - t, x.1.1.2.2)), x.1.2), x.2)

/-- what the honest prover says: the first part's value, masked -/
def splitVal (k : SplitAt G₁ G₂) (sl₁ : Slf E St₁ G₁.C.J) (m : S.Msg) (st : St₁) : E :=
  sl₁.val st (G₁.msg m) + k.val m

/-- The split. -/
abbrev ldSplitR (S : Sig E) (St₁ St₂ St₀ : Type) (E₀ : ExtSpec) :
    IOR (((E × (St₁ × St₂)) × St₀) × S.Smp) (E₀.prod S.ext)
      ((((E × St₁) × (E × St₂)) × St₀) × S.Smp) (E₀.prod S.ext) :=
  ldSay (0 : E) (splitNx S St₁ St₂ St₀) (E₀.prod S.ext)

abbrev ldSplitH (k : SplitAt G₁ G₂) (sl₁ : Slf E St₁ G₁.C.J) (St₂ St₀ Wp : Type) (E₀ : ExtSpec) :
    (ldSplitR S St₁ St₂ St₀ E₀).Honest (S.Wit × Wp) (S.Wit × Wp) :=
  ldSayH (0 : E) (splitNx S St₁ St₂ St₀) (E₀.prod S.ext) fun w x =>
    splitVal k sl₁ (S.msgs w.1) x.1.1.2.1

abbrev ldSplitN (S : Sig E) (St₁ St₂ St₀ : Type) (E₀ : ExtSpec) (Kc : Type) :
    IOR.Nums Kc (ldSplitR S St₁ St₂ St₀ E₀) :=
  ldSayN (0 : E) (splitNx S St₁ St₂ St₀) (E₀.prod S.ext) Kc

/-- The letters of the item "masked messages": of a witness the entries in Rd are read (all others
are set to 0; no encoding randomness); of the explicit part the claim (no sample); the own mask is
κ; the simulator draws the scalar. -/
def ldSplitD (k : SplitAt G₁ G₂) (sl₁ : Slf E St₁ G₁.C.J) (sl₂ : Slf E St₂ G₂.C.J)
    (Rd : S.Ent → Prop) [DecidablePred Rd] (St₀ Wp : Type) (E₀ : ExtSpec) :
    IOR.MaskData (ldSplitR S St₁ St₂ St₀ E₀) (S.Wit × Wp) where
  Kc  := S.Msg
  kc  := fun w => S.cut Rd (S.msgs w.1)
  Xp  := E × (St₁ × St₂)
  pub := fun x => x.1.1
  Mk  := E
  put := k.put
  Cl  := splitIn sl₁ sl₂
  msg := fun m xp _ => ((splitVal k sl₁ m xp.2.1, ()) : E × Unit)
  sim := fun _ _ => (unif E).map fun u => ((u, ()) : E × Unit)

end

/-! ## The statements -/

namespace Spec
open IOR

/-- Saying a value leads from A to B (`GoodB`), with the error 0, if: with the honest value the
relation goes forward; the condition is handed on, whatever is said; the cores agree; backward,
whatever is said, on the statements with the condition a witness of the new statement is one of the
old (relaxed relations). -/
def ldSpl_say : Prop :=
  ∀ (K X X' W Pl : Type) (d : Pl) (nx : X → Pl → X') (Ex : ExtSpec) (val : W → X → Pl)
      (A : Rels K X Ex W) (B : Rels K X' Ex W),
    (∀ x y w, A.rel x y w → B.rel (nx x (val w x)) y w) →
    (∀ x y a, A.on (x, y) → B.on (nx x a, y)) → (∀ w, B.core w = A.core w) →
    (∀ x y a w, A.on (x, y) → B.relR (nx x a, y) w → A.relR (x, y) w) →
    GoodB (ldSay d nx Ex) (ldSayH d nx Ex val) A B (fun _ _ w => w) (ldSayN d nx Ex K)

/-- The two rows sum to the old one. -/
def ldSpl_sum : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (G₁ G₂ : Grp S) (k : SplitAt G₁ G₂)
      (St₁ St₂ : Type) (sl₁ : Slf E St₁ G₁.C.J) (sl₂ : Slf E St₂ G₂.C.J) (τ : E) (st₁ : St₁)
      (st₂ : St₂) (m : S.Msg),
    (∀ t, splitOut k sl₁ sl₂ ((t, st₁), (τ - t, st₂)) m → splitIn sl₁ sl₂ (τ, (st₁, st₂)) m) ∧
    (splitIn sl₁ sl₂ (τ, (st₁, st₂)) m →
      splitOut k sl₁ sl₂ ((splitVal k sl₁ m st₁, st₁), (τ - splitVal k sl₁ m st₁, st₂)) m)

/-- Under the hypotheses below: the split is a masked block, from the row on two groups to a row on
each; relaxation by decoding with a sample on both sides; the identity extracts, on the statements
with the joint's condition; the error is 0; for all messages for which the claim holds, over a
uniform κ the scalar sent is uniform. -/
def ldSpl_good : Prop :=
  ∀ (E Kc St₀ Wp : Type) [Field E] [Fintype E] (S : Sig E) (G₁ G₂ : Grp S) (k : SplitAt G₁ G₂)
      (St₁ St₂ : Type) (sl₁ : Slf E St₁ G₁.C.J) (sl₂ : Slf E St₂ G₂.C.J) (E₀ : ExtSpec)
      (A₀ : Rels Kc St₀ E₀ (S.Msg × Wp)) (Rd : S.Ent → Prop) [DecidablePred Rd],
    (∀ st, sl₁ st k.e₁ = 0) → (∀ st, sl₂ st k.e₂ = 0) → (∀ st n, ¬ Rd (G₁.ent n) → sl₁ st n = 0) →
    (∀ st n, ¬ Rd (G₂.ent n) → sl₂ st n = 0) → Rd ⟨k.o, k.j⟩ →
    GoodM (ldSplitR S St₁ St₂ St₀ E₀) (ldSplitH k sl₁ St₂ St₀ Wp E₀)
      (S.over (claimRels (splitIn sl₁ sl₂) A₀)) (S.over (claimRels (splitOut k sl₁ sl₂) A₀))
      (fun _ _ w => w) (ldSplitN S St₁ St₂ St₀ E₀ Kc) (ldSplitD k sl₁ sl₂ Rd St₀ Wp E₀)

end Spec
end Cb
