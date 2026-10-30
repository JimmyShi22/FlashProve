-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBatPeel.lean: book-keeping between the steps of a proximity test with linear claims:
reductions without messages that write one linear claim on encoded messages in another form.

Definitions and statements; the proofs are in Cb/Ld/LdBatPeelProofs.lean.

In standard terms: A joint (`IOR.Rels`; with its types, `IOR.Joint`) consists of, for one kind of
statement and of witness: the honest relation; a second relation, called relaxed, of which
round-by-round knowledge soundness speaks; the set of statements of which that soundness speaks; and
a map from a witness to its core. `S.over A` (`Sig.over`, Cb/Ld/LdSig.lean) is the relation "each
word is the encoding of its pair (message, randomness), each message has the answers of its sample,
and the base joint A holds of the messages"; in its relaxed form each message is what the decoder
with a sample returns, and the relaxed relation of A holds of the messages. A step without rounds
(`StepT`, Ior/KnowCollRulesFrame.lean) is a reduction without messages: maps on statements, oracles
and witnesses that take exact witnesses forth and, at statements with the first joint's condition
(`on`), relaxed witnesses back.

Why: the batching on statements with samples (Cb/Ld/LdBatSig.lean) leaves one row on all entries of
all messages (`S.Ent`). The bridge (same file) needs rows on the message of one group, beside a
joint on the kept messages; the split (Cb/Ld/LdSplit.lean) needs "a part on G₁ plus a part on G₂".
Between these forms nothing happens: no round, no query, no error; words, samples and messages stay.
But the joints are different terms, and a chain needs a step.

Main names:
  `Spec.ldPeel_base`, the rule: a change of the base joint, the messages untouched.
  `Spec.ldPeel_cf`: a step from A to B ⇒ a step from `A.cf` to `B.cf` (`Rels.cf`,
    Ior/KnowCollGood.lean), the form in which chains are made.
  `Spec.ldPeel_onG`: a form that vanishes outside G has the same value on the group's message.
  `Spec.ldPeel_two`: a form that vanishes outside G₁ and G₂ is (its part on G₁) plus (what is left,
    on G₂).
  `Spec.ldPeel_onSub`: a form that vanishes outside the kept messages has the same value on them.
  `Spec.ldPeel_toSub`: if all members of G are kept, a form on the message of G has the same value
    on the message of `G.sub kp`.
  `Spec.ldPeel_sub_fits`: `G.sub kp` inherits "the joint radius implies each member's own"
    (`Grp.Fits`).

Limits: this file says nothing on a protocol. Which rows a protocol has, and which groups, is not
here.
The notions are steps and forms of this library's Lean text.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSplit
import Ior.KnowCollRulesFrame
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood

/-! ## 1. A change of the base joint -/

section
variable {E : Type} (S : Sig E) {St St' Wp Wp' : Type} {E₀ E₀' : ExtSpec}

/-- the explicit part: the samples stay -/
def sideF (f : St → St') : St × S.Smp → Option (St' × S.Smp) := fun x => some (f x.1, x.2)

/-- the oracles: the words stay -/
def sideG (g₀ : ExtMap E₀ E₀') : ExtMap (E₀.prod S.ext) (E₀'.prod S.ext) :=
  (g₀.comp (ExtMap.fst E₀ S.ext)).pair (ExtMap.snd E₀ S.ext)

/-- the honest prover: the pairs stay -/
def sideM (f : St → St') (up : St → S.Msg × Wp → Wp') :
    (St × S.Smp) × (S.Wit × Wp) → (St' × S.Smp) × (S.Wit × Wp') :=
  fun a => ((f a.1.1, a.1.2), (a.2.1, up a.1.1 (S.msgs a.2.1, a.2.2)))

/-- the extractor: the pairs stay -/
def sideB (dn : St × E₀.Str → S.Msg × Wp' → Wp) :
    (St × S.Smp) × (E₀.prod S.ext).Str → S.Wit × Wp' → S.Wit × Wp :=
  fun a w => (w.1, dn (a.1.1, a.2.1) (S.msgs w.1, w.2))

end

/-! ## 2. Forms -/

section
variable {E St : Type} {S : Sig E}

/-- a form on all entries, read on the entries of a group -/
def Slf.onG (sl : Slf E St S.Ent) (G : Grp S) : Slf E St G.C.J := fun st n => sl st (G.ent n)

/-- the same form, with zeros at the entries of the group -/
def Slf.offG [Zero E] (sl : Slf E St S.Ent) (G : Grp S) : Slf E St S.Ent := fun st n =>
  if G.mem n.1 then 0 else sl st n

/-- a form on all entries, read on the entries of the kept messages -/
def Slf.onSub (sl : Slf E St S.Ent) (kp : S.O → Prop) [DecidablePred kp] :
    Slf E St (S.sub kp).Ent :=
  fun st n => sl st ⟨n.1.1, n.2⟩

/-- The group among the kept oracle messages. -/
@[reducible] def Grp.sub (G : Grp S) (kp : S.O → Prop) [DecidablePred kp] : Grp (S.sub kp) :=
  { P := G.P, mem := fun a => G.mem a.1, pos := fun a => G.pos ⟨a.1.1, a.2⟩, e := G.e }

/-- a form on the message of G, as a form on the message of G.sub kp -/
def Slf.toSub {G : Grp S} (sl : Slf E St G.C.J) (kp : S.O → Prop) [DecidablePred kp] :
    Slf E St (G.sub kp).C.J :=
  fun st n => sl st ⟨⟨n.1.1.1, n.1.2⟩, n.2⟩

end

/-! ## The statements -/

namespace Spec
open IOR

/-- A step stays a step between the joints whose condition is moved into the relaxed relation
(`A.cf`, `B.cf`). -/
def ldPeel_cf : Prop :=
  ∀ (K X X' W W' : Type) (Ex Ex' : ExtSpec) (f : X → Option X') (g : ExtMap Ex Ex')
      (m : X × W → X' × W') (back : X × Ex.Str → W' → W) (A : Rels K X Ex W) (B : Rels K X' Ex' W'),
    StepT f g m back A B → StepT f g m back A.cf B.cf

/-- The rule: a change of the base joint, the messages untouched: the explicit part without the
samples is mapped by f, the further oracles by g₀, the further witness forth by up and back by dn.
States: if `g₀.IsLocal` and, for each tuple of messages, the exact relation goes forth, the relaxed
one comes back, condition and core are handed on, then `sideF S f`, `sideG S g₀`, `sideM S f up`,
`sideB S dn` are a step without rounds (`StepT`) from `S.over A` to `S.over A'`. -/
def ldPeel_base : Prop :=
  ∀ (E Kc St St' Wp Wp' : Type) [Field E] (S : Sig E) (E₀ E₀' : ExtSpec)
      (A : Rels Kc St E₀ (S.Msg × Wp)) (A' : Rels Kc St' E₀' (S.Msg × Wp')) (f : St → St')
      (g₀ : ExtMap E₀ E₀') (up : St → S.Msg × Wp → Wp') (dn : St × E₀.Str → S.Msg × Wp' → Wp),
    g₀.IsLocal → (∀ st y w, A.rel st y w → A'.rel (f st) (g₀.map y) (w.1, up st w)) →
    (∀ st y, A.on (st, y) → A'.on (f st, g₀.map y)) → (∀ st w, A'.core (w.1, up st w) = A.core w) →
    (∀ st y w, A.on (st, y) → A'.relR (f st, g₀.map y) w → A.relR (st, y) (w.1, dn (st, y) w)) →
    StepT (sideF S f) (sideG S g₀) (sideM S f up) (sideB S dn) (S.over A) (S.over A')

section
variable (E : Type) [Field E]

def ldPeel_onG : Prop :=
  ∀ (S : Sig E) (G : Grp S) (St : Type) (sl : Slf E St S.Ent) (st : St) (m : S.Msg),
    (∀ n : S.Ent, ¬ G.mem n.1 → sl st n = 0) → (sl.onG G).val st (G.msg m) = sl.val st (S.ents m)

def ldPeel_two : Prop :=
  ∀ (S : Sig E) (G₁ G₂ : Grp S) (St : Type) (sl : Slf E St S.Ent) (st : St) (m : S.Msg),
    (∀ n : S.Ent, ¬ G₁.mem n.1 → ¬ G₂.mem n.1 → sl st n = 0) →
    (sl.onG G₁).val st (G₁.msg m) + ((sl.offG G₁).onG G₂).val st (G₂.msg m) = sl.val st (S.ents m)

def ldPeel_onSub : Prop :=
  ∀ (S : Sig E) (kp : S.O → Prop) [DecidablePred kp] (St : Type)
      (sl : Slf E St S.Ent) (st : St) (m : S.Msg),
    (∀ n : S.Ent, ¬ kp n.1 → sl st n = 0) →
    (sl.onSub kp).val st ((S.sub kp).ents (S.res (T := OMsg.Msg) kp m)) = sl.val st (S.ents m)

def ldPeel_toSub : Prop :=
  ∀ (S : Sig E) (G : Grp S) (kp : S.O → Prop) [DecidablePred kp] (St : Type)
      (sl : Slf E St G.C.J) (st : St) (m : S.Msg),
    (∀ o, G.mem o → kp o) →
    (sl.toSub kp).val st ((G.sub kp).msg (S.res (T := OMsg.Msg) kp m)) = sl.val st (G.msg m)

def ldPeel_sub_fits : Prop :=
  ∀ (S : Sig E) (G : Grp S) (kp : S.O → Prop) [DecidablePred kp], G.Fits → (G.sub kp).Fits

end
end Spec
end Cb
