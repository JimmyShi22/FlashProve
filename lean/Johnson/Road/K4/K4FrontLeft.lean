-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4FrontLeft.lean: THE LINES left AND leftOn OF `K4Front` (K4PromiseFront.lean) AS
THEOREMS, AT EVERY MEANING WHOSE SENTENCES AT THE PUBLIC ITEMS left m AND leftOn m ARE THE LOOKUP's
OWN ITEMS `k3LeftItemAt X i` AND `k3LeftOnItemAt X i` (Johnson/Desc/First/Look/K3LeftItem.lean), at
a layers' link i of a public record X that `publicOf` returns. THE FOUR TIES THAT THE LINE left HELD
(the shape, lm, first and Q at which the item speaks) ARE PAID AS FAR AS THE PLAN's LETTERS, BY THE
LOOKUP's OWN LAWS (`left_lay`, `leftOn_lay`): the shape is X.y.fo, lm is X.y.h.lmb, first is 0, Q is
`LeftQ hp.ns`; that the road's caller can take first := 0 and Q3 := `LeftQ hp.ns` is typed by nobody
here. Statements and proofs: calls.

  `left_of_item`: the item left gives `K3LeftAt` at the record's own readers and these letters.
  `leftOn_of_item`: where the item left held at s, what was heard at the lookup's reader is the same
    at s', and `K3LeftOn` holds at s' at these letters: the item leftOn holds at s' (its conjunct
    `LeavesBare` reads what was heard alone: it rides).
  **`k4Front_of_items`**: `K4Front Mg Z links ps m X.y.fo X.y.h.lmb 0 (LeftQ hp.ns)` from: eL, eO
    (the meaning's two sentences ARE the items: iffs; rfl where the owner's layer lays them) · fit
    (the table's test on the rows) · look (a premise here).

Limits. eL, eO, fit AND look ARE PREMISES. That segment m of the table is link i of X is in no
statement: m and i are two letters, tied by eL and eO alone. That the lookup's yes MAKES the item
left is that kind's law's. X is what `Verify.publicOf` returns (h), as in the lookup's own two laws:
at another maker of the public record these laws are owed anew. Nothing on soundness.
-/
import Johnson.Road.K4.K4PromiseFront
import Johnson.Desc.First.Look.K3LeftItem

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (S LayOwn ModelPart Pub Meaning pubFit)
open VerifiableInference.OnPublicFiles (K3LeftAt K3LeftOn LeftQ LeavesBare k3LeftItemAt k3LeftOnItemAt
        left_lay leftOn_lay)

variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public} {i : ℕ}
  {hp : Layer.HPlan2}

/-- The item left gives the sharp promise, at the plan's letters. -/
theorem left_of_item (h : Verify.publicOf pol KL layout = .ok X)
    (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr) (h0 : i % (if X.p4 then 2 else 1) = 0)
    (hg : X.G[i / (if X.p4 then 2 else 1)]? = some hp) {s : S} (L : k3LeftItemAt X i s) :
    K3LeftAt S.fork? S.lookHeard? X.y.fo X.y.h.lmb 0 (LeftQ hp.ns) s :=
  ((left_lay h hn h0 hg).1 L).1

/-- The item leftOn, where the item left held, what was heard stays, and the lasting promise
holds. -/
theorem leftOn_of_item (h : Verify.publicOf pol KL layout = .ok X)
    (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr) (h0 : i % (if X.p4 then 2 else 1) = 0)
    (hg : X.G[i / (if X.p4 then 2 else 1)]? = some hp) {s s' : S} (L : k3LeftItemAt X i s)
    (hh : s'.lookHeard? = s.lookHeard?)
    (O : K3LeftOn S.fork? S.lookHeard? X.y.fo X.y.h.lmb 0 (LeftQ hp.ns) s') :
    k3LeftOnItemAt X i s' :=
  (leftOn_lay h hn h0 hg).2 ⟨O, fun g hg' => ((left_lay h hn h0 hg).1 L).2 g (hh.symm.trans hg')⟩

variable {P W : Type} (Mg : Meaning P W) (Z : P) {links : List ModelPart} {ps : List Place} {m : ℕ}

/-- **`K4Front` at a meaning whose two sentences are the lookup's own items.** -/
theorem k4Front_of_items (h : Verify.publicOf pol KL layout = .ok X)
    (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr) (h0 : i % (if X.p4 then 2 else 1) = 0)
    (hg : X.G[i / (if X.p4 then 2 else 1)]? = some hp)
    (eL : ∀ s, Mg.pubP (.left m) (Z, s) ↔ k3LeftItemAt X i s)
    (eO : ∀ s, Mg.pubP (.leftOn m) (Z, s) ↔ k3LeftOnItemAt X i s)
    (fit : pubFit Mg.more links ps = true)
    (look : ∀ s a, Mg.pub (.look m) (Z, s) = true → s.here = .lay a → a.fo = a.lookHeard) :
    K4Front Mg Z links ps m X.y.fo X.y.h.lmb 0 (LeftQ hp.ns) :=
  ⟨fit, fun s L => left_of_item h hn h0 hg ((eL s).1 L), look,
    fun s s' L hh O => (eO s').2 (leftOn_of_item h hn h0 hg ((eL s).1 L) hh O)⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.left_of_item
#print axioms OnBytes.Road.K4.leftOn_of_item
#print axioms OnBytes.Road.K4.k4Front_of_items
