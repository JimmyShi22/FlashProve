-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/OCompAll.lean: trees of queries: "whatever the tree puts out has the property P", and the rules
for bind in which what follows is judged only at such outputs.

One definition and theorems. Tools; no rule of a format occurs here. A tree of queries is an oracle
computation (`OComp`, ZKCP/Defs.lean); "asks at most t" is its `QueryBound`.

Why: the rule "bind asks the sum" (ZKCP/ManyOfOne.lean: `QueryBound.bind`) asks a bound on what
follows at every value, also at values that the first part never puts out. Where the second part's
count hangs on the first part's output (a walk up a tree: the next level's list comes out of the
level before), no such bound exists. With a property of the outputs it does.

Main names:
  `c.All P`: on every path of the tree (every answer, every coin) the output has P: as the
    definition's `QueryBound`, it also speaks of paths that no oracle produces.
  `QueryBound.bindP`: c.All P, c asks at most s, g a asks at most t for every a with P ⇒ c.bind g
    asks at most s + t.
  `NoCoin.bindP`: the same for "no coin toss".
  `All.det`: c.All P ⇒ P (c.det f), at every oracle f.

Limits: this file does not say the converse of `All.det` (a property of the results at all oracles
need not hold on paths that no oracle produces).
-/
import Run.OCompM

set_option autoImplicit false

namespace ZKCP
namespace OComp
variable {lam : ℕ} {α β : Type}

/-- Whatever the tree puts out has P, on every path. -/
def All (P : α → Prop) : OComp lam α → Prop
  | pure a => P a
  | query _ k => ∀ r, (k r).All P
  | sample _ k => ∀ r, (k r).All P

theorem all_pure {P : α → Prop} {a : α} (h : P a) : (pure a : OComp lam α).All P := h

theorem all_pure' {P : α → Prop} {a : α} (h : P a) : (Pure.pure a : OComp lam α).All P := h

theorem all_true : ∀ (c : OComp lam α), c.All fun _ => True
  | pure _ => trivial
  | query _ k => fun r => all_true (k r)
  | sample _ k => fun r => all_true (k r)

theorem All.mono {P Q : α → Prop} (hPQ : ∀ a, P a → Q a) : ∀ {c : OComp lam α}, c.All P → c.All Q
  | pure _, h => hPQ _ h
  | query _ _, h => fun r => All.mono hPQ (h r)
  | sample _ _, h => fun r => All.mono hPQ (h r)

theorem All.and {P Q : α → Prop} : ∀ {c : OComp lam α}, c.All P → c.All Q → c.All fun a => P a ∧ Q a
  | pure _, h, h' => ⟨h, h'⟩
  | query _ _, h, h' => fun r => All.and (h r) (h' r)
  | sample _ _, h, h' => fun r => All.and (h r) (h' r)

theorem All.bind {P : α → Prop} {Q : β → Prop} {g : α → OComp lam β} (hg : ∀ a, P a → (g a).All Q) :
    ∀ {c : OComp lam α}, c.All P → (c.bind g).All Q
  | pure _, h => hg _ h
  | query _ _, h => fun r => All.bind hg (h r)
  | sample _ _, h => fun r => All.bind hg (h r)

/-- Under the hypotheses below, bind asks the sum, what follows being judged only at outputs with
P. -/
theorem QueryBound.bindP {P : α → Prop} {g : α → OComp lam β}
    {t : ℕ} (hg : ∀ a, P a → (g a).QueryBound t) :
    ∀ (c : OComp lam α) (s : ℕ), c.All P → c.QueryBound s → (c.bind g).QueryBound (s + t)
  | pure a, s, hP, _ => QueryBound.mono (g a) t (s + t) (Nat.le_add_left _ _) (hg a hP)
  | query _ _, 0, _, h => h.elim
  | query _ k, s + 1, hP, h => by
      rw [Nat.add_right_comm]
      exact fun r => QueryBound.bindP hg (k r) s (hP r) (h r)
  | sample _ k, s, hP, h => fun r => QueryBound.bindP hg (k r) s (hP r) (h r)

/-- The same for "no coin toss". -/
theorem NoCoin.bindP {P : α → Prop} {g : α → OComp lam β} (hg : ∀ a, P a → (g a).NoCoin) :
    ∀ {c : OComp lam α}, c.All P → c.NoCoin → (c.bind g).NoCoin
  | pure _, hP, _ => hg _ hP
  | query _ _, hP, h => fun r => NoCoin.bindP hg (hP r) (h r)
  | sample _ _, _, h => h.elim

/-- If `c.All P`, at every oracle the result has P. -/
theorem All.det {P : α → Prop} (f : Oracle lam) : ∀ {c : OComp lam α}, c.All P → P (c.det f)
  | pure _, h => h
  | query q k, h => All.det f (c := k (f q)) (h (f q))
  | sample _ k, h => All.det f (c := k 0) (h 0)

end OComp
end ZKCP
