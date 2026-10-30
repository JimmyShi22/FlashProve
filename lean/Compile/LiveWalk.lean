-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/LiveWalk.lean: a way to show, part by part, that a token program never uses the string of a
dead token (one of the set D of Compile/SpecEraseDead.lean; words of this library:
lean/GLOSSARY.md).

One notion and its rules, generic in the family of oracles, for Compile/SpecEraseDead.lean ("a token
whose string is never used may have any string"; the purpose: its head). The words, as there: a
token program (`Step`, Rom/Defer.lean) names strings by tokens; in its erasure (`erase`,
Compile/Star.lean) a token is an index into a list of strings, the store; the dead tokens are the
set D in `NoUse D Q c n`; ag is a relation on the answers to each query of each oracle (so in
Compile/NeedBlocks.lean).

Compile/SpecEraseDead.lean asks two things of such a program: `NoUse` (a given dead token's string
is never used) and `FacDead` (after two answers related by ag the program goes on alike and never
uses the new token's string). Both are to be shown part by part. A part holds tokens in its
arguments, and returns tokens in its value. Some of these it, or a later part, will use: the live
ones. What has to be carried along is one sentence, that all live tokens have the property φ, for
two kinds of φ: "is not d" (for a dead d) and "is below n" (n the length of the store, the list of
the tokens' strings: so that a token which dies later is none of them).

  `LiveWalk ag Pre Post c`
           Pre φ: all live tokens in c's arguments have φ. Post φ a: all live tokens in the value a
           have φ. The two clauses:
    `nu`   If d is not 0, is below the length of the store, and no live token of the arguments is d,
           c never uses d's string, and no live token of its value is d.
    `fd`   If all live tokens of the arguments are below the length of the store, c is `FacDead`; a
           token that dies in c is no live token of its value; all live tokens of the value are
           below the length of the store then.
There is one rule for each kind of step, and `erase` for the end: the erasure of such a program,
started on a store that holds all its live tokens and followed by a g that forgets the store,
depends on its answers only up to ag (`OComp.FactorsBy`) if every g a does. `LiveW ag T TP c` is the
form for use, with the live tokens as sets: T, those in c's arguments; TP a, those in its value a.
`Ends G c`: every value that c returns has G (say "the list of the slot's tails is not empty").

The default token 0. The programs of Compile/Batch/Prover.lean and Compile/Batch/TokTree.lean read
lists of tokens with the default 0 (`getD`, `headD`, the root of a tree). So a token that a step
names is a live one or 0. The rules `marked`, `reveal`, `revealMore` therefore give φ 0 as a
hypothesis; a dead token is never 0: `markedDead` asks that there be a live token (h1), so the store
is not empty when the new token is made. Pre must be monotone in φ (`MonoP`): a sentence "all ..
have φ" is.

Notation: `n₀` in `fd`: a natural number, n₀ ≤ n; the condition of `FacDead` on a token d that dies
has n₀ ≤ d.

Limits: nothing on any program. The larger T, the less is said. With all tokens live nothing is
said: `LiveW ag (fun _ => True) TP c` holds of every program (`LiveW.ofAll`), and the clause `fd` is
empty for every T that is not bounded. A lemma's hypotheses bound T from below only. What bounds it
from above is the end: `LiveW.erase` asks that all of T be below the length of the store on which
the program starts. There the clause `fd` applies to every token that is made later. Sanity lemma
`LiveW.not_reveal`: the program that reveals token 1, not live (T = {2}), and returns its string is
no `LiveW`.
-/
import Compile.EraseDead

set_option autoImplicit false

namespace Compile
open Rom

variable {S : OSpec} {sp : Split S} {α β : Type} {ag : ∀ o, S.Dom o → S.Rng o → S.Rng o → Prop}

/-- monotone in φ, as a sentence of the form "all .. have φ" is -/
def MonoP (Pre : (Tok → Prop) → Prop) : Prop := ∀ φ ψ : Tok → Prop, (∀ u, φ u → ψ u) → Pre φ → Pre ψ

/-- The two facts on a part of a token program, with what it asks of the live tokens in its
arguments and says of those in its value. -/
structure LiveWalk (ag : ∀ o, S.Dom o → S.Rng o → S.Rng o → Prop) (Pre : (Tok → Prop) → Prop)
    (Post : (Tok → Prop) → α → Prop) (c : Step S sp α) : Prop where
  nu : ∀ d n : ℕ, 0 < d → d < n → Pre (fun u => u ≠ d) →
    NoUse (fun t => t = d) (fun a m => Post (fun u => u ≠ d) a ∧ d < m) c n
  fd : ∀ n₀ n : ℕ, n₀ ≤ n → Pre (fun u => u < n) →
    FacDead ag (fun d a m => 0 < d ∧ n₀ ≤ d ∧ d < m ∧ Post (fun u => u ≠ d) a)
      (fun a m => n ≤ m ∧ Post (fun u => u < m) a) c n

namespace LiveWalk

variable {Pre Pre' : (Tok → Prop) → Prop}
  {Post : (Tok → Prop) → α → Prop} {Post' : (Tok → Prop) → β → Prop}

theorem pure {a : α} (h : ∀ φ, Pre φ → Post φ a) :
    LiveWalk ag Pre Post (Step.pure a : Step S sp α) :=
  ⟨fun _ _ _ hd hp => ⟨h _ hp, hd⟩, fun _ _ _ hp => ⟨le_rfl, h _ hp⟩⟩

theorem sample (m : ℕ) {k : Fin (m + 1) → Step S sp α} (h : ∀ r, LiveWalk ag Pre Post (k r)) :
    LiveWalk ag Pre Post (Step.sample m k) :=
  ⟨fun d n h0 hd hp r => (h r).nu d n h0 hd hp, fun n₀ n hn hp r => (h r).fd n₀ n hn hp⟩

theorem plain (o : S.ι) (q : S.Dom o) {k : S.Rng o → Step S sp α}
    (he : ∀ r r', ag o q r r' → k r = k r') (h : ∀ r, LiveWalk ag Pre Post (k r)) :
    LiveWalk ag Pre Post (Step.plain o q k) :=
  ⟨fun d n h0 hd hp r => (h r).nu d n h0 hd hp,
    fun n₀ n hn hp => ⟨he, fun r => (h r).fd n₀ n hn hp⟩⟩

/-- to ask more and say less -/
theorem imp {c : Step S sp α} {Post₂ : (Tok → Prop) → α → Prop} (h : LiveWalk ag Pre Post c)
    (hp : ∀ φ, Pre' φ → Pre φ) (hq : ∀ φ a, Post φ a → Post₂ φ a) : LiveWalk ag Pre' Post₂ c :=
  ⟨fun d n h0 hd h' =>
      noUseMono S sp α _ _ _ _ c n (fun _ e => e)
        (fun a _ x => ⟨hq _ a x.1, x.2⟩) (h.nu d n h0 hd (hp _ h')),
    fun n₀ n hn h' =>
      facDeadMono S sp α ag _ _ _ _ c n (fun _ a _ x => ⟨x.1, x.2.1, x.2.2.1, hq _ a x.2.2.2⟩)
        (fun a _ x => ⟨x.1, hq _ a x.2⟩) (h.fd n₀ n hn (hp _ h'))⟩

private theorem up1 (hm : MonoP Pre) {n : ℕ} (hp : Pre fun u => u < n) : Pre fun u => u < n + 1 :=
  hm _ _ (fun _ h => Nat.lt_succ_of_lt h) hp

/-- the end conditions of fd, from a start one later -/
private theorem fdStep {c : Step S sp α} {n₀ n : ℕ}
    (h : FacDead ag (fun d a m => 0 < d ∧ n₀ ≤ d ∧ d < m ∧ Post (fun u => u ≠ d) a)
      (fun a m => n + 1 ≤ m ∧ Post (fun u => u < m) a) c (n + 1)) :
    FacDead ag (fun d a m => 0 < d ∧ n₀ ≤ d ∧ d < m ∧ Post (fun u => u ≠ d) a)
      (fun a m => n ≤ m ∧ Post (fun u => u < m) a) c (n + 1) :=
  facDeadMono S sp α ag _ _ _ _ c (n + 1) (fun _ _ _ x => x)
    (fun _ _ x => ⟨Nat.le_of_succ_le x.1, x.2⟩) h

/-- a new token is live -/
theorem fresh (hm : MonoP Pre) (ℓ : ℕ) {k : Tok → Step S sp α}
    (h : ∀ t, LiveWalk ag (fun φ => Pre φ ∧ φ t) Post (k t)) :
    LiveWalk ag Pre Post (Step.fresh ℓ k) :=
  ⟨fun d n h0 hd hp => (h n).nu d (n + 1) h0 (Nat.lt_succ_of_lt hd) ⟨hp, Nat.ne_of_gt hd⟩,
    fun n₀ n hn hp =>
      fdStep ((h n).fd n₀ (n + 1) (Nat.le_succ_of_le hn) ⟨up1 hm hp, Nat.lt_succ_self n⟩)⟩

/-- A marked query after which the new token may be dead. hm: Pre is monotone in φ (`MonoP`). h1:
there is a live token, so the store is not empty. ht, hu: its tokens are live, or the default token
0. hk: the new token live (an answer that is used). hd: after two answers related by ag: the same
continuation, in which the new token is not among the live ones. -/
theorem markedDead (hm : MonoP Pre) (o : S.ι) {t : Tok} {us : List Tok}
    (pt : Bits → List Bits → S.Dom o) (inj : ∀ vs, Function.Injective fun v => pt v vs)
    {k : sp.Vis o → Tok → Step S sp α} (h1 : ∀ n, Pre (fun u => u < n) → 0 < n)
    (ht : ∀ φ : Tok → Prop, φ 0 → Pre φ → φ t) (hu : ∀ φ : Tok → Prop, φ 0 → Pre φ → ∀ u ∈ us, φ u)
    (hk : ∀ v t', LiveWalk ag (fun φ => Pre φ ∧ φ t') Post (k v t'))
    (hd : ∀ v ws r r', ag o (pt v ws) r r' →
      ∀ t',
        k (sp.split o r).1 t' = k (sp.split o r').1 t' ∧
        LiveWalk ag Pre Post (k (sp.split o r).1 t')) :
    LiveWalk ag Pre Post (Step.marked o t us pt inj k) :=
  ⟨fun d n h0 hdn hp =>
      ⟨fun e => ht (fun u => u ≠ d) (Nat.ne_of_lt h0) hp e,
        fun u hu' e => hu (fun u => u ≠ d) (Nat.ne_of_lt h0) hp u hu' e,
        fun v => (hk v n).nu d (n + 1) h0 (Nat.lt_succ_of_lt hdn) ⟨hp, Nat.ne_of_gt hdn⟩⟩,
    fun n₀ n hn hp =>
      ⟨fun v ws r r' e =>
          ⟨(hd v ws r r' e n).1,
            noUseMono S sp α _ _ _ _ _ (n + 1) (fun _ x => x) (fun _ _ x => ⟨h1 n hp, hn, x.2, x.1⟩)
              ((hd v ws r r' e n).2.nu n (n + 1) (h1 n hp) (Nat.lt_succ_self n)
                (hm _ _ (fun _ h => Nat.ne_of_lt h) hp))⟩,
        fun v =>
          fdStep ((hk v n).fd n₀ (n + 1) (Nat.le_succ_of_le hn) ⟨up1 hm hp, Nat.lt_succ_self n⟩)⟩⟩

/-- a marked query at which ag relates no two answers -/
theorem marked (hm : MonoP Pre) (o : S.ι) {t : Tok} {us : List Tok}
    (pt : Bits → List Bits → S.Dom o) (inj : ∀ vs, Function.Injective fun v => pt v vs)
    {k : sp.Vis o → Tok → Step S sp α} (ht : ∀ φ : Tok → Prop, φ 0 → Pre φ → φ t ∧ ∀ u ∈ us, φ u)
    (hk : ∀ v t', LiveWalk ag (fun φ => Pre φ ∧ φ t') Post (k v t'))
    (hno : ∀ q r r', ¬ ag o q r r') :
    LiveWalk ag Pre Post (Step.marked o t us pt inj k) :=
  ⟨fun d n h0 hdn hp =>
      ⟨fun e => (ht (fun u => u ≠ d) (Nat.ne_of_lt h0) hp).1 e,
        fun u hu e => (ht (fun u => u ≠ d) (Nat.ne_of_lt h0) hp).2 u hu e,
        fun v => (hk v n).nu d (n + 1) h0 (Nat.lt_succ_of_lt hdn) ⟨hp, Nat.ne_of_gt hdn⟩⟩,
    fun n₀ n hn hp =>
      ⟨fun _ _ _ _ e => (hno _ _ _ e).elim,
        fun v =>
          fdStep ((hk v n).fd n₀ (n + 1) (Nat.le_succ_of_le hn) ⟨up1 hm hp, Nat.lt_succ_self n⟩)⟩⟩

/-- A reveal that names further tokens, live or dead, of whose strings what follows does not
depend. -/
theorem revealMore {ts more : List Tok} {k : List Bits → Step S sp α}
    (ht : ∀ φ : Tok → Prop, φ 0 → Pre φ → ∀ u ∈ ts, φ u)
    (hi : ∀ w x y : List Bits, w.length = ts.length → k (w ++ x) = k (w ++ y))
    (hk : ∀ w, LiveWalk ag Pre Post (k w)) :
    LiveWalk ag Pre Post (Step.reveal (ts ++ more) k) :=
  ⟨fun d n h0 hd hp => ⟨fun f f' hf => by
      rw [List.map_append, List.map_append,
        List.map_congr_left fun u hu => hf u ((ht (fun u => u ≠ d) (Nat.ne_of_lt h0) hp) u hu)]
      exact hi _ _ _ (List.length_map _), fun w => (hk w).nu d n h0 hd hp⟩,
   fun n₀ n hn hp w => (hk w).fd n₀ n hn hp⟩

theorem reveal {ts : List Tok} {k : List Bits → Step S sp α}
    (ht : ∀ φ : Tok → Prop, φ 0 → Pre φ → ∀ u ∈ ts, φ u) (hk : ∀ w, LiveWalk ag Pre Post (k w)) :
    LiveWalk ag Pre Post (Step.reveal ts k) :=
  ⟨fun d n h0 hd hp =>
      ⟨fun f f' hf => by
          rw [List.map_congr_left fun u hu =>
              hf u ((ht (fun u => u ≠ d) (Nat.ne_of_lt h0) hp) u hu)],
        fun w => (hk w).nu d n h0 hd hp⟩,
    fun n₀ n hn hp w => (hk w).fd n₀ n hn hp⟩

/-- One program after another. What follows holds the tokens of the first part's arguments and of
its value. -/
theorem bind (hm : MonoP Pre) {c : Step S sp α} {g : α → Step S sp β} (hc : LiveWalk ag Pre Post c)
    (hg : ∀ a, LiveWalk ag (fun φ => Pre φ ∧ Post φ a) Post' (g a)) :
    LiveWalk ag Pre Post' (c.bind g) :=
  ⟨fun d n h0 hd hp =>
      noUseBind S sp α β _ _ _ c g n (hc.nu d n h0 hd hp) fun a m x =>
        (hg a).nu d m h0 x.2 ⟨hp, x.1⟩,
    fun n₀ n hn hp =>
      facDeadBind S sp α β ag _ _ _ _ c g n (hc.fd n n le_rfl hp)
        (fun d a m x =>
          noUseMono S sp β _ _ _ _ _ m (fun _ e => e) (fun _ _ y => ⟨x.1, hn.trans x.2.1, y.2, y.1⟩)
            ((hg a).nu d m x.1 x.2.2.1
              ⟨hm _ _ (fun _ hu => Nat.ne_of_lt (Nat.lt_of_lt_of_le hu x.2.1)) hp, x.2.2.2⟩))
        (fun a m x =>
          facDeadMono S sp β ag _ _ _ _ _ m (fun _ _ _ y => y) (fun _ _ y => ⟨x.1.trans y.1, y.2⟩)
            ((hg a).fd n₀ m (hn.trans x.1)
              ⟨hm _ _ (fun _ hu => Nat.lt_of_lt_of_le hu x.1) hp, x.2⟩))⟩

/-- The end: the erasure of a program with `LiveWalk`, started on a store that holds all live
tokens, and followed by a g that forgets the store and depends on its answers only up to ag, depends
on its answers only up to ag. -/
theorem erase {γ : Type} {c : Step S sp α} (h : LiveWalk ag Pre Post c) (vs : List Bits)
    (hp : Pre fun u => u < vs.length) (g : α → OComp S γ) (hg : ∀ a, (g a).FactorsBy ag) :
    ((Compile.erase c vs).bind fun o => g o.1).FactorsBy ag :=
  facDeadErase S sp α γ ag _ _ c vs (fun o => g o.1) (h.fd 0 vs.length (Nat.zero_le _) hp)
    (fun _ _ _ _ _ _ => rfl) fun a _ _ => hg a

end LiveWalk

/-! ## What holds of every value that a program returns -/

/-- Every value that the program returns has G, whatever the answers, the coins and the tokens. -/
def Ends (G : α → Prop) : Step S sp α → Prop
  | .pure a => G a
  | .sample _ k => ∀ r, Ends G (k r)
  | .plain _ _ k => ∀ r, Ends G (k r)
  | .fresh _ k => ∀ t, Ends G (k t)
  | .marked _ _ _ _ _ k => ∀ v t, Ends G (k v t)
  | .reveal _ k => ∀ w, Ends G (k w)

theorem ends_true : ∀ c : Step S sp α, Ends (fun _ => True) c
  | .pure _ => trivial
  | .sample _ k => fun r => ends_true (k r)
  | .plain _ _ k => fun r => ends_true (k r)
  | .fresh _ k => fun t => ends_true (k t)
  | .marked _ _ _ _ _ k => fun v t => ends_true (k v t)
  | .reveal _ k => fun w => ends_true (k w)

theorem Ends.bind {G : α → Prop} {G' : β → Prop} {g : α → Step S sp β} :
    ∀ {c : Step S sp α}, Ends G c → (∀ a, G a → Ends G' (g a)) → Ends G' (c.bind g)
  | .pure a, h, hg => hg a h
  | .sample _ k, h, hg => fun r => Ends.bind (c := k r) (h r) hg
  | .plain _ _ k, h, hg => fun r => Ends.bind (c := k r) (h r) hg
  | .fresh _ k, h, hg => fun t => Ends.bind (c := k t) (h t) hg
  | .marked _ _ _ _ _ k, h, hg => fun v t => Ends.bind (c := k v t) (h v t) hg
  | .reveal _ k, h, hg => fun w => Ends.bind (c := k w) (h w) hg

theorem noUse_ends {D : Tok → Prop} {Q : α → ℕ → Prop} {G : α → Prop} :
    ∀ {c : Step S sp α} {n : ℕ}, NoUse D Q c n → Ends G c → NoUse D (fun a m => G a ∧ Q a m) c n
  | .pure _, _, h, he => ⟨he, h⟩
  | .sample _ k, _, h, he => fun r => noUse_ends (c := k r) (h r) (he r)
  | .plain _ _ k, _, h, he => fun r => noUse_ends (c := k r) (h r) (he r)
  | .fresh _ k, n, h, he => noUse_ends (c := k n) h (he n)
  | .marked _ _ _ _ _ k, n, h, he => ⟨h.1, h.2.1, fun v => noUse_ends (c := k v n) (h.2.2 v) (he v n)⟩
  | .reveal _ k, _, h, he => ⟨h.1, fun w => noUse_ends (c := k w) (h.2 w) (he w)⟩

theorem facDead_ends {Q : Tok → α → ℕ → Prop} {R : α → ℕ → Prop} {G : α → Prop} :
    ∀ {c : Step S sp α} {n : ℕ}, FacDead ag Q R c n → Ends G c →
      FacDead ag (fun d a m => G a ∧ Q d a m) (fun a m => G a ∧ R a m) c n
  | .pure _, _, h, he => ⟨he, h⟩
  | .sample _ k, _, h, he => fun r => facDead_ends (c := k r) (h r) (he r)
  | .plain _ _ k, _, h, he => ⟨h.1, fun r => facDead_ends (c := k r) (h.2 r) (he r)⟩
  | .fresh _ k, n, h, he => facDead_ends (c := k n) h (he n)
  | .marked _ _ _ _ _ k, n, h, he =>
    ⟨fun v ws r r' e => ⟨(h.1 v ws r r' e).1, noUse_ends (h.1 v ws r r' e).2 (he _ n)⟩,
      fun v => facDead_ends (c := k v n) (h.2 v) (he v n)⟩
  | .reveal _ k, _, h, he => fun w => facDead_ends (c := k w) (h w) (he w)

/-- a LiveWalk whose values all have G says so -/
theorem LiveWalk.andEnds {Pre : (Tok → Prop) → Prop} {Post : (Tok → Prop) → α → Prop} {G : α → Prop}
    {c : Step S sp α} (h : LiveWalk ag Pre Post c) (he : Ends G c) :
    LiveWalk ag Pre (fun φ a => G a ∧ Post φ a) c :=
  ⟨fun d n h0 hd hp =>
      noUseMono S sp α _ _ _ _ c n (fun _ e => e)
        (fun _ _ x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩) (noUse_ends (h.nu d n h0 hd hp) he),
    fun n₀ n hn hp =>
      facDeadMono S sp α ag _ _ _ _ c n (fun _ _ _ x => ⟨x.2.1, x.2.2.1, x.2.2.2.1, x.1, x.2.2.2.2⟩)
        (fun _ _ x => ⟨x.2.1, x.1, x.2.2⟩) (facDead_ends (h.fd n₀ n hn hp) he)⟩

/-- a hypothesis that is not about tokens may be put among those on the live tokens -/
theorem LiveWalk.ofImp {Pre : (Tok → Prop) → Prop} {Post : (Tok → Prop) → α → Prop} {G : Prop}
    {c : Step S sp α} (h : G → LiveWalk ag Pre Post c) :
    LiveWalk ag (fun φ => G ∧ Pre φ) Post c :=
  ⟨fun d n h0 hd hp => (h hp.1).nu d n h0 hd hp.2, fun n₀ n hn hp => (h hp.1).fd n₀ n hn hp.2⟩

/-! ## The same with sets of live tokens -/

/-- all tokens of the set T have φ -/
def allP (T : Tok → Prop) : (Tok → Prop) → Prop := fun φ => ∀ u, T u → φ u

theorem monoP_allP (T : Tok → Prop) : MonoP (allP T) := fun _ _ h hp u hu => h u (hp u hu)

/-- LiveWalk, with the live tokens given as sets: T: those in the arguments of c; TP a: those in its
value a. -/
def LiveW (ag : ∀ o, S.Dom o → S.Rng o → S.Rng o → Prop) (T : Tok → Prop)
    (TP : α → Tok → Prop) (c : Step S sp α) : Prop :=
  LiveWalk ag (allP T) (fun φ a => allP (TP a) φ) c

namespace LiveW

variable {T T' : Tok → Prop} {TP : α → Tok → Prop} {TP' : β → Tok → Prop}

/-- more live tokens in the arguments, fewer in the value -/
theorem imp {c : Step S sp α} {TP₂ : α → Tok → Prop} (h : LiveW ag T TP c)
    (hT : ∀ u, T u → T' u) (hP : ∀ a u, TP₂ a u → TP a u) : LiveW ag T' TP₂ c :=
  LiveWalk.imp h (fun _ hp u hu => hp u (hT u hu)) fun _ a hp u hu => hp u (hP a u hu)

private theorem add {c : Step S sp α} {t : Tok} (h : LiveW ag (fun u => T u ∨ u = t) TP c) :
    LiveWalk ag (fun φ => allP T φ ∧ φ t) (fun φ a => allP (TP a) φ) c :=
  LiveWalk.imp h (fun _ hp u hu => hu.elim (hp.1 u) fun e => e ▸ hp.2) fun _ _ hp => hp

theorem pure {a : α} (h : ∀ u, TP a u → T u) : LiveW ag T TP (Step.pure a : Step S sp α) :=
  LiveWalk.pure fun _ hp u hu => hp u (h u hu)

/-- a value that also holds the default token 0 (a field that is not yet set), if there is a live
token -/
theorem pureZ {a : α} (h1 : ∃ u, T u) (h : ∀ u, TP a u → T u ∨ u = 0) :
    LiveW ag T TP (Step.pure a : Step S sp α) :=
  ⟨fun _ _ h0 hd hp => ⟨fun u hu => (h u hu).elim (hp u) fun e => e ▸ Nat.ne_of_lt h0, hd⟩,
    fun _ _ _ hp =>
      ⟨le_rfl, fun u hu =>
          (h u hu).elim (hp u) fun e =>
            e ▸ h1.elim fun v hv => Nat.lt_of_le_of_lt (Nat.zero_le v) (hp v hv)⟩⟩

theorem sample (m : ℕ) {k : Fin (m + 1) → Step S sp α} (h : ∀ r, LiveW ag T TP (k r)) :
    LiveW ag T TP (Step.sample m k) :=
  LiveWalk.sample m h

theorem plain (o : S.ι) (q : S.Dom o) {k : S.Rng o → Step S sp α}
    (he : ∀ r r', ag o q r r' → k r = k r') (h : ∀ r, LiveW ag T TP (k r)) :
    LiveW ag T TP (Step.plain o q k) :=
  LiveWalk.plain o q he h

theorem fresh (ℓ : ℕ) {k : Tok → Step S sp α} (h : ∀ t, LiveW ag (fun u => T u ∨ u = t) TP (k t)) :
    LiveW ag T TP (Step.fresh ℓ k) :=
  LiveWalk.fresh (monoP_allP T) ℓ fun t => add (h t)

private theorem orZero {φ : Tok → Prop} (h0 : φ 0) (hp : allP T φ) {u : Tok} (hu : T u ∨ u = 0) :
    φ u :=
  hu.elim (hp u) fun e => e ▸ h0

theorem marked (o : S.ι) {t : Tok} {us : List Tok} (pt : Bits → List Bits → S.Dom o)
    (inj : ∀ vs, Function.Injective fun v => pt v vs) {k : sp.Vis o → Tok → Step S sp α}
    (ht : T t ∨ t = 0) (hu : ∀ u ∈ us, T u ∨ u = 0)
    (hk : ∀ v t', LiveW ag (fun u => T u ∨ u = t') TP (k v t')) (hno : ∀ q r r', ¬ ag o q r r') :
    LiveW ag T TP (Step.marked o t us pt inj k) :=
  LiveWalk.marked (monoP_allP T) o pt inj
    (fun _ h0 hp => ⟨orZero h0 hp ht, fun u hm => orZero h0 hp (hu u hm)⟩)
    (fun v t' => add (hk v t')) hno

/-- A marked query after which the new token may be dead. -/
theorem markedDead (o : S.ι) {t : Tok} {us : List Tok} (pt : Bits → List Bits → S.Dom o)
    (inj : ∀ vs, Function.Injective fun v => pt v vs) {k : sp.Vis o → Tok → Step S sp α}
    (h1 : ∃ u, T u) (ht : T t ∨ t = 0) (hu : ∀ u ∈ us, T u ∨ u = 0)
    (hk : ∀ v t', LiveW ag (fun u => T u ∨ u = t') TP (k v t'))
    (hd : ∀ v ws r r', ag o (pt v ws) r r' →
      ∀ t',
        k (sp.split o r).1 t' = k (sp.split o r').1 t' ∧ LiveW ag T TP (k (sp.split o r).1 t')) :
    LiveW ag T TP (Step.marked o t us pt inj k) :=
  LiveWalk.markedDead (monoP_allP T) o pt inj
    (fun _ hp => h1.elim fun u hu' => Nat.lt_of_le_of_lt (Nat.zero_le u) (hp u hu'))
    (fun _ h0 hp => orZero h0 hp ht) (fun _ h0 hp u hm => orZero h0 hp (hu u hm))
    (fun v t' => add (hk v t')) hd

theorem reveal {ts : List Tok} {k : List Bits → Step S sp α}
    (ht : ∀ u ∈ ts, T u ∨ u = 0) (hk : ∀ w, LiveW ag T TP (k w)) :
    LiveW ag T TP (Step.reveal ts k) :=
  LiveWalk.reveal (fun _ h0 hp u hm => orZero h0 hp (ht u hm)) hk

/-- A reveal that names further tokens, live or dead, of whose strings what follows does not
depend. -/
theorem revealMore {ts more : List Tok} {k : List Bits → Step S sp α} (ht : ∀ u ∈ ts, T u ∨ u = 0)
    (hi : ∀ w x y : List Bits, w.length = ts.length → k (w ++ x) = k (w ++ y))
    (hk : ∀ w, LiveW ag T TP (k w)) :
    LiveW ag T TP (Step.reveal (ts ++ more) k) :=
  LiveWalk.revealMore (fun _ h0 hp u hm => orZero h0 hp (ht u hm)) hi hk

/-- One program after another. -/
theorem bind {c : Step S sp α} {g : α → Step S sp β} (hc : LiveW ag T TP c)
    (hg : ∀ a, LiveW ag (fun u => T u ∨ TP a u) TP' (g a)) : LiveW ag T TP' (c.bind g) :=
  LiveWalk.bind (monoP_allP T) hc fun a =>
    LiveWalk.imp (hg a) (fun _ hp u hu => hu.elim (hp.1 u) (hp.2 u)) fun _ _ hp => hp

/-- One program after another, where every value of the first part has G. -/
theorem bindG {G : α → Prop} {c : Step S sp α} {g : α → Step S sp β} (hc : LiveW ag T TP c)
    (he : Ends G c) (hg : ∀ a, G a → LiveW ag (fun u => T u ∨ TP a u) TP' (g a)) :
    LiveW ag T TP' (c.bind g) :=
  LiveWalk.bind (monoP_allP T) (LiveWalk.andEnds hc he) fun a =>
    LiveWalk.imp (LiveWalk.ofImp (G := G a) fun hG => hg a hG)
      (fun _ hp => ⟨hp.2.1, fun u hu => hu.elim (hp.1 u) (hp.2.2 u)⟩) fun _ _ hp => hp

/-- Sanity lemma and warning: with all tokens live nothing is said: it holds of every program. -/
theorem ofAll (c : Step S sp α) : LiveW ag (fun _ => True) TP c :=
  ⟨fun d _ _ _ hp => absurd rfl (hp d trivial),
    fun _ n _ hp => absurd (hp n trivial) (Nat.lt_irrefl n)⟩

/-- Sanity lemma: the program that reveals token 1, not live (T = {2}), and returns its string is no
`LiveW`. -/
theorem not_reveal :
    ¬ LiveW ag (fun u => u = 2) (fun _ _ => False)
      (Step.reveal [1] fun w => Step.pure w : Step S sp (List Bits)) := by
  intro h
  have h1 := (h.nu 1 3 (by decide) (by decide) fun u hu => by rw [hu]; decide).1 (fun _ => [])
    (fun u => if u = 1 then [true] else []) fun u hu => (if_neg (show ¬ u = 1 from hu)).symm
  have e : ([[]] : List Bits) = [if (1 : Tok) = 1 then [true] else []] := Step.pure.inj h1
  rw [if_pos rfl] at e
  exact absurd e (by decide)

/-- The end: `LiveWalk.erase` for `LiveW`. -/
theorem erase {γ : Type} {c : Step S sp α} (h : LiveW ag T TP c) (vs : List Bits)
    (hp : ∀ u, T u → u < vs.length) (g : α → OComp S γ) (hg : ∀ a, (g a).FactorsBy ag) :
    ((Compile.erase c vs).bind fun o => g o.1).FactorsBy ag :=
  LiveWalk.erase h vs hp g hg

end LiveW

end Compile
