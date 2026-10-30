-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/WrapBetween.lean: an oracle algorithm made to ask more: before each of its queries,
and at its end; with the law of its output and log, and the count of its questions. General in the
family of oracles: it imports the library's Rom/ alone.

WHY. A proof on a compiled part may need that a maker has asked some strings before others (for a
stored table with a record: the strings of the table's seeds before a first call that holds its
root). That order is no rare event: a maker can leave it out and lose nothing. It is had by wrapping
the maker. Under a fixed family of oracles the wrapped maker has the maker's output; its log is
longer. Here two wrappings
are made, for any family of oracles, so that they serve typed oracles and the one oracle on bit
strings alike.

Main definitions.
 `between pre A`        A made to ask, before each of its queries (o, q), what `pre o q` asks. Coins
                        and continuations are untouched.
 `lenB pre g σ`         the lengthened log: each entry with the log of what `pre` asks for it, under
                        g, put before it.
 `AsksFirst pre g σ`    "asks first", as a property of logs: σ is a lengthened log.
 `atEnd ask A`          A made to ask, at its end, what `ask` asks, given A's output AND its log.
 `AsksOnly P c`         on every path c asks only oracles with the property P.
Main theorems.
 `between_law`          THE LAW OF OUTPUT AND LOG: under every g, as a law over the coins: A's
                        output with A's log lengthened. Asked: `pre` tosses no coin.
 `between_bound`, `between_noCoin`   THE COUNT IS A FACTOR: t (1 + n) questions, if `pre` asks at
                        most n.
 `between_asksFirst`, `lenB_append`, `lenB_split`   every log of a run of `between pre A` asks
                        first; in a lengthened log what `pre` asks for a query of the log that was
                        lengthened stands before that query's entry.
 `mem_lenB`, `lenB_ans` every entry of a log is an entry of the lengthened log; the lengthened log
                        of a log with g's answers has g's answers.
 `asksFirst_before`     THE FORM THAT A PROOF ON LOGS CAN USE: before EVERY entry of a log that asks
                        first stands what `pre` asks for it, IF `pre` ASKS NOTHING FOR ITS OWN
                        QUERIES.
 `atEnd_law`, `atEnd_bound`   A's output, and A's log with the log of what is asked put behind it;
                        THE COUNT IS A SUMMAND: t + n.
 `asksOnly_log`         every entry of the log of an algorithm with `AsksOnly P` stands at an oracle
                        with P.
Tools: `runEager_bind_pure`, `runEager_withTrace_det`, `runEager_withTrace_query`,
`runEager_withTrace_self`, `support_withTrace_ans` (every entry of every log of a run under g holds
g's own answer), `withTrace_bound`.

What is not claimed. NO `pre` AND NO `ask` IS GIVEN: both are variables, and all content is in them:
at `pre` that asks nothing every log asks first. `pre` sees the query alone, not what was asked
before: it asks again at each query, also where the same was asked already; its own queries are not
wrapped: so "before each entry of the log stands what `pre` asks for it" holds only if `pre` asks
nothing for its own queries (`asksFirst_before`). `AsksFirst` says that the log falls into such
pieces; which of its entries are the maker's own is not read off the log. Nothing on what a part or
a checker reads off the longer log. No probability over oracles. Nothing on any protocol or hash
function.

-/
import Rom.OverOneN
import Rom.Cache
import Rom.Prefix

set_option autoImplicit false

namespace OnBytes.Slice
open Rom

variable {S : OSpec} {α β : Type}

/-! ## Tools: logs of algorithms without coins -/

/-- An algorithm and then a function of its value: the law is the image. -/
theorem runEager_bind_pure (g : Fam S) (c : OComp S α) (f : α → β) :
    (c.bind fun a => OComp.pure (f a)).runEager g = (c.runEager g).map f := by
  rw [OComp.runEager_bind, ← PMF.bind_pure_comp]
  rfl

/-- An algorithm without coins, with its log, has under g one outcome. -/
theorem runEager_withTrace_det (g : Fam S) (c : OComp S α) (hc : c.NoCoin) :
    c.withTrace.runEager g = PMF.pure (c.withTrace.det g) := by
  induction c with
  | pure a => rfl
  | query o q k ih =>
    show ((k (g o q)).withTrace.bind fun out =>
      OComp.pure (out.1, (⟨o, q, g o q⟩ : QA S) :: out.2)).runEager g =
        PMF.pure (((k (g o q)).withTrace.bind fun out =>
          OComp.pure (out.1, (⟨o, q, g o q⟩ : QA S) :: out.2)).det g)
    rw [runEager_bind_pure, ih _ (hc _), PMF.pure_map, OComp.det_bind]
    rfl
  | sample n k _ => exact hc.elim

/-- At a query: the entry in front of the log of what follows; as laws. -/
theorem runEager_withTrace_query (g : Fam S) (o : S.ι) (q : S.Dom o) (k : S.Rng o → OComp S α) :
    (OComp.query o q k).withTrace.runEager g =
      ((k (g o q)).withTrace.runEager g).map fun z => (z.1, (⟨o, q, g o q⟩ : QA S) :: z.2) :=
  runEager_bind_pure g _ _

/-- The log of the algorithm that outputs its own log is that log; as laws. -/
theorem runEager_withTrace_self (g : Fam S) (c : OComp S α) :
    c.withTrace.withTrace.runEager g = (c.withTrace.runEager g).map fun x => (x, x.2) := by
  induction c with
  | pure a =>
    show PMF.pure _ = (PMF.pure _).map _
    rw [PMF.pure_map]
  | query o q k ih =>
    show (((k (g o q)).withTrace.bind fun out =>
        OComp.pure (out.1, (⟨o, q, g o q⟩ : QA S) :: out.2)).withTrace.bind fun out =>
        OComp.pure (out.1, (⟨o, q, g o q⟩ : QA S) :: out.2)).runEager g =
      (((k (g o q)).withTrace.bind fun out =>
        OComp.pure (out.1, (⟨o, q, g o q⟩ : QA S) :: out.2)).runEager g).map _
    rw [Rom.withTrace_bind, OComp.runEager_bind, OComp.runEager_bind, OComp.runEager_bind, ih,
      PMF.map_bind, PMF.bind_map, PMF.bind_bind]
    refine congrArg _ (funext fun x => ?_)
    show ((OComp.pure _ : OComp S _).runEager g).bind _ = _
    simp [OComp.runEager, PMF.pure_bind, PMF.pure_map]
  | sample n k ih =>
    show ((PMF.uniformOfFintype (Fin (n + 1))).bind fun r =>
        (k r).withTrace.withTrace.runEager g) =
      ((PMF.uniformOfFintype (Fin (n + 1))).bind fun r => (k r).withTrace.runEager g).map _
    rw [PMF.map_bind]
    exact congrArg _ (funext fun r => ih r)

/-- Every entry of every log of a run under g holds g's own answer. -/
theorem support_withTrace_ans (g : Fam S) (c : OComp S α) :
    ∀ z ∈ (c.withTrace.runEager g).support, ∀ e ∈ z.2, e.2.2 = g e.1 e.2.1 := by
  induction c with
  | pure a =>
    intro z hz e he
    have hz' : z = (a, []) := by simpa [OComp.withTrace, OComp.runEager] using hz
    rw [hz'] at he
    exact absurd he List.not_mem_nil
  | query o q k ih =>
    intro z hz e he
    have hz' : z ∈ (((k (g o q)).withTrace.bind fun out =>
        OComp.pure (out.1, ⟨o, q, g o q⟩ :: out.2)).runEager g).support := hz
    rw [OComp.runEager_bind, PMF.mem_support_bind_iff] at hz'
    obtain ⟨y, hy, hzy⟩ := hz'
    have hz2 : z = (y.1, ⟨o, q, g o q⟩ :: y.2) := by simpa [OComp.runEager] using hzy
    rw [hz2] at he
    rcases List.mem_cons.1 he with rfl | h
    · rfl
    · exact ih _ y hy e h
  | sample n k ih =>
    intro z hz e he
    have hz' : z ∈ ((PMF.uniformOfFintype (Fin (n + 1))).bind fun r =>
        (k r).withTrace.runEager g).support := hz
    rw [PMF.mem_support_bind_iff] at hz'
    obtain ⟨r, -, hr⟩ := hz'
    exact ih r z hr e he

/-- The algorithm that also outputs its log asks no more. -/
theorem withTrace_bound (c : OComp S α) : ∀ t, c.QueryBound t → c.withTrace.QueryBound t := by
  induction c with
  | pure a => exact fun _ _ => trivial
  | query o q k ih =>
    intro t h
    cases t with
    | zero => exact h.elim
    | succ t => exact fun r => OComp.QueryBound.bind (t := 0) (ih r t (h r)) fun _ => trivial
  | sample n k ih => exact fun t h r => ih r t (h r)

/-- The algorithm asks only oracles with the property P, on every path. -/
def AsksOnly (P : S.ι → Prop) : OComp S α → Prop
  | .pure _ => True
  | .query o _ k => P o ∧ ∀ r, AsksOnly P (k r)
  | .sample _ k => ∀ r, AsksOnly P (k r)

/-- Then every entry of its log under g (at a coin: the first branch's) stands at such an oracle. -/
theorem asksOnly_log (P : S.ι → Prop) (g : Fam S) (c : OComp S α) (h : AsksOnly P c) :
    ∀ x ∈ (c.withTrace.det g).2, P x.1 := by
  induction c with
  | pure a => exact fun x hx => absurd hx List.not_mem_nil
  | query o q k ih =>
    intro x hx
    have e : ((OComp.query o q k).withTrace.det g).2 =
        (⟨o, q, g o q⟩ : QA S) :: ((k (g o q)).withTrace.det g).2 := by
      show (((k (g o q)).withTrace.bind fun out =>
        OComp.pure (out.1, (⟨o, q, g o q⟩ : QA S) :: out.2)).det g).2 = _
      rw [OComp.det_bind]
      rfl
    rw [e] at hx
    rcases List.mem_cons.1 hx with rfl | hx'
    · exact h.1
    · exact ih _ (h.2 _) x hx'
  | sample n k ih => exact ih 0 (h 0)

/-! ## Asking before each query -/

section
variable (pre : (o : S.ι) → S.Dom o → OComp S Unit)

/-- **The algorithm made to ask first**: before each of its queries, what `pre` asks for that query.
Its coins and its continuations are untouched. Where nothing is to be asked `pre` is `pure ()`. -/
def between : OComp S α → OComp S α
  | .pure a => .pure a
  | .query o q k => (pre o q).bind fun _ => .query o q fun r => between (k r)
  | .sample n k => .sample n fun r => between (k r)

/-- **The lengthened log**: each entry with the log of what `pre` asks for it, under g, put before
it. -/
def lenB (g : Fam S) : Trace S → Trace S
  | [] => []
  | e :: σ => ((pre e.1 e.2.1).withTrace.det g).2 ++ e :: lenB g σ

/-- The lengthened log of two logs, one behind the other. -/
theorem lenB_append (g : Fam S) : ∀ σ τ : Trace S,
    lenB pre g (σ ++ τ) = lenB pre g σ ++ lenB pre g τ
  | [], _ => rfl
  | e :: σ, τ => by
    show _ ++ e :: lenB pre g (σ ++ τ) = (_ ++ e :: lenB pre g σ) ++ lenB pre g τ
    rw [lenB_append g σ τ, List.append_assoc]
    rfl

/-- Every entry of a log is an entry of the lengthened log. -/
theorem mem_lenB (g : Fam S) : ∀ (σ : Trace S) (e : QA S), e ∈ σ → e ∈ lenB pre g σ
  | [], _, h => h
  | a :: σ, e, h => by
    show e ∈ _ ++ a :: lenB pre g σ
    rcases List.mem_cons.1 h with rfl | h
    · exact List.mem_append_right _ List.mem_cons_self
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (mem_lenB g σ e h))

/-- The lengthened log of a log with g's answers has g's answers. Asked: `pre` tosses no coin. -/
theorem lenB_ans (hn : ∀ o q, (pre o q).NoCoin) (g : Fam S) :
    ∀ σ : Trace S, (∀ e ∈ σ, e.2.2 = g e.1 e.2.1) → ∀ e ∈ lenB pre g σ, e.2.2 = g e.1 e.2.1
  | [], _, _, he => absurd he List.not_mem_nil
  | a :: σ, h, e, he => by
    have he' : e ∈ ((pre a.1 a.2.1).withTrace.det g).2 ++ a :: lenB pre g σ := he
    rcases List.mem_append.1 he' with h1 | h1
    · refine support_withTrace_ans g (pre a.1 a.2.1) _ ?_ e h1
      rw [runEager_withTrace_det g _ (hn a.1 a.2.1)]
      exact (PMF.mem_support_pure_iff _ _).2 rfl
    · rcases List.mem_cons.1 h1 with rfl | h2
      · exact h _ List.mem_cons_self
      · exact lenB_ans hn g σ (fun x hx => h x (List.mem_cons_of_mem _ hx)) e h2

/-- **THE LAW OF OUTPUT AND LOG**: under every g the output and the log of the algorithm made to ask
first are, as a law over the coins, the algorithm's output with its log lengthened. Asked: `pre`
tosses no coin. -/
theorem between_law (hn : ∀ o q, (pre o q).NoCoin) (g : Fam S) (A : OComp S α) :
    (between pre A).withTrace.runEager g =
      (A.withTrace.runEager g).map fun z => (z.1, lenB pre g z.2) := by
  induction A with
  | pure a =>
    show PMF.pure _ = (PMF.pure _).map _
    rw [PMF.pure_map]
    rfl
  | query o q k ih =>
    show ((pre o q).bind fun _ => OComp.query o q fun r => between pre (k r)).withTrace.runEager g
      = _
    rw [Rom.withTrace_bind, OComp.runEager_bind, runEager_withTrace_det g _ (hn o q),
      PMF.pure_bind, runEager_bind_pure, runEager_withTrace_query, runEager_withTrace_query, ih,
      PMF.map_comp, PMF.map_comp, PMF.map_comp]
    rfl
  | sample n k ih =>
    show ((PMF.uniformOfFintype (Fin (n + 1))).bind fun r =>
        (between pre (k r)).withTrace.runEager g) =
      ((PMF.uniformOfFintype (Fin (n + 1))).bind fun r => (k r).withTrace.runEager g).map _
    rw [PMF.map_bind]
    exact congrArg _ (funext fun r => ih r)

/-- **THE COUNT: A FACTOR**: if `pre` asks at most n questions, the algorithm made to ask first asks
at most t (1 + n). -/
theorem between_bound (n : ℕ) (hq : ∀ o q, (pre o q).QueryBound n) (A : OComp S α) :
    ∀ t, A.QueryBound t → (between pre A).QueryBound (t * (1 + n)) := by
  induction A with
  | pure a => exact fun _ _ => trivial
  | query o q k ih =>
    intro t ht
    cases t with
    | zero => exact ht.elim
    | succ t =>
      have h1 : (OComp.query o q fun r => between pre (k r)).QueryBound (t * (1 + n) + 1) :=
        fun r => ih r t (ht r)
      exact OComp.QueryBound.mono (OComp.QueryBound.bind (hq o q) fun _ => h1) (by
        rw [Nat.succ_mul]
        omega)
  | sample m k ih => exact fun t ht r => ih r t (ht r)

/-- It tosses no coin, if the algorithm and `pre` toss none. -/
theorem between_noCoin (hn : ∀ o q, (pre o q).NoCoin) (A : OComp S α) (hA : A.NoCoin) :
    (between pre A).NoCoin := by
  induction A with
  | pure a => trivial
  | query o q k ih => exact OComp.NoCoin.bind (hn o q) fun _ r => ih r (hA r)
  | sample m k _ => exact hA.elim

/-- **"Asks first", as a property of logs**: the log is a lengthened log: it falls into pieces, each
the log of what `pre` asks for a query, under g, and then the entry of that query. -/
def AsksFirst (g : Fam S) (σ : Trace S) : Prop := ∃ σ₀, σ = lenB pre g σ₀

/-- **Every log of an algorithm made to ask first has that property.** -/
theorem between_asksFirst (hn : ∀ o q, (pre o q).NoCoin) (g : Fam S) (A : OComp S α) :
    ∀ z ∈ ((between pre A).withTrace.runEager g).support, AsksFirst pre g z.2 := by
  intro z hz
  rw [between_law pre hn g A] at hz
  obtain ⟨y, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hz
  exact ⟨y.2, rfl⟩

/-- In a lengthened log, before the entry of each query of the log stands what `pre` asks for it. -/
theorem lenB_split (g : Fam S) (σ τ : Trace S) (e : QA S) :
    lenB pre g (σ ++ e :: τ) =
      lenB pre g σ ++ ((pre e.1 e.2.1).withTrace.det g).2 ++ e :: lenB pre g τ := by
  rw [lenB_append, List.append_assoc]
  rfl

/-- **THE FORM THAT A PROOF ON LOGS CAN USE: before EVERY entry of a log that asks first stands what
`pre` asks for it.** Asked: `pre` asks nothing for its own queries (`idle`). Without that it is
false: the entries of what `pre` asks are entries of the log too, and they are not wrapped. -/
theorem asksFirst_before (g : Fam S) (σ : Trace S) (h : AsksFirst pre g σ)
    (idle : ∀ o q, ∀ x ∈ ((pre o q).withTrace.det g).2,
      ((pre x.1 x.2.1).withTrace.det g).2 = []) :
    ∀ a e b, σ = a ++ e :: b → ∀ x ∈ ((pre e.1 e.2.1).withTrace.det g).2, x ∈ a := by
  obtain ⟨σ₀, rfl⟩ := h
  induction σ₀ with
  | nil =>
    intro a e b hs
    exact absurd (congrArg List.length hs) (by simp [lenB])
  | cons e₀ σ' ih =>
    intro a e b hs x hx
    have hs' : ((pre e₀.1 e₀.2.1).withTrace.det g).2 ++ e₀ :: lenB pre g σ' = a ++ e :: b := hs
    rcases List.append_eq_append_iff.1 hs' with ⟨a', ha, hb⟩ | ⟨c', hc, hd⟩
    · cases a' with
      | nil =>
        rw [List.nil_append] at hb
        rw [ha, List.append_nil, (List.cons.inj hb).1]
        exact hx
      | cons y a'' =>
        have hb' := List.cons.inj hb
        rw [ha]
        exact List.mem_append_right _ (List.mem_cons_of_mem _ (ih a'' e b hb'.2 x hx))
    · cases c' with
      | nil =>
        rw [List.nil_append] at hd
        rw [List.append_nil] at hc
        rw [← hc, ← (List.cons.inj hd).1]
        exact hx
      | cons y c'' =>
        have hy := (List.cons.inj hd).1
        have he : e ∈ ((pre e₀.1 e₀.2.1).withTrace.det g).2 := by
          rw [hc, hy]
          exact List.mem_append_right _ List.mem_cons_self
        rw [idle e₀.1 e₀.2.1 e he] at hx
        exact absurd hx List.not_mem_nil

end

/-! ## Asking at the end -/

section
variable (ask : α × Trace S → OComp S Unit)

/-- **The algorithm made to ask at its end**: what `ask` asks, given the algorithm's output AND its
log. Its output is the algorithm's. -/
def atEnd (A : OComp S α) : OComp S α :=
  A.withTrace.bind fun x => (ask x).bind fun _ => .pure x.1

/-- **THE LAW OF OUTPUT AND LOG**: the algorithm's output, and its log with the log of what is asked
put behind it. Asked: `ask` tosses no coin. -/
theorem atEnd_law (hn : ∀ x, (ask x).NoCoin) (g : Fam S) (A : OComp S α) :
    (atEnd ask A).withTrace.runEager g =
      (A.withTrace.runEager g).map fun z => (z.1, z.2 ++ ((ask z).withTrace.det g).2) := by
  unfold atEnd
  rw [Rom.withTrace_bind, OComp.runEager_bind, runEager_withTrace_self, PMF.bind_map,
    ← PMF.bind_pure_comp]
  refine congrArg _ (funext fun x => ?_)
  show ((((ask x).bind fun _ => (OComp.pure x.1 : OComp S α)).withTrace.bind fun out' =>
    OComp.pure (out'.1, x.2 ++ out'.2)).runEager g) = PMF.pure _
  rw [runEager_bind_pure, Rom.withTrace_bind, OComp.runEager_bind,
    runEager_withTrace_det g _ (hn x), PMF.pure_bind]
  show (PMF.pure _).map _ = _
  rw [PMF.pure_map]
  show PMF.pure (x.1, x.2 ++ (((ask x).withTrace.det g).2 ++ [])) = _
  rw [List.append_nil]

/-- **THE COUNT: A SUMMAND.** -/
theorem atEnd_bound (n : ℕ) (hq : ∀ x, (ask x).QueryBound n) (A : OComp S α) (t : ℕ)
    (hA : A.QueryBound t) : (atEnd ask A).QueryBound (t + n) :=
  OComp.QueryBound.bind (withTrace_bound A t hA) fun x =>
    OComp.QueryBound.bind (t := 0) (hq x) fun _ => trivial

end

end OnBytes.Slice

