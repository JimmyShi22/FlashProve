-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/MemberOne.lean: the four sorts of a lookup's place as one: what
Honest/K3/Law/MemberYesAt.lean [not in this library] says in four theorems, one for each form of the
sub-protocol's decision, said once, with
the form read off the link's number and the lookup's sort by the verifier's own text (`quietAt`,
Johnson/Desc/First/Look/K3Whole.lean). Conditional, as that file's theorems are. Theorems, with
definitions.

Terms. Honest/K3/GLOSSARY.md ("decision", "member", "seat", "sort", "step without a round",
"sub-protocol").

What is shown.
  `QuietBehind`, `behind_keeps`: what stands behind the seated decision at link i's lookup: nothing,
    or the step without a round that the verifier's text lays there; an acceptance by it changes
    neither the reply's part nor the mark.
  `FormAt`, `formAt_of`, `formAt_blind`: the sub-protocol's rounds and decision at (i, digits, p);
    every sub-protocol of which `DecidesFrom` holds has it; such a sub-protocol decides without
    reading a sealed digest.
  `decide_behind`: the sub-protocol's decision accepts where the seated decision does and
    `QuietBehind` holds.
  `accepts_any`: the two theorems of Honest/K3/Law/SeatedAll.lean at the two seats, as one.
  `OneQ`, `BehindReturns`, `joined_one`, `member_one`: the sentence on the state behind the step;
    what is asked of the step behind the lookup (it returns at every state that the seated decision
    can leave); the composition at the lot's sub-protocol, and at the description's member.
  `behind_exists`: the step behind returns: from public numbers alone at every sort of place but
    one; at the digits of the head's link from the named hypothesis `HeadBehind`.

Hypotheses that remain. Each theorem's docstring names its own. By name, in `joined_one` and
`member_one`:
  `Fm`: the sub-protocol has the form `FormAt`. `hp`, `hN`: the place's parameters make the shape h;
    it has more than one call. `ha`: the face is that shape's.
  `hpl`, `hr`, `ho`, `hrd`: the sub-protocol stands at the place; its rounds are the entries'; it
    states no oracle message; the row has as many moves as it has rounds.
  `hS`, `hL`: `Stands` and `LedgerIn` (Honest/K3/Law/Top.lean). `hF`, `h0`, `hO`: of the verifier's
    state in front: the ledger is open, nothing was heard yet, no row waits.
  `hB`: `BehindReturns`.
  In `member_one` besides: `O`: the description returns (`IM.Open`); `hbl`: b is one of the lot's
    sub-protocols; `hm`, `hmp`: m is a member of the first chain's flat list, at b's place; `hs0`:
    no mark in front.
  In `accepts_any`: `hp`, `hN`, `hF`, `h0`, `hO`, and `hn`, `hh`: the ledger's next slot is the
    place's first; `hearV` returns. In `decide_behind`: `Fm`, `hl`, `hd`, `hB`: as many rounds as
    the parameters state; the seated decision accepts; `QuietBehind`. In `behind_keeps`: `h`:
    `QuietBehind`. In `formAt_of`: `H`: `DecidesFrom`.
  In `behind_exists`: `a1`, `hsh`, `a2`, `hn`: what the seat reads at s' as heard, its shape, the
    ledger and its next slot; `hlook`, `hlay`, `hatt`: a public test at each of three sorts of
    place; `hhead`: at the digits of the head's link `HeadBehind`.

Users. This file is imported by Honest/K3/Law/BehindHands.lean and Honest/K3/Law/MemberSite.lean.

Limits. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.MemberYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes.Model (Fork Aff)
open OnBytes.Model.Forest (Shape)
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc (Block Chain FileDescription Place OpenedColumn)
open VerifiableInference.Desc.K3 (HeardV hearV faceOf toHeard toHeardG seatCalls seatDigits quietAt
  quietHead
  quietLook quietDigits isHead)
open VerifiableInference.Desc.K3.Law (decideVia)
open VerifiableInference.Desc.First.Look (P sameShape)

local notation "FS" => VerifiableInference.Desc.First.S

variable {V₁ W₁ X₁ W : Type}

/-! ## 1 What stands behind the seated decision -/

/-- **From the state s' that the seated decision leaves to the state t that the sub-protocol's
decision leaves**, at link i's lookup on the digits (d) or on the calls: nothing stands there, or
the verifier's step without a round returns t. -/
def QuietBehind (X : OnBytes.Model.Verify.Public) (i : Nat) (d : Bool) (s' t : FS) : Prop :=
  match quietAt X i d with
  | none => t = s'
  | some f => f s' = .ok t

/-- It changes neither the part of the state that holds the reply nor the mark.
Conditional on `QuietBehind`. -/
theorem behind_keeps {X : OnBytes.Model.Verify.Public} {i : Nat} {d : Bool} {s' t : FS}
    (h : QuietBehind X i d s' t) : t.out = s'.out ∧ t.failed = s'.failed := by
  unfold QuietBehind at h
  cases hq : quietAt X i d with
  | none =>
    rw [hq] at h
    have e : t = s' := h
    rw [e]
    exact ⟨rfl, rfl⟩
  | some f =>
    rw [hq] at h
    exact quietAt_keeps X i d f hq s' t h

/-- **A sub-protocol's rounds and decision at link i's lookup with the parameters p.** -/
structure FormAt {Cl : Type} (claim : Aff → Cl) (X : OnBytes.Model.Verify.Public) (i : Nat)
    (d : Bool)
    (p : P) (b : Block FS Cl) : Prop where
  rounds : b.rounds = p.rounds
  form : (quietAt X i d = none ∧
      ∀ s rs gs, b.decide s rs gs = decideVia (seatOf claim d) p s rs) ∨
    ∃ f, quietAt X i d = some f ∧ ∀ s rs gs, b.decide s rs gs =
      (decideVia (seatOf claim d) p s (rs.take p.rounds.length)).bind f

/-- Every sub-protocol of which `DecidesFrom` holds, whole, has such a form, at the address's own
link, sort and parameters. Conditional on `DecidesFrom`. -/
theorem formAt_of {Cl : Type} {claim : Aff → Cl} {X : OnBytes.Model.Verify.Public} {a : Place}
    {b : Block FS Cl} (H : DecidesFrom claim X a b true) :
    ∃ i d p, a.link = some i ∧ a.piece = VerifiableInference.Desc.K3.pieceAt X i d ∧
      VerifiableInference.Desc.First.Look.placeAt X i d = some p ∧ FormAt claim X i d p b := by
  obtain ⟨i, d, p, h1, h2, h3, h4, h5⟩ := H
  refine ⟨i, d, p, h1, h2, h3, h4, ?_⟩
  rcases h5 with ⟨hq, hb⟩ | ⟨_, f, hq, hb⟩
  · rcases hq with hq | hq
    · exact nomatch hq
    · exact Or.inl ⟨hq, hb⟩
  · exact Or.inr ⟨f, hq, hb⟩

/-- **The sub-protocol's decision accepts** where the seated decision does, on as many rounds as the
parameters state, and what stands behind it returns. Conditional on these. -/
theorem decide_behind {Cl : Type} {claim : Aff → Cl} {X : OnBytes.Model.Verify.Public} {i : Nat}
    {d : Bool} {p : P} {b : Block FS Cl} (Fm : FormAt claim X i d p b) {s s' t : FS}
    {rs : List Fmt.RoundView} (gs : List (List (Nat × List UInt64))) (hl : rs.length = p.rounds.length)
    (hd : decideVia (seatOf claim d) p s rs = .ok s') (hB : QuietBehind X i d s' t) :
    b.decide s rs gs = .ok t := by
  unfold QuietBehind at hB
  rcases Fm.form with ⟨hq, hb⟩ | ⟨f, hq, hb⟩
  · rw [hq] at hB
    have e : t = s' := hB
    rw [hb, hd, e]
  · rw [hq] at hB
    rw [hb, ← hl, List.take_length, hd]
    exact hB

/-- Such a sub-protocol decides without reading a sealed digest.
Conditional on the form. -/
theorem formAt_blind {Cl : Type} {claim : Aff → Cl} {X : OnBytes.Model.Verify.Public} {i : Nat}
    {d : Bool} {p : P} {b : Block FS Cl} (Fm : FormAt claim X i d p b) : DecidesBlind b := by
  intro s rs gs
  rcases Fm.form with ⟨_, h⟩ | ⟨f, _, h⟩
  · rw [h, h, ProofFile.Honest.K3.NoDigest.decideVia_noDigest]
  · rw [h, h, ← List.map_take, ProofFile.Honest.K3.NoDigest.decideVia_noDigest]

/-- **The seated decision accepts and the seat holds what was heard**, at either seat. Conditional
on the place's shape; several calls; the seat's three in front; the count of slots; and the return
of `hearV`. -/
theorem accepts_any {Cl : Type} (claim : Aff → Cl) (d : Bool) (p : P) (h : Shape) (s : FS)
    {F G : Fork}
    {rs : List Fmt.RoundView} {g : HeardV} (hp : p.shape = some h) (hN : 1 < h.NC)
    (hF : (seatOf claim d).fork s = some F) (h0 : ((seatOf claim d).heard s).isNone = true)
    (hO : ((seatOf claim d).owed s).noneWaits = true) (hn : F.next = p.first)
    (hh : hearV (faceOf h) F rs = some (g, G)) :
    ∃ g' s', toHeard h (toHeardG g) = some g' ∧ decideVia (seatOf claim d) p s rs = .ok s' ∧
      (seatOf claim d).heard s' = some g' ∧ (seatOf claim d).fork s' = some G ∧
      s'.failed = s.failed := by
  cases d with
  | false => exact calls_accepts claim p h s hp hN hF h0 hO hn hh
  | true => exact digits_accepts claim p h s hp hN hF h0 hO hn hh

/-! ## 2 The composition, once -/

/-- **The sentence on the state behind the sub-protocol's step**: there is a state s' at which the
seat reads, as heard, the structure made of what `hearV` returned, and the ledger behind the
hearing; its mark is that in front; and `QuietBehind` leads from s' to the state behind the step. s'
is bound by "∃": some state of the verifier's between two steps, held by what readers return of it;
there is no equation on it. -/
def OneQ {Cl : Type} (claim : Aff → Cl) (X : OnBytes.Model.Verify.Public) (i : Nat) (d : Bool)
    (h : Shape)
    (s : FS) : FS → HeardV → Fork → Prop := fun t g G =>
  ∃ g' s', toHeard h (toHeardG g) = some g' ∧ (seatOf claim d).heard s' = some g' ∧
    (seatOf claim d).fork s' = some G ∧ s'.failed = s.failed ∧ QuietBehind X i d s' t

/-- What is asked of the step behind the lookup: it returns at every state that the seated
decision can leave. -/
def BehindReturns {Cl : Type} (claim : Aff → Cl) (X : OnBytes.Model.Verify.Public) (i : Nat)
    (d : Bool)
    (p : P) (h : Shape) (n : Nat) (s : FS) (F : Fork) : Prop :=
  ∀ (rs : List Fmt.RoundView) (g : HeardV) (G : Fork) (g' : OnBytes.Model.Forest.Heard) (s' : FS),
    rs.length = n → hearV (faceOf h) F rs = some (g, G) → toHeard h (toHeardG g) = some g' →
    decideVia (seatOf claim d) p s rs = .ok s' → (seatOf claim d).heard s' = some g' →
    (seatOf claim d).fork s' = some G → ∃ t, QuietBehind X i d s' t

/-- **The composition at a sub-protocol of the form.** Conditional on what `joined_of`
(Honest/K3/Law/Joined.lean) asks; its hypothesis on the decision's acceptance is shown from: the
form; the place's shape; several calls; the seat's three in front; as many rounds as entries; and
`BehindReturns`. No instance of these hypotheses is exhibited in this file. -/
theorem joined_one {Cl : Type} (claim : Aff → Cl) (X : OnBytes.Model.Verify.Public) (i : Nat)
    (d : Bool)
    (p : P) (h : Shape) (b : Block FS Cl) (Fm : FormAt claim X i d p b) (a : At)
    (ha : a.face = faceOf h) (J : LookJobs W) (wit : W₁ → W) (v : Option V₁) (es : List Fmt.Entry)
    (hpl : b.place = a.place) (hr : b.rounds = es.map declOf) (ho : b.oracles = es.map fun _ => [])
    (mid : Mid W₁ X₁) (ds : List Fmt.Drawn)
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit a).parts)
    (hrd : (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit a).rounds = b.rounds.length)
    (s : FS) (F : Fork) (hS : Stands a es mid ds) (hL : LedgerIn a.face p.first F)
    (hp : p.shape = some h) (hN : 1 < h.NC) (hF : (seatOf claim d).fork s = some F)
    (h0 : ((seatOf claim d).heard s).isNone = true)
    (hO : ((seatOf claim d).owed s).noneWaits = true)
    (hB : BehindReturns claim X i d p h es.length s F) (chain ft : Nat)
    (stored : Nat → Nat → Option (List UInt64)) (tree : Fmt.TreeSource → Option (Place × Table)) :
    JoinedAt b a J wit v mid ds c p.first s F chain ft stored tree (OneQ claim X i d h s) := by
  have hpr : p.rounds.length = es.length := by rw [← Fm.rounds, hr, List.length_map]
  refine joined_of _ h p.first b (formAt_blind Fm) a ha J wit v es hpl hr ho mid ds c hrd s F hS hL
    (fun rs g G gs hl hh => ?_) chain ft stored tree
  obtain ⟨g', s', hg, hd, a1, a2, a3⟩ := accepts_any claim d p h s hp hN hF h0 hO hL.next hh
  obtain ⟨t, ht⟩ := hB rs g G g' s' hl hh hg hd a1 a2
  exact ⟨t, decide_behind Fm gs (hl.trans hpr.symm) hd ht, g', s', hg, a1, a2, a3, ht⟩

/-- **The description's own member, once.** Conditional on the description's return (`IM.Open`); b
the lot's sub-protocol, m the member at its place; the form; all that `joined_one` asks; and no mark
in front. No instance of these hypotheses is exhibited in this file. -/
theorem member_one (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (b m : Block FS ProofFile.Cl)
    (hbl : b ∈ (K3Lot.lot Z).blocks Bs.G₀) (hm : m ∈ ch.blocksInOrder) (hmp : m.place = b.place)
    (claim : Aff → ProofFile.Cl) (X : OnBytes.Model.Verify.Public) (i : Nat) (d : Bool) (p : P)
      (h : Shape)
    (Fm : FormAt claim X i d p b) (a : At) (ha : a.face = faceOf h) (J : LookJobs W) (wit : W₁ → W)
    (v : Option V₁) (es : List Fmt.Entry) (hpl : b.place = a.place) (hr : b.rounds = es.map declOf)
    (ho : b.oracles = es.map fun _ => []) (mid : Mid W₁ X₁) (ds : List Fmt.Drawn)
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit a).parts)
    (hrd : (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit a).rounds = b.rounds.length)
    (s : FS) (F : Fork) (hS : Stands a es mid ds) (hL : LedgerIn a.face p.first F)
    (hp : p.shape = some h) (hN : 1 < h.NC) (hF : (seatOf claim d).fork s = some F)
    (h0 : ((seatOf claim d).heard s).isNone = true)
    (hO : ((seatOf claim d).owed s).noneWaits = true)
    (hB : BehindReturns claim X i d p h es.length s F) (hs0 : s.failed = none) (chain ft : Nat)
    (stored : Nat → Nat → Option (List UInt64)) (tree : Fmt.TreeSource → Option (Place × Table)) :
    JoinedAt m a J wit v mid ds c p.first s F chain ft stored tree (OneQ claim X i d h s) :=
  joinedAt_site o pol lay KL Fd Z Bs base ch A B O b m hbl hm hmp a J wit v mid ds c p.first s F
    chain
    ft stored tree _
    (fun t _ _ ⟨_, s', _, _, _, hf, hb⟩ => by rw [(behind_keeps hb).2, hf, hs0])
    (joined_one claim X i d p h ({ b with name := m.name } : Block FS ProofFile.Cl) ⟨Fm.rounds, Fm.form⟩ a
      ha
      J wit v es hpl hr ho mid ds c hrd s F hS hL hp hN hF h0 hO hB chain ft stored tree)

/-! ## 3 The step behind returns -/

/-- **What stands behind the lookup returns.** n: the number of the first slot behind the lookup's
hidden values. Conditional on: what was heard stored at the seat, with the shape h; the ledger open,
its count of slots at n; the public numbers of the place's sort; and, at the digits of the head's
link, the named hypothesis that the step there returns. -/
theorem behind_exists {Cl : Type} (claim : Aff → Cl) (X : OnBytes.Model.Verify.Public) (i : Nat)
    (d : Bool)
    (h : Shape) (n : Nat) (s' : FS) {g' : OnBytes.Model.Forest.Heard} {G : Fork}
    (a1 : (seatOf claim d).heard s' = some g') (hsh : g'.shape = h)
    (a2 : (seatOf claim d).fork s' = some G) (hn : G.next = n)
    (hlook : d = false → isHead X i = false → (i % (if X.p4 then 2 else 1) == 0) = true →
      sameShape h X.y.fo = true)
    (hlay : d = true → isHead X i = false → (i % (if X.p4 then 2 else 1) == 0) = true →
      ∀ hp, X.G[i / (if X.p4 then 2 else 1)]? = some hp → hp.used = n)
    (hatt : d = true → isHead X i = false → ¬ (i % (if X.p4 then 2 else 1) == 0) = true →
      ∀ a, X.A[i / (if X.p4 then 2 else 1)]? = some a → a.nMsg = n)
    (hhead : d = true → isHead X i = true → ∃ t, HeadBehind X s' t) :
    ∃ t, QuietBehind X i d s' t := by
  have a2' : s'.fork? = some G := by cases d <;> exact a2
  unfold QuietBehind
  cases hq : quietAt X i d with
  | none => exact ⟨s', rfl⟩
  | some f =>
    show ∃ t, f s' = .ok t
    unfold quietAt at hq
    dsimp only at hq
    by_cases hH : isHead X i = true
    · rw [if_pos hH] at hq
      cases d with
      | false =>
        rw [if_neg (by simp)] at hq
        cases hq
      | true =>
        rw [if_pos rfl] at hq
        obtain rfl := Option.some.inj hq
        exact hhead rfl hH
    · rw [if_neg hH] at hq
      have hH' : isHead X i = false := by simpa using hH
      generalize (if X.p4 = true then 2 else 1) = st at hq hlook hlay hatt
      by_cases hm : (i % st == 0) = true
      · rw [if_pos hm] at hq
        cases d with
        | true =>
          rw [if_pos rfl] at hq
          obtain ⟨hp, hg, rfl⟩ := Option.map_eq_some_iff.1 hq
          exact ⟨_, quietDigits_returns _ _ s' a2' (hn.trans (hlay rfl hH' hm hp hg).symm)⟩
        | false =>
          rw [if_neg (by simp)] at hq
          obtain rfl := Option.some.inj hq
          exact ⟨_, quietLook_returns _ s' a1 (by rw [hsh]; exact hlook rfl hH' hm)⟩
      · rw [if_neg hm] at hq
        cases d with
        | true =>
          rw [if_pos rfl] at hq
          obtain ⟨a, hg, rfl⟩ := Option.map_eq_some_iff.1 hq
          exact ⟨_, quietDigits_returns _ _ s' a2' (hn.trans (hatt rfl hH' hm a hg).symm)⟩
        | false =>
          rw [if_neg (by simp)] at hq
          cases hq

#print axioms ProofFile.Honest.K3.Law.behind_keeps
#print axioms ProofFile.Honest.K3.Law.formAt_of
#print axioms ProofFile.Honest.K3.Law.decide_behind
#print axioms ProofFile.Honest.K3.Law.formAt_blind
#print axioms ProofFile.Honest.K3.Law.accepts_any
#print axioms ProofFile.Honest.K3.Law.joined_one
#print axioms ProofFile.Honest.K3.Law.member_one
#print axioms ProofFile.Honest.K3.Law.behind_exists

end ProofFile.Honest.K3.Law
