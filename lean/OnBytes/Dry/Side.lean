-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Dry/Side.lean: THE PROVER's CHAIN AT TWO STRATEGIES, SIDE BY SIDE (TiedL,
Rom/Dry/Tied.lean): the two runs ask the same plain queries, and deferred queries of the same
oracles; and on the runs whose verifier messages lie in a set G on which the two strategies agree,
the two logs hold the same entries but for leaves, and the two runs keep the same as far as a proof
string shows it.

General lemmas. This file states no goal of the release. It serves OnBytes/Dry/View.lean.

How. One walk along the program's text (chainO, OnBytes/Prover/Defs.lean), part by part, as in
OnBytes/Dry/Control.lean. The leaves of trees are deferred, so both runs get the same digests
whatever the leaves hold; so all inner nodes are asked at the same points, and both runs have the
same roots. The climb in the request tree starts from an answer, so it is one program in both runs.
What else is asked is deferred, and its points hold: roots, chain values, the slot value (the same
in both runs), and plain parts, the first salt, the string behind the slot value.

G is a set of verifier messages, a letter. Where G has a member, the two strategies' first messages
have the same plain part, and the coins are the same, so these points are the same too. After a
round's verifier message c the walk goes on with the slice of G at c; if the slice is empty, nothing
more is claimed of the logs. At G = "nothing" this is the statement for ANY two strategies; at
G = {ρ₀} the statement for two strategies with one view at ρ₀.

Main names.
  TL, Lg         TiedL over the typed oracles, "deferred" by the name; the relation on logs: if "on"
                 holds, the same kept entries.
  tl_ask .. tl_fsO, tl_onFs   the parts.
  PutRel, FsRel  what two searches return: both nothing; or one answer, and the plain parts with ONE
                 number written in.
  RG             the relation at the chain's end.
  puts_lo, puts_sh   a number written into the plain parts, at a round with its own component and at
                 a shared round.
The walk itself (tied_chainO) is in OnBytes/Dry/Walk.lean.

Limits. One slot, one chain. rd, which positions count as read, is a letter.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Dry.Same
import OnBytes.Dry.Control
import Rom.Dry.Tied
import OnBytes.Prover.Step

set_option autoImplicit false

namespace OnBytes.Dry
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- The names of the typed oracles. -/
local notation "ON₂" => TypedOracleCompiler.Compile.Batch.OracleName

/-- The second form's answers of a Fiat-Shamir oracle. -/
local notation "FsAns₂" => TypedOracleCompiler.Compile.Batch.FsAns

/-- Side by side, over the typed oracles, "deferred" by the oracle's name. -/
abbrev TL (m : ON₂ → Bool) {α β : Type}
    (R : α → Trace (typedOracleFamily lam K L) → β → Trace (typedOracleFamily lam K L) → Prop)
    (l l' : Trace (typedOracleFamily lam K L)) (c : TypedOracleComputation lam K L α) (c' : TypedOracleComputation lam K L β) : Prop :=
  TiedL (S := typedOracleFamily lam K L) (fun o _ => m o) R l l' c c'

/-! ## The relation on logs -/

/-- If "on" holds, the two logs have the same kept entries. -/
def Lg (on : Prop) (keep : QA (typedOracleFamily lam K L) → Bool) (l l' : Trace (typedOracleFamily lam K L)) : Prop :=
  on → l.filter keep = l'.filter keep

theorem Lg.same {on : Prop} {keep : QA (typedOracleFamily lam K L) → Bool} {l l' : Trace (typedOracleFamily lam K L)}
    {e e' : QA (typedOracleFamily lam K L)} (he : on → e = e') (h : Lg on keep l l') :
    Lg on keep (l ++ [e]) (l' ++ [e']) := fun ho => by
  rw [List.filter_append, List.filter_append, h ho, he ho]

theorem Lg.drop {on : Prop} {keep : QA (typedOracleFamily lam K L) → Bool} {l l' : Trace (typedOracleFamily lam K L)}
    {e e' : QA (typedOracleFamily lam K L)} (he : keep e = false) (he' : keep e' = false)
    (h : Lg on keep l l') : Lg on keep (l ++ [e]) (l' ++ [e']) := fun ho => by
  rw [List.filter_append, List.filter_append, h ho]
  simp [List.filter_cons, he, he']

theorem Lg.same1 {on : Prop} {keep : QA (typedOracleFamily lam K L) → Bool} (l l' : Trace (typedOracleFamily lam K L))
    (e : QA (typedOracleFamily lam K L)) (h : Lg on keep l l') : Lg on keep (l ++ [e]) (l' ++ [e]) :=
  Lg.same (fun _ => rfl) h

/-! ## What two searches return -/

/-- β and β' are α and α' with one number written in; themselves where there is no test. -/
def PutRel {C P : Type} : Option (GrW C P) → P → P → P → P → Prop
  | none, α, α', β, β' => β = α ∧ β' = α'
  | some g, α, α', β, β' => ∃ n, β = g.put n α ∧ β' = g.put n α'

theorem PutRel.eq {C P : Type} {gr : Option (GrW C P)} {α α' β β' : P} (e : α = α')
    (h : PutRel gr α α' β β') : β = β' := by
  subst e
  cases gr with
  | none =>
    obtain ⟨h1, h2⟩ := h
    rw [h1, h2]
  | some g =>
    obtain ⟨n, h1, h2⟩ := h
    rw [h1, h2]

/-- Both searches have run out; or both return one answer, and plain parts with one number. -/
def FsRel {C P : Type} (gr : Option (GrW C P)) (α α' : P)
    (u v : Option (P × FsAns₂ lam K)) : Prop :=
  (u = none ∧ v = none) ∨ ∃ β β' a, u = some (β, a) ∧ v = some (β', a) ∧ PutRel gr α α' β β'

section Parts
variable (m : ON₂ → Bool) (on : Prop) (keep : QA (typedOracleFamily lam K L) → Bool)

/-! ## The parts -/

/-- one deferred query to one oracle -/
theorem tl_ask (o : ON₂) (ho : m o = true) (q q' : domOf lam L o) {l l' : Trace (typedOracleFamily lam K L)}
    (hs : ∀ r : rngOf lam K o, Lg on keep (l ++ [(⟨o, q, r⟩ : QA (typedOracleFamily lam K L))])
      (l' ++ [(⟨o, q', r⟩ : QA (typedOracleFamily lam K L))])) :
    TL m (fun r l₁ r' l₁' => r = r' ∧ Lg on keep l₁ l₁') l l' (askTypedOracle (L := L) (K := K) o q)
      (askTypedOracle (L := L) (K := K) o q') :=
  TiedL.both (S := typedOracleFamily lam K L) ho ho fun r => .done ⟨rfl, hs r⟩

/-- one program in both runs -/
theorem tl_refl {α : Type} (c : TypedOracleComputation lam K L α) (l l' : Trace (typedOracleFamily lam K L))
    (h : Lg on keep l l') : TL m (fun a l₁ b l₁' => a = b ∧ Lg on keep l₁ l₁') l l' c c :=
  TiedL.refl (S := typedOracleFamily lam K L) (fun l l' e h => Lg.same1 l l' e h) c l l' h

variable (hleaf : m .leaf = true)
  (hkeep : ∀ (q : LeafIn L) (r : Dig lam), keep (⟨OracleName.leaf, q, r⟩ : QA (typedOracleFamily lam K L)) = false)
include hleaf hkeep

theorem tl_leavesO : ∀ xs ys : List (LeafIn L), xs.length = ys.length →
    ∀ l l' : Trace (typedOracleFamily lam K L), Lg on keep l l' →
    TL m (fun u l₁ v l₁' => u = v ∧ Lg on keep l₁ l₁') l l'
      (leavesO (lam := lam) (K := K) xs) (leavesO (lam := lam) (K := K) ys)
  | [], [], _, _, _, h => .done ⟨rfl, h⟩
  | x :: xs, y :: ys, e, l, l', h =>
    TiedL.bind (tl_ask m on keep OracleName.leaf hleaf x y fun r => Lg.drop (hkeep _ _) (hkeep _ _) h)
      fun a l₁ b l₁' hab =>
      TiedL.bind (tl_leavesO xs ys (by simpa using e) l₁ l₁' hab.2) fun us l₂ vs l₂' huv =>
        .done ⟨by rw [hab.1, huv.1], huv.2⟩
  | [], _ :: _, e, _, _, _ => by simp at e
  | _ :: _, [], e, _, _, _ => by simp at e

theorem tl_treeO (d : ℕ) (inp inp' : ℕ → LeafIn L) (l l' : Trace (typedOracleFamily lam K L))
    (h : Lg on keep l l') :
    TL m (fun T l₁ T' l₁' => (T.lv = T'.lv ∧ T.inp = inp ∧ T'.inp = inp') ∧ Lg on keep l₁ l₁') l l'
      (treeO (lam := lam) (K := K) d inp) (treeO (lam := lam) (K := K) d inp') :=
  TiedL.bind (tl_leavesO m on keep hleaf hkeep _ _ (by simp) l l' h) fun u l₁ v l₁' huv => by
    obtain ⟨rfl, h₁⟩ := huv
    exact TiedL.bind (tl_refl m on keep _ l₁ l₁' h₁) fun lv l₂ lv' l₂' hlv =>
      .done ⟨⟨hlv.1, rfl, rfl⟩, hlv.2⟩

theorem tl_treesO {r : Round} (pad pad' : Body L) (sl sl' : ℕ → ℕ → Bits)
    (posAt : ℕ → ℕ → Option r.Pos) (emb : (p : r.Pos) → r.Sym p → Body L) (o o' : r.Orc) :
    ∀ (k : ℕ) (ds : List ℕ) (l l' : Trace (typedOracleFamily lam K L)), Lg on keep l l' →
      TL m (fun Ts l₁ Ts' l₁' =>
          TreesAt (leafAt pad sl posAt emb o) (leafAt pad' sl' posAt emb o') k Ts Ts' ∧
            Lg on keep l₁ l₁') l l'
        (treesO (lam := lam) (K := K) pad sl posAt emb o k ds)
        (treesO (lam := lam) (K := K) pad' sl' posAt emb o' k ds)
  | _, [], _, _, h => .done ⟨trivial, h⟩
  | k, d :: ds, l, l', h =>
    TiedL.bind (tl_treeO m on keep hleaf hkeep d (leafAt pad sl posAt emb o k)
      (leafAt pad' sl' posAt emb o' k) l l' h) fun T l₁ T' l₁' hT =>
      TiedL.bind (tl_treesO pad pad' sl sl' posAt emb o o' (k + 1) ds l₁ l₁' hT.2)
        fun Ts l₂ Ts' l₂' hTs => .done ⟨⟨hT.1, hTs.1⟩, hTs.2⟩

end Parts

/-! ## The search, a Fiat-Shamir query, and what follows it -/

section Fs
variable (m : ON₂ → Bool) (on : Prop) (keep : QA (typedOracleFamily lam K L) → Bool)
  {C P : Type} (chal : (Fin K → Dig lam) → C) (t : Tag) (hfb : m (.fb t) = true)
  (qf qf' : P → FbIn lam L t) (α α' : P) (hqf : on → qf = qf') (hα : on → α = α')
include hfb hqf hα

theorem tl_searchO (gr : GrW C P) : ∀ (fuel n : ℕ) (l l' : Trace (typedOracleFamily lam K L)),
    Lg on keep l l' →
    TL m (fun u l₁ v l₁' => FsRel (some gr) α α' u v ∧ Lg on keep l₁ l₁') l l'
      (searchO gr chal (fun β => askTypedOracle (L := L) (K := K) (OracleName.fb t) (qf β)) α fuel n)
      (searchO gr chal (fun β => askTypedOracle (L := L) (K := K) (OracleName.fb t) (qf' β)) α' fuel n)
  | 0, _, _, _, h => .done ⟨Or.inl ⟨rfl, rfl⟩, h⟩
  | fuel + 1, n, l, l', h =>
    TiedL.bind (tl_ask m on keep (OracleName.fb t) hfb (qf (gr.put n α)) (qf' (gr.put n α')) fun r =>
      Lg.same (fun ho => by rw [hqf ho, hα ho]) h) fun a l₁ a' l₁' haa => by
      obtain ⟨rfl, h₁⟩ := haa
      by_cases hk : gr.ok (chal a.1) = true
      · simp only [if_pos hk]
        exact .done ⟨Or.inr ⟨_, _, a, rfl, rfl, n, rfl, rfl⟩, h₁⟩
      · simp only [if_neg hk]
        exact tl_searchO gr fuel (n + 1) l₁ l₁' h₁

theorem tl_fsO (gr : Option (GrW C P)) (cap : ℕ) (l l' : Trace (typedOracleFamily lam K L))
    (h : Lg on keep l l') :
    TL m (fun u l₁ v l₁' => FsRel gr α α' u v ∧ Lg on keep l₁ l₁') l l'
      (fsO gr cap chal (fun β => askTypedOracle (L := L) (K := K) (OracleName.fb t) (qf β)) α)
      (fsO gr cap chal (fun β => askTypedOracle (L := L) (K := K) (OracleName.fb t) (qf' β)) α') := by
  cases gr with
  | none =>
    exact TiedL.bind (tl_ask m on keep (OracleName.fb t) hfb (qf α) (qf' α') fun r =>
      Lg.same (fun ho => by rw [hqf ho, hα ho]) h) fun a l₁ a' l₁' haa => by
      obtain ⟨rfl, h₁⟩ := haa
      exact .done ⟨Or.inr ⟨α, α', a, rfl, rfl, rfl, rfl⟩, h₁⟩
  | some g => exact tl_searchO m on keep chal t hfb qf qf' α α' hqf hα g _ _ l l' h

end Fs

theorem tl_onFs (m : ON₂ → Bool) (on : Prop) (keep : QA (typedOracleFamily lam K L) → Bool) {C P β₁ β₂ : Type}
    {R : Res β₁ → Trace (typedOracleFamily lam K L) → Res β₂ → Trace (typedOracleFamily lam K L) → Prop}
    (gr : Option (GrW C P)) (α α' : P) (i : ℕ) (k : P × FsAns₂ lam K → TypedOracleComputation lam K L (Res β₁))
    (k' : P × FsAns₂ lam K → TypedOracleComputation lam K L (Res β₂))
    (hR : ∀ l₁ l₁', Lg on keep l₁ l₁' → R (.ranOut i) l₁ (.ranOut i) l₁')
    (hk : ∀ β β' a l₁ l₁', PutRel gr α α' β β' → Lg on keep l₁ l₁' →
      TL m R l₁ l₁' (k (β, a)) (k' (β', a))) :
    ∀ (u : Option (P × FsAns₂ lam K)) (l₁ : Trace (typedOracleFamily lam K L)) (v : Option (P × FsAns₂ lam K))
      (l₁' : Trace (typedOracleFamily lam K L)), FsRel gr α α' u v ∧ Lg on keep l₁ l₁' →
      TL m R l₁ l₁' (onFs i k u) (onFs i k' v) := by
  rintro u l₁ v l₁' ⟨⟨rfl, rfl⟩ | ⟨β, β', a, rfl, rfl, hp⟩, h⟩
  · exact .done (hR _ _ h)
  · exact hk β β' a l₁ l₁' hp h

/-! ## The relation at the chain's end -/

/-- Two outcomes of the chain with the two logs: of one kind, with the same verifier messages and
phase (SameC, OnBytes/Dry/Control.lean); at two values: the left run's transcript as it was hashed
is its strategy's own run but for nonces; and if the verifier messages lie in G: the same kept
entries in the logs, the same kept as far as it shows, the same request root. -/
def RG (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (G : Rho s → Prop) (rd : OPos s → Bool)
    (σ : Strat s Unit) (keep : QA (typedOracleFamily lam K L) → Bool) (u : Res (OutP lam L s))
    (l₁ : Trace (typedOracleFamily lam K L)) (v : Res (OutP lam L s)) (l₁' : Trace (typedOracleFamily lam K L)) : Prop :=
  SameC s u v ∧ ∀ z z', u = .ok z → v = .ok z' →
    Puts s A W (σ.run z.1).1 (trK s z.2.1 z.1) ∧
    (G z.1 → l₁.filter keep = l₁'.filter keep ∧ KeptSame s A W rd z.2.1 z'.2.1 ∧
      z.2.2.2 = z'.2.2.2)

theorem RG.ranOut (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (G : Rho s → Prop)
    (rd : OPos s → Bool) (σ : Strat s Unit) (keep : QA (typedOracleFamily lam K L) → Bool) (i : ℕ)
    (l₁ l₁' : Trace (typedOracleFamily lam K L)) : RG s A W G rd σ keep (.ranOut i) l₁ (.ranOut i) l₁' :=
  ⟨rfl, fun _ _ hz _ => by cases hz⟩

theorem RG.noFormat (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (G : Rho s → Prop)
    (rd : OPos s → Bool) (σ : Strat s Unit) (keep : QA (typedOracleFamily lam K L) → Bool)
    (l₁ l₁' : Trace (typedOracleFamily lam K L)) : RG s A W G rd σ keep .noFormat l₁ .noFormat l₁' :=
  ⟨trivial, fun _ _ hz _ => by cases hz⟩

/-- One round in front. hP1, hP2: what is kept of the round in the left run is the strategy's
message but for a nonce. hK: if G has a member, the two runs have kept the same of the round. -/
theorem RG.cons {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s} {w : WireRB lam K r a}
    {W : RoundsQueryLayout lam K s A} (G : Rho (r :: s) → Prop) (rd : OPos (r :: s) → Bool) (m₁ : r.Msg)
    (k : r.Chal → Strat s Unit) (keep : QA (typedOracleFamily lam K L) → Bool) (c : r.Chal)
    (kp kp' : r.Msg × List (TreeK lam L) × List (TreeK lam L)) (rq rq' : Option (Dig lam))
    (hP1 : kp.1.1 = m₁.1)
    (hP2 : kp.1.2 = m₁.2 ∨
      (∃ g n, a.kind = .lo ∧ w.grJ = some g ∧
        kp.1.2 = a.plain.symm ((a.plain m₁.2).1, g.put n (a.plain m₁.2).2)) ∨
      (∃ g n, a.kind = .sh ∧ w.gr0 = some g ∧
        kp.1.2 = a.plain.symm (g.put n (a.plain m₁.2).1, (a.plain m₁.2).2)))
    (hK : (∃ ρ, G ρ) → kp.1.2 = kp'.1.2 ∧
      (∀ p, rd (.inl p) = true → r.rd kp.1.1 p = r.rd kp'.1.1 p) ∧
      TreesSame w.posAt0 (fun p => rd (.inl p)) 0 kp.2.1 kp'.2.1 ∧
      TreesSame w.posAtJ (fun p => rd (.inl p)) 0 kp.2.2 kp'.2.2 ∧ rq = rq')
    (u : Res (OutP lam L s)) (l₂ : Trace (typedOracleFamily lam K L)) (v : Res (OutP lam L s))
    (l₂' : Trace (typedOracleFamily lam K L))
    (h : RG s A W (fun ρ' => G ((c, ρ') : Rho (r :: s))) (fun p => rd (.inr p)) (k c) keep u l₂ v
      l₂') :
    RG (r :: s) (a, A) (w, W) G rd ((m₁, k) : Strat (r :: s) Unit) keep (u.map (consP c kp rq)) l₂
      (v.map (consP c kp' rq')) l₂' := by
  refine ⟨SameC.cons c kp kp' rq rq' u v h.1, fun z z' hz hz' => ?_⟩
  cases u with
  | ok w₁ =>
    cases v with
    | ok w₂ =>
      obtain rfl : consP c kp rq w₁ = z := Res.ok.inj hz
      obtain rfl : consP c kp' rq' w₂ = z' := Res.ok.inj hz'
      obtain ⟨hp, hg⟩ := h.2 w₁ w₂ rfl rfl
      refine ⟨?_, fun hG => ?_⟩
      · exact (show Puts (r :: s) (a, A) (w, W) ((m₁, c, ((k c).run w₁.1).1) : Tr (r :: s))
          ((kp.1, c, trK s w₁.2.1 w₁.1) : Tr (r :: s)) from ⟨hP1, rfl, hP2, hp⟩)
      · obtain ⟨e1, e2, e3⟩ := hg hG
        obtain ⟨k1, k2, k3, k4, k5⟩ := hK ⟨_, hG⟩
        refine ⟨e1, (show KeptSame (r :: s) (a, A) (w, W) rd (kp, w₁.2.1) (kp', w₂.2.1) from
          ⟨k1, k2, k3, k4, e2⟩), ?_⟩
        show (rq.orElse fun _ => w₁.2.2.2) = (rq'.orElse fun _ => w₂.2.2.2)
        rw [k5, e3]
    | noFormat => cases hz'
    | ranOut j => cases hz'
  | noFormat => cases hz
  | ranOut j => cases hz

/-! ## What is kept of a round -/

/-- in a local round: the plain part as it was hashed is the message's but for a nonce -/
theorem puts_lo {r : Round} {a : RAnn r} {w : WireRB lam K r a} (hk : a.kind = .lo) (pl : r.Plain)
    {α' β β' : a.Pj} (hp : PutRel w.grJ (a.plain pl).2 α' β β') :
    a.plain.symm ((a.plain pl).1, β) = pl ∨
      (∃ g n, a.kind = .lo ∧ w.grJ = some g ∧
        a.plain.symm ((a.plain pl).1, β) = a.plain.symm ((a.plain pl).1, g.put n (a.plain pl).2)) ∨
      (∃ g n, a.kind = .sh ∧ w.gr0 = some g ∧
        a.plain.symm ((a.plain pl).1, β) =
          a.plain.symm (g.put n (a.plain pl).1, (a.plain pl).2)) := by
  cases hg : w.grJ with
  | none =>
    rw [hg] at hp
    obtain ⟨h1, -⟩ := hp
    rw [h1]
    exact Or.inl (a.plain.symm_apply_apply pl)
  | some g =>
    rw [hg] at hp
    obtain ⟨n, h1, -⟩ := hp
    rw [h1]
    exact Or.inr (Or.inl ⟨g, n, hk, rfl, rfl⟩)

/-- in a shared round -/
theorem puts_sh {r : Round} {a : RAnn r} {w : WireRB lam K r a} (hk : a.kind = .sh) (pl : r.Plain)
    {α' β β' : a.P0} (hp : PutRel w.gr0 (a.plain pl).1 α' β β') :
    a.plain.symm (β, (a.plain pl).2) = pl ∨
      (∃ g n, a.kind = .lo ∧ w.grJ = some g ∧
        a.plain.symm (β, (a.plain pl).2) = a.plain.symm ((a.plain pl).1, g.put n (a.plain pl).2)) ∨
      (∃ g n, a.kind = .sh ∧ w.gr0 = some g ∧
        a.plain.symm (β, (a.plain pl).2) =
          a.plain.symm (g.put n (a.plain pl).1, (a.plain pl).2)) := by
  cases hg : w.gr0 with
  | none =>
    rw [hg] at hp
    obtain ⟨h1, -⟩ := hp
    rw [h1]
    exact Or.inl (a.plain.symm_apply_apply pl)
  | some g =>
    rw [hg] at hp
    obtain ⟨n, h1, -⟩ := hp
    rw [h1]
    exact Or.inr (Or.inr ⟨g, n, hk, rfl, rfl⟩)

end OnBytes.Dry
