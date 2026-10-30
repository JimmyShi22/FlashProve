-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/BlockLib.lean: blocks of one round, with soundness, completeness and masked form.

The general block of one round is `Block.one`; its special cases are `name`, `pads` and `sample`.
The properties are `Block.Clean` (Blocks/Block.lean, also for x, y), `Hon.AccOn` and `Hon.Masked`
(Blocks/BlockHon.lean); for `name`, masked form comes from `masked_one`. (Words of this library:
lean/GLOSSARY.md.)

 * `name`: the prover sends scalars or vectors for a hidden quantity t. Before the block a relation
   S is about t; after it, about what was sent, and it also says that what was sent is t. Prover
   messages that are not rounds of a sumcheck (`pads` apart) follow this pattern.
 * `pads`: the prover sends a pad vector.
 * `sample`: the verifier sends a challenge and rejects if it fails a public check (for instance: a
   coordinate by which a later block divides is 0). So the public part of every block's withheld set
   (`Hon.withheld`; the part: `Hon.Bad`; Blocks/BlockHon.lean) is a set of the block's own
   randomness, and the later block's relation has the premise "no coordinate is 0".

The distribution of masked scalars comes from `masked_scalars_unif` (Prob/Linear.lean).
-/
import Blocks.BlockHon
noncomputable section -- Lean tags what it cannot compile

namespace Blocks
open Iop Prob

/-- A round of a block: vectors (the vector a has `rows a` rows of `len a` entries), scalars indexed
by K, then a challenge in C. No block reads a vector, so the round has no positions. -/
@[reducible] def vRound (E : Type) [Zero E] (A : Type) (rows len : A → ℕ) (K C : Type)
    [Fintype C] [Nonempty C] : Round where
  Orc := ∀ a, Fin (rows a) → Fin (len a) → E
  Pos := Empty
  Sym := fun _ => Empty
  rd := fun _ p => p.elim
  Plain := K → E
  Chal := C
  dOrc := fun _ _ _ => 0
  dPlain := fun _ => 0

namespace Block
variable {Xi Yi Xo Yo : Type}

/-- A block of one round. -/
@[reducible] def one (r : Round) (pb : Xi → r.Chal → r.Plain → Option Xo)
    (im : Yi → r.Msg → r.Chal → Yo) : Block Xi Yi Xo Yo where
  shape := [r]
  pub x ρ p := pb x ρ.1 p.1
  imp y τ := im y τ.1 τ.2.1

/-- Soundness of one round: a set of at most e bad challenges (hcnt), which may depend on the
statement and on the prover's message, and a backward step (hback). -/
theorem clean_one {r : Round} {pb : Xi → r.Chal → r.Plain → Option Xo}
    {im : Yi → r.Msg → r.Chal → Yo} {Ri : Xi → Yi → Prop} {Ro : Xo → Yo → Prop}
    (bad : Xi → Yi → r.Msg → Set r.Chal) (e : ℕ) (hcnt : ∀ x y m, cnt (fun c => c ∈ bad x y m) ≤ e)
    (hback : ∀ x y m c xo, c ∉ bad x y m → pb x c m.2 = some xo → Ro xo (im y m c) → Ri x y) :
    (one r pb im).Clean Ri Ro (e, ()) :=
  Clean.of_badFam (B := one r pb im) (fun x y => (bad x y, fun _ _ => ()))
    (fun x y => ⟨hcnt x y, fun _ _ => trivial⟩)
    fun x y τ xo hτ hxo hRo => hback x y τ.1 τ.2.1 xo hτ.1 hxo hRo

/-- `name`: the prover's message is stored, the plain part in x and the vectors in y. -/
@[reducible] def name (Xi Yi : Type) (r : Round) : Block Xi Yi (Xi × r.Plain) (Yi × r.Orc) :=
  one r (fun x _ p => some (x, p)) (fun y m _ => (y, m.1))

/-- Soundness of `name`. t is the hidden quantity, a function of the statement; `sent` computes the
same quantity from the message (for a masked scalar: the scalar minus its pad, which is in y). If S
holds of what was sent, and what was sent is t, then S holds of t. All errors are 0. -/
theorem clean_name {r : Round} {T : Type} (t : Xi → Yi → T)
    (sent : Xi → Yi → r.Msg → T) (S : T → Xi → Yi → Prop) :
    (name Xi Yi r).Clean (fun x y => S (t x y) x y)
      (fun xo yo =>
        S (sent xo.1 yo.1 (yo.2, xo.2)) xo.1 yo.1 ∧ sent xo.1 yo.1 (yo.2, xo.2) = t xo.1 yo.1)
      (0, ()) :=
  clean_one (fun _ _ _ => ∅) 0 (fun _ _ _ => le_of_eq (cnt_false fun _ h => h))
      fun x y m c xo _ hxo hRo => by
    obtain rfl := Option.some.inj hxo
    have h1 : S (sent x y (m.1, m.2)) x y := hRo.1
    have h2 : sent x y (m.1, m.2) = t x y := hRo.2
    rw [← h2]
    exact h1

/-- The round of a pad vector of length n. -/
abbrev padRound (E : Type) [Zero E] (n : ℕ) : Round :=
  vRound E Unit (fun _ => 1) (fun _ => n) Empty Unit

/-- `pads`: the prover sends a pad vector; it joins the implicit part. -/
@[reducible] def pads (Xi Yi E : Type) [Zero E] (n : ℕ) : Block Xi Yi Xi (Yi × (Fin n → E)) :=
  one (padRound E n) (fun x _ _ => some x) (fun y m _ => (y, m.1 () 0))

/-- Soundness of `pads`: any relation that does not mention the new pad vector is preserved. All
errors are 0. -/
theorem clean_pads {E : Type} [Zero E] (n : ℕ) (R : Xi → Yi → Prop) :
    (pads Xi Yi E n).Clean R (fun x yo => R x yo.1) (0, ()) :=
  clean_one (fun _ _ _ => ∅) 0 (fun _ _ _ => le_of_eq (cnt_false fun _ h => h))
      fun x y m c xo _ hxo hRo => by
    obtain rfl := Option.some.inj hxo
    exact hRo

/-- The round of a challenge: the prover sends nothing. -/
abbrev chalRound (E : Type) [Zero E] (C : Type) [Fintype C] [Nonempty C] : Round :=
  vRound E Empty (fun a => Empty.elim a) (fun a => Empty.elim a) Empty C

/-- `sample`: the verifier sends a challenge, rejects if it fails the public check `ok`, and stores
it. -/
@[reducible] def sample (Xi Yi E : Type) [Zero E] (C : Type) [Fintype C]
    [Nonempty C] (ok : C → Bool) : Block Xi Yi (Xi × C) Yi :=
  one (chalRound E C) (fun x c _ => if ok c then some (x, c) else none) (fun y _ _ => y)

/-- Soundness of `sample`: a set of at most e bad challenges (hcnt) and a backward step (hback), in
which the challenge has passed the check. -/
theorem clean_sample {E : Type} [Zero E] {C : Type} [Fintype C] [Nonempty C] {ok : C → Bool}
    {Ri : Xi → Yi → Prop} {Ro : Xi × C → Yi → Prop} (bad : Xi → Yi → Set C) (e : ℕ)
    (hcnt : ∀ x y, cnt (fun c => c ∈ bad x y) ≤ e)
    (hback : ∀ x y c, c ∉ bad x y → ok c = true → Ro (x, c) y → Ri x y) :
    (sample Xi Yi E C ok).Clean Ri Ro (e, ()) :=
  clean_one (fun x y _ => bad x y) e (fun x y _ => hcnt x y) fun x y m c xo hc hxo hRo => by
    by_cases hok : ok c = true
    · rw [if_pos hok] at hxo
      obtain rfl := Option.some.inj hxo
      exact hback x y c hc hok hRo
    · rw [if_neg hok] at hxo
      exact absurd hxo (by simp)

end Block

namespace Hon
variable {Xi Yi Xo Yo P E Ii Io : Type}

/-- The honest prover of one round. -/
@[reducible] def one {r : Round} {pb : Xi → r.Chal → r.Plain → Option Xo}
    {im : Yi → r.Msg → r.Chal → Yo} (msg : Ii → (P → E) → r.Msg) (nx : Ii → r.Chal → Io)
    (Bd : Set r.Chal) (Wn : Ii → Set r.Chal) :
    Hon (Block.one r pb im) P E Ii Io where
  strat a π := (msg a π, fun _ => ())
  next a ρ := nx a ρ.1
  Bad := {ρ | ρ.1 ∈ Bd}
  Win a := {ρ | ρ.1 ∈ Wn a}

/-- Completeness of one round, under h. -/
theorem accOn_one {r : Round} {pb : Xi → r.Chal → r.Plain → Option Xo}
    {im : Yi → r.Msg → r.Chal → Yo} {msg : Ii → (P → E) → r.Msg}
    {nx : Ii → r.Chal → Io} {Bd : Set r.Chal} {Wn : Ii → Set r.Chal}
    {Hi : Ii → (P → E) → Xi → Yi → Prop} {Ho : Io → (P → E) → Xo → Yo → Prop}
    (h : ∀ a π x y c, Hi a π x y → c ∉ Bd → c ∉ Wn a →
      ∃ xo, pb x c (msg a π).2 = some xo ∧ Ho (nx a c) π xo (im y (msg a π) c)) :
    (Hon.one (pb := pb) (im := im) msg nx Bd Wn).AccOn Hi Ho := fun a π x y ρ hi hρ =>
  h a π x y ρ.1 hi (fun hb => hρ (Or.inl hb)) fun hw => hρ (Or.inr hw)

variable [Fintype P] [DecidableEq P] [AddCommGroup E] [Fintype E]

/-- The distribution of the plain part of one round with scalars indexed by K: uniform scalars,
mapped by `enc`. -/
def simOne {r : Round} {K : Type} [Fintype K] [DecidableEq K] (E : Type)
    [AddCommGroup E] [Fintype E] (enc : (K → E) → r.Plain) : Rho [r] → PMF (Plains [r]) :=
  fun _ => (unif (K → E)).map fun s => (enc s, ())

/-- Masked form of one round. The plain part consists of the scalars val k + π (idx k), k in K: each
has its own pad (idx is injective), and the values depend only on pads in D, none of which masks a
scalar of this round. -/
theorem masked_one {r : Round} {pb : Xi → r.Chal → r.Plain → Option Xo}
    {im : Yi → r.Msg → r.Chal → Yo} {msg : Ii → (P → E) → r.Msg} {nx : Ii → r.Chal → Io}
    {Bd : Set r.Chal} {Wn : Ii → Set r.Chal} {K : Type} [Fintype K] [DecidableEq K]
    (enc : (K → E) → r.Plain) (V : Ii → Prop) (idx : K → P) (hidx : Function.Injective idx)
    (val : Ii → (P → E) → K → E) (D : Set P)
    (hmsg : ∀ a π, V a → (msg a π).2 = enc fun k => val a π k + π (idx k))
    (hval : ∀ a π π', V a → (∀ p ∈ D, π p = π' p) → val a π = val a π')
    (hD : Disjoint D (Set.range idx)) :
    (Hon.one (pb := pb) (im := im) msg nx Bd Wn).Masked
      V (Set.range idx) (D ∪ Set.range idx) (simOne E enc) := by
  constructor
  · intro a ρ π π' ha _ hπ
    show ((msg a π).2, ()) = ((msg a π').2, ())
    rw [hmsg a π ha, hmsg a π' ha, hval a π π' ha fun p hp => hπ p (Or.inl hp)]
    have : (fun k => π (idx k)) = fun k => π' (idx k) := funext fun k => hπ _ (Or.inr ⟨k, rfl⟩)
    exact congrArg (fun u : K → E => (enc (fun k => val a π' k + u k), ())) this
  · intro a ρ σ ha _
    have h1 : ∀ π : P → E,
        ((Hon.one (pb := pb) (im := im) msg nx Bd Wn).tr a (mix (Set.range idx) π σ) ρ).plains =
          (fun s : K → E => ((enc s, ()) : Plains [r])) (fun k => val a σ k + π (idx k)) := by
      intro π
      show ((msg a (mix (Set.range idx) π σ)).2, ()) = (enc (fun k => val a σ k + π (idx k)), ())
      rw [hmsg a _ ha, hval a (mix (Set.range idx) π σ) σ ha fun p hp =>
        mix_notMem _ _ fun hr => Set.disjoint_left.1 hD hp hr]
      have : (fun k => mix (Set.range idx) π σ (idx k)) = fun k => π (idx k) :=
        funext fun k => mix_mem _ _ ⟨k, rfl⟩
      exact congrArg (fun u : K → E => (enc (fun k => val a σ k + u k), ())) this
    rw [map_congr' _ h1]
    refine (map_eq_map_map (f := fun (π : P → E) k => val a σ k + π (idx k))
      (g := fun s : K → E => ((enc s, ()) : Plains [r])) (unif (P → E)) fun _ => rfl).trans ?_
    unfold simOne
    rw [masked_scalars_unif (fun _ _ => False) ⟨fun p => Acc.intro p fun _ h => h.elim⟩ idx hidx
        (fun k _ => val a σ k) fun k => readsBelow_const _ _ _]
    rfl

/-- A round whose plain part is a fixed value is masked: it uses no pad and reads none. -/
theorem masked_one_const {r : Round} {pb : Xi → r.Chal → r.Plain → Option Xo}
    {im : Yi → r.Msg → r.Chal → Yo} {msg : Ii → (P → E) → r.Msg} {nx : Ii → r.Chal → Io}
    {Bd : Set r.Chal} {Wn : Ii → Set r.Chal} (V : Ii → Prop) (p₀ : r.Plain)
    (hmsg : ∀ a π, V a → (msg a π).2 = p₀) :
    (Hon.one (pb := pb) (im := im) msg nx Bd Wn).Masked V ∅ ∅ (fun _ => PMF.pure (p₀, ())) := by
  constructor
  · intro a ρ π π' ha _ _
    show ((msg a π).2, ()) = ((msg a π').2, ())
    rw [hmsg a π ha, hmsg a π' ha]
  · intro a ρ σ ha _
    have h1 : ∀ π : P → E,
        ((Hon.one (pb := pb) (im := im) msg nx Bd Wn).tr a (mix ∅ π σ) ρ).plains =
          ((p₀, ()) : Plains [r]) := by
      intro π
      show ((msg a (mix ∅ π σ)).2, ()) = (p₀, ())
      rw [hmsg a _ ha]
    rw [map_congr' _ h1]
    exact PMF.map_const _ _

omit [Fintype P] [DecidableEq P] [Fintype E] [AddCommGroup E] in
/-- Completeness of `name`, at every ρ: the statement is unchanged, the message stored. -/
theorem accOn_name {r : Round} (msg : Ii → (P → E) → r.Msg) (Hi : Ii → (P → E) → Xi → Yi → Prop) :
    (Hon.one (pb := fun (x : Xi) _ p => some (x, p)) (im := fun (y : Yi) m _ => (y, m.1)) msg
        (fun a _ => a) ∅ fun _ => ∅).AccOn
      Hi (fun a π xo yo => Hi a π xo.1 yo.1 ∧ (yo.2, xo.2) = msg a π) :=
  accOn_one fun a π x _ _ hi _ _ => ⟨(x, (msg a π).2), rfl, hi, rfl⟩

/-- The honest prover of `pads`: the vector holds the pads idx 0, idx 1, ... -/
@[reducible] def pads (Xi Yi : Type) {n : ℕ} (idx : Fin n → P) :
    Hon (Block.pads Xi Yi E n) P E Ii Ii :=
  Hon.one (fun _ π => (fun _ _ j => π (idx j), fun k => Empty.elim k)) (fun a _ => a) ∅ fun _ => ∅

omit [Fintype P] [DecidableEq P] [Fintype E] in
/-- Completeness of `pads`, at every ρ: the statement is unchanged, and the new pad vector holds the
pads `idx j`. -/
theorem accOn_pads {n : ℕ} (idx : Fin n → P) (Hi : Ii → (P → E) → Xi → Yi → Prop) :
    (Hon.pads (E := E) (Ii := Ii) Xi Yi idx).AccOn
      Hi (fun a π x yo => Hi a π x yo.1 ∧ ∀ j, yo.2 j = π (idx j)) :=
  accOn_one fun _ _ x _ _ hi _ _ => ⟨x, rfl, hi, fun _ => rfl⟩

/-- `pads` is masked: it has no plain part. (That each pad masks at most one scalar is required
where two masking blocks are composed.) -/
theorem masked_pads {n : ℕ} (idx : Fin n → P) (V : Ii → Prop) :
    (Hon.pads (E := E) (Ii := Ii) Xi Yi idx).Masked
      V ∅ ∅ (fun _ => PMF.pure ((fun k => Empty.elim k), ())) :=
  masked_one_const V _ fun _ _ _ => rfl

/-- The honest prover of `sample`: the next state is `nx`; the public part of the withheld set holds
the challenges that fail the check. -/
@[reducible] def sample (Xi Yi : Type) {C : Type} [Fintype C] [Nonempty C]
    (ok : C → Bool) (nx : Ii → C → Io) :
    Hon (Block.sample Xi Yi E C ok) P E Ii Io :=
  Hon.one (fun _ _ => (fun a => Empty.elim a, fun k => Empty.elim k)) nx
    {c | ok c = false} fun _ => ∅

omit [Fintype P] [DecidableEq P] [Fintype E] in
/-- Completeness of `sample`, under h: outside the public withheld set the challenge is kept. -/
theorem accOn_sample {C : Type} [Fintype C] [Nonempty C] (ok : C → Bool) (nx : Ii → C → Io)
    {Hi : Ii → (P → E) → Xi → Yi → Prop} {Ho : Io → (P → E) → Xi × C → Yi → Prop}
    (h : ∀ a π x y c, Hi a π x y → ok c = true → Ho (nx a c) π (x, c) y) :
    (Hon.sample (P := P) (E := E) Xi Yi ok nx).AccOn Hi Ho :=
  accOn_one fun a π x y c hi hb _ => by
    have hok : ok c = true := by
      cases hc : ok c
      · exact absurd hc hb
      · rfl
    exact ⟨(x, c), if_pos hok, h a π x y c hi hok⟩

/-- `sample` is masked: the prover sends nothing. -/
theorem masked_sample {C : Type} [Fintype C] [Nonempty C] (ok : C → Bool)
    (nx : Ii → C → Io) (V : Ii → Prop) :
    (Hon.sample (P := P) (E := E) Xi Yi ok nx).Masked
      V ∅ ∅ (fun _ => PMF.pure ((fun k => Empty.elim k), ())) :=
  masked_one_const V _ fun _ _ _ => rfl

end Hon
end Blocks
