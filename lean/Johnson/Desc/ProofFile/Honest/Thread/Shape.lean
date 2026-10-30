-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/Shape.lean: the acceptance of one sub-protocol, divided
into structure and values. It is stated once, over `Block.step` and a projection of the verifier's
state onto its shape, which is meant to hold flags, counts, marks and lengths, but no field element.
The file has definitions that are meant as hypotheses, and conditional lemmas on them, general in
the parameters of a `Thread` (Honest/Thread/Thr.lean): no kind is named.

  1  `Shape`, `Shape.run`, `Shape.yes`, `Shape.Blind`, `Plain`, `Shape.Typed`   the parameters; the
     shape's own run; the named public hypothesis, executable; two forms of "the shape is blind"
  2  `Carries` (B1), `Returns` (B2), `FitsAt`, `Values`   the hypotheses on one sub-protocol
  3  `run_front`, `shape_reach`, `shape_at`, `want_length`, `accepted_of_shape`   the rule

The division. Each kind writes its `decide` once as "guards on the shape, then values". (B1)
`Carries`: where the sub-protocol's own step accepts and the shape's own step `g` returns, `g`
returns the shape after that acceptance. (That `g` returns comes from the named hypothesis.) (B2)
`Returns`: where `g` returns at the state's shape, the step's own tests on rounds and columns pass,
and the sub-protocol's named tests on values (`vals`) pass, the sub-protocol's `decide` returns.
`Values`: these named tests pass on the honest side, outside the stops and the sub-protocol's fall.
That is what is left of `Accepted` (Honest/Thread/Pays.lean) for each kind's algebra. `FitsAt`: what
was played and read passes the step's own tests on rounds and columns.

Three ways to fill the parameters. A typed shape: `Sh` without a field element, `g` an explicit
definition of the guards. The sub-protocol's own definition at an erased state: `Sh := S`, `sh` puts
a fixed element for every field element and for every number that is drawn or sent, and `g b` is the
sub-protocol's own step at such states. A table from one fixed reference run: `g b a` returns the
reference run's next shape where a is its shape at b.

The named hypothesis. `Shape.yes Z a n = true`: the shape's run over the first n sub-protocols
returns, from the chain's first shape a. It reads the parameter `g` alone: no input, no coin, no
challenge. It is a hypothesis with a name, not something that can be taken for granted. Where it is
checked by evaluation, a theorem that uses it rests on that evaluation, as with `FileDescription.planOk`;
Honest/Thread/ShapeRun.lean (not in the sealed library; its build does not check it) has lemmas for
proving it in pieces. Whoever states a final statement over `accepted_of_shape` lists it among that
statement's hypotheses. Beside it the rule asks (`hfirst`) that every state at which the chain may
begin, at a valid input, has the first shape a. A shape may see a mark that the start sets where
the instance fails a public test; at a valid input it does not.

Blind. The shape is meant to read no sent value and no coin: a rejection that depends on such a
value is to be a fall's, not a guard's. The form for it, at each function that sets such a value in
the state, is `Shape.Blind Z turn`: the shape does not see the change. By type, for whoever takes a
typed shape, there is `Shape.Typed Z`: `Sh` is built from Nat, Bool, String, Unit, lists, pairs and
options alone (`Plain`); a number can still be computed from a value. No lemma of this file takes
`Shape.Blind` or `Shape.Typed` as a hypothesis: the rule does not need them.

Limits.
  * `Plain` excludes a field element by type and nothing more.
  * Nothing compares `g` with a description's plan, or `vals` with the fall's test.
  * It is not proved that any of the hypotheses can be met at a description of the protocol.
  * None of them, and none of the lemmas, is one of the library's goals.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open Johnson.Desc.First.Walk.Tied (Reach reach_of_fold)

/-! ## 1 The parameters -/

/-- Types that are built from numbers, Bools, strings, the unit type, lists, options and pairs
alone. -/
inductive Plain : Type → Prop
  | nat : Plain Nat
  | bool : Plain Bool
  | str : Plain String
  | unit : Plain Unit
  | list {α : Type} : Plain α → Plain (List α)
  | opt {α : Type} : Plain α → Plain (Option α)
  | prod {α β : Type} : Plain α → Plain β → Plain (α × β)

/-- **The parameters of the division**, for one chain's state. -/
structure Shape (S : Type) where
  /-- the type of shapes -/
  Sh : Type
  /-- a state's shape -/
  sh : S → Sh
  /-- the guards of the sub-protocol after a border, on the shape; executable -/
  g : Nat → Sh → Except String Sh
  /-- that sub-protocol's named tests on values: from the state, its rounds without the sealed
  digest, and the groups of columns that it is shown -/
  vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- The shape's own run over the first `n` sub-protocols. -/
def Shape.run (Z : Shape S) : Nat → Z.Sh → Except String Z.Sh
  | 0, a => .ok a
  | n + 1, a => (Z.run n a).bind (Z.g n)

/-- **The named public hypothesis**, executable: the shape's run returns. -/
def Shape.yes (Z : Shape S) (a : Z.Sh) (n : Nat) : Bool := (Z.run n a).toOption.isSome

/-- The shape does not see the change `turn` of the state. It is a definition, meant as a
hypothesis. -/
def Shape.Blind (Z : Shape S) (turn : S → S) : Prop := ∀ s, Z.sh (turn s) = Z.sh s

/-- The type of shapes holds no field element. It is a definition, meant as a hypothesis. -/
def Shape.Typed (Z : Shape S) : Prop := Plain Z.Sh

/-! ## 2 The hypotheses on one sub-protocol -/

/-- **(B1)**: where the sub-protocol's own step accepts and the shape's own step returns, it returns
the shape after that acceptance. It is a definition, meant as a hypothesis. Nothing is claimed of
it, and it is none of the library's goals. -/
def Carries (bs : List (Block S Cl)) (ft : Nat) (Z : Shape S) (b : Nat) : Prop :=
  ∀ blk, bs[b]? = some blk → ∀ s rs cols s' n t, blk.step ft s rs cols = .ok (s', n) →
    Z.g b (Z.sh s) = .ok t → t = Z.sh s'

/-- **(B2)**: if the guards return, the step's own tests pass and the named tests on values pass,
then the sub-protocol's `decide` returns. It is a definition, meant as a hypothesis. Nothing is
claimed of it, and it is none of the library's goals. -/
def Returns (bs : List (Block S Cl)) (ft : Nat) (Z : Shape S) (b : Nat) : Prop :=
  ∀ blk, bs[b]? = some blk → ∀ s rs cols t, Z.g b (Z.sh s) = .ok t → blk.Fits ft rs cols →
    Z.vals b s (rs.map noDigest) (blk.shown ft rs cols) = true →
    ∃ s', blk.decide s (rs.map noDigest) (blk.shown ft rs cols) = .ok s'

variable (T : Thread Bk S Cl V W X Pb)

/-- What was played and read passes the step's own tests on rounds and columns. It is a definition,
meant as a hypothesis. Nothing is claimed of it, and it is none of the library's goals. -/
def FitsAt (b : Nat) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k m E ds y cols, drawsFit blk.rounds ds = true →
    T.Moved blk k m E ds y cols → blk.Fits T.ft (roundsOf y.1) cols

/-- **The values**: from the invariant before the sub-protocol and the prover's side of the step,
where nothing of the sub-protocol stops and the parameter `fall` does not fire: the sub-protocol's
named tests on values pass. It is a definition, meant as a hypothesis. Nothing is claimed of it, and
it is none of the library's goals. -/
def Values (Z : Shape S) (fall : Nat → S → List Fmt.Drawn → Option String) (b : Nat) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols, Thr T b k s m E →
    drawsFit blk.rounds ds = true →
    chainStopAt (T.φ.sees m.st.input) [blk] T.hs m.loc ds = none → fall b s ds = none →
    T.Moved blk k m E ds y cols →
    Z.vals b s ((roundsOf y.1).map noDigest) (blk.shown T.ft (roundsOf y.1) cols) = true

/-! ## 3 The rule -/

/-- A run that returns has returned at every earlier border. -/
theorem run_front (Z : Shape S) (a : Z.Sh) : ∀ (n j : Nat), j ≤ n → Z.yes a n = true →
    ∃ e, Z.run j a = .ok e
  | 0, j, hj, _ => by
    cases Nat.le_zero.1 hj
    exact ⟨a, rfl⟩
  | n + 1, j, hj, h => by
    have hn : Z.yes a n = true := by
      unfold Shape.yes at h ⊢
      cases hr : Z.run n a with
      | ok e => rfl
      | error e =>
        have h' : (((Z.run n a).bind (Z.g n)).toOption.isSome) = true := h
        rw [hr] at h'
        cases h'
    rcases Nat.lt_or_ge j (n + 1) with hlt | hge
    · exact run_front Z a n j (Nat.le_of_lt_succ hlt) hn
    · cases Nat.le_antisymm hj hge
      unfold Shape.yes at h
      cases hr : Z.run (n + 1) a with
      | ok e => exact ⟨e, rfl⟩
      | error e =>
        rw [hr] at h
        cases h

/-- Along every state that is reached by the sub-protocols' own steps: where the shape's run
returns, it returns that state's shape. -/
theorem shape_reach (Z : Shape S) {P : Type} {start : P → S} {ft : Nat} {bs : List (Block S Cl)}
    (hC : ∀ j, Carries bs ft Z j) {b : Nat} {a : P × S} (h : Reach ft bs start b a) :
    ∀ e, Z.run b (Z.sh (start a.1)) = .ok e → e = Z.sh a.2 := by
  induction h with
  | zero z =>
    intro e he
    exact (Except.ok.inj he).symm
  | succ _ hb hy ih =>
    intro e he
    obtain ⟨R, c, -, hs⟩ := hy
    have he' : (Z.run _ _).bind (Z.g _) = .ok e := he
    cases hk : Z.run _ _ with
    | error w =>
      rw [hk] at he'
      cases he'
    | ok e' =>
      rw [hk] at he'
      have e1 := ih e' hk
      subst e1
      exact hC _ _ hb _ _ _ _ _ _ hs he'

/-- **At a border at which the invariant holds, the verifier's state has the shape that the shape's
run has there.** -/
theorem shape_at (Z : Shape S) {a₀ : Z.Sh} {n b : Nat} {k : Coins Bk} {s : S} {m : Mid W X}
    {E : Env} (hn : n ≤ T.bs.length) (hb : b ≤ n) (hyes : Z.yes a₀ n = true)
    (hfirst : ∀ k w h s₀, T.valid w → T.begun k w h s₀ → Z.sh s₀ = a₀)
    (hC : ∀ j, Carries T.bs T.ft Z j) (hA : Thr T b k s m E) : Z.run b a₀ = .ok (Z.sh s) := by
  unfold Thr Thread.Made at hA
  obtain ⟨-, -, -, -, ⟨-, -, -, -, s₀, c₀, hbeg, -, hf⟩, -, hval⟩ := hA
  have hr : Reach T.ft T.bs (fun _ : Unit => s₀) b ((), s) :=
    reach_of_fold b (Nat.le_trans hb hn) s _ _ _ _ hf
  obtain ⟨e, he⟩ := run_front Z a₀ n b hb hyes
  have e1 := shape_reach Z hC hr e (by rw [hfirst _ _ _ _ hval hbeg]; exact he)
  rw [he, e1]

/-- The columns that `fillCols` has filled for a sub-protocol's own reads are as many as its step
takes. -/
theorem want_length {blk : Block S Cl} {chain ft : Nat}
    {stored : Nat → Nat → Option (List UInt64)} {tree : Fmt.TreeSource → Option (Place × Table)}
    {ds : List Fmt.Drawn} {rs : List Fmt.RoundView} {cols : List OpenedColumn} (hdr : rs.map (·.drawn) = ds)
    (hc : fillCols (readsOf chain ft stored tree blk.rounds ds) [] = .ok cols) :
    (blk.want ft rs).length = cols.length := by
  have e := congrArg List.length (fillCols_kept _ _ _ hc)
  rw [readsOf_wants, List.length_map] at e
  rw [e]
  unfold Block.want
  rw [hdr]

/-- **The rule**: from the named hypothesis, `hfirst` (every state at which the chain may begin, at
a valid input, has the first shape), (B1) at every sub-protocol, (B2) at this one, `FitsAt` and the
values: the sub-protocol is accepted (`Accepted`). A conditional lemma on this folder's own
definitions. It is none of the library's goals. -/
theorem accepted_of_shape (Z : Shape S) {a₀ : Z.Sh} {n b : Nat}
    {fall : Nat → S → List Fmt.Drawn → Option String} (hn : n ≤ T.bs.length) (hb : b < n)
    (hyes : Z.yes a₀ n = true) (hfirst : ∀ k w h s₀, T.valid w → T.begun k w h s₀ → Z.sh s₀ = a₀)
    (hC : ∀ j, Carries T.bs T.ft Z j) (hR : Returns T.bs T.ft Z b) (hF : FitsAt T b)
    (hV : Values T Z fall b) : Accepted T fall b := by
  intro blk hblk k s m E ds y cols hA hd hst hf hMv
  have hs := shape_at T Z hn (Nat.le_of_lt hb) hyes hfirst hC hA
  obtain ⟨t, ht⟩ := run_front Z a₀ n (b + 1) hb hyes
  have hg : Z.g b (Z.sh s) = .ok t := by
    have ht' : (Z.run b a₀).bind (Z.g b) = .ok t := ht
    rw [hs] at ht'
    exact ht'
  have hfit := hF blk hblk k m E ds y cols hd hMv
  obtain ⟨s', hdec⟩ := hR blk hblk s (roundsOf y.1) cols t hg hfit
    (hV blk hblk k s m E ds y cols hA hd hst hf hMv)
  have hMv' := hMv
  unfold Thread.Moved at hMv'
  obtain ⟨⟨l, -, hy⟩, hc⟩ := hMv'
  have hw := want_length (blk := blk) (rs := roundsOf y.1)
    (yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hy)) hc
  refine ⟨s', ?_⟩
  unfold Thread.Stepped
  refine ⟨hMv, ?_⟩
  rw [← hw]
  exact (step_iff T.ft blk s s' (roundsOf y.1) cols _).2 ⟨hfit, hdec, rfl⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.run_front
#print axioms ProofFile.Honest.shape_reach
#print axioms ProofFile.Honest.shape_at
#print axioms ProofFile.Honest.want_length
#print axioms ProofFile.Honest.accepted_of_shape
