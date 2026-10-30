-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/Bare.lean: the hypotheses at a sub-protocol without a
prover's side. `Bare`: no prover's side is defined at the sub-protocol's place, and none of its
rounds has a root or an oracle message, reads a stored table or opens a tree; a sub-protocol without
a round is among these. There the prover's side of the step is fixed by the functions of
Honest/Frame.lean: each round shows no item, the challenges are heard, nothing is read, no tree is
new (`moved_bare`). So the hypotheses of Honest/Thread/PaysS.lean, which are asked from `ThrS`
(Honest/Thread/Said.lean), reduce to conditions on the sub-protocol's own step, at rounds that show
no item and at no column, and on the `Thread`'s parameters: the structure `NoHouse` (`NoHouse`: no
prover's side). The lemmas are general in the `Thread`, in `Said`, in the fall, in the
sub-protocol's number and in the sub-protocol: no kind is named.

What this is. Definitions, meant as hypotheses, and conditional lemmas on this folder's own
functions and definitions. None of the library's goals.

Where the content lies. In `NoHouse.yes`, at a sub-protocol that runs a kind's tests. The parameter
`fall` is free there: a fall that fires wherever the step rejects makes that field hold vacuously.
What the fall is to be, and how many lists of challenges it covers at each fixed input and coins,
has to be proved beside it.

  0  `Mid.past`, `Bare`   the state of a run after such rounds; the sub-protocol
  1  `play_bare`, `reads_plain`, `add_plain`, `moved_bare`, `past_input`   what the step is there
  2  `flat_nil`, `playsS_bare`   `PlaysS` holds there
  3  `NoHouse`, `noHouse_owes`, `noHouse_yes`, `noHouse_said`   the structure; the hypotheses that
     follow from it

Holds vacuously. As every such hypothesis: at an invariant that is false everywhere. `behind` and
`owes` also where a round declares an item in the clear: the step accepts no round that shows none.

Limits.
  * `RidesPastS` names no sub-protocol: it is a field of the structure, to be proved by whoever
    supplies the items that ride past.
  * The fields' "for all m" run over the state's field `opened` too, `none` among its values. At
    such a sub-protocol no part is called and no column is read (`moved_bare`): `Mid.past` carries
    the field on, and `SaidNext` is asked at the state that takes no column, which is `m.past ds`
    (`took_nil`, Honest/Law/RunsFile.lean).
  * Nothing is proved of any sub-protocol of the protocol.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.Quiet
import Johnson.Desc.ProofFile.Honest.Law.Thread
import Johnson.Desc.ProofFile.Honest.Law.RunsFile

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn Strs)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-! ## 0 The sub-protocol -/

/-- The state of a run after rounds at which no prover's side is defined: the challenges are heard;
each round shows no item, with no stored run to fall back on; the field `opened` is carried on, as
`Step.hear` (Honest/Frame.lean) carries it. -/
def Mid.past (m : Mid W X) : List Fmt.Drawn → Mid W X
  | [] => m
  | d :: ds => Mid.past ⟨m.st.hears d, m.loc ++ [d], m.seen ++ [⟨[], d⟩], m.opened⟩ ds

/-- **A sub-protocol without a prover's side, as far as the functions of Honest/Frame.lean see it**:
no prover's side is defined at its place; for each round it declares the empty list of oracle
messages; none of its rounds has a root, reads a stored table or opens a tree. A sub-protocol
without a round is among these. Executable tests, stated as equations. -/
structure Bare (hs : List (Placed V W X)) (blk : Block S Cl) : Prop where
  none : (hs.find? fun g => g.place == blk.place) = none
  lists : blk.oracles = blk.rounds.map fun _ => []
  plain : ∀ r ∈ blk.rounds, r.entry.roots = 0 ∧ r.stored = [] ∧ r.opens = []

/-! ## 1 What the step is there -/

theorem past_input : ∀ (ds : List Fmt.Drawn) (m : Mid W X), (m.past ds).st.input = m.st.input
  | [], _ => rfl
  | d :: ds, m => by
    show ((⟨m.st.hears d, m.loc ++ [d], m.seen ++ [⟨[], d⟩], m.opened⟩ :
      Mid W X).past ds).st.input = _
    rw [past_input ds]
    rfl

/-- `Step`s without a move, a stop or a root: what `play` returns, with no stored run to fall back
on. -/
theorem play_bare : ∀ (ss : List (Step W X)) (ds : List Fmt.Drawn) (m : Mid W X)
    (y : List Played × Mid W X),
    (∀ s ∈ ss, s.move = none ∧ s.bad = (fun _ _ => none) ∧ s.hid = (fun _ _ => none) ∧
      s.decl.entry.roots = 0) →
    play ss ds [] m = .ok y →
    roundsOf y.1 = ds.map (fun d => ⟨[], d⟩) ∧ y.2 = m.past ds ∧ tablesOf y.1 = []
  | [], [], m, y, _, h => by
    have h' : (Except.ok ([], m) : Except Refusal (List Played × Mid W X)) = .ok y := h
    cases h'
    exact ⟨rfl, rfl, rfl⟩
  | [], _ :: _, _, _, _, h => by simp [play] at h
  | _ :: _, [], _, _, _, h => by simp [play] at h
  | s :: ss, d :: ds, m, y, hs, h => by
    obtain ⟨h1, h2, h3, h4⟩ := hs s List.mem_cons_self
    have ht : s.tell none m = .ok ⟨[], [], false⟩ := by
      unfold Step.tell Step.stop
      rw [h1, h2, h3, h4]
      rfl
    have hh : s.hear ⟨[], [], false⟩ d m =
        .ok ⟨m.st.hears d, m.loc ++ [d], m.seen ++ [⟨[], d⟩], m.opened⟩ := by
      unfold Step.hear
      rw [h1]
    have h' : ((s.tell none m).bind fun x => (s.hear x d m).bind fun m' =>
        (play ss ds [] m').map fun y =>
          ((⟨s.name, s.addr.place, if x.told then s.addr.part else 0, x.told, x.vals, x.tables,
            d⟩ : Played) :: y.1, y.2)) = .ok y := h
    rw [ht] at h'
    have h'' : ((s.hear ⟨[], [], false⟩ d m).bind fun m' =>
        (play ss ds [] m').map fun y =>
          ((⟨s.name, s.addr.place, 0, false, [], [], d⟩ : Played) :: y.1, y.2)) = .ok y := h'
    rw [hh] at h''
    obtain ⟨y', hy', rfl⟩ := exMap_ok h''
    obtain ⟨a1, a2, a3⟩ := play_bare ss ds _ y' (fun u hu => hs u (List.mem_cons_of_mem _ hu)) hy'
    refine ⟨?_, a2, ?_⟩
    · show (⟨[], d⟩ : Fmt.RoundView) :: roundsOf y'.1 = ⟨[], d⟩ :: ds.map fun d => ⟨[], d⟩
      rw [a1]
    · show ([] : List (Option (Place × Table))) ++ tablesOf y'.1 = []
      rw [a3]
      rfl

/-- Rounds that read nothing. -/
theorem reads_plain (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) : ∀ (l : List Fmt.DeclaredRound)
    (ds : List Fmt.Drawn), (∀ r ∈ l, r.stored = [] ∧ r.opens = []) →
    readsOf chain ft stored tree l ds = []
  | [], _, _ => by simp [readsOf]
  | _ :: _, [], _ => by simp [readsOf]
  | r :: l, d :: ds, h => by
    obtain ⟨h1, h2⟩ := h r List.mem_cons_self
    unfold readsOf
    rw [h1, h2, reads_plain chain ft stored tree l ds fun u hu => h u (List.mem_cons_of_mem _ hu)]
    rfl

/-- Rounds that produce no table leave the available tables unchanged, at an `E` with no tree of its
own beyond those sent (`Env.Tight`, Honest/Law/Along.lean). -/
theorem add_plain (E : Env) (hE : ∀ n, E.sent ≤ n → E.tree (.own n) = none) (ps : List Played)
    (h : tablesOf ps = []) : E.add ps = E := by
  have e : E.add ps = E.add [] := by
    unfold Env.add
    rw [h]
    rfl
  rw [e, Env.add_nil E hE]

section
variable (T : Thread Bk S Cl V W X Pb)

/-- **At a sub-protocol without a prover's side: each round shows no item; the challenges are heard;
no table is produced; nothing is read.** -/
theorem moved_bare {blk : Block S Cl} {k : Coins Bk} {m : Mid W X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid W X} {cols : List OpenedColumn} (hB : Bare T.hs blk)
    (hM : T.Moved blk k m E ds y cols) :
    roundsOf y.1 = ds.map (fun d => ⟨[], d⟩) ∧ y.2 = m.past ds ∧ tablesOf y.1 = [] ∧
      cols = [] := by
  obtain ⟨⟨l, hl, hy⟩, hc⟩ := hM
  have hl' := steps_one_none hB.none hl
  subst hl'
  obtain ⟨a1, a2, a3⟩ := play_bare _ ds m y (fun s hs => by
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hs
    exact ⟨rfl, rfl, rfl, (hB.plain r.1 (List.of_mem_zip hr).1).1⟩) hy
  rw [reads_plain _ _ _ _ _ _ fun r hr => (hB.plain r hr).2] at hc
  have hc' : (Except.ok [] : Except String (List OpenedColumn)) = .ok cols := hc
  cases hc'
  exact ⟨a1, a2, a3, rfl⟩

/-! ## 2 It plays -/

theorem flat_nil {α β : Type} : ∀ l : List α, (l.map fun _ => ([] : List β)).flatMap id = []
  | [] => rfl
  | _ :: l => flat_nil l

variable (Said : Nat → Coins Bk → Mid W X → Prop) {b : Nat} {blk : Block S Cl}

/-- **`PlaysS` holds at a sub-protocol without a prover's side**, with no further hypothesis. -/
theorem playsS_bare (hblk : T.bs[b]? = some blk) (hB : Bare T.hs blk) : PlaysS T Said b := by
  intro blk' hblk' k s m E ds l _ hd _ hl
  rw [hblk] at hblk'
  cases hblk'
  have hl' := steps_one_none hB.none hl
  have hlen : ds.length = (bareSteps blk : List (Step W X)).length := by
    rw [drawsFit_length _ _ hd]
    unfold bareSteps
    rw [List.length_map, List.length_zip, hB.lists, List.length_map, Nat.min_self]
  obtain ⟨y, hy⟩ := play_bare_ok (bareSteps blk : List (Step W X)) ds m (fun u hu => by
    obtain ⟨r, -, rfl⟩ := List.mem_map.1 hu
    exact ⟨rfl, rfl, rfl⟩) hlen
  have hM : T.Moved blk k m E ds y [] := by
    refine ⟨⟨l, hl, by rw [hl']; exact hy⟩, ?_⟩
    rw [reads_plain _ _ _ _ _ _ fun r hr => (hB.plain r hr).2]
    rfl
  refine ⟨y, [], hM, ?_⟩
  intro σ hσ
  have ho : blk.oracles.flatMap id = [] := by
    rw [hB.lists]
    exact flat_nil _
  have e : T.hand (b + 1) = T.hand b := by
    unfold Thread.hand
    rw [treesTo_succ hblk, ho]
    rfl
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hσ
  rw [e] at h1
  simp [h1] at h2

end

/-! ## 3 The structure `NoHouse`; the hypotheses -/

/-- **What has to be proved at a sub-protocol without a prover's side**: conditions on the
sub-protocol's own step, at rounds that show no item and at no column, and on the `Thread`'s
parameters. A structure of hypotheses. -/
structure NoHouse (T : Thread Bk S Cl V W X Pb) (Said : Nat → Coins Bk → Mid W X → Prop)
    (fall : Nat → S → List Fmt.Drawn → Option String) (b : Nat) (blk : Block S Cl) : Prop where
  /- `blk` is the thread's sub-protocol number `b` -/
  seat : T.bs[b]? = some blk
  /- it is `Bare` at the thread's prover's sides -/
  bare : Bare T.hs blk
  /- `Said` passes from `b` to `b + 1` when the challenges are heard; asked at every `k`, `m`, `ds`,
  without `ThrS` -/
  said : ∀ k m ds, Said b k m → drawsFit blk.rounds ds = true → Said (b + 1) k (m.past ds)
  /- where the step accepts, at rounds that show no item and at no column: the form, the riders and
  `keeps` after it -/
  behind : ∀ k s m E ds s', ThrS T Said b k s m E → drawsFit blk.rounds ds = true →
    blk.step T.ft s (ds.map fun d => ⟨[], d⟩) [] = .ok (s', 0) →
    T.Form (b + 1) k s' (m.past ds) ∧ T.rides (b + 1) m.st.input s' ∧ T.keeps b s s'
  /- there also the items that the thread's row `b` owes -/
  owes : ∀ k s m E ds s', ThrS T Said b k s m E → drawsFit blk.rounds ds = true →
    blk.step T.ft s (ds.map fun d => ⟨[], d⟩) [] = .ok (s', 0) →
    T.Items (T.row b).owes k s' (m.past ds) E
  /- where no fall fires, the step accepts at such rounds -/
  yes : ∀ k s m E ds, ThrS T Said b k s m E → drawsFit blk.rounds ds = true →
    fall b s ds = none → ∃ s', blk.step T.ft s (ds.map fun d => ⟨[], d⟩) [] = .ok (s', 0)
  /- `RidesPastS` itself, taken as a hypothesis -/
  rides : RidesPastS T Said b

section
variable {T : Thread Bk S Cl V W X Pb} {Said : Nat → Coins Bk → Mid W X → Prop}
  {fall : Nat → S → List Fmt.Drawn → Option String} {b : Nat} {blk : Block S Cl}

/-- **The four hypotheses that say nothing of a fall.** -/
theorem noHouse_owes (N : NoHouse T Said fall b blk) :
    PlaysS T Said b ∧ BehindS T Said b ∧ ExchangeS T Said b ∧ RidesPastS T Said b := by
  refine ⟨playsS_bare T Said N.seat N.bare, ?_, ?_, N.rides⟩
  · intro blk' hblk' k s m E ds y cols s' hA hd hS
    rw [N.seat] at hblk'
    cases hblk'
    obtain ⟨hM, hstep⟩ := hS
    obtain ⟨a1, a2, -, rfl⟩ := moved_bare T N.bare hM
    rw [a1] at hstep
    rw [a2, past_input]
    exact N.behind k s m E ds s' hA hd hstep
  · intro blk' hblk' k s m E ds y cols s' hA hd hS
    rw [N.seat] at hblk'
    cases hblk'
    obtain ⟨hM, hstep⟩ := hS
    obtain ⟨a1, a2, a3, rfl⟩ := moved_bare T N.bare hM
    rw [a1] at hstep
    rw [a2, add_plain E (thr_tight T hA.1) y.1 a3]
    exact N.owes k s m E ds s' hA hd hstep

/-- **The acceptance (`AcceptedS`).** -/
theorem noHouse_yes (N : NoHouse T Said fall b blk) : AcceptedS T Said fall b := by
  intro blk' hblk' k s m E ds y cols hA hd _ hf hM
  rw [N.seat] at hblk'
  cases hblk'
  obtain ⟨a1, -, -, rfl⟩ := moved_bare T N.bare hM
  obtain ⟨s', hs'⟩ := N.yes k s m E ds hA hd hf
  exact ⟨s', hM, by rw [a1]; exact hs'⟩

/-- **`Said` holds after the sub-protocol (`SaidNext`).** -/
theorem noHouse_said (N : NoHouse T Said fall b blk) : SaidNext T Said b := by
  intro blk' hblk' k s m E ds y cols _ hS hd hM
  rw [N.seat] at hblk'
  cases hblk'
  obtain ⟨-, a2, -, rfl⟩ := moved_bare T N.bare hM
  rw [a2, took_nil]
  exact N.said k m ds hS hd

end

end ProofFile.Honest

#print axioms ProofFile.Honest.past_input
#print axioms ProofFile.Honest.play_bare
#print axioms ProofFile.Honest.reads_plain
#print axioms ProofFile.Honest.add_plain
#print axioms ProofFile.Honest.moved_bare
#print axioms ProofFile.Honest.flat_nil
#print axioms ProofFile.Honest.playsS_bare
#print axioms ProofFile.Honest.noHouse_owes
#print axioms ProofFile.Honest.noHouse_yes
#print axioms ProofFile.Honest.noHouse_said
#print axioms ProofFile.Honest.Mid.past
#print axioms ProofFile.Honest.Bare
#print axioms ProofFile.Honest.NoHouse
