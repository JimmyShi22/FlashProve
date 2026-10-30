-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K13/Exact.lean: kind K13, the members' batching: the condition `exact`
of `Good` (Honest/Side.lean) at each of the kind's two parts. What a part shows, played alone by the
frame's `play`, over its own coins and the block that it spends, drawn uniformly, has the
distribution of what the simulator beside it outputs over its own coins. Definitions that the
statements need, and statements with their proofs.

The kind's row has two parts. Part 0 sends nothing in one round (`quietPart`, beside `quietSim`).
Part 1 is a masked sumcheck of kCol rounds after a first round of one scalar (the frame's `sumPart`
at the kind's job `k13Job`, lifted to the first chain's input, beside `sumSim`). It takes no coin of
its own and spends one block of 2 kCol + 1 coins of the index-mask message.

How. `exact_sum` is one call of the frame's statement for `sumPart` at every job
(`exact_sumPart_lift`, Honest/SumLaw/SumExact.lean). Its premises: the library's test on the call's
shape accepts (hk); the declared rounds state the call's scalars (`stated_R1`); the challenges fit
the declared rounds (hd). `exact_side` says the same at each member of a side that has the kind's
row beside a sub-protocol with the kind's rounds; `k13_exactMember` is that statement under the name
that the frame's lemmas take (`ExactMember`, Honest/Small/Field.lean), at any `On` and `bud`.

What is fixed before the coins are drawn, at any value: the state of the prover's run before the
part (m: the input, with the index and the stored tables' pads and encoding randomness; the
challenges heard; the rounds shown), what the simulator is handed (`front`), the part's challenges
(ds, which fit its declared rounds) and the positions read (asks). So the statement holds at each
fixed randomness of the committed tables. The kind's parts do not read that randomness: `k13Ask`
(Part.lean of this folder) reads the index and the public instance alone.

What the parts read of the rounds shown before them: nothing (`k13Job_noneSeen`, `k13P1_noneSeen`,
`members_noneSeen`). The frame's statement for `sumPart` leaves that condition to its caller.

  `k13_shapeOk`, `k13_shapeOk_false`, `shapeOk_of_pileForm`   the test on the shape accepts just
     where there is at least one variable; it accepts where the verifier's test on the pile's form
     does
  `sim_run`, `coinsE_range`, `shapeOf`, `range_two`, `cut_pairs`, `sim_shape`   the simulator takes
     2 kCol + 1 coins and outputs them in a row: one scalar, then pairs
  `k13P1`, `k13R1`, `stated_R1`   the sumcheck's part, its declared rounds, and that these state the
     call's scalars
  `exact_sum`   the condition at the sumcheck's part
  `k13_members`, `members_noneSeen`, `exact_side`, `k13_exactMember`   the members of a side with
     the kind's row; the condition at each of them

Limits.
  * This is the borrower's half. The block that part 1 spends is taken as uniform and independent of
    everything that is fixed. In a run these coins are mask entries of an oracle message that was
    sent earlier. That they are still uniform beside what their sender has shown is the condition
    `fresh` at the part that owns these coins in the book, at this part's address. It is not shown
    here, and the statements of this file say nothing about hiding without it.
  * Each statement is about one part. No joint distribution of the two parts, or with another part,
    is stated here; the frame's rule (`rule_views`, Honest/Law/Rule/Row.lean) joins parts.
  * `exact_sumPart_lift` holds at every job. So these statements do not say that the kind's job is
    the protocol's summand.
  * The job's functions are total: where fewer challenges were heard than the job reads, where the
    pile's rows do not fit, or where the matrix is read out of range, a default value stands for a
    challenge or a summand, never for a coin, and the statements hold there too.
  * All challenges are fixed in advance: the honest-verifier form.
  * A `Face` at this input exists at Pb := Xi alone (`Face.own`, Honest/Frame.lean); at any other Pb
    the statements that take a face hold vacuously.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.K13.Plays
import Johnson.Desc.ProofFile.Honest.K13.CoinsThere
import Johnson.Desc.ProofFile.Honest.SumLaw.SumExact
import Johnson.Desc.ProofFile.Honest.Small.Quiet
import Johnson.Desc.ProofFile.Honest.Small.NoneSeenSum
import Johnson.Desc.K13.OwnLaws
import Johnson.Desc.K13.Honest.Tell

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes (E)
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Oracle Place)
open VerifiableInference.Desc.Part.MaskedSum (Var ownSlots ownSlots_one_add shapeOk)
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Honest (onNat pairsOf tellL)
open ProofFile.Honest.SumLaw

/-! ## The test on the call's shape -/

/-- **The library's test on a masked sumcheck's shape** (`shapeOk`,
Johnson/Desc/Part/MaskedSum4.lean) **accepts the kind's shape just where there is at least one
variable.** -/
theorem k13_shapeOk (k : Nat) : shapeOk (k13Shape k) = true ↔ 1 ≤ k := by
  constructor
  · intro h
    cases k with
    | zero => exact absurd h (by decide)
    | succ n => omega
  · intro h
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    show ((List.replicate (n + 1) (Var.plain 3)).all
      (fun v => decide (2 ≤ v.d) && decide (v.d ≤ 65)) &&
        !(List.replicate (n + 1) (Var.plain 3)).isEmpty) = true
    rw [Bool.and_eq_true]
    refine ⟨List.all_eq_true.2 fun v hv => ?_, rfl⟩
    rw [List.eq_of_mem_replicate hv]
    rfl

/-- It rejects the kind's shape just where there is no variable. -/
theorem k13_shapeOk_false (k : Nat) : shapeOk (k13Shape k) = false ↔ k = 0 := by
  constructor
  · intro h
    by_contra hk
    rw [(k13_shapeOk k).2 (by omega)] at h
    cases h
  · rintro rfl
    rfl

/-- Where the verifier's own test on the pile's form accepts (`pileForm`,
Johnson/Desc/K13/Own.lean), the shape passes. -/
theorem shapeOk_of_pileForm (kCol : Nat) (pile : List OnBytes.TensorRow)
    (h : VerifiableInference.Desc.K13.Own.pileForm kCol pile = .ok ()) :
    shapeOk (k13Shape kCol) = true := by
  obtain ⟨_, _, hk, _⟩ := (VerifiableInference.Desc.K13.Own.pileForm_iff kCol pile).1 h
  exact (k13_shapeOk kCol).2 hk


/-! ## The counts, and what the simulator yields -/

/-- The simulator takes 2 k + 1 coins. -/
theorem sim_run (k : Nat) : runOf (k13Shape k) = 2 * k + 1 := by
  rw [← run_count, k13_ownRun]
  rfl

/-- Coins laid as the program's elements, as a list by number. -/
theorem coinsE_range {d : Due} (c : Cs d) :
    coinsE c = (List.range d.e).map fun j => k13E (onNat c.e j) := by
  unfold coinsE
  refine List.ext_getElem (by rw [List.length_ofFn, List.length_map, List.length_range]) ?_
  intro i h1 h2
  rw [List.getElem_ofFn, List.getElem_map, List.getElem_range]
  have hi : i < d.e := by
    rw [List.length_ofFn] at h1
    exact h1
  show _ = k13E (onNat c.e i)
  have e : onNat c.e i = c.e ⟨i, hi⟩ := dif_pos hi
  rw [e]
  rfl

/-- One scalar, then pairs, as rounds shown: no column. -/
def shapeOf (x : GE × List (GE × GE)) : Option (List Shown) :=
  some (⟨[.e (k13E x.1).triple], []⟩ ::
    x.2.map fun p => ⟨[.e (k13E p.1).triple, .e (k13E p.2).triple], []⟩)

/-- The first two of a list by number. -/
theorem range_two {β : Type} (g : Nat → β) (m : Nat) :
    (List.range (m + 2)).map g = g 0 :: g 1 :: (List.range m).map fun j => g (j + 2) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.range_succ_eq_map, List.map_cons,
    List.map_map]
  rfl

/-- A list by number, cut in twos. -/
theorem cut_pairs : ∀ (n : Nat) (w : Nat → GE),
    roundsCut (List.replicate n 2) ((List.range (2 * n)).map fun j => k13E (w j)) =
      (pairsOf w n).map fun p => [k13E p.1, k13E p.2]
  | 0, _ => rfl
  | n + 1, w => by
    have e : 2 * (n + 1) = 2 * n + 2 := by omega
    rw [e, range_two]
    show [k13E (w 0), k13E (w 1)] ::
      roundsCut (List.replicate n 2) ((List.range (2 * n)).map fun j => k13E (w (j + 2))) = _
    rw [cut_pairs n fun j => w (j + 2)]
    rfl

/-- **What the simulator yields has that shape**, at its coins in a row. -/
theorem sim_shape {Pb : Type} (a : Addr) (k : Nat) (pb : Pb) (front : Before)
    (ds : List Fmt.Drawn) (asks : List (List (List Nat))) (c : Cs (sumSim (Pb := Pb) a
      (k13Shape k)).takes) :
    (sumSim (Pb := Pb) a (k13Shape k)).tell pb front ds asks c = shapeOf (tellL (onNat c.e) k) := by
  show some ((roundsCut (scalarsOf (k13Shape k)) (coinsE c)).map fun l =>
    (⟨l.map fun x => .e x.triple, []⟩ : Shown)) = _
  rw [k13_scalars, coinsE_range]
  show some ((roundsCut (1 :: List.replicate k 2)
    ((List.range (runOf (k13Shape k))).map fun j => k13E (onNat c.e j))).map _) = _
  rw [sim_run, List.range_succ_eq_map, List.map_cons, List.map_map]
  show some ((([k13E (onNat c.e 0)] : List E) :: roundsCut (List.replicate k 2)
    ((List.range (2 * k)).map fun j => k13E (onNat c.e (j + 1)))).map _) = _
  rw [cut_pairs k fun j => onNat c.e (j + 1), List.map_cons, List.map_map]
  rfl

/-! ## The sentence -/

variable {W₀ Rc Xi Tr X : Type}

/-- The sumcheck's part, at the first chain's input. -/
abbrev k13P1 (weights : W₀ → Weights) (pile : PileOf Xi) (p : Where) :
    Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  (k13Sum p).lift (fun _ => ()) (k13Ask weights pile) (fun _ => ()) fun x _ => x

/-- Its declared rounds: "PSC epsilon", then kCol times "PSC round"; no oracle message. -/
def k13R1 (p : Where) : List (Fmt.DeclaredRound × List Oracle) :=
  ({ entry := VerifiableInference.Desc.K13.epsEntry p }, []) ::
    List.replicate p.lin.kCol ({ entry := VerifiableInference.Desc.K13.roundEntry p }, [])

/-- They state just the call's scalars, and no oracle message. -/
theorem stated_R1 (p : Where) : StatedBy (scalarsOf (k13Shape p.lin.kCol)) (k13R1 p) := by
  rw [k13_scalars]
  exact ⟨items_eps p, rfl, stated_rounds p p.lin.kCol⟩

/-- **The condition `exact` at the sumcheck's part**: the borrower's half (see the head's Limits).
`ca`: what the part carries: nothing. -/
theorem exact_sum {Pb : Type} (weights : W₀ → Weights) (pile : PileOf Xi) (p : Where)
    (hk : shapeOk (k13Shape p.lin.kCol) = true) (nm : String) (a a' : Addr)
    (v : Option (Local W₀ Rc Xi Tr))
    (m : Mid (Local W₀ Rc Xi Tr) X) (pb : Pb) (front : Before) (ds : List Fmt.Drawn)
    (hd : drawsFit ((k13R1 p).map (·.1)) ds = true) (asks : List (List (List Nat)))
    (ca : CsAll (k13P1 (Rc := Rc) (Tr := Tr) (X := X) weights pile p).carries) :
    (Prob.unif (Cs (k13P1 (Rc := Rc) (Tr := Tr) (X := X) weights pile p).takes ×
        CsAll (k13P1 (Rc := Rc) (Tr := Tr) (X := X) weights pile p).spends)).map
        (fun c => (play ((k13P1 weights pile p).steps nm a (k13R1 p) v (c.1, c.2, ca)) ds []
          m).toOption.map fun y => shownOf y.1 asks) =
      (Prob.unif (Cs (sumSim (Pb := Pb) a' (k13Shape p.lin.kCol)).takes)).map fun c =>
        (sumSim (Pb := Pb) a' (k13Shape p.lin.kCol)).tell pb front ds asks c :=
  exact_sumPart_lift (fun _ => ()) (k13Ask weights pile) (fun _ => ()) (fun x _ => x)
    (fun _ _ => rfl) (fun _ => rfl) (runName indexMaskRun ⟨k13Place p, 1⟩ "sum") "no ends"
    (k13Job p.lin.matrixRows p.lin.kCol) hk (k13R1 p) (stated_R1 p) rfl nm a a' v m pb front ds hd
    asks ca

/-! ## What the kind's job reads of what has been seen -/

/-- **The kind's job reads nothing of what has been seen**: of a front its five functions read what
was heard alone (`SumJob.readsNoneSeen`, Honest/Small/NoneSeenSum.lean: a sentence that can fail).
-/
theorem k13Job_noneSeen (nR k : Nat) : (k13Job nR k).readsNoneSeen := by
  intro w fr fr' hh _
  obtain ⟨heard, own, seen⟩ := fr
  obtain ⟨heard', own', seen'⟩ := fr'
  have hh' : heard = heard' := hh
  subst hh'
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **So the sumcheck's part, lifted to the first chain's input, reads nothing of what has been
seen**: each of its moves says the same at any two lists of rounds shown. -/
theorem k13P1_noneSeen (weights : W₀ → Weights) (pile : PileOf Xi) (p : Where) :
    (k13P1 (Rc := Rc) (Tr := Tr) (X := X) weights pile p).readsNoneSeen :=
  ProofFile.Honest.Small.lift_noneSeen _ _ _ _ _
    (ProofFile.Honest.Small.sumPart_noneSeen _ _ _ (k13Job_noneSeen p.lin.matrixRows p.lin.kCol))

/-! ## At a side -/

variable {S Cl Pb : Type}

/-- The members of a side that has the kind's row beside a sub-protocol with the kind's rounds. -/
theorem k13_members (weights : W₀ → Weights) (pile : PileOf Xi) (p : Where)
    (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (hrow : σ.row = k13Pairs weights pile p)
    (hr : σ.block.rounds = VerifiableInference.Desc.K13.battRounds p)
    (ho : σ.block.oracles = List.replicate (2 + p.lin.kCol) []) :
    σ.members =
      [⟨0, [({ entry := VerifiableInference.Desc.K13.sigmaEntry p }, [])], quietPart,
          quietSim ⟨k13Place p, 0⟩⟩,
        ⟨1, k13R1 p, k13P1 weights pile p, sumSim ⟨k13Place p, 1⟩ (k13Shape p.lin.kCol)⟩] := by
  have hn : (k13P1 (Rc := Rc) (Tr := Tr) (X := X) weights pile p).moves.length =
      1 + p.lin.kCol := by
    show ((k13Sum p).moves.map _).length = _
    rw [List.length_map, k13Sum_moves]
  have hR1 : (k13R1 p).length = 1 + p.lin.kCol := by
    show (List.replicate p.lin.kCol _).length + 1 = _
    rw [List.length_replicate]
    omega
  have hz : σ.block.rounds.zip σ.block.oracles =
      ({ entry := VerifiableInference.Desc.K13.sigmaEntry p }, []) :: k13R1 p := by
    rw [hr, ho, none_stated]
    show _ :: _ :: (List.replicate p.lin.kCol _).zip (List.replicate p.lin.kCol _) = _
    rw [List.zip_replicate']
    rfl
  unfold Side.members
  rw [hrow, hz]
  have ht : (k13R1 p).take (k13P1 (Rc := Rc) (Tr := Tr) (X := X) weights pile p).moves.length =
      k13R1 p := List.take_of_length_le (by rw [hR1, hn])
  show ([⟨0, _, _, _⟩, ⟨1, (k13R1 p).take (k13P1 (Rc := Rc) (Tr := Tr) (X := X) weights pile
    p).moves.length, _, _⟩] : List (Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)) = _
  rw [ht]
  rfl

/-- **No member's part of such a side reads anything of what has been seen.** -/
theorem members_noneSeen (weights : W₀ → Weights) (pile : PileOf Xi) (p : Where)
    (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (hrow : σ.row = k13Pairs weights pile p)
    (hr : σ.block.rounds = VerifiableInference.Desc.K13.battRounds p)
    (ho : σ.block.oracles = List.replicate (2 + p.lin.kCol) []) :
    ∀ u ∈ σ.members, u.part.readsNoneSeen := by
  intro u hu
  rw [k13_members weights pile p σ hrow hr ho] at hu
  rcases List.mem_cons.1 hu with rfl | hu
  · exact ProofFile.Honest.Small.quietPart_noneSeen 1
  · rcases List.mem_cons.1 hu with rfl | hu
    · exact k13P1_noneSeen weights pile p
    · cases hu

/-- **The condition `exact` at each member of such a side**, with no premise but that the challenges
fit the member's declared rounds: the borrower's half (see the head's Limits). -/
theorem exact_side (weights : W₀ → Weights) (pile : PileOf Xi) (p : Where)
    (hk : shapeOk (k13Shape p.lin.kCol) = true)
    (φ : Face (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Pb)
    (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (hrow : σ.row = k13Pairs weights pile p)
    (hr : σ.block.rounds = VerifiableInference.Desc.K13.battRounds p)
    (ho : σ.block.oracles = List.replicate (2 + p.lin.kCol) []) :
    ∀ u ∈ σ.members, ∀ (ca : CsAll u.part.carries) (m : Mid (Local W₀ Rc Xi Tr) X)
      (front : Before) (ds : List Fmt.Drawn) (asks : List (List (List Nat))),
      drawsFit (u.rounds.map (·.1)) ds = true →
      (Prob.unif (Cs u.part.takes × CsAll u.part.spends)).map
          (fun c => σ.shows φ u (c.1, c.2, ca) m ds asks) =
        (Prob.unif (Cs u.sim.takes)).map fun c => u.tells φ c m.st.input front ds asks := by
  intro u hu
  rw [k13_members weights pile p σ hrow hr ho] at hu
  rcases List.mem_cons.1 hu with rfl | hu
  · intro ca m front ds asks hd
    have hrs : ProofFile.Honest.Small.statedOf
        [(({ entry := VerifiableInference.Desc.K13.sigmaEntry p }, []) :
          Fmt.DeclaredRound × List Oracle)] = List.replicate 1 ([], []) := by
      show [(_, [])] = [([], [])]
      rw [items_sigma p]
    have hq := fun c => ProofFile.Honest.Small.shows_quiet φ σ 0 1 _ ⟨k13Place p, 0⟩ id id id
      (fun x _ => x) hrs c m ds asks hd
    rw [ProofFile.Honest.Small.quietPart_lift] at hq
    exact map_unif_point (some (List.replicate 1 ⟨[], []⟩)) _ _ (fun c => hq (c.1, c.2, ca))
      (fun _ => rfl)
  · rcases List.mem_cons.1 hu with rfl | hu
    · intro ca m front ds asks hd
      exact exact_sum weights pile p hk σ.block.name ⟨σ.block.place, 1⟩ ⟨k13Place p, 1⟩
        (φ.sees m.st.input) m (φ.pub m.st.input) front ds hd asks ca
    · cases hu

/-- **The same under the frame's name** (`ExactMember`, Honest/Small/Field.lean: the field `exact`
of `Good` at one member, without its hypothesis on the opened columns), at any chain, first tree,
`On` and `bud`: a statement that holds without these hypotheses holds under them. From it
`exactAt_of_exact` (the same file) gives the field's own text at every `pre`. -/
theorem k13_exactMember (weights : W₀ → Weights) (pile : PileOf Xi) (p : Where)
    (hk : shapeOk (k13Shape p.lin.kCol) = true)
    (φ : Face (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Pb)
    (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (hrow : σ.row = k13Pairs weights pile p)
    (hr : σ.block.rounds = VerifiableInference.Desc.K13.battRounds p)
    (ho : σ.block.oracles = List.replicate (2 + p.lin.kCol) []) (chain firstTree : Nat)
    (On : (u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) → CsAll u.part.carries →
      Mid (Local W₀ Rc Xi Tr) X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) :
    ∀ u ∈ σ.members, ProofFile.Honest.Small.ExactMember φ σ chain firstTree On bud u :=
  fun u hu ca m front ds asks _ _ hd _ _ _ =>
    exact_side weights pile p hk φ σ hrow hr ho u hu ca m front ds asks hd

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_shapeOk
#print axioms ProofFile.Honest.K13.k13_shapeOk_false
#print axioms ProofFile.Honest.K13.shapeOk_of_pileForm
#print axioms ProofFile.Honest.K13.sim_run
#print axioms ProofFile.Honest.K13.coinsE_range
#print axioms ProofFile.Honest.K13.range_two
#print axioms ProofFile.Honest.K13.cut_pairs
#print axioms ProofFile.Honest.K13.shapeOf
#print axioms ProofFile.Honest.K13.sim_shape
#print axioms ProofFile.Honest.K13.k13P1
#print axioms ProofFile.Honest.K13.k13R1
#print axioms ProofFile.Honest.K13.stated_R1
#print axioms ProofFile.Honest.K13.exact_sum
#print axioms ProofFile.Honest.K13.k13Job_noneSeen
#print axioms ProofFile.Honest.K13.k13P1_noneSeen
#print axioms ProofFile.Honest.K13.k13_members
#print axioms ProofFile.Honest.K13.members_noneSeen
#print axioms ProofFile.Honest.K13.exact_side
#print axioms ProofFile.Honest.K13.k13_exactMember
