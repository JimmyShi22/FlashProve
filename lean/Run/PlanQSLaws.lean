-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQSLaws.lean: facts about the protocol and wiring of Run/PlanQS.lean that the library's
theorems ask for.

Why. Run/PlanQS.lean writes rounds, protocol, wiring and interface again as skeletons, so that the
evaluator can run them, and proves of the verifier one thing: what is evaluated is the run of
`Compile.Batch.verifyOneProtocol` at `(PSof C ds dec).up` and `wqS`. For a theorem of the library to speak
of that run, its hypotheses have to be met at these very terms. Here are four of them (`psof_up`,
`psof_local`, `wqS_okg`, which has three hypotheses of its own, `shapeS_eq`), with two auxiliary
statements (`viewS_congr`, `wireS_eq`). They are generic: every choice of challenge types C (for
each round the type of the verifier's message, and the map from such a message to the format's
record of what was drawn; `CK` in the code), every list ds of rounds' data, every decision dec on
the view.
A wiring is the data that say how deep the trees are, where a position stands among a tree's leaves,
and how hash output becomes challenges (`ProtocolQueryLayout`, Iop/BatchWire.lean); its laws are the conditions
`ProtocolQueryLayout.OKG` there.

The two interfaces. The run functions do not stand at the interface `LtS` but at `LbS`
(Run/PlanQS.lean). The Batch of `LbS` is the same protocol (`(PSof C ds dec).up.loc`, local rounds
alone). In the theorems vbs_*, vbsP_*, vbsPF_* of Run/M1RunTie.lean and its companion files,
Run/M2Tie.lean and Run/PlanQSToy.lean, the field B of the wiring of `LbS` (`Wb`, Run/PlanQS.lean) is
the same `wqS` or `wqSF` (Run/PlanQSF.lean). (For both: `batch_same`, Run/BatchS.lean.) What is said
here of `LtS`, of its Test and of wirings holds as it stands, for these are facts about terms.

1. What the file contains. Statements (`Run.PQ.Spec.*`) and their proofs.

2. What is checked when the file compiles. Only the types and the proofs.

3. Theorems.
   `psof_up`            `(PSof C ds dec).up = BatchInteractiveOracleProof.ofProto (LtS C ds dec).offline`. The batch
                        protocol at which `verifyOneProtocol` is run is "the interface's Test, local rounds
                        only". (The protocols are the same term; the two annotations "all rounds
                        local" are equal by induction on the rounds.)
   `rhoS_eq`            (A tool of the proofs, without a Spec.)
   `viewS_congr`        Two transcripts with the same verifier messages and plain parts that agree
                        at the wanted positions have the same view.
   `psof_local`         `(PSof C ds dec).up.loc.IsLocal` (Iop/InteractiveOracleProof.lean): the decision depends on
                        the oracles only at the positions read. For every dec.
   `wireS_eq`           The wiring of a round is what the library's step for a round with a test of
                        work makes of Run/PlanQWire.lean's wiring.
   `wqS_okg`            `ChalUnif C K chal ds` → `DrawnFits C ds` → (every round's work ≤ 64) →
                        `(wqS C K chal ds dec).OKG` (Iop/BatchWire.lean). That is: places and leaves
                        answer each other; a component without a tree has no position; uniform
                        blocks give uniform verifier messages, test bits among them; nonces are read
                        back; at most `nOpen ds` openings; depths at most `maxDepth ds`. The three
                        hypotheses are those of the law of Run/PlanQWire.lean's wiring
                        (Run/PlanQWireLaws.lean: `wqT_okg`).
   `shapeS_eq`          `Twin.up (SL C ds) = (shapeL C ds).grind ℕ (gL C ds)`.

4. What is not claimed.
   A limit that weighs (found in a second, independent reading). `ChalUnif` is an equation of laws:
   uniform blocks give an exactly uniform verifier message. With challenges as sampled values (a
   round's verifier message is the values of the format's draws) it holds for rounds that draw
   positions, pairs of bits, a sealed value or nothing, and it is false for every round that draws a
   field element: after six failing tries the element is 0, so 0 is a little likelier than the other
   values (Run/DrawPage.lean has the bias as a bound). So `wqS_okg` cannot be applied, with
   challenges as sampled values, to a protocol whose rounds draw field elements. For these the law
   of a wiring would have to take a bias in the place of the equation (the form of Iop/Draw.lean:
   `Shape.Draws.Good`). By another such reading, the library has no such form of a wiring's law and
   goes another way: the protocol is changed first (Iop/BatchWireDraw.lean: a round's verifier
   message becomes its string of blocks, reads and decision apply the sampler, the wiring hands
   blocks on). That wiring's equation is exact, and the bias goes into the numbers. So for such a
   protocol the law is to be had in that form only. It is not here; it is Run/PlanPull.lean's
   `planPull_okg`.
   `DrawnFits` at a given choice of challenge types. The laws of a whole wiring of the interface
   (`QueryLayout.OKG`), of which `wqS_okg` is one clause (Run/M1Door.lean, Run/BatchDoor.lean). Nothing on
   how queries are spelled, on a parser, on the hash or on a file.
   No statement on soundness.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PlanQS
import Run.PlanQLocal
import Run.PlanQWireLaws

set_option autoImplicit false

namespace Run.PQ
open Iop Rom Compile Compile.Batch Prob
open Run.Twin (RS PS)

namespace Spec

/-- States: the protocol that is run, `(PSof C ds dec).up`, is the Test of its own interface
`LtS C ds dec`, local rounds only. -/
def psof_up : Prop :=
  ∀ (C : CK) (ds : List RD) (dec : View → Bool),
    (PSof C ds dec).up = BatchInteractiveOracleProof.ofProto (LtS C ds dec).offline

def viewS_congr : Prop :=
  ∀ (C : CK) (ds : List RD) (τ τ' : Iop.Tr (uL C ds)), τ.rho = τ'.rho → τ.plains = τ'.plains →
    (∀ nx ∈ wanted ds (drawnSL C ds τ.rho),
      ∀ p, posAtS C ds nx.1 nx.2 = some p → τ.read p = τ'.read p) →
    viewSL C ds τ = viewSL C ds τ'

/-- States: the verifier is local (`InteractiveOracleProof.IsLocal`, Iop/InteractiveOracleProof.lean). -/
def psof_local : Prop :=
  ∀ (C : CK) (ds : List RD) (dec : View → Bool), (PSof C ds dec).up.loc.IsLocal

def wireS_eq : Prop :=
  ∀ (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (d : RD),
    wireS C K chal d = (wireOf C K chal d).grindLocal Dn d.entry.work

/-- States: under `ChalUnif C K chal ds`, `DrawnFits C ds` and work ≤ 64 in every round, the wiring
obeys the laws (`ProtocolQueryLayout.OKG`). Where `ChalUnif` fails: the head, 4. -/
def wqS_okg : Prop :=
  ∀ (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
      (ds : List RD) (dec : View → Bool),
    ChalUnif C K chal ds → DrawnFits C ds →
    (∀ d ∈ ds, d.entry.work ≤ 64) → (wqS C K chal ds dec).OKG

def shapeS_eq : Prop :=
  ∀ (C : CK) (ds : List RD), Twin.up (SL C ds) = (shapeL C ds).grind ℕ (gL C ds)

end Spec

/-! ## The protocol is the interface's Test -/

theorem psof_up : Spec.psof_up := fun C ds dec =>
  congrArg (BatchInteractiveOracleProof.mk (PSof C ds dec).up.loc) (Twin.allLo_eq (SOf C ds))

/-! ## The verifier is local -/

theorem rhoS_eq (C : CK) : ∀ (ds : List RD) (τ : Iop.Tr (uL C ds)), rhoSL C ds τ = τ.rho
  | [], _ => rfl
  | _ :: ds, (_, c, τ) => congrArg (Prod.mk c) (rhoS_eq C ds τ)

theorem rvS_congr (C : CK) :
    ∀ (ds : List RD) (τ τ' : Iop.Tr (uL C ds)),
      τ.rho = τ'.rho → τ.plains = τ'.plains → rvSL C ds τ = rvSL C ds τ'
  | [], _, _, _, _ => rfl
  | d :: ds, (m, c, τ), (m', c', τ'), hρ, hp => by
      have e1 : c = c' := congrArg Prod.fst hρ
      have e2 : τ.rho = τ'.rho := congrArg Prod.snd hρ
      have e3 : m.2 = m'.2 := congrArg Prod.fst hp
      have e4 : τ.plains = τ'.plains := congrArg Prod.snd hp
      show (⟨PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2),
            C.dr d.entry d.kind (GChal.old (b := d.entry.work) c)⟩ : RV) :: rvSL C ds τ =
        ⟨PlainOf.gots d.items (GPlain.old (b := d.entry.work) m'.2),
            C.dr d.entry d.kind (GChal.old (b := d.entry.work) c')⟩ :: rvSL C ds τ'
      rw [e1, e3, rvS_congr C ds τ τ' e2 e4]

theorem colAtS_congr (C : CK) :
    ∀ (ds : List RD) (τ τ' : Iop.Tr (uL C ds)) (n x : Nat),
      (∀ p, posAtS C ds n x = some p → τ.read p = τ'.read p) →
      colAtS C ds τ n x = colAtS C ds τ' n x
  | [], _, _, _, _, _ => rfl
  | d :: ds, (m, c, τ), (m', c', τ'), n, x, h => by
      unfold colAtS
      unfold posAtS at h
      by_cases ht : d.tree.isSome = true
      · rw [if_pos ht, if_pos ht]
        rw [if_pos ht] at h
        by_cases hn : n = 0
        · rw [if_pos hn, if_pos hn]
          rw [if_pos hn] at h
          by_cases hx : x < posN d.tree
          · rw [dif_pos hx, dif_pos hx]
            rw [dif_pos hx] at h
            have e : m.1 ⟨x, hx⟩ = m'.1 ⟨x, hx⟩ := h _ rfl
            rw [e]
          · rw [dif_neg hx, dif_neg hx]
        · rw [if_neg hn, if_neg hn]
          rw [if_neg hn] at h
          refine colAtS_congr C ds τ τ' (n - 1) x fun p hp => ?_
          exact h (.inr p) (by rw [hp]; rfl)
      · rw [if_neg ht, if_neg ht]
        rw [if_neg ht] at h
        refine colAtS_congr C ds τ τ' n x fun p hp => ?_
        exact h (.inr p) (by rw [hp]; rfl)

theorem viewS_congr : Spec.viewS_congr := by
  intro C ds τ τ' hρ hp hr
  unfold viewSL
  rw [rvS_congr C ds τ τ' hρ hp, rhoS_eq, rhoS_eq, ← hρ]
  congr 1
  refine filterMap_congr_mem _ _ _ fun nx hnx => ?_
  rw [colAtS_congr C ds τ τ' nx.1 nx.2 (hr nx hnx)]

theorem psof_local : Spec.psof_local := by
  rintro C ds dec x y y' ⟨m0, c0, τ⟩ ⟨m0', c0', τ'⟩ hρ hp _ hr
  have e1 : τ.rho = τ'.rho := congrArg Prod.snd hρ
  have e2 : τ.plains = τ'.plains := congrArg Prod.snd hp
  show (passSL C ds (rhoSL C ds τ) && dec (viewSL C ds τ)) =
    (passSL C ds (rhoSL C ds τ') && dec (viewSL C ds τ'))
  rw [rhoS_eq, rhoS_eq, ← e1, viewS_congr C ds τ τ' e1 e2 fun nx hnx p hpos => ?_]
  refine hr (Sum.inr p) ?_
  show (Sum.inr p : OPos (Twin.up (SOf C ds))) ∈
    (((wanted ds (drawnSL C ds τ.rho)).filterMap fun nx =>
      (posAtS C ds nx.1 nx.2).map fun p => (Sum.inr p : OPos (Twin.up (SOf C ds))))).toFinset
  rw [List.mem_toFinset, List.mem_filterMap]
  exact ⟨nx, hnx, by rw [hpos]; rfl⟩

/-! ## The wiring -/

theorem wireS_eq : Spec.wireS_eq := fun _ _ _ _ => rfl

theorem wireS_okg (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (d : RD)
    (hc : (unif (Fin K → Dig 256)).map (chal d.entry d.kind) = unif (C.Ch d.entry d.kind))
    (hw : d.entry.work ≤ 64) : (wireS C K chal d).OKG :=
  WireRB.OKG.grindLocal (wireOf_ok C K chal d hc).toG
    (D := Dn) (n := 64) (fun _ _ _ _ => rfl) (by decide) hw

/-- every map from a nonempty type into a type with one value carries the uniform distribution to
the uniform distribution -/
theorem unif_unique {A T : Type} [Fintype A] [Nonempty A] [Fintype T] [Nonempty T]
    [Subsingleton T] (g : A → T) : (unif A).map g = unif T := by
  rw [map_unif_eq_unif_iff]
  intro d
  have h1 : ∀ a, g a = d := fun a => Subsingleton.elim _ _
  have h2 : Fintype.card T = 1 := Fintype.card_eq_one_iff.2 ⟨d, fun y => Subsingleton.elim _ _⟩
  simp [cnt, h1, h2]

theorem wire0S_okg (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) :
    (wire0S C K chal).OKG :=
  { place_lt0 := fun p => p.elim, place_ltJ := fun p => p.elim,
    posAt0_place := fun p => p.elim, posAtJ_place := fun p => p.elim
    place_posAt0 := fun _ _ h => by cases h
    place_posAtJ := fun _ _ h => by cases h
    no0 := fun _ _ => rfl, noJ := fun _ _ => rfl, chal_unif := unif_unique _
    gr0_ok := fun _ e => by cases e
    grJ_ok := fun _ e => by cases e }

theorem wiresS_okg (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) :
    ∀ ds : List RD, ChalUnif C K chal ds → (∀ d ∈ ds, d.entry.work ≤ 64) →
      RoundsQueryLayout.OKG (uL C ds) (Twin.allLo (SL C ds)) (wiresSL C K chal ds)
  | [], _, _ => trivial
  | d :: ds, hc, hw =>
    ⟨wireS_okg C K chal d (hc d List.mem_cons_self) (hw d List.mem_cons_self),
      wiresS_okg C K chal ds (fun e he => hc e (List.mem_cons_of_mem _ he)) fun e he =>
        hw e (List.mem_cons_of_mem _ he)⟩

theorem wantedSL_len (C : CK) (all : List RD) :
    ∀ (ds : List RD),
      DrawnFits C ds → ∀ ρ : Rho (uL C ds), (wantedL all ds (drawnSL C ds ρ)).length ≤ nOpen ds
  | [], _, _ => Nat.le_refl _
  | d :: ds, h, (c, ρ) => by
      show (_ ++ wantedL all ds (drawnSL C ds ρ)).length ≤
        (d.entry.poss * d.opens.length :: ds.map fun d => d.entry.poss * d.opens.length).sum
      rw [List.length_append, List.sum_cons]
      exact Nat.add_le_add (share_len all d.opens _ _ (h d List.mem_cons_self _))
        (wantedSL_len C all ds (fun e he => h e (List.mem_cons_of_mem _ he)) ρ)

theorem depthSL (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (n : Nat) :
    ∀ ds : List RD, (∀ d ∈ ds, depthOf d.tree ≤ n) →
      RoundsQueryLayout.DepthLe n (uL C ds) (Twin.allLo (SL C ds)) (wiresSL C K chal ds)
  | [], _ => trivial
  | d :: ds, h =>
    ⟨⟨Nat.zero_le _, h d List.mem_cons_self⟩,
      depthSL C K chal n ds fun e he => h e (List.mem_cons_of_mem _ he)⟩

theorem wqS_okg : Spec.wqS_okg := fun C K chal ds dec hc hd hw =>
  { sh := ⟨wire0S_okg C K chal, wiresS_okg C K chal ds hc hw⟩
    ext := ⟨List.nodup_nil, fun p => p.elim0, fun _ p => p.elim0⟩
    opens := fun _ ρ _ => by
      show (List.toFinset _).card + (∅ : Finset Empty).card ≤ nOpen ds
      rw [Finset.card_empty, Nat.add_zero]
      exact le_trans (List.toFinset_card_le _)
        (le_trans (List.length_filterMap_le _ _) (wantedSL_len C ds ds hd ρ.2))
    depth := ⟨⟨Nat.zero_le _, Nat.zero_le _⟩,
      depthSL C K chal _ ds (foldl_max_le (fun d => depthOf d.tree) ds 0).2⟩ }

/-! ## The shape -/

theorem shapeS_eq : Spec.shapeS_eq := fun C ds => by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
      show (roundS C d).up :: Twin.up (SL C ds) =
        (roundOf C d).grind ℕ d.entry.work :: (shapeL C ds).grind ℕ (gL C ds)
      rw [ih]
      rfl

end Run.PQ
