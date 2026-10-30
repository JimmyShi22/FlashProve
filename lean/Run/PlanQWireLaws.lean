-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQWireLaws.lean: the wiring that is made from a chain's description obeys the laws of a wire,
given two laws on the kit of verifier's messages (and, for the wiring with the proof-of-work test,
at most 64 bits of work in every round). (64: the format's bound on a round's bits of work: `askOK`,
Fmt/Rules5.lean; the test reads one word.)

Statements and proofs. Tools on this library's own terms; no text is rendered.
A wiring (`ProtocolQueryLayout`, Iop/BatchWire.lean) is the data that say how deep the trees are, where a
position stands among a tree's leaves, and how hash output becomes challenges; the compiled verifier
(`Compile.Batch.verifyOneProtocol`, Compile/Batch/Verifier.lean) takes it beside the protocol. A wiring has a
wire for each round (`WireRB`). The laws of a wire are the conditions `WireRB.OK`, `ProtocolQueryLayout.OK` and,
where rounds may have a proof-of-work test, `ProtocolQueryLayout.OKG` of Iop/BatchWire.lean.
The kit is `C : CK` (Run/PlanQTypes.lean), the choice of challenge types.
Run/PlanQWire.lean makes the wires; Run/ToyQLaws.lean shows the laws, under a hypothesis of its own,
for one toy whose wires are written out term by term (Run/ToyQ.lean). Here they are shown for every
list of rounds' data, under the two hypotheses (for `wqT` also the bound on work). Many statements
of this library are written twice: a definition in the namespace `Spec` states a proposition, and a
theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

The two hypotheses, round by round, the first on the kit C and its sampler, the second on the kit
alone:
  `ChalUnif C K chal ds`: uniform blocks give a uniform verifier's message, exactly. Nothing here
    says at which rounds it holds. (For drawn positions below a power of two it is another file's
    theorem: Run/ToyChalLaw.lean: `poss_unif`, under the hypotheses of its statement. For a round
    that draws field elements it cannot hold exactly at the format's drawing, which has a cap on its
    tries: there the road to a theorem goes through block samplers with a bias, not through this
    law. Of the other kinds nothing is said.)
  `DrawnFits C ds`: the record of what was drawn holds at most as many positions as the plan's entry
    says.

Main names:
  `Spec.wireOf_ok`, `Spec.w0_ok`, `Spec.wiresL_ok`: the laws of a round's wire without a test
    (Iop/BatchWire.lean: `WireRB.OK`): a position's place is below 2 ^ depth; places and leaves
    answer each other; a round without a root has no position; the sampler's law; for one round, the
    trivial round, all rounds. The sampler's law is a hypothesis: of the one round in
    `Spec.wireOf_ok`, `ChalUnif` in `Spec.wiresL_ok`; `Spec.w0_ok` has no hypothesis.
  `Spec.wanted_len`: under `DrawnFits C ds`, at most `nOpen ds` pairs (tree, position) are asked
    for.
  `Spec.wq0_ok`: `ChalUnif` → `DrawnFits` → `(wq0 C K chal ds dec).OK`.
  `Spec.wqT_okg`: the same two, and every round has at most 64 bits of work →
    `(wqT C K chal ds dec).OKG`: the wiring with the test.

Limits: this file says nothing on the two hypotheses at a kit. It does not say that the protocol's
verifier is local, or that the protocol is sound for anything.
Terms: lean/GLOSSARY.md.
-/
import Run.PlanQWire
import Fmt.Rules6Laws
import Iop.GrindProofs

set_option autoImplicit false

namespace Run.PQ
open Iop Prob

/-- uniform blocks give a uniform verifier's message, in every round -/
def ChalUnif (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (ds : List RD) :
    Prop :=
  ∀ d ∈ ds, (unif (Fin K → Dig 256)).map (chal d.entry d.kind) = unif (C.Ch d.entry d.kind)

/-- what was drawn holds at most the entry's number of positions -/
def DrawnFits (C : CK) (ds : List RD) : Prop :=
  ∀ d ∈ ds, ∀ c, (C.dr d.entry d.kind c).poss.length ≤ d.entry.poss

namespace Spec

def wireOf_ok : Prop :=
  ∀ (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (d : RD),
    (unif (Fin K → Dig 256)).map (chal d.entry d.kind) = unif (C.Ch d.entry d.kind) →
    (wireOf C K chal d).OK

def w0_ok : Prop := ∀ K : Nat, (w0 K).OK

def wiresL_ok : Prop :=
  ∀ (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (ds : List RD),
    ChalUnif C K chal ds →
    RoundsQueryLayout.OK (shapeL C ds) (RoundSplits.allLocal (shapeL C ds)) (wiresL C K chal ds)

def wanted_len : Prop :=
  ∀ (C : CK) (ds : List RD),
    DrawnFits C ds → ∀ ρ : Rho (shapeL C ds), (wanted ds (drawnL C ds ρ)).length ≤ nOpen ds

def wq0_ok : Prop :=
  ∀ (Y : Type) (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
      (ds : List RD) (dec : Y → View → Bool),
    ChalUnif C K chal ds → DrawnFits C ds → (wq0 C K chal ds dec).OK

def wqT_okg : Prop :=
  ∀ (Y : Type) (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
      (ds : List RD) (dec : Y → View → Bool),
    ChalUnif C K chal ds → DrawnFits C ds →
    (∀ d ∈ ds, d.entry.work ≤ 64) → (wqT C K chal ds dec).OKG

end Spec

theorem posN_eq (t : Option _root_.Fmt.Shape) (h : t.isSome = true) : posN t = 2 ^ depthOf t := by
  cases t with
  | none => cases h
  | some s => rfl

theorem posN_none (t : Option _root_.Fmt.Shape) (h : t.isSome = false) : posN t = 0 := by
  cases t with
  | none => rfl
  | some s => cases h

theorem wireOf_ok : Spec.wireOf_ok := fun C K chal d hc =>
  { place_lt0 := fun _ h => by cases h
    place_ltJ := fun (p : Fin (posN d.tree)) _ => by
      show p.val < 2 ^ depthOf d.tree
      by_cases ht : d.tree.isSome = true
      · rw [← posN_eq _ ht]
        exact p.isLt
      · have h0 := posN_none d.tree (by simpa using ht)
        exact absurd (lt_of_lt_of_eq p.isLt h0) (Nat.not_lt_zero _)
    posAt0_place := fun _ h => by cases h
    posAtJ_place := fun (p : Fin (posN d.tree)) _ => by
      show (if h : p.val < posN d.tree then some (⟨p.val, h⟩ : Fin (posN d.tree)) else none) =
        some p
      rw [dif_pos p.isLt]
    place_posAt0 := fun _ _ h => by cases h
    place_posAtJ := fun j (p : Fin (posN d.tree)) h => by
      have h' : (if h : j < posN d.tree then some (⟨j, h⟩ : Fin (posN d.tree)) else none) =
          some p := h
      by_cases hj : j < posN d.tree
      · rw [dif_pos hj] at h'
        exact ⟨rfl, by rw [← Option.some.inj h']; rfl⟩
      · rw [dif_neg hj] at h'
        cases h'
    no0 := fun _ _ => rfl
    noJ := fun h j => by
      show (if h : j < posN d.tree then some (⟨j, h⟩ : Fin (posN d.tree)) else none) = none
      rw [dif_neg (by rw [posN_none d.tree h]; exact Nat.not_lt_zero _)]
    chal_unif := hc, gr0_none := rfl, grJ_none := rfl }

theorem unif_unit (Ch : Type) [Fintype Ch] [Nonempty Ch] :
    (unif Ch).map (fun _ => ()) = unif Unit := by
  rw [map_unif_eq_unif_iff]
  intro d
  simp [cnt]

theorem w0_ok : Spec.w0_ok := fun _ =>
  { place_lt0 := fun p => p.elim, place_ltJ := fun p => p.elim,
    posAt0_place := fun p => p.elim, posAtJ_place := fun p => p.elim
    place_posAt0 := fun _ _ h => by cases h
    place_posAtJ := fun _ _ h => by cases h
    no0 := fun _ _ =>
      rfl, noJ := fun _ _ => rfl, chal_unif := unif_unit _, gr0_none := rfl, grJ_none := rfl }

theorem wiresL_ok : Spec.wiresL_ok := by
  intro C K chal ds
  induction ds with
  | nil => intro _; trivial
  | cons d ds ih =>
      intro h
      exact ⟨wireOf_ok C K chal d (h d List.mem_cons_self),
        ih fun e he => h e (List.mem_cons_of_mem _ he)⟩

/-- one round's share -/
theorem share_len (all : List RD) (opens : List Nat) (D : _root_.Fmt.Drawn)
    (n : Nat) (h : D.poss.length ≤ n) :
    (opens.flatMap fun t => match treeSh all t with
      | none => []
      | some s => (_root_.Fmt.listOf (D.poss.map (· % 2 ^ s.a))).map fun x => (t, x)).length ≤ n * opens.length := by
  induction opens with
  | nil => simp
  | cons t ts ih =>
      rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_succ, Nat.add_comm]
      refine Nat.add_le_add ih ?_
      cases treeSh all t with
      | none => exact Nat.zero_le _
      | some s =>
          show ((_root_.Fmt.listOf (D.poss.map (· % 2 ^ s.a))).map fun x => (t, x)).length ≤ n
          rw [List.length_map]
          exact le_trans (_root_.Fmt.listOf_len _) (by rw [List.length_map]; exact h)

theorem wantedL_len (C : CK) (all : List RD) :
    ∀ (ds : List RD),
      DrawnFits C ds → ∀ ρ : Rho (shapeL C ds), (wantedL all ds (drawnL C ds ρ)).length ≤ nOpen ds
  | [], _, _ => Nat.le_refl _
  | d :: ds, h, (c, ρ) => by
      show (_ ++ wantedL all ds (drawnL C ds ρ)).length ≤
        (d.entry.poss * d.opens.length :: ds.map fun d => d.entry.poss * d.opens.length).sum
      rw [List.length_append, List.sum_cons]
      exact Nat.add_le_add (share_len all d.opens _ _ (h d List.mem_cons_self c))
        (wantedL_len C all ds (fun e he => h e (List.mem_cons_of_mem _ he)) ρ)

theorem wanted_len : Spec.wanted_len := fun C ds h ρ => wantedL_len C ds ds h ρ

theorem foldl_max_le (f : RD → Nat) :
    ∀ (ds : List RD) (a : Nat),
      a ≤ ds.foldl (fun a d => max a (f d)) a ∧ ∀ d ∈ ds, f d ≤ ds.foldl (fun a d => max a (f d)) a
  | [], a => ⟨Nat.le_refl _, fun _ h => by cases h⟩
  | e :: ds, a => by
      obtain ⟨h1, h2⟩ := foldl_max_le f ds (max a (f e))
      refine ⟨le_trans (le_max_left _ _) h1, fun d hd => ?_⟩
      rcases List.mem_cons.1 hd with rfl | hd
      · exact le_trans (le_max_right _ _) h1
      · exact h2 d hd

theorem depthL (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (n : Nat) :
    ∀ ds : List RD, (∀ d ∈ ds, depthOf d.tree ≤ n) →
      RoundsQueryLayout.DepthLe n (shapeL C ds) (RoundSplits.allLocal (shapeL C ds)) (wiresL C K chal ds)
  | [], _ => trivial
  | d :: ds, h =>
    ⟨⟨Nat.zero_le _, h d List.mem_cons_self⟩,
      depthL C K chal n ds fun e he => h e (List.mem_cons_of_mem _ he)⟩

theorem wq0_ok : Spec.wq0_ok := fun Y C K chal ds dec hc hd =>
  { sh := ⟨w0_ok K, wiresL_ok C K chal ds hc⟩
    ext := ⟨List.nodup_nil, fun p => p.elim0, fun _ p => p.elim0⟩
    opens := fun _ ρ _ => by
      show (List.toFinset _).card + (∅ : Finset Empty).card ≤ nOpen ds
      rw [Finset.card_empty, Nat.add_zero]
      exact le_trans (List.toFinset_card_le _)
        (le_trans (List.length_filterMap_le _ _) (wanted_len C ds hd ρ.2))
    depth := ⟨⟨Nat.zero_le _, Nat.zero_le _⟩,
      depthL C K chal _ ds (foldl_max_le (fun d => depthOf d.tree) ds 0).2⟩ }

theorem gL_le (C : CK) (n : Nat) : ∀ ds : List RD, (∀ d ∈ ds, d.entry.work ≤ n) → (gL C ds).AllLe n
  | [], _ => trivial
  | d :: ds, h => ⟨h d List.mem_cons_self, gL_le C n ds fun e he => h e (List.mem_cons_of_mem _ he)⟩

theorem wqT_okg : Spec.wqT_okg := fun Y C K chal ds dec hc hd hw =>
  ProtocolQueryLayout.OKG.grindLocal (wq0_ok Y C K chal ds dec hc hd).toG (D := Dn) (n := 64)
    (fun _ _ _ _ => rfl) (by decide) (g := gOf C ds) ⟨Nat.zero_le _, gL_le C 64 ds hw⟩

end Run.PQ
