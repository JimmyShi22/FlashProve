-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Tied.lean: the condition `Tied` on the private input and the
explicit input of an honest side of a file's protocol that is written over the IOP as written in
Lean (`honestBatchProverOfFile`, Honest/StratC.lean); six equations `TiedAt` on the index committer's share
(Honest/Committer.lean); and that under these every valid pair is tied (`tied`). General in all
variables. Definitions, statements and proofs.

Why. A statement on such an honest side is made for pairs that are `Tied`. As long as the variables
in that condition are free it can be met trivially: by a relation that excludes some values of the
stored tables' pads and encoding randomness, by an external string that is not an encoder's table,
by plain parts that carry something of the index. `TiedAt` says what has to be proved of them at an
object with OOD samples.

  `Tied D F H J ext pubJ sh Rel w x`, with w = (index, r, OOD seed), where r is the stored tables'
     pads and encoding randomness. `rel`: Rel holds. `key`: the key that the shared part computes
     without an instance is the key that the prover reads from the explicit input. `table`: the
     prover's stored columns are the second halves of the external string's symbols, at every stored
     item that a declared round names. `seam`: what the three rounds without a challenge send is
     `pubJ` of the explicit input and the two coins r2, r3. `start`: the shared chain's first state
     is `sh` of that key. Of D it reads the depth alone.
  The variables of an object with OOD samples (`Iop.HolographicProtocol`, Hiop/RecInterface.lean): ans, Ryes; wr:
     the writing map, from the object's instance (request, OOD sample) to the explicit input; Cm:
     the index committer's share; kp: the key of an OOD sample; n: the copy's number, a parameter,
     fixed before the index.
  `relAt ans Ryes wr`: the explicit input is what is written for (a request x' with Ryes i x', the
     OOD sample of (i, r) at some OOD seed). Nothing else.
  `TiedAt`: six equations: `ood`, `writes`, `start`, `full`, `silent3`, `reads`.
  `tied`: under `TiedAt`, at every (index, r, OOD seed) and every instance a of the object that is
     valid for them (the two clauses of `HolographicProtocol.validB`): `Tied` at the explicit input wr a, for every
     prover H with the committer's stored table and key put in.
  `rel_of`: the guard on r: Ryes i x' gives `relAt` at what is written for x' and the sample at all
     r and s: the relation excludes no r and no OOD seed. `rel_iff`: where wr is one to one it is
     equivalent to Ryes i x'; `rel_iff_id`: so at the identity.

Limits.
  * `TiedAt` does not say that the committer's columns are an encoder's: at a committer whose
    columns are empty lists it holds too. Never quote `tied` without an equation "the committer's
    external string is the object's encoded index, whole symbols".
  * `TiedAt` has no clause on what the committer has beyond the table's length.
  * Ryes, ans, wr, kp, sh, pubJ are variables here: which relation, which answers and which map is
    for the caller to say.
  * n is fixed before the index. Who picks it is not said.
  * `Tied` does not exclude an IOP that rejects early at every coin. Nothing says that a run is
    played.
  * `Tied` may be read as part of a goal; it counts as none.
  * It is no statement on what a view shows, and none of zero knowledge.
  * The lemmas prove no property of a prover or a protocol.

Where this comes from. The file was written for another part of this project and was taken over from
it.
-/
import Johnson.Desc.ProofFile.Honest.StratC
import Johnson.Desc.ProofFile.Honest.Committer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open OnBytes.Slice (ofF)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (FileDescription)
open _root_.Run.PQ (SgX)

/-! ## 1. The condition -/

section Letters
variable {W₀ Rc Sd Xi Ky Tr X₀ Xh TF TJ T3 R₂ R₃ : Type} [Inhabited R₃] (D : WholeD)
  (F : FileDescription Xi) (H : Prover W₀ Rc Xi Ky Tr X₀ Xh)
  (J : R₂ → R₃ → KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3)
  (ext : W₀ × Rc × Sd → (Iop.oneExternalString (2 ^ D.a) SgX).Str) (pubJ : R₂ → R₃ → Xi → TF × TJ × T3)
  (sh : Ky → F.S₂) (Rel : W₀ → Rc → Xi → Prop)

/-- **The pairs (private input, explicit input) of which a statement on the honest side speaks.** -/
structure Tied (w : W₀ × Rc × Sd) (x : Xi) : Prop where
  /- Rel holds -/
  rel : Rel w.1 w.2.1 x
  /- the key that the shared part computes without an instance is the key that the prover reads from
  the explicit input -/
  key : ∀ r2 r3, (J r2 r3).keyOf w.1 w.2.1 w.2.2 = H.key x
  /- the prover's stored columns are the second halves of the external string's symbols, at every
  stored item that a declared round names -/
  table : ∀ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ s ∈ d.stored, ∀ (p : ℕ) (h : p < 2 ^ D.a),
    H.storedWords w.1 w.2.1 s.item p = some (ext w ⟨p, h⟩).2
  /-- what the three rounds without a challenge send is computed from the explicit input and the two
  coins (and from whatever is fixed in pubJ: below, the copy's number n); the joining round's is
  taken at r3 := `default`, as `honestBatchProverOfFile` takes it (Honest/StratC.lean) -/
  seam : ∀ r2 r3, ((J r2 r3).front w.1 w.2.1 w.2.2 x, (J r2 default).join w.1 w.2.1 w.2.2,
    (J r2 r3).seam w.1 w.2.1 w.2.2 x) = pubJ r2 r3 x
  /-- the shared chain's first state is a function of the key -/
  start : F.start₂ (F.pub x) = sh (H.key x)

end Letters

/-! ## 2. The six equations, and that they give the condition -/

section Equations
variable {I X RI Seed Ans Xi Ky Tr X₀ Xh TF TJ T3 R₂ R₃ : Type} (ans : I → RI → Seed → Ans)
  (Ryes : I → X → Prop) (wr : X × (Seed × Ans) → Xi) (Cm : Committer I RI Seed X Xi Ky)
  (kp : Seed × Ans → Ky) (n : ℕ) (D : WholeD) (F : FileDescription Xi) (sh : Ky → F.S₂)
  (front : ℕ → R₂ → R₃ → I → RI → Seed → Xi → TF) (join : R₂ → I → RI → Seed → TJ)
  (seam : R₂ → R₃ → I → RI → Seed → Xi → T3) (pubJ : ℕ → R₂ → R₃ → Xi → TF × TJ × T3)

/-- The relation: the explicit input is what is written for a request that holds at the index and
the OOD sample of (i, r) at some OOD seed. Nothing more. -/
def relAt : I → RI → Xi → Prop := fun i r ξ => ∃ s x', ξ = wr (x', (s, ans i r s)) ∧ Ryes i x'

/-- **The relation excludes no value of the stored tables' pads and encoding randomness and no OOD
seed.** -/
theorem rel_of (i : I) (r : RI) (s : Seed) (x' : X) (h : Ryes i x') :
    relAt ans Ryes wr i r (wr (x', (s, ans i r s))) := ⟨s, x', rfl, h⟩

/-- Where the writing map is one to one it is equivalent to Ryes. -/
theorem rel_iff (hw : Function.Injective wr) (i : I) (r : RI) (s : Seed) (x' : X) :
    relAt ans Ryes wr i r (wr (x', (s, ans i r s))) ↔ Ryes i x' :=
  ⟨fun ⟨_, x₂, e, h⟩ => by
    have e1 : x' = x₂ := congrArg Prod.fst (hw e)
    rw [e1]
    exact h, rel_of ans Ryes wr i r s x'⟩

/-- So at the identity as the writing map. -/
theorem rel_iff_id (ans : I → RI → Seed → Ans) (Ryes : I → X → Prop) (i : I) (r : RI) (s : Seed)
    (x' : X) : relAt ans Ryes id i r (x', (s, ans i r s)) ↔ Ryes i x' :=
  rel_iff ans Ryes id Function.injective_id i r s x'

/-- **The six equations** that whoever writes an honest side over a committer's share has to prove.
-/
structure TiedAt : Prop where
  /-- the committer's key without an instance is the key of the object's OOD sample -/
  ood : ∀ k : Isk I RI Seed, Cm.ood k = kp (k.seed, ans k.index k.coins k.seed)
  /-- the explicit input is what the writing map writes for the request and the OOD sample -/
  writes : ∀ (k : Isk I RI Seed) (x' : X),
    Cm.xi k x' = wr (x', (k.seed, ans k.index k.coins k.seed))
  /-- at written inputs: the shared chain's first state is a function of the key -/
  start : ∀ a : X × (Seed × Ans), F.start₂ (F.pub (wr a)) = sh (Cm.key (wr a))
  /-- the encoded index is whole below 2 ^ a -/
  full : ∀ i r p, p < 2 ^ D.a → (Cm.enc i r p).isSome = true
  /-- what the three rounds without a challenge send are functions of the explicit input, of n and
  of the two coins alone -/
  silent3 : ∀ r2 r3 (k : Isk I RI Seed) (x' : X),
    (front n r2 r3 k.index k.coins k.seed (Cm.xi k x'), join r2 k.index k.coins k.seed,
      seam r2 r3 k.index k.coins k.seed (Cm.xi k x')) = pubJ n r2 r3 (Cm.xi k x')
  /-- the key of a written input is the key of the OOD sample that was written -/
  reads : ∀ a : X × (Seed × Ans), Cm.key (wr a) = kp a.2

variable {ans Ryes wr Cm kp n D F sh front join seam pubJ}

/-- **Every valid pair is tied**: at every (index, the stored tables' pads and encoding randomness,
OOD seed) and every instance of the object that is valid for them. -/
theorem tied [Inhabited R₃] (h : TiedAt ans wr Cm kp n D F sh front join seam pubJ)
    (H : Prover I RI Xi Ky Tr X₀ Xh) (w : I × RI × Seed) (a : X × (Seed × Ans))
    (ha : a.2 = (w.2.2, ans w.1 w.2.1 w.2.2) ∧ Ryes w.1 a.1) :
    Tied D F (Cm.prover H) (fun r2 r3 => Cm.seam (front n r2 r3) (join r2) (seam r2 r3))
      (Cm.ext D.a) (pubJ n) sh (relAt ans Ryes wr) w (wr a) := by
  have ea : a = (a.1, (w.2.2, ans w.1 w.2.1 w.2.2)) := Prod.ext rfl ha.1
  have ex : Cm.xi ⟨w.1, w.2.1, w.2.2⟩ a.1 = wr a := by
    rw [h.writes]
    exact congrArg wr ea.symm
  refine ⟨⟨w.2.2, a.1, congrArg wr ea, ha.2⟩, fun _ _ => ?_, fun _ _ s _ p hp => ?_,
    fun r2 r3 => ?_, h.start a⟩
  · show Cm.ood ⟨w.1, w.2.1, w.2.2⟩ = Cm.key (wr a)
    rw [h.ood, h.reads, ha.1]
  · obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (h.full w.1 w.2.1 p hp)
    show (Cm.enc w.1 w.2.1 p).map (·.map ofF) = some (((Cm.enc w.1 w.2.1 p).getD []).map ofF)
    rw [hc]
    rfl
  · have e := h.silent3 r2 r3 ⟨w.1, w.2.1, w.2.2⟩ a.1
    rw [ex] at e
    exact e

end Equations

end ProofFile.Honest

#print axioms ProofFile.Honest.rel_of
#print axioms ProofFile.Honest.rel_iff
#print axioms ProofFile.Honest.rel_iff_id
#print axioms ProofFile.Honest.tied
