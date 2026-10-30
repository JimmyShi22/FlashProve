-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/StateFirst.lean: long answers of a random oracle expanded from a short state.

Compile/Batch/CutLinks.lean calls this step "state first". The file has definitions and the
statement `Spec.stateFirst`; the proof ends in Rom/StateFirstTop.lean. A chain oracle (`Link.chain`;
in the scheme, the oracle for the rest of a Fiat-Shamir answer after its first block:
Compile/Batch/CutLinks.lean) is a random oracle whose answer is K hash blocks of `lam` bits, a
chaining value and one more hash block, which no algorithm reads (the unread last block; `HidFree`,
`agH` in Lean names). It is replaced by an oracle that returns a state of two hash blocks, the
chaining value and the unread last block, and hash block j of the old answer becomes dr (state, j)
for one new oracle dr. So a long query is hashed for its state only, not for every hash block. This
is the implementation's construction for its hash blocks from 1 on (by reading its sources: a state,
its first half as the tail, blocks derived from the whole state with a counter); there is no second
stage. Other oracles are unchanged (`Link.plain`).
`stSpec` is the second family of oracles; `OComp.stateFirst` and `stateFirstArg` are an algorithm
and a scheme over it. Both families are typed; Rom/Family.lean leads from the second to one hash
function.

`Spec.stateFirst`: let nC, nP, nV bound the queries at chain oracles of the committer, of the prover
(on batches of at most B) and of the verifier. Let the extractor read only entries at unchanged
oracles (`PlainOnly`), and let no algorithm of the scheme `A` read the last block (`HidFree`). If
`A` has completeness error α, index binding ε and index privacy ζ (`IsZKCPArgWith`, ZKCP/Gen.lean),
then `stateFirstArg C A` has, for `extSt C E` and `simSt C Sim`, the bounds

  α + n² / 2^(2 lam)                      with n = nC + nP + B nV,
  ε tC tP + n² / 2^(2 lam)                with n = tC + tP + nV,
  ζ t N + n² / 2^(2 lam) + t h / 2^lam    with h = nC + N nP and n = t + h.

The collision term (`collP`) is for the event that a new state equals an older state or the state in
an older query to dr. The guessing term (`hitP`) is for the event that the adversary queries dr at a
state of the honest side that it has not been shown: of such a state the first half may be known,
the second is not (`HidFree`). The arguments of ε and ζ do not change: a query to the second family
costs the reduction at most one query to the first.

Notation:
  `Dg lam`: a hash block, `Fin lam → Bool` (Rom/NeedA.lean)
  typed (the head of Rom/SpecCut.lean): oracles are typed: one for each kind of query, with
      structured inputs and outputs
  `FacOK ag A` (Rom/OverOneNGen.lean): the three algorithms read an answer only up to a relation ag
      on answers
  `CostBoundAt w t` (Rom/OverOneN.lean): on every path, whatever the answers and the coins, the
      weights w o q of the queries add up to at most t
  B, α, ε, ζ: in `IsZKCPArgWith R A B E Sim α ε ζ` (ZKCP/Gen.lean): a natural number B, a number α
      and two functions ε, ζ of two natural numbers; its fields: `HasCompletenessError R A B α`,
      `HasIndexBindingWith R A E ε`, `HasIndexPrivacyWith R A B Sim ζ`
  tC, tP: natural numbers, the arguments of ε; in `HasIndexBindingWith` (ZKCP/Gen.lean) with
      `Ct.QueryBound tC` and `(Pt st).QueryBound tP`
  t, N: natural numbers, the arguments of ζ; in `PrivacyFor` (ZKCP/Gen.lean) `ζ tV N`, with
      `(Vt ivk).QueryBound tV` (`AdvVerifier.QueryBound`, the same file; t is its tV); N counts
      batches
  `QueryBound` of `Ct`, `Pt st` (Rom/OComp.lean): at most t queries in all, on every path; a
      repeated query counts again

Limits. (1) Nothing is said about one hash function f: compose with `IsZKCPArgWith.overOne`
(Rom/Carry.lean); over f a state is then two queries, each on the whole typed query. (2) Querying
only the hash blocks that a round needs is a further step, which for algorithms that meet its
condition (`ReadsBy`) changes no result for any fixed family of functions (Rom/StateFirstLazy.lean).
(3) This file's model is not the released programs' (lean/LIMITS.md, L1); how the released programs
do it: docs/format/FORMAT.md. The released programs' hash function, and with it their tree hashes
and leaf hashes, is composed of a compression function (docs/format/FORMAT.md, section 3). Here
every hash block is derived from the state (a front block on the whole query: Rom/SpecCut.lean). (4)
The added terms are coarse: the second could be t / 2^lam plus about h² / 2^(lam + 1), a gain only
for h < 2 t. It is small only if h counts few queries, so nC and nP should bound the queries at
chain oracles, not all hash work. (5) Only the three properties are carried over: not adaptive or
refined completeness, correctness of extraction, or session-augmented index binding. (6) Nothing is
said on whether a given scheme meets the hypotheses. `HidFree` needs a hash block that no algorithm
reads: a wire record (Iop/BatchWire.lean) whose K is the largest number of hash blocks that a round
reads has none, and K must be taken one larger.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Rom.NeedA
import Rom.Carry
import Rom.OverOneNGen
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Rom
open ZKCP
open scoped ENNReal


/-- How an oracle with answers in R is treated. -/
inductive Link (lam : ℕ) (R : Type) : Type
  | plain : Link lam R
  | chain (K : ℕ) (e : R ≃ (Fin K → Dg lam) × Dg lam × Dg lam) : Link lam R

namespace Link
variable {lam : ℕ} {R : Type}

/-- what the oracle answers in the second family: as before, or a state (the chaining value, and its
hidden half, the unread last block) -/
def Ans : Link lam R → Type
  | .plain => R
  | .chain _ _ => Dg lam × Dg lam

instance finAns [Fintype R] : ∀ c : Link lam R, Fintype c.Ans
  | .plain => inferInstanceAs (Fintype R)
  | .chain _ _ => inferInstanceAs (Fintype (Dg lam × Dg lam))
instance neAns [Nonempty R] : ∀ c : Link lam R, Nonempty c.Ans
  | .plain => inferInstanceAs (Nonempty R)
  | .chain _ _ => inferInstanceAs (Nonempty (Dg lam × Dg lam))

def isPlain : Link lam R → Bool
  | .plain => true
  | .chain _ _ => false

/-- the number of expanded hash blocks of a chain oracle's answer (the answer has two more: the
chaining value and the unread last block); 0 for an unchanged oracle -/
def nK : Link lam R → ℕ
  | .plain => 0
  | .chain K _ => K

/-- the typed answer, where the oracle is unchanged -/
def back : (c : Link lam R) → c.Ans → Option R
  | .plain, r => some r
  | .chain _ _, _ => none

/-- the state in a typed answer: (chaining value, unread last block) -/
def stateOf : Link lam R → R → Option (Dg lam × Dg lam)
  | .plain, _ => none
  | .chain _ e, r => some (e r).2

/-- two typed answers agree but for the unread last block -/
def agH : Link lam R → R → R → Prop
  | .plain, r, r' => r = r'
  | .chain _ e, r, r' => (e r).1 = (e r').1 ∧ (e r).2.1 = (e r').2.1

/-- hash block j of a typed answer -/
def blockOf : Link lam R → R → ℕ → Option (Dg lam)
  | .plain, _, _ => none
  | .chain K e, r, j => if h : j < K then some ((e r).1 ⟨j, h⟩) else none

end Link

variable (S : OSpec) (lam : ℕ) (C : ∀ o, Link lam (S.Rng o))

/-- The second family. -/
def stSpec : OSpec where
  ι := S.ι ⊕ Unit
  Dom := fun x => match x with
    | .inl o => S.Dom o
    | .inr _ => (Dg lam × Dg lam) × ℕ
  Rng := fun x => match x with
    | .inl o => (C o).Ans
    | .inr _ => Dg lam
  finRng := fun x => match x with
    | .inl o => Link.finAns (C o)
    | .inr _ => inferInstanceAs (Fintype (Dg lam))
  neRng := fun x => match x with
    | .inl o => Link.neAns (C o)
    | .inr _ => inferInstanceAs (Nonempty (Dg lam))

variable {S lam} {α : Type}

/-- dr (σ, off), dr (σ, off + 1), .., one after the other -/
def askDr (σ : Dg lam × Dg lam) : (off K : ℕ) → OComp (stSpec S lam C) (Fin K → Dg lam)
  | _, 0 => .pure fun i => i.elim0
  | off, K + 1 => .query (S := stSpec S lam C) (.inr ()) (σ, off) fun r =>
      (askDr σ (off + 1) K).bind fun rest => .pure (Fin.cons (α := fun _ => Dg lam) r rest)

/-- from the answer of the second family to the typed answer -/
def expand {R : Type} : (c : Link lam R) → c.Ans → OComp (stSpec S lam C) R
  | .plain, r => .pure r
  | .chain K e, σ => (askDr C σ 0 K).bind fun bl => .pure (e.symm (bl, σ))

/-- The same algorithm over the second family. -/
def OComp.stateFirst : OComp S α → OComp (stSpec S lam C) α
  | .pure a => .pure a
  | .sample n k => .sample n fun r => (k r).stateFirst
  | .query o q k =>
    .query (S := stSpec S lam C) (.inl o) q fun a =>
      (expand C (C o) a).bind fun r => (k r).stateFirst

variable {I X W PP IVK ISK Pf : Type}

def stateFirstArg (A : Gen.Arg S I X W IVK ISK Pf) : Gen.Arg (stSpec S lam C) I X W IVK ISK Pf where
  C := fun i => (A.C i).stateFirst C
  P := fun k b => (A.P k b).stateFirst C
  V := fun v x π => (A.V v x π).stateFirst C

/-! ## The extractor -/

/-- the entries at unchanged oracles, as entries of the first family -/
def plainTr (tr : Trace (stSpec S lam C)) : Trace S :=
  tr.filterMap fun e => match e with
    | ⟨.inl o, q, a⟩ => ((C o).back a).map fun r => (⟨o, q, r⟩ : QA S)
    | ⟨.inr _, _, _⟩ => none

/-- the entries of a trace of the first family at unchanged oracles -/
def plainOf (tr : Trace S) : Trace S := tr.filter fun e => (C e.1).isPlain

/-- The extractor reads only entries at unchanged oracles. -/
def PlainOnly (E : Gen.Extractor S I X W IVK Pf) : Prop :=
  (∀ v tr, E.Ei v tr = E.Ei v (plainOf C tr)) ∧
  (∀ v tr x π tr', E.Ew v tr x π tr' = E.Ew v (plainOf C tr) x π (plainOf C tr'))

def extSt (E : Gen.Extractor S I X W IVK Pf) : Gen.Extractor (stSpec S lam C) I X W IVK Pf where
  Ei v tr := E.Ei v (plainTr C tr)
  Ew v tr x π tr' := E.Ew v (plainTr C tr) x π (plainTr C tr')

/-! ## The simulator -/

/-- what the simulator stores: the state of Sim; the chain answers that it has given, oldest first:
(oracle, query, typed answer); its answers of dr at other queries -/
structure SimSt (S : OSpec) (lam : ℕ) (T : Type) where
  s : T
  made : List (QA S)
  loose : List (((Dg lam × Dg lam) × ℕ) × Dg lam)

/-- the stored answer at the query (o, q) -/
def findMade (made : List (QA S)) (o : S.ι) (q : S.Dom o) : Option (S.Rng o) :=
  made.findSome? fun e =>
    if h : e.1 = o then (if h ▸ e.2.1 = q then some (h ▸ e.2.2) else none) else none

/-- hash block j of the oldest stored answer that has the state σ and a hash block j -/
def findBlock (made : List (QA S)) (σ : Dg lam × Dg lam) (j : ℕ) : Option (Dg lam) :=
  made.findSome? fun e => if (C e.1).stateOf e.2.2 = some σ then (C e.1).blockOf e.2.2 j else none

/-- the answer at an oracle of the first family: at an unchanged oracle Sim's answer; at a chain
oracle the state of the stored answer, or of a new one -/
def ansInl {T : Type} (ans : T → (o : S.ι) → S.Dom o → PMF (S.Rng o × T))
    (st : SimSt S lam T) (o : S.ι) (q : S.Dom o) :
    (c : Link lam (S.Rng o)) → PMF (c.Ans × SimSt S lam T)
  | .plain => (ans st.s o q).map fun out => (out.1, { st with s := out.2 })
  | .chain _ e =>
      match findMade st.made o q with
      | some r => PMF.pure ((e r).2, st)
      | none =>
        (ans st.s o q).map fun out =>
          ((e out.1).2, { st with s := out.2, made := st.made ++ [⟨o, q, out.1⟩] })

/-- the answer of dr -/
def ansDr {T : Type} (st : SimSt S lam T) (p : (Dg lam × Dg lam) × ℕ) :
    PMF (Dg lam × SimSt S lam T) :=
  match st.loose.lookup p with
  | some r => PMF.pure (r, st)
  | none =>
    match findBlock C st.made p.1 p.2 with
    | some r => PMF.pure (r, st)
    | none =>
      (PMF.uniformOfFintype (Dg lam)).map fun r => (r, { st with loose := (p, r) :: st.loose })

/-- The simulator over the second family. -/
def simSt (Sim : Gen.Simulator S PP IVK X Pf) :
    Gen.Simulator (stSpec S lam C) PP IVK X Pf where
  St := SimSt S lam Sim.St
  init := fun pp N => (Sim.init pp N).map fun out => (out.1, ⟨out.2, [], []⟩)
  answer := fun st x => match x with
    | .inl o => fun q => ansInl Sim.answer st o q (C o)
    | .inr _ => fun p => ansDr C st p
  prove := fun st xs => (Sim.prove st.s xs).map fun out => (out.1, { st with s := out.2 })

/-- The three algorithms do not read the last block of a chain answer. -/
def HidFree (A : Gen.Arg S I X W IVK ISK Pf) : Prop := FacOK (fun o _ r r' => (C o).agH r r') A

/-- the weight of a query: 1 at a chain oracle, 0 at an unchanged one -/
def wCh (o : S.ι) (_ : S.Dom o) : ℕ := if (C o).isPlain then 0 else 1

/-! ## The added error terms, and the statement -/

/-- the collision term: n new states, each against at most m older values, at 2 lam uniform bits -/
def collP (lam n m : ℕ) : ℝ≥0∞ := ((n * m : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ (2 * lam)
/-- the guessing term: t guesses, each against at most h hidden halves of lam bits -/
def hitP (lam t h : ℕ) : ℝ≥0∞ := ((t * h : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ lam

/-- The statement of this step. nC, nP, nV bound the queries of the three algorithms at chain
oracles (P's on batches of at most B); the extractor reads entries at unchanged oracles only
(PlainOnly); no algorithm reads the last block (HidFree; used for C and P, in the privacy clause).
(not all hypotheses are named here: see the statement below) -/
def Spec.stateFirst : Prop :=
  ∀ (S : OSpec) (lam : ℕ) (C : ∀ o, Link lam (S.Rng o)) (I X W PP IVK ISK Pf : Type)
      (R : Gen.RelPair I X W PP) (A : Gen.Arg S I X W IVK ISK Pf) (B : ℕ)
      (E : Gen.Extractor S I X W IVK Pf) (Sim : Gen.Simulator S PP IVK X Pf) (α : ℝ≥0∞)
      (ε ζ : ℕ → ℕ → ℝ≥0∞) (nC nP nV : ℕ),
    (∀ i, (A.C i).CostBoundAt (wCh C) nC) →
    (∀ k b, b.length ≤ B → (A.P k b).CostBoundAt (wCh C) nP) →
    (∀ v x π, (A.V v x π).CostBoundAt (wCh C) nV) → PlainOnly C E →
    HidFree C A → Gen.IsZKCPArgWith R A B E Sim α ε ζ →
    Gen.IsZKCPArgWith R (stateFirstArg C A) B (extSt C E) (simSt C Sim)
      (α + collP lam (nC + nP + B * nV) (nC + nP + B * nV))
      (fun tC tP => ε tC tP + collP lam (tC + tP + nV) (tC + tP + nV)) (fun t N =>
        ζ t N + collP lam (t + (nC + N * nP)) (t + (nC + N * nP)) + hitP lam t (nC + N * nP))

end Rom
