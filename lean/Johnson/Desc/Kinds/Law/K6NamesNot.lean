-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6NamesNot.lean: WHICH ARRAYS THE OUTPUT HEAD's CLAIMS NAME: the claims of
its runs "norm", "policy", "logits", the key vectors that it hands to the lookup's run "join" and
the forms that it hands to the lookup's run "planes" name entries of the array of the head's reads
(number iU3) alone, and no run of entries. Asked for a count of the weights on the digits' array and
on the symbol arrays. Statements and proofs.

What it is not. Implications. FOUR PREMISES ARE NAMED, AND NOT SHOWN HERE BUT WHERE IT IS SAID:
K6HeardAt at s0 (the head's hearing is read back there: paid in the statements at 347 alone: at a
state reached in front of the head's batching, in the goals' scope, where the public files are read
and opened into the letters at the format's second hash function, under the test on the plan of the IOP as
written in Lean) · AlikeFront s0 s (the state in front of a run goes on from s0, as far as the
readers in front of the reads see; the forms with Alike s0 s, which has two clauses more, on the
reads, follow by one call each, and spend these two nowhere) · t ≠ iU3 (that the array of the reads
is none of the digits' and the symbols': a fact on the plan's numbers and on the approximate range
proof's structure at the state; in the statements at 347 iU3 is read off the public parameters, and
that the state's structure names the same number is not shown) · the kind's test on the plan (p.ok:
paid in the statements at 347 out of the test on the plan of the IOP as written in Lean:
parOk_open). Nothing on the claims of "join" and "planes" themselves: their texts are the lookup's,
and they hold forms that the lookup's hearing laid. Nothing on rows and columns (Law/K6RunsRow0.lean
has these, at other letters, under further premises). Nothing on soundness or on any other property
of the protocol.

WHOSE IS NamesNot? It is typed here to the sign of the sentence as it was asked, so that the
statements below can be read; where the count's own files type it, this definition should fall and
the statements be held at theirs.

  `NamesNot t cl`      the claim names no entry and no run of array t
  `entsAt_ent`, `entsAt_entryAt`   the form of one entry, and so of a read's entry, names its own
                       array alone, whatever the position
  `entriesAt_reads`    so do all entries that the seat's reader of the reads' places hands
  `letters_ents`       at the letters read at a state where the head's hearing is read back: the
                       premises of Law/FourRunsCell.lean's claims_ents | keyVector_ents
  `namesNot_run_front`, `namesNot_run`     **the three runs**: under AlikeFront; under Alike
  `namesNot_keys_front`, `namesNot_keys`   **the key vectors**: under AlikeFront; under Alike
  `namesNot_readers`   **the planes' readers' forms**: no premise but t ≠ iU3
  `parOk_open`         in the goals' scope the kind's test on the plan follows from that of the IOP
                       as written in Lean
  `namesNot_run_front_347`, `namesNot_keys_front_347`, `namesNot_run_347`, `namesNot_keys_347`
                       the four where s0 is a state reached in front of the head's batching (by
                       Johnson/Desc/First/Link/Law/K6HeardAtBatch.lean)

-/
import Mathlib
import Johnson.Desc.Kinds.Law.FourRunsCell
import Johnson.Desc.Kinds.Law.RunsFixedFront
import Johnson.Desc.Kinds.Law.PlanesArm
import Johnson.Desc.Kinds.Law.SeatedBridge
import Johnson.Desc.First.Link.Law.K6HeardAtBatch
import Johnson.IMR.K6Seat
import Johnson.IMR.PlanAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (oneE)
open OnBytes.Model (Aff)
open VerifiableInference.Desc (Block Chain FileDescription Claim)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied (RchAt)

/-- The claim names no entry and no run of entries of array t. -/
def NamesNot (t : ℕ) (cl : Claim) : Prop :=
  (∀ x ∈ cl.form.ents, x.tree ≠ t) ∧ ∀ u ∈ cl.runs, u.tree ≠ t

/-- The form of one entry names that entry's array alone. -/
theorem entsAt_ent (t r i : Nat) : EntsAt (fun t' _ _ => t' = t) (Aff.ent t r i) := by
  intro y hy
  obtain rfl : y = { tree := t, row := r, idx := i, coef := oneE } := by
    simpa [Aff.ent] using hy
  exact rfl

/-- The form of a read's entry names array iU3 alone, whatever the position. -/
theorem entsAt_entryAt (iU3 K3 pos : Nat) : EntsAt (fun t _ _ => t = iU3) (entryAt iU3 K3 pos) := by
  unfold entryAt
  exact entsAt_ent iU3 _ _

/-- All entries that the seat's reader of the reads' places hands name array iU3 alone. The sizes
are a letter: the bound on the index is not spent. -/
theorem entriesAt_reads [Sizes] (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (s : S)
    (x : FinalNorm.Reads × Reads) (hx : (seatAt h iU3).reads s = some x) :
    EntriesAt (fun t _ _ => t = iU3) x.1 x.2 := by
  obtain ⟨o, F, tt, tr, -, -, -, -, -, a1, a2, a3⟩ := reads_are h iU3 s x hx
  refine ⟨fun r i _ => ?_, fun i _ => ?_, fun r i _ => ?_⟩
  · rw [a1 r i]
    exact entsAt_entryAt _ _ _
  · rw [a2 i]
    exact entsAt_entryAt _ _ _
  · rw [a3 r i]
    exact entsAt_entryAt _ _ _

section At

variable (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (p : Par)

/-- **At the letters that are read at a state where the head's hearing is read back.** -/
theorem letters_ents (hok : p.ok = true) {s : S} (k : K6HeardAt h iU3 p s)
    {v : Given × Behind × Places} (hv : lettersAt p (seatAt h iU3) s = .ok v) :
    (letI := v.1
     letI := v.2.1
     EntriesAt (fun t _ _ => t = iU3) v.2.2.final v.2.2.head) ∧
    (letI := v.1
     letI := v.2.1
     HeardBare) ∧
    (letI := v.1
     Norm.S2 ∣ Norm.d) ∧
    (letI := v.1
     JVa ≤ JV) := by
  obtain ⟨g, H, F0, G, rs, hg, hH, hW, hh, -⟩ := k
  obtain ⟨H', x, k1, k2, k3, k4⟩ := lettersAt_ok h iU3 p hv
  rw [hH] at k2
  obtain rfl := Option.some.inj k2
  have hg1 : (Except.ok v.1 : Except String Given) = .ok g := k1.symm.trans hg
  obtain rfl := Except.ok.inj hg1
  obtain ⟨hd, hJ⟩ := sizes_of_plan p (seatAt h iU3) s v.1 hok k1
  have hh' : (letI := v.1
    hear F0 rs = some ((v.2.1.norm, v.2.1.final, v.2.1.head), G, [])) := by
    rw [k4]
    exact hh
  have hB : (letI := v.1
    letI := v.2.1
    HeardBare) := by
    letI := v.1
    exact heardBare_of_hear hW hh'
  have e5 : v.2.2 = ⟨x.1, x.2⟩ := by rw [k4]
  refine ⟨?_, hB, hd, hJ⟩
  show @EntriesAt v.1.sizes (fun t _ _ => t = iU3) v.2.2.final v.2.2.head
  rw [e5]
  exact @entriesAt_reads v.1.sizes h iU3 s x k3

/-- **THE THREE RUNS.** s0: a state at which the head's hearing is read back; s: a state that goes
on from it. The claims of a return of "norm", "policy" or "logits" at s name no entry and no run of
an array other than the reads'. -/
theorem namesNot_run_front (hok : p.ok = true) (l piece : Nat) (name : String)
    (run : Nat → S → Except String (List Claim × S))
    (hrun : (kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some run) {s0 s : S}
    (k : K6HeardAt h iU3 p s0) (a : AlikeFront s0 s) (m : Nat) (cls : List Claim) (s' : S)
    (e : run m s = .ok (cls, s')) {t : Nat} (ht : t ≠ iU3) : ∀ cl ∈ cls, NamesNot t cl := by
  have k' : K6HeardAt h iU3 p s := k6HeardAt_front h iU3 p a k
  obtain ⟨g, b, x, fs, h1, h2, h3⟩ :=
    k6_run_spec asClaim (seatAt h iU3) l piece p name run m s s' cls hrun e
  obtain ⟨hA, hB, hd, -⟩ := letters_ents h iU3 p hok k' h1
  intro cl hcl
  rw [h3] at hcl
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hcl
  refine ⟨fun y hy => ?_, fun u hu => ?_⟩
  · have hE : EntsAt (fun t _ _ => t = iU3) f := by
      letI := g
      letI := b
      letI := x
      exact claims_ents hA hB hd name fs h2 f hf
    have hy' : y ∈ f.ents := hy
    have e1 : y.tree = iU3 := hE y (Array.mem_toList_iff.2 hy')
    exact fun e2 => ht (e2.symm.trans e1)
  · have hr : (asClaim f).runs = #[] := rfl
    rw [hr] at hu
    simp at hu

/-- The same under Alike, which asks two clauses more, on the reads; they are not spent. -/
theorem namesNot_run (hok : p.ok = true) (l piece : Nat) (name : String)
    (run : Nat → S → Except String (List Claim × S))
    (hrun : (kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some run) {s0 s : S}
    (k : K6HeardAt h iU3 p s0) (a : Alike s0 s) (m : Nat) (cls : List Claim) (s' : S)
    (e : run m s = .ok (cls, s')) {t : Nat} (ht : t ≠ iU3) : ∀ cl ∈ cls, NamesNot t cl :=
  namesNot_run_front h iU3 p hok l piece name run hrun k (alikeFront_of a) m cls s' e ht

/-- **THE KEY VECTORS** that the head hands to the lookup's run "join". -/
theorem namesNot_keys_front (hok : p.ok = true) {s0 s : S} (k : K6HeardAt h iU3 p s0)
    (a : AlikeFront s0 s) (KF : Array Form) (e : callerKeys p (seatAt h iU3) s = some KF) {t : Nat}
    (ht : t ≠ iU3) : ∀ f ∈ KF, ∀ x ∈ f.ents, x.tree ≠ t := by
  have k' : K6HeardAt h iU3 p s := k6HeardAt_front h iU3 p a k
  unfold callerKeys at e
  cases hv : lettersAt p (seatAt h iU3) s with
  | error msg =>
    rw [hv] at e
    cases e
  | ok v =>
    rw [hv] at e
    obtain ⟨hA, hB, hd, hJ⟩ := letters_ents h iU3 p hok k' hv
    obtain rfl := Option.some.inj e
    intro f hf y hy
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp (List.mem_toArray.1 hf)
    letI := v.1
    letI := v.2.1
    letI := v.2.2
    have e1 : y.tree = iU3 := keyVector_ents hA hB hd hJ c.1 c.2 y (Array.mem_toList_iff.2 hy)
    exact fun e2 => ht (e2.symm.trans e1)

/-- The same under Alike. -/
theorem namesNot_keys (hok : p.ok = true) {s0 s : S} (k : K6HeardAt h iU3 p s0) (a : Alike s0 s)
    (KF : Array Form) (e : callerKeys p (seatAt h iU3) s = some KF) {t : Nat} (ht : t ≠ iU3) :
    ∀ f ∈ KF, ∀ x ∈ f.ents, x.tree ≠ t :=
  namesNot_keys_front h iU3 p hok k (alikeFront_of a) KF e ht

end At

/-- **THE FORMS THAT THE HEAD HANDS TO THE LOOKUP's RUN "planes".** -/
theorem namesNot_readers (iU3 : Nat) {s : S}
    {r : (Nat → Nat → Option Form) × (Nat → Option Form)}
    (e : callerReaders (planesAt iU3) s = some r) {t : Nat} (ht : t ≠ iU3) :
    (∀ b col f, r.1 b col = some f → ∀ x ∈ f.ents, x.tree ≠ t) ∧
      ∀ col f, r.2 col = some f → ∀ x ∈ f.ents, x.tree ≠ t := by
  unfold callerReaders at e
  obtain ⟨at_, h1, rfl⟩ := Option.map_eq_some_iff.1 e
  obtain ⟨o, F, tt, tr, -, -, -, -, -, rfl⟩ := planesAt_some iU3 s at_ h1
  have one : ∀ (q : PlaneRead) (col : Nat) (f : Form),
      planeEntry tt.tab iU3 tr.K q col = some f → ∀ x ∈ f.ents, x.tree ≠ t := by
    intro q col f hf x hx
    unfold planeEntry at hf
    obtain ⟨en, -, h2⟩ := Option.bind_eq_some_iff.mp hf
    split at h2
    · obtain rfl := Option.some.inj h2
      have e1 : x.tree = iU3 := entsAt_ent iU3 _ _ x (Array.mem_toList_iff.2 hx)
      exact fun e2 => ht (e2.symm.trans e1)
    · cases h2
  exact ⟨fun b col f hf => one _ col f hf, fun col f hf => one PlaneRead.pin col f hf⟩

section At347

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- In the goals' scope the kind's test on the plan follows from that of the IOP as written in Lean:
the output head's own member is seated alone, and its test on the plan holds the kind's. A near
neighbour, general in the written IOP, with the member as a premise: SeatedPlan.seated_plan_pays
(Law/SeatedPlan.lean). -/
theorem parOk_open (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hOk : F.planOk = true) :
    (parOf Bs.G₀.W.hS (workOf Bs.G₀.W)).ok = true := by
  obtain ⟨Lk, b, b', ms, e1, e2, -, hb', hA, -⟩ := IM.k6_of hS hR O
  exact (seatedClaims_plan hb' (IM.plan_alone O hOk e1 e2 hA)).1

/-- **THE THREE RUNS, where s0 is a state reached in front of the head's batching.** -/
theorem namesNot_run_front_347 {Str : Type} (hS : VerifierAndGoals.InScope Pb = true)
    (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hOk : F.planOk = true)
    (a : (ProofFile.InstPub × S) × Str) (hr : RchAt (P4.FD Z A B c) 347 a) (l piece : Nat)
    (name : String) (run : Nat → S → Except String (List Claim × S))
    (hrun : (kind asClaim (seatAt Bs.G₀.W.hS (readsOf Bs.G₀.W)) l piece
      (parOf Bs.G₀.W.hS (workOf Bs.G₀.W))).claims.lookup name = some run) {s : S}
    (al : AlikeFront a.1.2 s) (m : Nat) (cls : List Claim) (s' : S)
    (e : run m s = .ok (cls, s')) {t : Nat} (ht : t ≠ readsOf Bs.G₀.W) :
    ∀ cl ∈ cls, NamesNot t cl :=
  namesNot_run_front _ _ _ (parOk_open hS hR O hOk) l piece name run hrun
    (LinkJoin.k6HeardAt_347 hS hR O hOk a hr) al m cls s' e ht

/-- The same under Alike. -/
theorem namesNot_run_347 {Str : Type} (hS : VerifierAndGoals.InScope Pb = true)
    (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hOk : F.planOk = true)
    (a : (ProofFile.InstPub × S) × Str) (hr : RchAt (P4.FD Z A B c) 347 a) (l piece : Nat)
    (name : String) (run : Nat → S → Except String (List Claim × S))
    (hrun : (kind asClaim (seatAt Bs.G₀.W.hS (readsOf Bs.G₀.W)) l piece
      (parOf Bs.G₀.W.hS (workOf Bs.G₀.W))).claims.lookup name = some run) {s : S}
    (al : Alike a.1.2 s) (m : Nat) (cls : List Claim) (s' : S) (e : run m s = .ok (cls, s'))
    {t : Nat} (ht : t ≠ readsOf Bs.G₀.W) : ∀ cl ∈ cls, NamesNot t cl :=
  namesNot_run_front_347 hS hR O hOk a hr l piece name run hrun (alikeFront_of al) m cls s' e ht

/-- **THE KEY VECTORS, where s0 is a state reached in front of the head's batching.** -/
theorem namesNot_keys_front_347 {Str : Type} (hS : VerifierAndGoals.InScope Pb = true)
    (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hOk : F.planOk = true)
    (a : (ProofFile.InstPub × S) × Str) (hr : RchAt (P4.FD Z A B c) 347 a) {s : S}
    (al : AlikeFront a.1.2 s) (KF : Array Form)
    (e : callerKeys (parOf Bs.G₀.W.hS (workOf Bs.G₀.W))
      (seatAt Bs.G₀.W.hS (readsOf Bs.G₀.W)) s = some KF)
    {t : Nat} (ht : t ≠ readsOf Bs.G₀.W) : ∀ f ∈ KF, ∀ x ∈ f.ents, x.tree ≠ t :=
  namesNot_keys_front _ _ _ (parOk_open hS hR O hOk) (LinkJoin.k6HeardAt_347 hS hR O hOk a hr) al KF
    e ht

/-- The same under Alike. -/
theorem namesNot_keys_347 {Str : Type} (hS : VerifierAndGoals.InScope Pb = true)
    (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hOk : F.planOk = true)
    (a : (ProofFile.InstPub × S) × Str) (hr : RchAt (P4.FD Z A B c) 347 a) {s : S} (al : Alike a.1.2 s)
    (KF : Array Form)
    (e : callerKeys (parOf Bs.G₀.W.hS (workOf Bs.G₀.W))
      (seatAt Bs.G₀.W.hS (readsOf Bs.G₀.W)) s = some KF)
    {t : Nat} (ht : t ≠ readsOf Bs.G₀.W) : ∀ f ∈ KF, ∀ x ∈ f.ents, x.tree ≠ t :=
  namesNot_keys_front_347 hS hR O hOk a hr (alikeFront_of al) KF e ht

end At347

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.entsAt_ent
#print axioms VerifiableInference.Desc.Kinds.Head.Law.entsAt_entryAt
#print axioms VerifiableInference.Desc.Kinds.Head.Law.entriesAt_reads
#print axioms VerifiableInference.Desc.Kinds.Head.Law.letters_ents
#print axioms VerifiableInference.Desc.Kinds.Head.Law.namesNot_run_front
#print axioms VerifiableInference.Desc.Kinds.Head.Law.namesNot_run
#print axioms VerifiableInference.Desc.Kinds.Head.Law.namesNot_keys_front
#print axioms VerifiableInference.Desc.Kinds.Head.Law.namesNot_keys
#print axioms VerifiableInference.Desc.Kinds.Head.Law.namesNot_readers
#print axioms VerifiableInference.Desc.Kinds.Head.Law.parOk_open
#print axioms VerifiableInference.Desc.Kinds.Head.Law.namesNot_run_front_347
#print axioms VerifiableInference.Desc.Kinds.Head.Law.namesNot_run_347
#print axioms VerifiableInference.Desc.Kinds.Head.Law.namesNot_keys_front_347
#print axioms VerifiableInference.Desc.Kinds.Head.Law.namesNot_keys_347
