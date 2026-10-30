-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/K8SitsBetween.lean: WHAT STANDS BETWEEN THE SMALLNESS TEST's THREE
RUNS LEAVES ITS RECORD AND THE LIST OF TABLES: the two premises of K08SitsMeet and K08SitsRun
(K8SitsMeet.lean), brought down to one field of the carried record, and that field's staying shown
run by run, from the other kinds' own lemmas.

Statements and proofs.
Main names:
  k8Field s: the smallness test's record and the list of tables, as the carried record has them
    (tl?, funs?).
  partOf_some: the part is there just where the record, the ledger and the list of tables are.
  between_of: where k8Field stays from s1 to s2 and s2 has the ledger G, the premise (between)
    holds; (kept) is the same sentence.
  **K08SitsField** (a closed Prop), **k08_sits_field**: K08SitsRun with its two premises replaced
    by: k8Field s2 = k8Field s1 and k8Field s3' = k8Field s3. No ledger is a letter any more: that a
    ledger is there at s2 and at s3' is had from the two runs' own yeses.
  wrote_field; back_field, freeSlot_field: K4's runs "back" and "free-slot", as its block typed at
    Claim states them (blockAtC; from backAtC, freeSlotAtS, wrote_reads).
  logits_field: K6's own runs (from k6_same). head_field, merge_field: K11's run "the merge" (from
    its text).
  beside_k8Field: k8Field is a reader beside what the batching's blocks and the closing write
    (K9.Beside): so atS_set_keeps (Batch/Law/Keeps.lean) holds of it: with batch_writes: the record
    behind the seated batching is atS.set x.2 b, x.2 the record behind the LAST run of claims:
    k8Field there is k8Field x.2. batch_keeps AND adds_keeps CANNOT BE CALLED AT IT: they ask the
    staying of the whole gatherer, and the gatherer runs "K8.equations", which writes the record.
Limits. EACH LEMMA SPEAKS OF ONE RUN OR ONE WRITING, AS ITS KIND's BLOCK STATES IT. THAT THE
DRIVER's GATHERING BEHIND "K8.equations" AND ITS RUNS BEHIND THE BATCHING ARE MADE OF JUST THESE, IN
THE ORDER's ROW, IS NOT SAID HERE: so the two premises are not yet paid at a seat.
(Where this and lean/THEOREM.md differ, the page
holds.)
The runs of the
digits' lookup ("objects", "guests") stand in front of "K8.equations", not behind it: nothing is
said of them. K4's lemmas speak of blockAtC p's runs, K6's of its kind at the real seat, the merge's
of headMergeClaim: not of a block laid through a further wrapper.

-/
import Johnson.Desc.First.TailClaims.K8SitsMeet
import Johnson.Desc.First.K4.ReadsAtS
import Johnson.Desc.First.K4.RunsAtC
import Johnson.Desc.First.Batch.Law.Keeps
import Johnson.Desc.Kinds.Law.HeadRunsCarry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims

/-- The smallness test's record and the list of tables, as the carried record has them. -/
def k8Field (s : S) : Option HTailF2 × Option (Array HFun) := (s.tl?, s.funs?)

/-- The part is there just where the record, the ledger and the list of tables are. -/
theorem partOf_some {s : S} {q : K8Part} :
    partOf s = some q ↔ s.tl? = some q.tl ∧ s.fork? = some q.F ∧ s.funs? = some q.funs := by
  obtain ⟨tl, funs, F⟩ := q
  show ((s.tl?.bind fun p => s.fork?.map fun x => (p, x)).bind fun x =>
    s.funs?.map fun fs => (⟨x.1, fs, x.2⟩ : K8Part)) = some ⟨tl, funs, F⟩ ↔ _
  cases s.tl? <;> cases s.fork? <;> cases s.funs? <;> simp
  intro _
  exact And.comm

/-- **Where the field stays and the ledger is G, the premise holds.** -/
theorem between_of {s1 s2 : S} {G : Fork} (h : k8Field s2 = k8Field s1) (hG : s2.fork? = some G) :
    ∀ q1, partOf s1 = some q1 → partOf s2 = some { q1 with F := G } := by
  intro q1 hq
  obtain ⟨a, _, c⟩ := partOf_some.1 hq
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  exact partOf_some.2 ⟨h1.trans a, hG, h2.trans c⟩

/-- **K08SitsRun, with the two premises as the staying of one field.** -/
def K08SitsField : Prop :=
  ∀ (p : K8.ParW) (runE : Nat → S → Except String (List Claim × S))
    (runL runT : S → Except String S),
    ("K8.equations", runE) ∈ (K8.whole p).claims → ("K8.lsTail", runL) ∈ (K8.whole p).after →
    ("K8.tests", runT) ∈ (K8.whole p).after →
    ∀ (front : Nat) (s0 s1 s2 s3 s3' s4 : S) (cls : List Claim),
      runE front s0 = .ok (cls, s1) → k8Field s2 = k8Field s1 → runL s2 = .ok s3 →
      k8Field s3' = k8Field s3 → runT s3' = .ok s4 →
      ∃ (q : K8Part) (tl' ts : HTailF2) (F1 G' Fc : Fork), partOf s0 = some q ∧
        equations (q.F.nClaim + front) q.tl q.funs q.F = .ok (tl', F1, cls) ∧
        (∀ u, blank u ts = blank u q.tl) ∧ rkSelfTestP ts Fc = .ok () ∧
        s3'.fork? = some G' ∧ Fc.theta = G'.theta ∧ partOf s4 = some ⟨ts, q.funs, Fc⟩

theorem k08_sits_field : K08SitsField := by
  intro p runE runL runT hE hL hT front s0 s1 s2 s3 s3' s4 cls h1 hf2 h3 hf3 h4
  obtain ⟨q2, hq2, -⟩ := (sits_lsTail p runL hL s2 s3).1 h3
  obtain ⟨q3, -, hq3, -, -⟩ := (sits_tests p runT hT s3' s4).1 h4
  have g2 := (partOf_some.1 hq2).2.1
  have g3 := (partOf_some.1 hq3).2.1
  obtain ⟨q, tl', ts, F1, Fc, a, b, c, d, e, f⟩ :=
    k08_sits_run p runE runL runT hE hL hT front s0 s1 s2 s3 s3' s4 cls q2.F q3.F h1
      (between_of hf2 g2) h3 (between_of hf3 g3) h4
  exact ⟨q, tl', ts, F1, q3.F, Fc, a, b, c, d, g3, e, f⟩

/-- Behind a writing of K4's. -/
theorem wrote_field {s s' : S} {a : LayOwn} {G : Fork} (h : OnBytes.Desc.First.K4.Wrote s a G s') :
    k8Field s' = k8Field s ∧ s'.fork? = some G := by
  obtain ⟨_, hf, _, hG, hr⟩ := OnBytes.Desc.First.K4.wrote_reads h
  exact ⟨Prod.ext hr.tl hf, hG⟩

/-- K4's run "back". -/
theorem back_field {p : OnBytes.Desc.First.K4.Par}
    {run : Nat → S → Except String (List Claim × S)}
    (hr : (OnBytes.Desc.First.K4.blockAtC p).claims.lookup "back" = some run) {n : Nat} {s s' : S}
    {cl : List Claim} (h : run n s = .ok (cl, s')) :
    k8Field s' = k8Field s ∧ ∃ G, s'.fork? = some G := by
  obtain ⟨a, _, _, G, _, _, _, hw⟩ := OnBytes.Desc.First.K4.backAtC hr h
  exact ⟨(wrote_field hw).1, G, (wrote_field hw).2⟩

/-- K4's run "free-slot": the ledger stays too. -/
theorem freeSlot_field {p : OnBytes.Desc.First.K4.Par} {run : S → Except String S}
    (hr : (OnBytes.Desc.First.K4.blockAtC p).after.lookup "free-slot" = some run) {s s' : S}
    (h : run s = .ok s') : k8Field s' = k8Field s ∧ s'.fork? = s.fork? := by
  obtain ⟨a, hw⟩ := OnBytes.Desc.First.K4.freeSlotAtS (p := p)
    (show (OnBytes.Desc.First.K4.blockAtS p).after.lookup "free-slot" = some run from hr) h
  obtain ⟨_, _, h0, hG, _⟩ := OnBytes.Desc.First.K4.wrote_reads hw
  exact ⟨(wrote_field hw).1, hG.trans h0.symm⟩

/-- K6's own runs ("norm", "policy", "logits"): the record behind is the record in front. -/
theorem logits_field (h : OnBytes.Model.Head.Shape) (iU3 l piece : Nat)
    (p : VerifiableInference.Desc.Kinds.Head.Par)
    (c : String × (Nat → S → Except String (List Claim × S)))
    (hc : c ∈ (VerifiableInference.Desc.Kinds.Head.kind VerifiableInference.Desc.Kinds.Head.asClaim
      (VerifiableInference.Desc.Kinds.Head.seatAt h iU3) l piece p).claims)
    (n : Nat) (s : S) (y : List Claim × S) (hy : c.2 n s = .ok y) :
    k8Field y.2 = k8Field s ∧ y.2.fork? = s.fork? := by
  rw [VerifiableInference.Desc.Kinds.Head.Law.k6_same h iU3 l piece p c hc n s y hy]
  exact ⟨rfl, rfl⟩

/-- A writing of the ledger alone in the head's link. -/
theorem head_field {s : S} {a : HeadOwn} (h : s.here = .head a) (G : Fork) :
    k8Field { s with here := .head { a with F := G } } = k8Field s ∧
      ({ s with here := .head { a with F := G } } : S).fork?.isSome = s.fork?.isSome := by
  unfold k8Field S.tl? S.funs? S.fork?
  simp only [h]
  by_cases ho : a.opened = true <;> simp [ho]

/-- K11's run "the merge". -/
theorem merge_field {n : Nat} {s : S} {y : List Claim × S}
    (h : Johnson.Desc.First.ForkMerge.headMergeClaim n s = .ok y) :
    k8Field y.2 = k8Field s ∧ y.2.fork?.isSome = s.fork?.isSome := by
  unfold Johnson.Desc.First.ForkMerge.headMergeClaim at h
  cases hh : s.here with
  | head a =>
    simp only [hh, bind, Except.bind] at h
    split at h
    · cases h
    · split at h
      · cases h
      · obtain rfl := Except.ok.inj h
        exact head_field hh _
  | _ => simp [hh] at h

/-- The field is a reader beside what the batching's blocks and the closing write. -/
theorem beside_k8Field : VerifiableInference.Desc.K9.Beside k8Field :=
  ⟨fun s L => Prod.ext (VerifiableInference.Desc.K9.beside_tl.link s L)
      (VerifiableInference.Desc.K9.beside_funs.link s L),
    fun s F => Prod.ext (VerifiableInference.Desc.K9.beside_tl.fork s F)
      (VerifiableInference.Desc.K9.beside_funs.fork s F),
    fun s st o => Prod.ext (VerifiableInference.Desc.K9.beside_tl.rows s st o)
      (VerifiableInference.Desc.K9.beside_funs.rows s st o),
    fun s c => Prod.ext (VerifiableInference.Desc.K9.beside_tl.walk s c)
      (VerifiableInference.Desc.K9.beside_funs.walk s c)⟩

end VerifiableInference.Desc.First.TailClaims.Law

#print axioms VerifiableInference.Desc.First.TailClaims.Law.between_of
#print axioms VerifiableInference.Desc.First.TailClaims.Law.k08_sits_field
#print axioms VerifiableInference.Desc.First.TailClaims.Law.back_field
#print axioms VerifiableInference.Desc.First.TailClaims.Law.freeSlot_field
#print axioms VerifiableInference.Desc.First.TailClaims.Law.logits_field
#print axioms VerifiableInference.Desc.First.TailClaims.Law.merge_field
#print axioms VerifiableInference.Desc.First.TailClaims.Law.beside_k8Field
