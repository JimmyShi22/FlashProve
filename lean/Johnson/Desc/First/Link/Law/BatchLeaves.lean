-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/BatchLeaves.lean: AT THE PROOF FILE's SEAT, THE LINK's BATCHING's OWN
STEP LEAVES EVERY READING OF THE APPROXIMATE RANGE PROOF's STRUCTURE THAT READS NONE OF THE FOURTEEN
FIELDS WHICH `blank` BLANKS: so a «planned» reading has the built link's planned value BEHIND the
batching too. Theorems. It changes no other file.

Why. The link's table asks `SortsAt` at the states behind the batching (its field htin's debt h1).
`planned_at_batch` (PlannedAtDraw.lean) ends in front of it.

  `beside_read`: `readTl g` stands beside what the batching's blocks write (`K9.Beside`).
  `batch_leaves`: at a link with `TocK8.K8At` (Johnson/TocK8R/AtSeat.lean: the
    link's order is pre ++ "K8.equations" :: post; each run of pre and post leaves the structure;
    the
    run at "K8.equations" stands under K8's own) whose batching is K9's under the seat's dress: a
    yes
    of the link's batching from s to sB ⊢ readTl g sB = readTl g s. By `K9.batch_writes`,
    `claimsInBy_keeps` and `sits_equations`, and `eq_blank` (TailClaims/EquationsBlank.lean).
  `batch_leaves_scope`: in scope, at `IM.Open … secondHashFunction`: the entry of the number 14 l + i + 3 + n of
    the flat list leaves `readTl g`.
  `planned_behind_batch`, `planned_behind_rch`: **readTl g = some (g Xl.tl) at every state reached
    at 14 l + i + 4 + n: BEHIND the batching.**
  `sorts_behind_batch`: **sortsB sh Xl.tl = true ⊢ SortsAt sh a.1.2 there.**
Limits. In scope, at secondHashFunction alone. No member. sortsB at the release's 25 built links is an
evaluation, no theorem. Nothing on soundness.
-/
import Johnson.TocK8R.AtSeat
import Johnson.Desc.First.TailClaims.EquationsBlank
import Johnson.Desc.First.Link.Law.PlannedAtRch

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (readTl)
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open Johnson.Desc.First.Walk.Tied (Reach RchAt rchAt_raw)
open ProofFile (Cl)

variable {α : Type} {g : HTailF2 → α}

theorem beside_read (g : HTailF2 → α) : K9.Beside (readTl g) :=
  ⟨fun s L => congrArg (Option.map g) (K9.beside_tl.link s L),
    fun s F => congrArg (Option.map g) (K9.beside_tl.fork s F),
    fun s st o => congrArg (Option.map g) (K9.beside_tl.rows s st o),
    fun s c => congrArg (Option.map g) (K9.beside_tl.walk s c)⟩

/-- **A yes of the link's batching leaves the reading.** -/
theorem batch_leaves (hb0 : ∀ u tl, g (blank u tl) = g tl) {Lk : Link S Cl}
    {p : First.K8.ParW} {i : ℕ} {pre post mid : List (ℕ × String)}
    (K : TocK8.K8At Lk p i pre post mid) {w : K9.Where} {a9 : Place}
    (hk : a9.kind ≠ KindName.K7)
    (hb : ∀ f, IM.LaidAlone ProofFile.sameReply (Lk.batch f) (K9.batch atS w f) (Lk.batch f).name a9) :
    (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).Leaves (readTl g) := by
  intro s rs gs sB h1
  have y := ((IM.yes_alone (hb _) hk s sB rs gs).1 h1).1
  rw [K.order] at y
  obtain ⟨a, z, b, hz, rfl⟩ := K9.batch_writes _ w _ y
  rw [K9.atS_set_keeps (beside_read g), ← K9.atS_set_keeps (beside_read g) s a]
  refine claimsInBy_keeps (readTl g) _ _ z (fun o ho run hl n e c e₁ hr => ?_) hz
  have field : k8Field e₁ = k8Field e → readTl g e₁ = readTl g e := fun h =>
    congrArg (Option.map g) (congrArg Prod.fst h)
  rcases List.mem_append.1 ho with ho | ho
  · exact field (K.hpre o ho run hl n e c e₁ hr)
  · rcases List.mem_cons.1 ho with rfl | ho
    · obtain ⟨r, hm, hu⟩ := K.hE run hl
      obtain ⟨q, tl', F1, hq, he, rfl⟩ := (sits_equations p r hm n e e₁ c).1 (hu _ _ _ hr)
      have ht : e.tl? = some q.tl := (partOf_some.1 hq).1
      have e1 : k8PartP.set e { q with tl := tl', F := F1 } = (e.putTl tl').putFork F1 := rfl
      rw [e1, (beside_read g).fork]
      unfold readTl
      rw [First.K8.putTl_tl e q.tl tl' ht, ht]
      show some (g tl') = some (g q.tl)
      rw [← hb0 q.tl tl', eq_blank q.tl he, hb0]
    · exact field (K.hpost o ho run hl n e c e₁ hr)

variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- In scope: the batching's entry of each link leaves the reading. -/
theorem batch_leaves_scope (hb0 : ∀ u tl, g (blank u tl) = g tl)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {x : ℕ × ℕ × ℕ}
    (hx : x ∈ P1K8S.stretches) :
    ∀ b, c.blocksInOrder[14 * x.1 + x.2.1 + 3 + x.2.2]? = some b → b.Leaves (readTl g) := by
  intro b hb
  have hl : x.1 < 25 := by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    exact List.mem_range.1 hl
  obtain ⟨Lk, e, hf⟩ := P1K8S.batch_behind hS hR O x hx
  obtain ⟨L9, w, -, -, e9, -, -, -, -, -, hb9, -⟩ := (IM.k9_of hS hR O).2 x.1 hl
  obtain ⟨Lk', Xl, e', -, K, -⟩ := TocK8.k08_scope hS hR O x.1 hl
  obtain rfl : Lk = L9 := Option.some.inj (e.symm.trans e9)
  obtain rfl : Lk = Lk' := Option.some.inj (e.symm.trans e')
  obtain rfl := Option.some.inj (hf.symm.trans hb)
  exact batch_leaves hb0 K (a9 := IM.a9Of x.1 (IM.subAt x.1)) (fun h => nomatch h) hb9

/-- **BEHIND THE BATCHING.** -/
theorem planned_behind_batch (hg : Planned g) (hb0 : ∀ u tl, g (blank u tl) = g tl)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {x : ℕ × ℕ × ℕ} (hx : x ∈ P1K8S.stretches) {Xl : LinkH}
    (e3 : Bs.G₀.built[x.1]? = some Xl) (a : ProofFile.InstPub × S)
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * x.1 + x.2.1 + 3 + x.2.2 + 1) a) :
    readTl g a.2 = some (g Xl.tl) :=
  reach_carries 0 c.blocksInOrder (ProofFile.startS Z) (readTl g) (14 * x.1 + x.2.1 + 3 + x.2.2) 1
    (fun j h1 h2 b hb => by
      obtain rfl : j = 14 * x.1 + x.2.1 + 3 + x.2.2 := by omega
      exact batch_leaves_scope hb0 hS hR O hx b hb)
    (fun _ => some (g Xl.tl)) (fun b hb => planned_at_batch hg hS hR O hx e3 b hb) a h

theorem planned_behind_rch (hg : Planned g) (hb0 : ∀ u tl, g (blank u tl) = g tl)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {x : ℕ × ℕ × ℕ} (hx : x ∈ P1K8S.stretches) {Xl : LinkH}
    (e3 : Bs.G₀.built[x.1]? = some Xl) {Str : Type} (a : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) (14 * x.1 + x.2.1 + 3 + x.2.2 + 1) a) :
    readTl g a.1.2 = some (g Xl.tl) :=
  planned_behind_batch hg hb0 hS hR O hx e3 a.1 (rchAt_raw h)

/-- **A Bool on the plan pays `SortsAt` behind the batching.** -/
theorem sorts_behind_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {x : ℕ × ℕ × ℕ} (hx : x ∈ P1K8S.stretches) {Xl : LinkH}
    (e3 : Bs.G₀.built[x.1]? = some Xl) {sh : List Look} (hB : sortsB sh Xl.tl = true)
    {Str : Type} (a : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) (14 * x.1 + x.2.1 + 3 + x.2.2 + 1) a) : SortsAt sh a.1.2 :=
  sortsAt_of_five (planned_behind_rch planned_five (fun _ _ => rfl) hS hR O hx e3 a h) hB

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.batch_leaves
#print axioms VerifiableInference.Desc.LinkJoin.batch_leaves_scope
#print axioms VerifiableInference.Desc.LinkJoin.planned_behind_batch
#print axioms VerifiableInference.Desc.LinkJoin.planned_behind_rch
#print axioms VerifiableInference.Desc.LinkJoin.sorts_behind_batch
