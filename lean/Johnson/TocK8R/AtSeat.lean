-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TocK8R/AtSeat.lean: THE SMALLNESS TEST's THREE RUNS AT THE SEAT: at each of the 25 links of
onlineDescription's first chain, in scope, the premises of k08_sits_front
(Johnson/Desc/First/TailClaims/K8SitsFront.lean) hold: the link's two orders have the shape that it
asks; the runs that the link's list of blocks states at K8's number under K8's three names stand
under those of K8.whole; and each run of claims ahead of "K8.equations", each behind it, and each
run between "K8.lsTail" and "K8.tests" leaves the smallness test's structure and the list of tables.
So the yes of the link's batching's block and the yes of the frame's step behind it say what
k08_sits_front concludes.

Statements and proofs: by calls. The seats are those of Johnson/IMR/ (k3_of, k4_of,
k5_of, k6_of, k8_of_layers, k8_of_attention, k8_of_head, k11_of, k9_of; claim_yes, after_yes,
yes_alone). The lemmas on the kinds' runs are K8SitsBetween.lean's and K8SitsFrontRuns.lean's.
Main names:
  mem_of_lookup; seat_leaves, seat_after_leaves: a run that is looked up in a seated block leaves
    the field if the lot's block's run of that name does.
  EntryLeaves, AfterLeaves: what the machine asks at one entry of an order. entry_of_seat,
    after_of_seat. k8_three: K8's own three runs, from its seat.
  k3_runs, k4_front, k4_back, k4_freeSlot, k5_runs, k6_runs, k11_runs: the lots' blocks, as they are
    seated: each run leaves the field.
  K8At Lk p i pre post mid: the eight premises, at a link.
  **k8At_layers**, **k8At_attention**, **k8At_head**: K8At at each link of that sort, in scope; p is
    K8's lot's own parameter at the plan's link Xl of that number.
  SeatSays Lk i pre post mid s sB sE: some a, b, z with the gathering's yes from atS.set s a and sB
    = atS.set z.2 b; and, at them, all fifteen conjuncts of k08_sits_front's conclusion.
  **k08_at_seat**: at a link with K8At whose batching is K9.batch atS w under the seat's dress: the
    yes of the link's batching's block from s to sB and the yes of the link's runBehind from sB to
    sE give SeatSays.
  ixOf, preOf, postOf, midOf: K8's number and the three stretches, by the link's sort.
    **k08_scope**: ALL 25 LINKS IN ONE SENTENCE: at each l < 25: the link, the plan's link, K8At,
    and: the two yeses give SeatSays.
Limits. In scope, at an opening's own letters (IM's Open …): not yet «from onlineDescription's value» in one
piece. From yeses alone: nothing says that a block says yes. IN SeatSays a, b AND z ARE SOME: of a
and b nothing is said but that they are there. Nothing on the ledger but what k08_sits_front says.
K08Run is not called. That the two blocks stand in the chain's flat list one behind the other is
k9_of's and the frame's: not said here.

-/
import Johnson.IMR.K3Seat
import Johnson.IMR.K4Seat
import Johnson.IMR.K5Seat
import Johnson.IMR.K6Seat
import Johnson.IMR.K8Seat
import Johnson.IMR.K11Seat
import Johnson.IMR.LinkSeat
import Johnson.Desc.First.TailClaims.K8SitsFrontRuns

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace TocK8

open Inst.Model
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName Claim claimsInBy afterIn)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching orderOf orderAfterOf)
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open ProofFile (Cl)
open IM

/-- What is found under a key is a member. -/
theorem mem_of_lookup {α : Type} : ∀ (l : List (String × α)) (k : String) (v : α),
    l.lookup k = some v → (k, v) ∈ l
  | [], _, _, h => nomatch h
  | c :: l, k, v, h => by
    rw [show c = (c.1, c.2) from rfl, List.lookup_cons] at h
    cases hk : k == c.1 with
    | true =>
      simp only [hk] at h
      have e : k = c.1 := by simpa using hk
      obtain rfl := Option.some.inj h
      rw [e]
      exact List.mem_cons_self
    | false =>
      simp only [hk] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup l k v h)

section Seat

variable {same : S → S → Bool} {b b' : Block S Cl} {name : String} {a : Place}

/-- A run of claims that is looked up in a seated block leaves the field if each run of the lot's
block does. -/
theorem seat_leaves (h : LaidAlone same b b' name a) {n : String}
    (hk : ∀ r', b'.claims.lookup n = some r' → Leaves8 r')
    {r : ℕ → S → Except String (List Cl × S)} (hr : b.claims.lookup n = some r) :
    Leaves8 r := by
  obtain ⟨r', hl, -, hy⟩ := claim_yes h hr
  intro k e c e₁ hrun
  exact hk r' hl k e c e₁ ((hy k e (c, e₁)).1 hrun).1

/-- The like behind the batching. -/
theorem seat_after_leaves (h : LaidAlone same b b' name a) {n : String}
    (hk : ∀ r', b'.after.lookup n = some r' → ∀ e e₁, r' e = .ok e₁ → k8Field e₁ = k8Field e)
    {r : S → Except String S} (hr : b.after.lookup n = some r) :
    ∀ e e₁, r e = .ok e₁ → k8Field e₁ = k8Field e := by
  obtain ⟨r', hl, -, hy⟩ := after_yes h hr
  intro e e₁ hrun
  exact hk r' hl e e₁ ((hy e e₁).1 hrun).1

end Seat

/-- What the machine asks at one entry of the order of claims. -/
def EntryLeaves (bs : List (Block S Cl)) (o : ℕ × String) : Prop :=
  ∀ run, ((bs[o.1]?).bind fun b => b.claims.lookup o.2) = some run →
    ∀ n e c e₁, run n e = .ok (c, e₁) → k8Field e₁ = k8Field e

/-- What it asks at one entry of the order behind the batching. -/
def AfterLeaves (bs : List (Block S Cl)) (o : ℕ × String) : Prop :=
  ∀ run, ((bs[o.1]?).bind fun b => b.after.lookup o.2) = some run →
    ∀ e e₁, run e = .ok e₁ → k8Field e₁ = k8Field e

theorem entry_of_seat {same : S → S → Bool} {bs : List (Block S Cl)} {j : ℕ} {b b' : Block S Cl}
    {name : String} {a : Place} (hb : bs[j]? = some b) (h : LaidAlone same b b' name a)
    (n : String) (hk : ∀ r', b'.claims.lookup n = some r' → Leaves8 r') :
    EntryLeaves bs (j, n) := by
  intro run hr
  rw [show ((j, n) : ℕ × String).1 = j from rfl, hb] at hr
  exact seat_leaves h hk hr

theorem after_of_seat {same : S → S → Bool} {bs : List (Block S Cl)} {j : ℕ} {b b' : Block S Cl}
    {name : String} {a : Place} (hb : bs[j]? = some b) (h : LaidAlone same b b' name a)
    (n : String)
    (hk : ∀ r', b'.after.lookup n = some r' → ∀ e e₁, r' e = .ok e₁ → k8Field e₁ = k8Field e) :
    AfterLeaves bs (j, n) := by
  intro run hr
  rw [show ((j, n) : ℕ × String).1 = j from rfl, hb] at hr
  exact seat_after_leaves h hk hr

/-- **The premises of k08_sits_front, at a link.** -/
structure K8At (Lk : Link S Cl) (p : VerifiableInference.Desc.First.K8.ParW) (i : ℕ)
    (pre post mid : List (ℕ × String)) : Prop where
  order : Lk.order = pre ++ (i, "K8.equations") :: post
  after : Lk.orderAfter = (i, "K8.lsTail") :: mid ++ [(i, "K8.tests")]
  hE : ∀ r', ((Lk.hear[i]?).bind fun b => b.claims.lookup "K8.equations") = some r' →
    ∃ r, ("K8.equations", r) ∈ (VerifiableInference.Desc.First.K8.whole p).claims ∧ RunUnder r' r
  hL : ∀ r', ((Lk.hear[i]?).bind fun b => b.after.lookup "K8.lsTail") = some r' →
    ∃ r, ("K8.lsTail", r) ∈ (VerifiableInference.Desc.First.K8.whole p).after ∧ AfterUnder r' r
  hT : ∀ r', ((Lk.hear[i]?).bind fun b => b.after.lookup "K8.tests") = some r' →
    ∃ r, ("K8.tests", r) ∈ (VerifiableInference.Desc.First.K8.whole p).after ∧ AfterUnder r' r
  hpre : ∀ o ∈ pre, EntryLeaves Lk.hear o
  hpost : ∀ o ∈ post, EntryLeaves Lk.hear o
  hmid : ∀ o ∈ mid, AfterLeaves Lk.hear o

/-- K8's own three, from its seat. -/
theorem k8_three {same : S → S → Bool} {bs : List (Block S Cl)} {i : ℕ} {b : Block S Cl}
    {p : VerifiableInference.Desc.First.K8.ParW} {name : String} {a : Place}
    (hb : bs[i]? = some b)
    (h : LaidAlone same b (VerifiableInference.Desc.First.K8.whole p) name a) :
    (∀ r', ((bs[i]?).bind fun b => b.claims.lookup "K8.equations") = some r' →
      ∃ r, ("K8.equations", r) ∈ (VerifiableInference.Desc.First.K8.whole p).claims ∧
        RunUnder r' r) ∧
    (∀ r', ((bs[i]?).bind fun b => b.after.lookup "K8.lsTail") = some r' →
      ∃ r, ("K8.lsTail", r) ∈ (VerifiableInference.Desc.First.K8.whole p).after ∧
        AfterUnder r' r) ∧
    (∀ r', ((bs[i]?).bind fun b => b.after.lookup "K8.tests") = some r' →
      ∃ r, ("K8.tests", r) ∈ (VerifiableInference.Desc.First.K8.whole p).after ∧
        AfterUnder r' r) := by
  rw [hb]
  refine ⟨fun r' hr => ?_, fun r' hr => ?_, fun r' hr => ?_⟩
  · obtain ⟨r, hl, -, hy⟩ := claim_yes h hr
    exact ⟨r, mem_of_lookup _ _ _ hl, fun n t y hrun => ((hy n t y).1 hrun).1⟩
  · obtain ⟨r, hl, -, hy⟩ := after_yes h hr
    exact ⟨r, mem_of_lookup _ _ _ hl, fun t y hrun => ((hy t y).1 hrun).1⟩
  · obtain ⟨r, hl, -, hy⟩ := after_yes h hr
    exact ⟨r, mem_of_lookup _ _ _ hl, fun t y hrun => ((hy t y).1 hrun).1⟩

/-! ## The lots' blocks: each run leaves the field -/

/-- From «each member» to «what is looked up». -/
theorem of_mem {b' : Block S Cl} (h : ∀ c ∈ b'.claims, Leaves8 c.2) (n : String) :
    ∀ r', b'.claims.lookup n = some r' → Leaves8 r' :=
  fun r' hl => h (n, r') (mem_of_lookup _ _ _ hl)

/-- The lookup's block at an address, as its lot seats it. -/
theorem k3_runs {X : Verify.Public} {Z : ProofFile.Pub} {a : Place} {b' : Block S Cl}
    (h : k3At X Z a = some b') (n : String) :
    ∀ r', b'.claims.lookup n = some r' → Leaves8 r' :=
  of_mem (stated_field _ _ _ _ _ _ _ h) n

/-- K4's block as its lot seats it: "front". -/
theorem k4_front (x : Bool × OnBytes.Desc.First.K4.Par) :
    ∀ r', (ProofFile.k4Block x).claims.lookup "front" = some r' → Leaves8 r' :=
  fun _ hl => front_field (p := { x.2 with k3Runs := true }) hl

/-- "back". -/
theorem k4_back (x : Bool × OnBytes.Desc.First.K4.Par) :
    ∀ r', (ProofFile.k4Block x).claims.lookup "back" = some r' → Leaves8 r' :=
  fun _ hl _ _ _ _ h => (back_field (p := { x.2 with k3Runs := true }) hl h).1

/-- "free-slot". -/
theorem k4_freeSlot (x : Bool × OnBytes.Desc.First.K4.Par) :
    ∀ r', (ProofFile.k4Block x).after.lookup "free-slot" = some r' →
      ∀ e e₁, r' e = .ok e₁ → k8Field e₁ = k8Field e :=
  fun _ hl _ _ h => (freeSlot_field (p := { x.2 with k3Runs := true }) hl h).1

/-- K5's block as its lot seats it. -/
theorem k5_runs {W : Verify.Public} {l g : ℕ} {before : List (ℕ × ℕ)} {b' : Block S Cl}
    (h : VerifiableInference.Desc.First.Att.P.k5AtN W l g before = some b') (Z : ProofFile.Pub)
    (nm n : String) : ∀ r', (k5Dress Z nm b').claims.lookup n = some r' → Leaves8 r' :=
  fun r' hl => k5AtN_field h (n, r') (mem_of_lookup _ _ _ hl)

/-- K6's block as its lot seats it. -/
theorem k6_runs {W : Verify.Public} {l : ℕ} {ms : List (ℕ × ℕ)} {b' : Block S Cl}
    (h : VerifiableInference.Desc.Kinds.Head.seatedClaims W l ms = some b') (n : String) :
    ∀ r', b'.claims.lookup n = some r' → Leaves8 r' := by
  obtain ⟨b6, h6, rfl⟩ := Option.map_eq_some_iff.1 h
  exact fun r' hl => k6_block_field h6 (n, r') (mem_of_lookup _ _ _ hl)

/-- K11's block as its lot seats it. -/
theorem k11_runs (Z : ProofFile.Pub) (look : String) (G : ProofFile.Ground) (n : String) :
    ∀ r', (K11.blkAt Z look G).claims.lookup n = some r' → Leaves8 r' := by
  intro r' hl k e c e₁ h
  have hm : (n, r') ∈ [("the merge", Johnson.Desc.First.ForkMerge.headMergeClaim)] :=
    mem_of_lookup _ _ _ hl
  obtain rfl := (Prod.mk.inj (List.mem_singleton.1 hm)).2
  exact (merge_field h).1

/-! ## The three sorts of link -/

section Scope

variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **AT EACH LAYERS' LINK.** -/
theorem k8At_layers (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ g < 12, ∃ (Lk : Link S Cl) (Xl : OnBytes.Model.Stages.LinkH),
      c.links[2 * g]? = some Lk ∧ Bs.G₀.built[2 * g]? = some Xl ∧
      K8At Lk (ProofFile.k8ParW Z Bs.G₀ Xl (2 * g)) 4
        [(1, "objects"), (1, "guests"), (2, "front"), (6, "objects"), (6, "guests")]
        [(2, "back")] [(2, "free-slot")] := by
  intro g hg
  have hne : 2 * g ≠ 24 := by omega
  obtain ⟨Lk, -, -, -, e, -, -, -, -, -, -, -, -, -, -, hord, haft, -⟩ :=
    (k9_of hS hR O).2 (2 * g) (by omega)
  rw [subAt_layers g hg] at hord haft
  obtain ⟨L1, b1, b1', e1, hb1, hs1, la1⟩ := k3_of hS hR O (2 * g) (by omega) false
  obtain rfl : Lk = L1 := Option.some.inj (e.symm.trans e1)
  obtain ⟨L6, b6, b6', e6, hb6, hs6, la6⟩ := k3_of hS hR O (2 * g) (by omega) true
  obtain rfl : Lk = L6 := Option.some.inj (e.symm.trans e6)
  obtain ⟨L4, b4, x, e4, hb4, -, la4, -⟩ := k4_of hS hR O g hg
  obtain rfl : Lk = L4 := Option.some.inj (e.symm.trans e4)
  obtain ⟨L8, b8, Xl, -, e8, hb8, hX, la8, -⟩ := k8_of_layers hS hR O g hg
  obtain rfl : Lk = L8 := Option.some.inj (e.symm.trans e8)
  have i1 : k3Ix (2 * g) false = 1 := by simp [k3Ix, hne]
  have i6 : k3Ix (2 * g) true = 6 := by simp [k3Ix, hne]
  rw [i1] at hb1
  rw [i6] at hb6
  obtain ⟨hE, hL, hT⟩ := k8_three hb8 la8
  refine ⟨Lk, Xl, e, hX, ⟨hord, haft, hE, hL, hT, ?_, ?_, ?_⟩⟩
  · intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl
    · exact entry_of_seat hb1 la1 _ (k3_runs hs1 _)
    · exact entry_of_seat hb1 la1 _ (k3_runs hs1 _)
    · exact entry_of_seat hb4 la4 _ (k4_front x)
    · exact entry_of_seat hb6 la6 _ (k3_runs hs6 _)
    · exact entry_of_seat hb6 la6 _ (k3_runs hs6 _)
  · intro o ho
    obtain rfl := List.mem_singleton.1 ho
    exact entry_of_seat hb4 la4 _ (k4_back x)
  · intro o ho
    obtain rfl := List.mem_singleton.1 ho
    exact after_of_seat hb4 la4 _ (k4_freeSlot x)

/-- **AT EACH ATTENTION LINK.** -/
theorem k8At_attention (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ g < 12, ∃ (Lk : Link S Cl) (Xl : OnBytes.Model.Stages.LinkH),
      c.links[2 * g + 1]? = some Lk ∧ Bs.G₀.built[2 * g + 1]? = some Xl ∧
      K8At Lk (ProofFile.k8ParW Z Bs.G₀ Xl (2 * g + 1)) 4
        [(1, "objects"), (1, "guests"), (2, "first"), (2, "keys"), (2, "join"), (2, "second"),
          (1, "planes"), (6, "objects"), (6, "guests")] [] [] := by
  intro g hg
  have hne : 2 * g + 1 ≠ 24 := by omega
  obtain ⟨Lk, -, -, -, e, -, -, -, -, -, -, -, -, -, -, hord, haft, -⟩ :=
    (k9_of hS hR O).2 (2 * g + 1) (by omega)
  rw [subAt_attention g] at hord haft
  obtain ⟨L1, b1, b1', e1, hb1, hs1, la1⟩ := k3_of hS hR O (2 * g + 1) (by omega) false
  obtain rfl : Lk = L1 := Option.some.inj (e.symm.trans e1)
  obtain ⟨L6, b6, b6', e6, hb6, hs6, la6⟩ := k3_of hS hR O (2 * g + 1) (by omega) true
  obtain rfl : Lk = L6 := Option.some.inj (e.symm.trans e6)
  obtain ⟨L5, b5, b5', -, e5, hb5, hs5, la5, -⟩ := k5_of hS hR O g hg
  obtain rfl : Lk = L5 := Option.some.inj (e.symm.trans e5)
  obtain ⟨L8, b8, Xl, -, e8, hb8, hX, la8, -⟩ := k8_of_attention hS hR O g hg
  obtain rfl : Lk = L8 := Option.some.inj (e.symm.trans e8)
  have i1 : k3Ix (2 * g + 1) false = 1 := by simp [k3Ix, hne]
  have i6 : k3Ix (2 * g + 1) true = 6 := by simp [k3Ix, hne]
  rw [i1] at hb1
  rw [i6] at hb6
  obtain ⟨hE, hL, hT⟩ := k8_three hb8 la8
  refine ⟨Lk, Xl, e, hX, ⟨hord, haft, hE, hL, hT, ?_, (fun _ ho => nomatch ho),
    (fun _ ho => nomatch ho)⟩⟩
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact entry_of_seat hb1 la1 _ (k3_runs hs1 _)
  · exact entry_of_seat hb1 la1 _ (k3_runs hs1 _)
  · exact entry_of_seat hb5 la5 _ (k5_runs hs5 Z _ _)
  · exact entry_of_seat hb5 la5 _ (k5_runs hs5 Z _ _)
  · exact entry_of_seat hb5 la5 _ (k5_runs hs5 Z _ _)
  · exact entry_of_seat hb5 la5 _ (k5_runs hs5 Z _ _)
  · exact entry_of_seat hb1 la1 _ (k3_runs hs1 _)
  · exact entry_of_seat hb6 la6 _ (k3_runs hs6 _)
  · exact entry_of_seat hb6 la6 _ (k3_runs hs6 _)

/-- **AT THE HEAD's LINK.** -/
theorem k8At_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ (Lk : Link S Cl) (Xl : OnBytes.Model.Stages.LinkH), c.links[24]? = some Lk ∧
      Bs.G₀.built[24]? = some Xl ∧ K8At Lk (ProofFile.k8ParW Z Bs.G₀ Xl 24) 5
        [(2, "objects"), (2, "guests"), (3, "norm"), (3, "join"), (3, "policy"), (2, "planes"),
          (7, "objects"), (7, "guests")] [(3, "logits"), (8, "the merge")] [] := by
  obtain ⟨Lk, -, -, -, e, -, -, -, -, -, -, -, -, -, -, hord, haft, -⟩ :=
    (k9_of hS hR O).2 24 (by omega)
  rw [subAt_head] at hord haft
  obtain ⟨L2, b2, b2', e2, hb2, hs2, la2⟩ := k3_of hS hR O 24 (by omega) false
  obtain rfl : Lk = L2 := Option.some.inj (e.symm.trans e2)
  obtain ⟨L7, b7, b7', e7, hb7, hs7, la7⟩ := k3_of hS hR O 24 (by omega) true
  obtain rfl : Lk = L7 := Option.some.inj (e.symm.trans e7)
  obtain ⟨L3, b3, b3', ms, e3, hb3, -, hs3, la3, -⟩ := k6_of hS hR O
  obtain rfl : Lk = L3 := Option.some.inj (e.symm.trans e3)
  obtain ⟨L8, b8, Xl, e8, hb8, hX, la8, -⟩ := k8_of_head hS hR O
  obtain rfl : Lk = L8 := Option.some.inj (e.symm.trans e8)
  obtain ⟨L11, b11, e11, hb11, la11, -⟩ := k11_of hS hR O
  obtain rfl : Lk = L11 := Option.some.inj (e.symm.trans e11)
  have hb2' : Lk.hear[2]? = some b2 := hb2
  have hb7' : Lk.hear[7]? = some b7 := hb7
  obtain ⟨hE, hL, hT⟩ := k8_three hb8 la8
  refine ⟨Lk, Xl, e, hX, ⟨hord, haft, hE, hL, hT, ?_, ?_, (fun _ ho => nomatch ho)⟩⟩
  · intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact entry_of_seat hb2' la2 _ (k3_runs hs2 _)
    · exact entry_of_seat hb2' la2 _ (k3_runs hs2 _)
    · exact entry_of_seat hb3 la3 _ (k6_runs hs3 _)
    · exact entry_of_seat hb3 la3 _ (k6_runs hs3 _)
    · exact entry_of_seat hb3 la3 _ (k6_runs hs3 _)
    · exact entry_of_seat hb2' la2 _ (k3_runs hs2 _)
    · exact entry_of_seat hb7' la7 _ (k3_runs hs7 _)
    · exact entry_of_seat hb7' la7 _ (k3_runs hs7 _)
  · intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact entry_of_seat hb3 la3 _ (k6_runs hs3 _)
    · exact entry_of_seat hb11 la11 _ (k11_runs Z _ _ _)

end Scope

/-! ## From the two yeses at the seat -/

/-- A yes of the frame's step behind the batching is a yes of the runs behind it. -/
theorem afterIn_of_behind {Lk : Link S Cl} {s t : S} (h : Lk.runBehind s = .ok t) :
    afterIn Lk.hear Lk.orderAfter s = .ok t := by
  unfold Link.runBehind at h
  split at h
  · exact h
  · exact nomatch h

/-- **What the two yeses say at a link**: some a, b, z with the gathering's yes from atS.set s a and
sB = atS.set z.2 b; and, at them, all of k08_sits_front's conclusion. -/
def SeatSays (Lk : Link S Cl) (i : ℕ) (pre post mid : List (ℕ × String)) (s sB sE : S) : Prop :=
  ∃ (a b : VerifiableInference.Desc.K9.Part) (z : List Claim × S),
    claimsInBy Lk.each Lk.hear (pre ++ (i, "K8.equations") :: post)
      (VerifiableInference.Desc.K9.atS.set s a) = .ok z ∧
    sB = VerifiableInference.Desc.K9.atS.set z.2 b ∧
    ∃ (x : List Claim × S) (cls rest : List Claim) (s3' : S) (rT' : S → Except String S)
      (q : K8Part) (tl' ts : HTailF2) (F1 G' Fc : Fork),
      claimsInBy Lk.each Lk.hear pre (VerifiableInference.Desc.K9.atS.set s a) = .ok x ∧
      z.1 = x.1 ++ cls ++ rest ∧ partOf x.2 = some q ∧
      s.tl? = some q.tl ∧ s.funs? = some q.funs ∧ q.funs = q.tl.funs ∧
      equations (q.F.nClaim + x.1.length) q.tl q.funs q.F = .ok (tl', F1, cls) ∧
      (∀ u, blank u ts = blank u q.tl) ∧ rkSelfTestP ts Fc = .ok () ∧
      afterIn Lk.hear ((i, "K8.lsTail") :: mid) (VerifiableInference.Desc.K9.atS.set z.2 b) =
        .ok s3' ∧
      ((Lk.hear[i]?).bind fun b => b.after.lookup "K8.tests") = some rT' ∧ rT' s3' = .ok sE ∧
      s3'.fork? = some G' ∧ Fc.theta = G'.theta ∧ partOf sE = some ⟨ts, q.funs, Fc⟩

/-- **AT A LINK WITH K8At WHOSE BATCHING IS K9's UNDER THE SEAT's DRESS: FROM THE TWO YESES.** -/
theorem k08_at_seat {Lk : Link S Cl} {p : VerifiableInference.Desc.First.K8.ParW} {i : ℕ}
    {pre post mid : List (ℕ × String)} (K : K8At Lk p i pre post mid)
    {w : VerifiableInference.Desc.K9.Where} {a9 : Place} (hk : a9.kind ≠ KindName.K7)
    (hb : ∀ g, LaidAlone ProofFile.sameReply (Lk.batch g)
      (VerifiableInference.Desc.K9.batch VerifiableInference.Desc.K9.atS w g) (Lk.batch g).name a9)
    (s sB sE : S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (h1 : (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).decide s rs gs = .ok sB)
    (h2 : Lk.runBehind sB = .ok sE) : SeatSays Lk i pre post mid s sB sE := by
  have y := ((yes_alone (hb _) hk s sB rs gs).1 h1).1
  rw [K.order] at y
  obtain ⟨a, b, z, hz, rfl⟩ := k08_sits_batch Lk.each Lk.hear i pre post w s sB rs gs y
  have ha := afterIn_of_behind h2
  rw [K.after] at ha
  exact ⟨a, b, z, hz, rfl, k08_sits_front p Lk.each Lk.hear i pre post mid K.hE K.hL K.hT K.hpre
    K.hpost K.hmid s sE a b z hz ha⟩

/-! ## All 25 links, in one sentence -/

/-- K8's number among a link's blocks, by the link's sort. -/
def ixOf : ModelPart → ℕ
  | .head => 5
  | _ => 4

/-- The entries ahead of "K8.equations". -/
def preOf : ModelPart → List (ℕ × String)
  | .layers => [(1, "objects"), (1, "guests"), (2, "front"), (6, "objects"), (6, "guests")]
  | .attention =>
    [(1, "objects"), (1, "guests"), (2, "first"), (2, "keys"), (2, "join"), (2, "second"),
      (1, "planes"), (6, "objects"), (6, "guests")]
  | .head =>
    [(2, "objects"), (2, "guests"), (3, "norm"), (3, "join"), (3, "policy"), (2, "planes"),
      (7, "objects"), (7, "guests")]

/-- The entries behind it. -/
def postOf : ModelPart → List (ℕ × String)
  | .layers => [(2, "back")]
  | .attention => []
  | .head => [(3, "logits"), (8, "the merge")]

/-- The entries between "K8.lsTail" and "K8.tests". -/
def midOf : ModelPart → List (ℕ × String)
  | .layers => [(2, "free-slot")]
  | _ => []

/-- **AT EACH OF THE 25 LINKS OF onlineDescription's FIRST CHAIN, IN SCOPE: THE PREMISES HOLD, AND THE TWO
YESES SAY IT.** -/
theorem k08_scope {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ l < 25, ∃ (Lk : Link S Cl) (Xl : OnBytes.Model.Stages.LinkH),
      c.links[l]? = some Lk ∧ Bs.G₀.built[l]? = some Xl ∧
      K8At Lk (ProofFile.k8ParW Z Bs.G₀ Xl l) (ixOf (subAt l)) (preOf (subAt l)) (postOf (subAt l))
        (midOf (subAt l)) ∧
      ∀ (s sB sE : S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))),
        (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).decide s rs gs = .ok sB →
        Lk.runBehind sB = .ok sE →
        SeatSays Lk (ixOf (subAt l)) (preOf (subAt l)) (postOf (subAt l)) (midOf (subAt l)) s sB
          sE := by
  intro l hl
  obtain ⟨L9, w, -, -, e9, -, -, -, -, -, hb, -⟩ := (k9_of hS hR O).2 l hl
  have key : ∃ (Lk : Link S Cl) (Xl : OnBytes.Model.Stages.LinkH),
      c.links[l]? = some Lk ∧ Bs.G₀.built[l]? = some Xl ∧
      K8At Lk (ProofFile.k8ParW Z Bs.G₀ Xl l) (ixOf (subAt l)) (preOf (subAt l)) (postOf (subAt l))
        (midOf (subAt l)) := by
    by_cases h24 : l = 24
    · subst h24
      exact k8At_head hS hR O
    · by_cases he : l % 2 = 0
      · have ej : 2 * (l / 2) = l := by omega
        have h := k8At_layers hS hR O (l / 2) (by omega)
        rw [ej] at h
        have hs : subAt l = .layers := by
          rw [← ej]
          exact subAt_layers (l / 2) (by omega)
        rw [hs]
        exact h
      · have ej : 2 * (l / 2) + 1 = l := by omega
        have h := k8At_attention hS hR O (l / 2) (by omega)
        rw [ej] at h
        have hs : subAt l = .attention := by
          rw [← ej]
          exact subAt_attention (l / 2)
        rw [hs]
        exact h
  obtain ⟨Lk, Xl, e, hX, K⟩ := key
  obtain rfl : Lk = L9 := Option.some.inj (e.symm.trans e9)
  exact ⟨Lk, Xl, e, hX, K, fun s sB sE rs gs h1 h2 =>
    k08_at_seat K (a9 := a9Of l (subAt l)) (fun h => nomatch h) hb s sB sE rs gs h1 h2⟩

end TocK8

#print axioms TocK8.k8At_layers
#print axioms TocK8.k8At_attention
#print axioms TocK8.k8At_head
#print axioms TocK8.k08_at_seat
#print axioms TocK8.k08_scope
