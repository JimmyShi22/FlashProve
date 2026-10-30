-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/K8SitsFrontRuns.lean: EACH RUN OF CLAIMS THAT A LINK's ORDER LAYS
AHEAD OF "K8.equations" LEAVES THE SMALLNESS TEST's STRUCTURE AND THE LIST OF TABLES: run by run, at
its own kind's text: the premise of k08_front_field (K8SitsFront.lean).

Statements and proofs.
Main names:
  putFork_field: a laying of the ledger leaves k8Field.
  via_field: the two runs "objects" and "guests" of the lookup's block (K3.Law.blockVia), at a seat
    whose mark is a laying of the ledger.
  join_field, planes_field: the lookup's runs "join" and "planes" (K3.joinRun, K3.planesRun) at such
    a seat.
  lookSeat_mark: both real seats of the lookup (at the calls; at the digits) mark by a laying of the
    ledger.
  own_field, whole_field, **stated_field**: every run of claims of the lookup's block at an address,
    as K3.theOwn, K3.theWhole and K3.theStated make it.
  front_field: K4's run "front" (blockAtC; from frontAtC and wrote_field).
  **runsN_field**, **k5AtN_field**: K5's four named runs typed at Claim ("first", "keys", "join",
    "second"), as its block at a segment states them (Att.P.runsN, Att.P.k5AtN: Att/SeatN.lean):
    from runN_ok, K5Law.runsK_step and K5Law.with_join_step: each hands the state back or marks one
    debt in the ledger.
  k5_field: K5's own three runs under another wrapper (K9.runOfForms; from K5Law.runOfForms_hands):
    NOT the constant of k5AtN.
  **k6_block_field**: K6's block with its four runs ("norm", "join", "policy", "logits":
    Kinds.Head.blockClaims): from k6_have (HeadRunsCarry.lean). k6_join_field: its "join" alone (by
    join_field).
Limits. EACH LEMMA SPEAKS OF ONE KIND's TEXT. THE ORDERS (Driver/Chain.lean): layers: (1, "objects")
(1, "guests") (2, "front") (6, "objects") (6, "guests"); attention: (1, "objects") (1, "guests") (2,
"first") (2, "keys") (2, "join") (2, "second") (1, "planes") (6, "objects") (6, "guests"); head: (2,
"objects") (2, "guests") (3, "norm") (3, "join") (3, "policy") (2, "planes") (7, "objects") (7,
"guests"). THAT THE BLOCKS AT THESE NUMBERS OF A DESCRIPTION's LINK ARE THESE KINDS' BLOCKS (under
Block.guarded and whatever else the maker lays over them) IS NOT SAID HERE. "K8.equations" READS THE
SMALLNESS TEST's STRUCTURE, THE LIST OF TABLES, THE LEDGER AND THE COUNT: THE FIELD HERE HOLDS THE
FIRST TWO ALONE: many of these runs WRITE THE LEDGER (a mark, a slot's filling): of the ledger
nothing is said. The guests' list of the lookup's block at an address is empty; via_field holds at
any list.

-/
import Johnson.Desc.First.TailClaims.K8SitsFront
import Johnson.Desc.First.Look.K3OwnIs
import Johnson.Desc.First.Look.K3Runs
import Johnson.Desc.First.Att.Claims.RunsHand
import Johnson.Desc.First.Att.SeatN

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims

/-- A laying of the ledger leaves the field. -/
theorem putFork_field (s : S) (G : Fork) : k8Field (s.putFork G) = k8Field s :=
  beside_k8Field.fork s G

/-- A run leaves the field. -/
def Leaves8 {Cl : Type} (run : Nat → S → Except String (List Cl × S)) : Prop :=
  ∀ n e c e₁, run n e = .ok (c, e₁) → k8Field e₁ = k8Field e

/-- A yes of two steps in a row. -/
theorem exc_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => exact nomatch h
  | ok a => exact ⟨a, rfl, h⟩

section Look

variable {Cl : Type}

/-- The lookup's own two runs, at a seat whose mark is a laying of the ledger. -/
theorem via_field (seat : K3.Seat S Cl) (hm : ∀ s G, seat.mark s G = s.putFork G) (piece : Nat)
    (laid : Array Nat) (before : List (Nat × Nat)) (p : First.Look.P)
    (guests : List (First.Look.Guest S Cl)) :
    ∀ c ∈ (K3.Law.blockVia seat piece laid before p guests).claims, Leaves8 c.2 := by
  intro c hc n e cl e₁ h
  simp only [K3.Law.blockVia, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨F, -, h⟩ := exc_bind_ok h
    obtain ⟨g, -, h⟩ := exc_bind_ok h
    obtain rfl := (Prod.mk.inj (Except.ok.inj h)).2
    rw [hm]
    exact putFork_field e _
  · cases h1 : (guests.mapM fun (g : First.Look.Guest S Cl) => g.form e) with
    | none => simp only [h1, Option.map, named] at h; exact nomatch h
    | some l =>
      simp only [h1, Option.map, named] at h
      obtain rfl := (Prod.mk.inj (Except.ok.inj h)).2
      rfl

/-- "join". -/
theorem join_field (seat : K3.Seat S Cl) (hm : ∀ s G, seat.mark s G = s.putFork G)
    (keys : S → Option (Array Aff)) : Leaves8 (K3.joinRun seat keys) := by
  intro n e cl e₁ h
  unfold K3.joinRun at h
  obtain ⟨F, -, h⟩ := exc_bind_ok h
  obtain ⟨g, -, h⟩ := exc_bind_ok h
  obtain ⟨_, -, h⟩ := exc_bind_ok h
  obtain ⟨KF, -, h⟩ := exc_bind_ok h
  obtain ⟨x, -, h⟩ := exc_bind_ok h
  obtain rfl := (Prod.mk.inj (Except.ok.inj h)).2
  rw [hm]
  exact putFork_field e _

/-- "planes". -/
theorem planes_field (seat : K3.Seat S Cl) (hm : ∀ s G, seat.mark s G = s.putFork G) (lm : Nat)
    (readers : K3.Readers S) : Leaves8 (K3.planesRun seat lm readers) := by
  intro n e cl e₁ h
  unfold K3.planesRun at h
  obtain ⟨F, -, h⟩ := exc_bind_ok h
  obtain ⟨g, -, h⟩ := exc_bind_ok h
  obtain ⟨_, -, h⟩ := exc_bind_ok h
  obtain ⟨r, -, h⟩ := exc_bind_ok h
  obtain ⟨x, -, h⟩ := exc_bind_ok h
  obtain rfl := (Prod.mk.inj (Except.ok.inj h)).2
  rw [hm]
  exact putFork_field e _

/-- Both real seats mark by a laying of the ledger. -/
theorem lookSeat_mark (claim : Aff → Cl) (digits : Bool) (s : S) (G : Fork) :
    (K3.seatOfLookupOnDigitsOrCalls claim digits).mark s G = s.putFork G := by
  cases digits <;> rfl

/-- Every run of the lookup's block at an address. -/
theorem own_field (claim : Aff → Cl) (runs : Bool) (X : Model.Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Place) (b : Block S Cl)
    (h : K3.theOwn claim runs X codes shape a = some b) : ∀ c ∈ b.claims, Leaves8 c.2 := by
  unfold K3.theOwn at h
  split at h
  · cases h
  · obtain ⟨i, -, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨digits, -, h⟩ := List.exists_of_findSome?_eq_some h
    split at h
    · cases h
    · obtain ⟨p, -, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨sent, -, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨laid, -, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨key, -, h⟩ := Option.map_eq_some_iff.1 h
      subst h
      cases runs
      · intro c hc
        exact nomatch hc
      · exact via_field (K3.seatOfLookupOnDigitsOrCalls claim digits) (lookSeat_mark claim digits) a.piece laid sent p
          []

/-- The same with the quiet step behind it. -/
theorem whole_field (claim : Aff → Cl) (runs : Bool) (X : Model.Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Place) (B : Block S Cl)
    (h : K3.theWhole claim runs X codes shape a = some B) : ∀ c ∈ B.claims, Leaves8 c.2 := by
  obtain ⟨b, hb, hB⟩ := K3.theWhole_is claim runs X codes shape a B h
  rcases hB with ⟨-, e⟩ | ⟨f, -, e⟩
  · rw [e]
    exact own_field claim runs X codes shape a b hb
  · rw [e]
    intro c hc
    have hc' : c ∈ b.claims ++ [] := hc
    rw [List.append_nil] at hc'
    exact own_field claim runs X codes shape a b hb c hc'

/-- **Every run of claims of the lookup's block as it is stated at an address.** -/
theorem stated_field (claim : Aff → Cl) (readers : Nat → Option (K3.Readers S))
    (X : Model.Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place)
    (B : Block S Cl) (h : K3.theStated claim readers X codes shape a = some B) :
    ∀ c ∈ B.claims, Leaves8 c.2 := by
  unfold K3.theStated at h
  obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.1 h
  have hw := whole_field claim true X codes shape a b hb
  split at h
  · cases h
    exact hw
  · split at h
    · cases h
      exact hw
    · split at h
      · cases h
        exact hw
      · obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h
        intro c hc
        rcases List.mem_append.1 (show c ∈ b.claims ++ [("planes", _)] from hc) with hc | hc
        · exact hw c hc
        · obtain rfl := List.mem_singleton.1 hc
          exact planes_field (K3.seatCalls claim) (fun _ _ => rfl) p.lm _

end Look

/-- K4's run "front". -/
theorem front_field {p : OnBytes.Desc.First.K4.Par}
    {run : Nat → S → Except String (List Claim × S)}
    (hr : (OnBytes.Desc.First.K4.blockAtC p).claims.lookup "front" = some run) : Leaves8 run := by
  intro n e cl e₁ h
  obtain ⟨a, _, _, G, _, _, _, hw⟩ := OnBytes.Desc.First.K4.frontAtC hr h
  exact (wrote_field hw).1

/-- K5's three runs: the state is handed back. -/
theorem k5_field (seat : First.Att.P.SeatC S) (c : First.Att.P.ParC) :
    ∀ r ∈ First.Att.P.runsK seat c, Leaves8 (VerifiableInference.Desc.K9.runOfForms r).2 := by
  intro r hr n e cl e₁ h
  rw [(K5Law.runOfForms_hands seat c r hr n e cl e₁ h).1]

/-- **K5's four named runs, typed at Claim, as its block at a segment states them** ("first",
"keys", "join", "second"): each hands the state back or marks one debt in the ledger. -/
theorem runsN_field (A : Attention.Plan) : ∀ c ∈ First.Att.P.runsN A, Leaves8 c.2 := by
  intro c hc n e cl e₁ h
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hc
  obtain ⟨l, h0, -⟩ := First.Att.P.runN_ok h
  rcases K5Law.with_join_step _ (First.Att.P.keysOfO A) (K5Law.runsK_step _ _) r hr n e l e₁ h0 with
    rfl | ⟨F, g, -, -, rfl⟩
  · rfl
  · exact putFork_field e _

/-- The same of the block. -/
theorem k5AtN_field {W : Verify.Public} {l g : Nat} {before : List (Nat × Nat)}
    {b : Block S Claim} (h : First.Att.P.k5AtN W l g before = some b) :
    ∀ c ∈ b.claims, Leaves8 c.2 := by
  unfold First.Att.P.k5AtN at h
  obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h
  exact runsN_field p

/-- K6's "join". -/
theorem k6_join_field (keys : S → Option (Array Aff)) :
    Leaves8 (K3.joinRun (K3.seatCalls VerifiableInference.Desc.Kinds.Head.asClaim) keys) :=
  join_field _ (fun _ _ => rfl) keys

/-- **K6's block with its four runs** ("norm", "join", "policy", "logits"). -/
theorem k6_block_field {W : Verify.Public} {l : Nat} {b6 : Block S Claim}
    (h : VerifiableInference.Desc.Kinds.Head.blockClaims W l = some b6) :
    ∀ c ∈ b6.claims, Leaves8 c.2 := by
  intro c hc n e cl e₁ hr
  exact VerifiableInference.Desc.Kinds.Head.Law.k6_have (fun s s' => k8Field s' = k8Field s) W l
    (fun _ => rfl) (fun s F g _ _ => putFork_field s _) b6 h c hc n e (cl, e₁) hr

end VerifiableInference.Desc.First.TailClaims.Law

#print axioms VerifiableInference.Desc.First.TailClaims.Law.stated_field
#print axioms VerifiableInference.Desc.First.TailClaims.Law.join_field
#print axioms VerifiableInference.Desc.First.TailClaims.Law.front_field
#print axioms VerifiableInference.Desc.First.TailClaims.Law.k5_field
#print axioms VerifiableInference.Desc.First.TailClaims.Law.k5AtN_field
#print axioms VerifiableInference.Desc.First.TailClaims.Law.k6_block_field
