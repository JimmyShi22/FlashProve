-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Law/BlindRunsK3.lean: THE LOOKUPS' RUNS OF CLAIMS COMMUTE WITH THE
SMALLNESS TEST's DRAW (`RunBlind`, Johnson/Desc/First/K8/BlindReaders.lean): "objects", "guests",
"planes", and "join" as a calling kind states it: at the kind's own text, up to `K3.theStated`
(Johnson/Desc/First/Look/K3Stated.lean), and under the seat's guard. Rules over letters, and
theorems.
  `RunBlindC`: `RunBlind` at any type of claims. `runBlind_named`, `runBlind_need`, `runBlind_pure`,
    `runBlind_map`: THE RULES: a run that is a row of readings and
    tests, each blind to the draw's one writing (`TlBlind`, BlindPub.lean), and ends in fixed claims
    and a state whose ledger is blind, commutes with the draw. `blind_putFork`: the ledger that is
    read behind a laying of a ledger.
  `ClaimsBlind b`: all runs that the sub-protocol b states. `claimsBlind_andThen`;
    `runBlind_guarded`, `claimsBlind_guarded`: under `Block.guarded` (Johnson/Desc/SeatGuard.lean),
    where the run leaves what goes on to the later chains and the guard reads that alone.
  `via_blind`, `planesRun_blind`, `joinRun_blind`: the four runs at a seat whose three readers are
    blind; `calls_blind`, `digits_blind`: both seats are such. `theOwn_blind`, `theWhole_blind`,
    `theStated_blind`: **the kind's sub-protocol at an address.**
Limits. THE CALLING KINDS' READERS (of the planes' matrix: hr) AND KEYS (hk) ARE PREMISES: blind
where their text reads neither of the two fields that the draw writes: not shown here. That the runs
leave what goes on to the later chains (ho) is a premise of the rule on the guard. The walk from
`theStated` to what the seated link states is not made here. Nothing on soundness.

-/
import Johnson.Desc.First.K8.BlindReaders
import Johnson.Desc.First.Look.K3Stated
import Johnson.Desc.SeatGuard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Claim Place named need)
open VerifiableInference.Desc.First (S)

/-! ## The rules -/

/-- The ledger that is read behind a laying of a ledger. -/
theorem blind_putFork (G : Fork) : TlBlind fun s : S => (s.putFork G).fork? := fun s t h => by
  refine drawn_ind (motive := fun s t => (t.putFork G).fork? = (s.putFork G).fork?) ?_ ?_ ?_ h <;>
    intros <;> simp_all [S.putFork, S.fork?]

/-- `RunBlind`, at any type of claims. At `Claim` it is `RunBlind`, by unfolding. -/
def RunBlindC {C : Type} (f : S → Except String (List C × S)) : Prop :=
  ∀ s t, Drawn s t →
    ((f t).toOption.map fun z => (z.1, z.2.fork?)) = (f s).toOption.map fun z => (z.1, z.2.fork?)

section
variable {C : Type}

theorem runBlind_named {α : Type} (msg : String) (o : S → Option α) (ho : TlBlind o)
    (k : α → S → Except String (List C × S)) (hk : ∀ a, RunBlindC (k a)) :
    RunBlindC fun s => (named msg (o s)).bind fun a => k a s := fun s t hd => by
  show ((named msg (o t)).bind fun a => k a t).toOption.map _ =
    ((named msg (o s)).bind fun a => k a s).toOption.map _
  rw [ho s t hd]
  cases o s with
  | none => rfl
  | some a => exact hk a s t hd

theorem runBlind_need (msg : String) (c : S → Bool) (hc : TlBlind c)
    (k : S → Except String (List C × S)) (hk : RunBlindC k) :
    RunBlindC fun s => (need msg (c s)).bind fun _ => k s := fun s t hd => by
  show ((need msg (c t)).bind fun _ => k t).toOption.map _ =
    ((need msg (c s)).bind fun _ => k s).toOption.map _
  rw [hc s t hd]
  cases c s with
  | false => rfl
  | true => exact hk s t hd

/-- A run's end: claims that are fixed, and a state whose ledger is blind. -/
theorem runBlind_pure (cl : List C) (w : S → S) (hw : TlBlind fun s => (w s).fork?) :
    RunBlindC fun s => (pure (cl, w s) : Except String (List C × S)) := fun s t hd => by
  have e : (w t).fork? = (w s).fork? := hw s t hd
  show some (cl, (w t).fork?) = some (cl, (w s).fork?)
  rw [e]

/-- The claims are turned one by one. -/
theorem runBlind_map {C' : Type} (g : C → C') (f : S → Except String (List C × S))
    (hf : RunBlindC f) : RunBlindC fun s => (f s).map fun y => (y.1.map g, y.2) := fun s t hd => by
  have e := hf s t hd
  show ((f t).map fun y => (y.1.map g, y.2)).toOption.map _ =
    ((f s).map fun y => (y.1.map g, y.2)).toOption.map _
  cases ht : f t with
  | error x =>
    cases hs : f s with
    | error y => rfl
    | ok z =>
      rw [ht, hs] at e
      exact nomatch e
  | ok z' =>
    cases hs : f s with
    | error y =>
      rw [ht, hs] at e
      exact nomatch e
    | ok z =>
      rw [ht, hs] at e
      obtain ⟨e1, e2⟩ := Prod.mk.inj (Option.some.inj e)
      show some (z'.1.map g, z'.2.fork?) = some (z.1.map g, z.2.fork?)
      rw [e1, e2]

end

/-- All runs of claims that a sub-protocol states commute with the draw. -/
def ClaimsBlind (b : Block S Claim) : Prop := ∀ c ∈ b.claims, ∀ n, RunBlind (c.2 n)

/-- **Under the seat's guard**: where the run leaves what goes on to the later chains. -/
theorem runBlind_guarded (same : S → S → Bool) (hs : ∀ s z : S, z.out = s.out → same s z = true)
    (f : S → Except String (List Claim × S)) (hf : RunBlind f)
    (ho : ∀ s z, f s = .ok z → z.2.out = s.out) :
    RunBlind fun t => (f t).bind fun y =>
      (VerifiableInference.Desc.seatSame same t y.2).map fun _ => y := by
  have e : ∀ t, ((f t).bind fun y =>
      (VerifiableInference.Desc.seatSame same t y.2).map fun _ => y) = f t := fun t => by
    cases h : f t with
    | error x => rfl
    | ok y =>
      show (VerifiableInference.Desc.seatSame same t y.2).map (fun _ => y) = .ok y
      unfold VerifiableInference.Desc.seatSame
      rw [if_pos (hs t y.2 (ho t y h))]
      rfl
  intro s t hd
  show ((f t).bind fun y =>
      (VerifiableInference.Desc.seatSame same t y.2).map fun _ => y).toOption.map _ =
    ((f s).bind fun y =>
      (VerifiableInference.Desc.seatSame same s y.2).map fun _ => y).toOption.map _
  rw [e, e]
  exact hf s t hd

theorem claimsBlind_guarded (same : S → S → Bool)
    (hs : ∀ s z : S, z.out = s.out → same s z = true) (but : Place → Bool) {b : Block S Claim}
    (h : ClaimsBlind b) (ho : ∀ c ∈ b.claims, ∀ n s z, c.2 n s = .ok z → z.2.out = s.out) :
    ClaimsBlind (b.guarded same but) := by
  intro c hc n
  obtain ⟨c₀, h₀, rfl⟩ := List.mem_map.1 hc
  exact runBlind_guarded same hs (c₀.2 n) (h c₀ h₀ n) (ho c₀ h₀ n)

theorem claimsBlind_andThen (name : String) {p q : Block S Claim} (hp : ClaimsBlind p)
    (hq : ClaimsBlind q) : ClaimsBlind (p.andThen name q) := fun c hc n => by
  rcases List.mem_append.1 hc with h | h
  · exact hp c h n
  · exact hq c h n

/-! ## K3's runs -/

section
variable {C : Type} (seat : K3.Seat S C) (hfk : TlBlind seat.fork) (hhd : TlBlind seat.heard)
  (hmk : ∀ G, TlBlind fun s => (seat.mark s G).fork?)
include hfk hhd hmk

/-- "objects" and "guests" (no guest is seated). -/
theorem via_blind (piece : ℕ) (laid : Array ℕ) (before : List (ℕ × ℕ)) (p : First.Look.P) :
    ∀ c ∈ (K3.Law.blockVia seat piece laid before p []).claims, ∀ n, RunBlindC (c.2 n) := by
  intro c hc n
  have hc' : c ∈ (K3.Law.blockVia seat piece laid before p []).claims := hc
  unfold K3.Law.blockVia at hc'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
  rcases hc' with rfl | rfl
  · exact runBlind_named _ seat.fork hfk _ fun F => runBlind_named _ seat.heard hhd _ fun g =>
      runBlind_pure _ (fun s => seat.mark s (F.paid g.owedObjects)) (hmk _)
  · exact runBlind_pure [] (fun s => s) blind_fork

/-- "planes", where the calling kind's readers are blind. -/
theorem planesRun_blind (lm : ℕ) (readers : K3.Readers S) (hr : TlBlind readers) (n : ℕ) :
    RunBlindC (K3.planesRun seat lm readers n) :=
  runBlind_named _ seat.fork hfk _ fun _ => runBlind_named _ seat.heard hhd _ fun _ =>
    runBlind_need _ (fun _ => _) (fun _ _ _ => rfl) _ <|
      runBlind_named _ readers hr _ fun _ =>
        runBlind_named _ (fun _ => _) (fun _ _ _ => rfl) _ fun x =>
          runBlind_pure _ (fun s => seat.mark s x.2.1) (hmk _)

/-- "join", where the calling kind's keys are blind. -/
theorem joinRun_blind (keys : S → Option (Array Aff)) (hk : TlBlind keys) (n : ℕ) :
    RunBlindC (K3.joinRun seat keys n) :=
  runBlind_named _ seat.fork hfk _ fun _ => runBlind_named _ seat.heard hhd _ fun _ =>
    runBlind_need _ (fun _ => _) (fun _ _ _ => rfl) _ <|
      runBlind_named _ keys hk _ fun _ =>
        runBlind_named _ (fun _ => _) (fun _ _ _ => rfl) _ fun x =>
          runBlind_pure _ (fun s => seat.mark s x.2.1) (hmk _)

end

theorem calls_blind {C : Type} (claim : Aff → C) :
    TlBlind (K3.seatCalls claim).fork ∧ TlBlind (K3.seatCalls claim).heard ∧
      ∀ G, TlBlind fun s => ((K3.seatCalls claim).mark s G).fork? :=
  ⟨blind_fork, blind_lookHeard, blind_putFork⟩

theorem digits_blind {C : Type} (claim : Aff → C) :
    TlBlind (K3.seatDigits claim).fork ∧ TlBlind (K3.seatDigits claim).heard ∧
      ∀ G, TlBlind fun s => ((K3.seatDigits claim).mark s G).fork? :=
  ⟨blind_fork, blind_tlHeard, blind_putFork⟩

/-- K3's own sub-protocol at an address. -/
theorem theOwn_blind (claim : Aff → Claim) (runs : Bool) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Place) {b : Block S Claim}
    (h : K3.theOwn claim runs X codes shape a = some b) : ClaimsBlind b := by
  unfold K3.theOwn at h
  split at h
  · exact nomatch h
  · obtain ⟨i, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨digits, _, h⟩ := List.exists_of_findSome?_eq_some h
    split at h
    · exact nomatch h
    · obtain ⟨p, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨sent, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨laid, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨key, _, rfl⟩ := Option.map_eq_some_iff.1 h
      have W : ClaimsBlind (K3.Law.blockVia
          (if digits = true then K3.seatDigits claim else K3.seatCalls claim) a.piece laid sent p
          []) := by
        cases digits with
        | true =>
          exact via_blind _ (digits_blind claim).1 (digits_blind claim).2.1
            (digits_blind claim).2.2 a.piece laid sent p
        | false =>
          exact via_blind _ (calls_blind claim).1 (calls_blind claim).2.1
            (calls_blind claim).2.2 a.piece laid sent p
      cases runs with
      | true => exact W
      | false => exact fun _ hc => nomatch hc

/-- With the step without a round joined behind it. -/
theorem theWhole_blind (claim : Aff → Claim) (runs : Bool) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Place) {b : Block S Claim}
    (h : K3.theWhole claim runs X codes shape a = some b) : ClaimsBlind b := by
  unfold K3.theWhole at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  have W := theOwn_blind claim runs X codes shape a h0
  cases hf : (a.link.bind fun i => K3.quietAt X i (a.piece == K3.pieceAt X i true)) with
  | none => exact W
  | some f => exact claimsBlind_andThen _ W fun _ hc => nomatch hc

/-- **K3's SUB-PROTOCOL AT AN ADDRESS, WHOLE, WITH ITS RUNS STATED: EVERY RUN COMMUTES WITH THE
DRAW**, where the calling kinds' readers of the planes' matrix are blind. -/
theorem theStated_blind (claim : Aff → Claim) (readers : ℕ → Option (K3.Readers S))
    (hr : ∀ i r, readers i = some r → TlBlind r) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Place) {b : Block S Claim}
    (h : K3.theStated claim readers X codes shape a = some b) : ClaimsBlind b := by
  unfold K3.theStated at h
  obtain ⟨b₀, h0, h⟩ := Option.bind_eq_some_iff.1 h
  have W := theWhole_blind claim true X codes shape a h0
  split at h
  · cases h
    exact W
  · split at h
    · cases h
      exact W
    · split at h
      · cases h
        exact W
      · obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h
        intro c hc n
        rcases List.mem_append.1 hc with hc | hc
        · exact W c hc n
        · obtain rfl := List.mem_singleton.1 hc
          exact planesRun_blind _ (calls_blind claim).1 (calls_blind claim).2.1
            (calls_blind claim).2.2 _ _ (hr _ _ (by assumption)) n

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.runBlind_guarded
#print axioms VerifiableInference.Desc.First.K8.planesRun_blind
#print axioms VerifiableInference.Desc.First.K8.joinRun_blind
#print axioms VerifiableInference.Desc.First.K8.theStated_blind
