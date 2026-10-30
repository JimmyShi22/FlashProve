-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/Keep/RunsPlain.lean: The kind "lookup" (K3): ITS THREE RUNS OF CLAIMS MEET KIND K9's
PREMISE ON A RUN (PlainOk, Johnson/Desc/First/Batch/Law/PlainRuns.lean; so RunOk,
Johnson/Desc/First/Batch/Law/Gather.lean) AT THE REAL RECORD: the lens atS, the letters O9 φ Ok Fu
and Fx9 φ Ok (Johnson/Desc/First/Batch/Law/FitsAtS.lean). THE UPPER STOREY, over
Johnson/Top/H/Keep/RunsAtS.lean. Definitions, statements and proofs.

What is asked of the letters.
  φ: it holds what was heard at the seat (hd (φ s) = seat.heard s) and is blind to S.putFork.
  Ok: at a fixed part q with a snapshot u at which g was heard it gives K3Ok: u's ledger has its
    sizes; g's shape is lawful; g stands for some rounds at a ledger earlier than u's.
  For "planes" and "join": THE CALLER's CLAUSE: the worths of its forms, read at the record e of the
    run, in the world of any full later record t, are functions of the fixed part and the data.

Main names:
  K3Ok, pick, pick_spec: the promise on the fixed part; rounds chosen out of it, once for all.
  plainOk_of_atS: ONE LEMMA FOR THE THREE: the nine clauses of PlainOk from what RunsAtS.lean gives.
  objects_plainOk, objects_runOk: "objects": NOTHING OF THE CALLER.
  planes_plainOk, join_plainOk: under the caller's clause.
  The lists of values have the length len q at ALL q and y (objVals_length, ...): what the
  discipline on the exponents asks (plain_inWin).

Limits. That Ok can be had with K3Ok inside (what was heard stays and the ledger is later, from K3's
yes to the draw) is each later piece's own; the caller's clause is the calling kind's. K3.block's
runs, not the seated block's by name.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Batch.Law.PlainRuns
import Johnson.Desc.First.Batch.Law.FitsAtS
import Johnson.Top.H.Keep.RunsAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun _root_.Fo
open Cb Cb.Fo Cb.Fo.PlaneClaims
open OnBytes.K.Kc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat joinRun planesRun Readers)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L (claimValue worldAt Bound core PlainOk RunOk plainTm
  runOk_of_plain Pub9 pubOf Fx9 more9 good9 O9 GoesOn fx_of_more kept_of_more part_of_more laterK)

abbrev GE := Cb.Gl.E

/-! ## Two "later" -/

theorem fo_of_psc {F G : Fork} (h : OnBytes.PscRun.Later F G) : _root_.Fo.Later F G :=
  ⟨h.next, h.ns, h.keep⟩

theorem psc_of_fo {F G : Fork} (h : _root_.Fo.Later F G) (hG : Sized G) :
    OnBytes.PscRun.Later F G := ⟨h.next, h.ns, fun _ => hG, h.keep⟩

/-! ## What OnlyUnder keeps -/

theorem core_onlyUnder {F G : Fork} (h : OnlyUnder F G) : core G = core F := by
  obtain ⟨G0, i, hS, rfl⟩ := h
  unfold OnBytes.PscRun.Same at hS
  show core G0 = core F
  rw [hS]
  rfl

theorem fields_onlyUnder {F G : Fork} (h : OnlyUnder F G) :
    G.trees = F.trees ∧ G.LS = F.LS ∧ G.ns = F.ns ∧ G.planClaimsF = F.planClaimsF := by
  obtain ⟨G0, i, hS, rfl⟩ := h
  unfold OnBytes.PscRun.Same at hS
  show G0.trees = F.trees ∧ G0.LS = F.LS ∧ G0.ns = F.ns ∧ G0.planClaimsF = F.planClaimsF
  rw [hS]
  exact ⟨rfl, rfl, rfl, rfl⟩

variable {α : Type} (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop)

/-! ## One lemma for the three -/

/-- **The nine clauses of PlainOk** from what the lower storey gives. -/
theorem plainOk_of_atS (hφp : ∀ s G, φ (s.putFork G) = φ s)
    (run : ℕ → S → Except String (List Desc.Claim × S))
    (vals : α × Option Pub9 → Bound GE → List GE) (len : α × Option Pub9 → ℕ)
    (H : ∀ q front e a c e₁, Fx9 φ Ok q e → atS.get? e = some a → run front e = .ok (c, e₁) →
      ∃ a₁ G, atS.get? e₁ = some a₁ ∧ Left a a₁ G ∧ e₁ = e.putFork G ∧ OnlyUnder a.F G ∧
        OnBytes.PscRun.Later a.F G ∧ c.length = len q ∧ (∀ cl ∈ c, cl.eqFirst = none) ∧
        ∀ t b y, Fx9 φ Ok q t → Fu t → atS.get? t = some b → OnBytes.PscRun.Later G b.F →
          c.map (claimValue Reading.gl (worldAt Reading.gl b.L b.F y)) = vals q y) :
    PlainOk Reading.gl atS (O9 (K := GE) φ Ok Fu) (Fx9 φ Ok) run vals len := by
  intro q front e a c e₁ hf hg ha _ hr
  obtain ⟨a₁, G, h1, hl, rfl, hU, hLt, hlen, hpl, hv⟩ := H q front e a c e₁ hf ha hr
  obtain ⟨t1, t2, t3, t4⟩ := fields_onlyUnder hU
  obtain ⟨a', ha', g1, g2⟩ := hg
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
  have hgo : GoesOn (pubOf a') a₁ := by
    refine ⟨by rw [hl.F]; exact hLt, by rw [hl.F]; exact t4, by rw [hl.F, t1]; rfl,
      by rw [hl.L]; rfl, by rw [hl.L]; rfl, by rw [hl.d]; rfl⟩
  have hm : more9 φ e (e.putFork G) := ⟨hφp e G, fun x hx => by
    obtain rfl : x = a' := Option.some.inj (hx.symm.trans ha)
    exact ⟨a₁, h1, hgo⟩⟩
  have hf1 : Fx9 φ Ok q (e.putFork G) := fx_of_more φ Ok q e _ hf hm
  refine ⟨a₁, h1, by rw [hl.F]; exact core_onlyUnder hU, by rw [hl.F, t1],
    ⟨a₁, h1, by rw [hl.L]; exact g1, by rw [hl.F, t2, t3]; exact g2⟩, hm, hf1, hlen, hpl,
    fun t b y ht hfu hb => ?_⟩
  have hk := (kept_of_more φ _ t a₁ b h1 hb ht.2.1).1
  rw [hl.F] at hk
  exact hv t b y (fx_of_more φ Ok q _ t hf1 ht.2.1) hfu hb hk

/-! ## The promise on the fixed part -/

variable (hd : α → Option Heard) (lm jLK : ℕ)

/-- What a pair (what was heard, rounds) is to the fixed part q. -/
def Stood (q : α × Option Pub9) (x : Heard × Rounds GE) : Prop :=
  hd q.1 = some x.1 ∧ ∃ F0 u, q.2 = some u ∧
    HeardIs Reading.gl x.1 F0 (endsOf x.1.shape lm jLK x.2) ∧ _root_.Fo.Later F0 u.F

/-- **K3's promise on the fixed part.** -/
def K3Ok (q : α × Option Pub9) : Prop :=
  ∀ g u, hd q.1 = some g → q.2 = some u →
    Sized u.F ∧ FoNums.ok g.shape = true ∧ ∃ rs, Stood hd lm jLK q (g, rs)

open Classical in
/-- Rounds for which what was heard stands, chosen once for all. -/
def pick (q : α × Option Pub9) : Option (Heard × Rounds GE) :=
  if h : ∃ x, Stood hd lm jLK q x then some (Classical.choose h) else none

theorem pick_spec {q : α × Option Pub9} {x : Heard × Rounds GE}
    (h : pick hd lm jLK q = some x) : Stood hd lm jLK q x := by
  unfold pick at h
  split at h
  · rename_i hx
    rw [← Option.some.inj h]
    exact Classical.choose_spec hx
  · cases h

theorem pick_some {q : α × Option Pub9} {g : Heard} {u : Pub9} (hk : K3Ok hd lm jLK q)
    (hg : hd q.1 = some g) (hu : q.2 = some u) : ∃ rs, pick hd lm jLK q = some (g, rs) := by
  obtain ⟨_, _, rs, hs⟩ := hk g u hg hu
  have hx : ∃ x, Stood hd lm jLK q x := ⟨_, hs⟩
  have e : pick hd lm jLK q = some (Classical.choose hx) := by
    unfold pick
    rw [dif_pos hx]
  have e1 : (Classical.choose hx).1 = g :=
    Option.some.inj ((Classical.choose_spec hx).1.symm.trans hg)
  exact ⟨(Classical.choose hx).2, by rw [e, ← e1]⟩

/-! ## What the three runs share in front -/

section
variable (seat : Seat S Desc.Claim) (hA : AtS2 seat) (hs : SeatFits seat (·.form))
  (hφh : ∀ s, seat.heard s = hd (φ s)) (hOk : ∀ q, Ok q → K3Ok hd lm jLK q)
include hφh hOk

/-- At a state that goes on from q at which g was heard: the rounds that were picked, and the four
premises of the lower storey. -/
theorem front_of_fx {q : α × Option Pub9} {e : S} {a : Desc.K9.Part} {g : Heard}
    (hf : Fx9 φ Ok q e) (ha : atS.get? e = some a) (hg : seat.heard e = some g) :
    ∃ rs F0, pick hd lm jLK q = some (g, rs) ∧
      HeardIs Reading.gl g F0 (endsOf g.shape lm jLK rs) ∧ _root_.Fo.Later F0 a.F ∧
      FoNums.ok g.shape = true ∧ Sized a.F := by
  obtain ⟨k0, f1, u, b, hu, hb, go⟩ := hf
  obtain rfl : b = a := Option.some.inj (hb.symm.trans ha)
  have hg' : hd q.1 = some g := by rw [← f1, ← hφh]; exact hg
  obtain ⟨su, ok, _⟩ := hOk q k0 g u hg' hu
  obtain ⟨rs, hp⟩ := pick_some hd lm jLK (hOk q k0) hg' hu
  obtain ⟨_, F0, u', hu', hI, hL⟩ := pick_spec hd lm jLK hp
  obtain rfl : u = u' := Option.some.inj (hu.symm.trans hu')
  exact ⟨rs, F0, hp, hI, hL.trans (fo_of_psc go.1), ok, go.1.sized su⟩

end

/-! ## "objects" -/

/-- The values of "objects": the flat rows' residues at the data's mask row. -/
def objVals (q : α × Option Pub9) (y : Bound GE) : List GE :=
  match pick hd lm jLK q with
  | some x => (endsOf x.1.shape lm jLK x.2).rows.map (rowRes (muOf y.mask))
  | none => []

def objLen (q : α × Option Pub9) : ℕ :=
  match pick hd lm jLK q with
  | some x => (endsOf x.1.shape lm jLK x.2).rows.length
  | none => 0

theorem objVals_length (q : α × Option Pub9) (y : Bound GE) :
    (objVals hd lm jLK q y).length = objLen hd lm jLK q := by
  unfold objVals objLen
  cases pick hd lm jLK q <;> simp

section
variable (seat : Seat S Desc.Claim) (hA : AtS2 seat) (hs : SeatFits seat (·.form))
  (hφp : ∀ s G, φ (s.putFork G) = φ s) (hφh : ∀ s, seat.heard s = hd (φ s))
  (hOk : ∀ q, Ok q → K3Ok hd lm jLK q)
include hA hs hφp hφh hOk

/-- **"objects" meets PlainOk: nothing of the caller.** -/
theorem objects_plainOk :
    PlainOk Reading.gl atS (O9 (K := GE) φ Ok Fu) (Fx9 φ Ok) (objectsRun seat)
      (objVals hd lm jLK) (objLen hd lm jLK) := by
  refine plainOk_of_atS φ Ok Fu hφp _ _ _ fun q front e a c e₁ hf ha hr => ?_
  obtain ⟨_, g, _, hg, _⟩ := objects_cut seat hr
  obtain ⟨rs, F0, hp, hI, hL, ok, sa⟩ := front_of_fx φ Ok hd lm jLK seat hφh hOk hf ha hg
  obtain ⟨a₁, G, h1, h2, h3, _, hU, l1, s1, hpl, hv⟩ :=
    objects_atS Reading.gl seat hA hs lm ha hg hI hL ok sa hr
  have hval : ∀ y, objVals hd lm jLK q y =
      (endsOf g.shape lm jLK rs).rows.map (rowRes (muOf y.mask)) := fun y => by
    unfold objVals
    rw [hp]
  refine ⟨a₁, G, h1, h2, h3, hU, psc_of_fo l1 s1, ?_, hpl, fun t b y _ _ _ hk => ?_⟩
  · have := congrArg List.length (hv a.L G ⟨fun _ _ _ _ => 0, fun _ => 0⟩ (Later.refl G))
    rw [List.length_map, List.length_map] at this
    unfold objLen
    rw [hp]
    exact this
  · rw [hval]
    exact hv b.L b.F y (fo_of_psc hk)

/-- **So it meets RunOk.** -/
theorem objects_runOk :
    RunOk Reading.gl atS (O9 (K := GE) φ Ok Fu) (Fx9 φ Ok) (objectsRun seat)
      (plainTm (objVals hd lm jLK)) (objLen hd lm jLK) :=
  runOk_of_plain Reading.gl atS _ _ _ _ _ (fun e t a ha hm => part_of_more φ e t a ha hm)
    (objects_plainOk φ Ok Fu hd lm jLK seat hA hs hφp hφh hOk)

/-! ## "planes", under the caller's clause -/

/-- The values of "planes". bv, pv: the worths of the caller's forms. -/
def plVals (bv : α × Option Pub9 → Bound GE → ℕ → ℕ → GE)
    (pv : α × Option Pub9 → Bound GE → ℕ → GE) (q : α × Option Pub9) (y : Bound GE) : List GE :=
  match pick hd lm jLK q with
  | some x => [claimLeaves x.1.shape lm jLK x.2 (muOf y.mask) (bv q y 0),
      claimBits x.1.shape lm jLK x.2 (muOf y.mask) (bv q y 1), Pin.countK x.1.shape lm (pv q y)]
  | none => []

/-- n where rounds were picked, else 0. -/
def pickLen (n : ℕ) (q : α × Option Pub9) : ℕ :=
  match pick hd lm jLK q with
  | some _ => n
  | none => 0

omit hA hs hφp hφh hOk in
theorem plVals_length (bv : α × Option Pub9 → Bound GE → ℕ → ℕ → GE)
    (pv : α × Option Pub9 → Bound GE → ℕ → GE) (q : α × Option Pub9) (y : Bound GE) :
    (plVals hd lm jLK bv pv q y).length = pickLen hd lm jLK 3 q := by
  unfold plVals pickLen
  cases pick hd lm jLK q <;> rfl

/-- **"planes" meets PlainOk under the caller's clause.** -/
theorem planes_plainOk (readers : Readers S)
    (bv : α × Option Pub9 → Bound GE → ℕ → ℕ → GE) (pv : α × Option Pub9 → Bound GE → ℕ → GE)
    (hb : ∀ q e t b y, Fx9 φ Ok q e → Fx9 φ Ok q t → Fu t → atS.get? t = some b → ∀ k col,
      (bitOf readers e k col).value Reading.gl (worldAt Reading.gl b.L b.F y) = bv q y k col)
    (hp' : ∀ q e t b y, Fx9 φ Ok q e → Fx9 φ Ok q t → Fu t → atS.get? t = some b → ∀ col,
      (pinOf readers e col).value Reading.gl (worldAt Reading.gl b.L b.F y) = pv q y col) :
    PlainOk Reading.gl atS (O9 (K := GE) φ Ok Fu) (Fx9 φ Ok) (planesRun seat lm readers)
      (plVals hd lm jLK bv pv) (pickLen hd lm jLK 3) := by
  refine plainOk_of_atS φ Ok Fu hφp _ _ _ fun q front e a c e₁ hf ha hr => ?_
  obtain ⟨_, g, _, hg⟩ := planes_heard seat lm readers hr
  obtain ⟨rs, F0, hp, hI, hL, ok, sa⟩ := front_of_fx φ Ok hd lm jLK seat hφh hOk hf ha hg
  obtain ⟨a₁, G, h1, h2, h3, _, hU, l1, s1, hpl, hv⟩ :=
    planes_atS Reading.gl seat hA hs lm readers ha hg hI hL ok sa hr
  refine ⟨a₁, G, h1, h2, h3, hU, psc_of_fo l1 s1, ?_, hpl, fun t b y hft hfu hbt hk => ?_⟩
  · have := congrArg List.length (hv a.L G ⟨fun _ _ _ _ => 0, fun _ => 0⟩ (Later.refl G))
    rw [List.length_map] at this
    unfold pickLen
    rw [hp]
    exact this
  · rw [hv b.L b.F y (fo_of_psc hk)]
    unfold plVals
    rw [hp]
    have e0 : (fun col => (bitOf readers e 0 col).value Reading.gl
        (worldAt Reading.gl b.L b.F y)) = bv q y 0 :=
      funext fun col => hb q e t b y hf hft hfu hbt 0 col
    have e1 : (fun col => (bitOf readers e 1 col).value Reading.gl
        (worldAt Reading.gl b.L b.F y)) = bv q y 1 :=
      funext fun col => hb q e t b y hf hft hfu hbt 1 col
    have e2 : (fun col => (pinOf readers e col).value Reading.gl
        (worldAt Reading.gl b.L b.F y)) = pv q y :=
      funext fun col => hp' q e t b y hf hft hfu hbt col
    rw [e0, e1, e2]

/-! ## "join", under the caller's clause -/

/-- The value of "join". kv: the worths of the caller's key forms. -/
def jnVals (kv : α × Option Pub9 → Bound GE → ℕ → GE) (q : α × Option Pub9) (y : Bound GE) :
    List GE :=
  match pick hd lm jLK q with
  | some x => [claimJoin x.1.shape lm jLK x.2 (muOf y.mask) (kv q y)]
  | none => []

omit hA hs hφp hφh hOk in
theorem jnVals_length (kv : α × Option Pub9 → Bound GE → ℕ → GE) (q : α × Option Pub9)
    (y : Bound GE) : (jnVals hd lm jLK kv q y).length = pickLen hd lm jLK 1 q := by
  unfold jnVals pickLen
  cases pick hd lm jLK q <;> rfl

/-- **"join" meets PlainOk under the caller's clause.** -/
theorem join_plainOk (keys : S → Option (Array Aff))
    (kv : α × Option Pub9 → Bound GE → ℕ → GE)
    (hkv : ∀ q e t b y, Fx9 φ Ok q e → Fx9 φ Ok q t → Fu t → atS.get? t = some b → ∀ k,
      ((keysOf keys e).getD k (Aff.ofConst zeroE)).value Reading.gl
        (worldAt Reading.gl b.L b.F y) = kv q y k) :
    PlainOk Reading.gl atS (O9 (K := GE) φ Ok Fu) (Fx9 φ Ok) (joinRun seat keys)
      (jnVals hd lm jLK kv) (pickLen hd lm jLK 1) := by
  refine plainOk_of_atS φ Ok Fu hφp _ _ _ fun q front e a c e₁ hf ha hr => ?_
  obtain ⟨_, g, _, hg⟩ := join_heard seat keys hr
  obtain ⟨rs, F0, hp, hI, hL, ok, sa⟩ := front_of_fx φ Ok hd lm jLK seat hφh hOk hf ha hg
  obtain ⟨a₁, G, h1, h2, h3, _, hU, l1, s1, hpl, hv⟩ :=
    join_atS Reading.gl seat hA hs lm keys ha hg hI hL ok sa hr
  refine ⟨a₁, G, h1, h2, h3, hU, psc_of_fo l1 s1, ?_, hpl, fun t b y hft hfu hbt hk => ?_⟩
  · have := congrArg List.length (hv a.L G ⟨fun _ _ _ _ => 0, fun _ => 0⟩ (Later.refl G))
    rw [List.length_map] at this
    unfold pickLen
    rw [hp]
    exact this
  · rw [hv b.L b.F y (fo_of_psc hk)]
    unfold jnVals
    rw [hp]
    have e0 : (fun k => ((keysOf keys e).getD k (Aff.ofConst zeroE)).value Reading.gl
        (worldAt Reading.gl b.L b.F y)) = kv q y := funext fun k => hkv q e t b y hf hft hfu hbt k
    rw [e0]

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.plainOk_of_atS
#print axioms VerifiableInference.OnPublicFiles.objects_plainOk
#print axioms VerifiableInference.OnPublicFiles.objects_runOk
#print axioms VerifiableInference.OnPublicFiles.planes_plainOk
#print axioms VerifiableInference.OnPublicFiles.join_plainOk
