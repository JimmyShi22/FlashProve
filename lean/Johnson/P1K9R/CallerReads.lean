-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K9R/CallerReads.lean: the kind "lookup" (K3), for the batching kind's law (K9): THE FIRST
OF THE THREE SENTENCES ON THE CALLER's FORMS (CallerFormsQ.read, Johnson/P1K9R/CallerFenced.lean)
AT THE TWO CALLERS' OWN READERS: at a state that goes on from the fixed part q the caller's readers
of the planes' matrix, and attention's key forms, ARE FUNCTIONS OF q. Definitions, statements and
proofs. A law file; no running text imports it.

WHAT IS READ OFF q. Attention (First.Att.P.readersOfO A · keysOfO A): what the lookup on the calls
and the hearing have left (rd q.1: the closed φ keeps both) and the SNAPSHOT's ledger in place of
the live one: that the two ledgers give one answer is inAt_one
(Johnson/Desc/First/Att/Claims/InAtOne.lean), under its promise K5OkAt at the snapshot (hQ: a
clause of the named Ok at an attention link). The head (Kinds.Head.callerReaders (planesAt iU3)):
the tables and "opened" (kap q.1: the closed φ keeps both) and the number of columns of the reads'
array in the snapshot's ledger (goesOn_K). NO NEW CLAUSE IS ASKED OF Ok; φ NEED NOT KEEP MORE.
KIN: read_off_q (Johnson/Desc/First/Att/Claims/K5Still.lean): the side "returns".

  inQ rd c q · inOf_off_q        attention's input of its runs, off q
  attReadersQ · attReaders_off_q · attKeysQ · attKeys_off_q
  headPlanesQ · headPlanes_off_q · headReadersQ · headReaders_off_q
  bitQ · pinQ · keyQ             the forms off q, in bitOf's, pinOf's and keysOf's own shapes
  read_bits · read_pin · read_keys   CallerFormsQ's field read, general in readers that are read
                                 off q; att_* and head_*: at the two callers.
Limits. The two other sentences (filled · pinned) are not here. A law at states that go on from q:
idle where none does. Nothing on soundness.

-/
import Johnson.P1K9R.CallerFenced
import Johnson.Desc.First.Att.Claims.InAtOne
import Johnson.Desc.First.Att.Claims.K5Still
import Johnson.Desc.Kinds.Law.RunsStill
import Johnson.Desc.First.Link.Law.K11Run

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open OnBytes.PscRun (Later)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (ParC)
open VerifiableInference.Desc.K3 (Readers)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L (Pub9 Fx9 GoesOn)
open VerifiableInference.Desc.PhiAll (psiAtt psiAtt_at goesOn_K get_att)
open VerifiableInference.Desc.K11Run (get_head)
open VerifiableInference.Desc.Kinds.Head (callerReaders planesAt planeEntry PlaneRead)
open VerifiableInference.Desc.Kinds.Head.Law (Seen seenOf)
open K5Law

variable {α : Type} (φ : S → α) (Ok : α × Option Pub9 → Prop)

/-! ## 1 The forms, off whatever reads the readers off q -/

/-- bitOf's shape, off q. -/
def bitQ (R : α × Option Pub9 → Option ((ℕ → ℕ → Option Aff) × (ℕ → Option Aff))) (i : ℕ × ℕ)
    (q : α × Option Pub9) : Aff := ((R q).bind fun r => r.1 i.1 i.2).getD {}

/-- pinOf's shape, off q. -/
def pinQ (R : α × Option Pub9 → Option ((ℕ → ℕ → Option Aff) × (ℕ → Option Aff))) (col : ℕ)
    (q : α × Option Pub9) : Aff := ((R q).bind fun r => r.2 col).getD {}

/-- keysOf's shape, off q. -/
def keyQ (KQ : α × Option Pub9 → Option (Array Aff)) (k : ℕ) (q : α × Option Pub9) : Aff :=
  ((KQ q).getD #[]).getD k (Aff.ofConst zeroE)

theorem read_bits {readers : Readers S}
    {R : α × Option Pub9 → Option ((ℕ → ℕ → Option Aff) × (ℕ → Option Aff))}
    (h : ∀ q e, Fx9 φ Ok q e → readers e = R q) (i : ℕ × ℕ) (q : α × Option Pub9) (e : S)
    (he : Fx9 φ Ok q e) : bitOf readers e i.1 i.2 = bitQ R i q := by
  unfold bitOf bitQ
  rw [h q e he]

theorem read_pin {readers : Readers S}
    {R : α × Option Pub9 → Option ((ℕ → ℕ → Option Aff) × (ℕ → Option Aff))}
    (h : ∀ q e, Fx9 φ Ok q e → readers e = R q) (col : ℕ) (q : α × Option Pub9) (e : S)
    (he : Fx9 φ Ok q e) : pinOf readers e col = pinQ R col q := by
  unfold pinOf pinQ
  rw [h q e he]

theorem read_keys {keys : S → Option (Array Aff)} {KQ : α × Option Pub9 → Option (Array Aff)}
    (h : ∀ q e, Fx9 φ Ok q e → keys e = KQ q) (k : ℕ) (q : α × Option Pub9) (e : S)
    (he : Fx9 φ Ok q e) : (keysOf keys e).getD k (Aff.ofConst zeroE) = keyQ KQ k q := by
  unfold keysOf keyQ
  rw [h q e he]

/-! ## 2 Attention -/

section att
variable (rd : α → Option (Forest.Heard × P.Heard)) (c : ParC)

/-- Attention's input of its runs, off q: the snapshot's ledger for the live one. -/
def inQ (q : α × Option Pub9) : Option (P.Runs.In × ℕ) :=
  (rd q.1).bind fun gh => q.2.bind fun u => inAt c gh.1 gh.2 u.F

variable (hrd : ∀ e, rd (φ e) = psiAtt e)
  (hQ : ∀ q u g h, Ok q → q.2 = some u → rd q.1 = some (g, h) → K5OkAt c g.zk h u.F)
include hrd hQ

/-- **At a state that goes on from q the runs' input is read off q.** -/
theorem inOf_off_q {q : α × Option Pub9} {e : S} (hf : Fx9 φ Ok q e) :
    P.inOf (P.seatCO c) c e = inQ rd c q := by
  obtain ⟨hok, hφ, u, b, hu, hb, go⟩ := hf
  have hr : rd q.1 = psiAtt e := by rw [← hφ, hrd]
  unfold inQ
  rw [hr, hu]
  cases he : e.here with
  | att a =>
    rw [inOf_isAt he, psiAtt_at e a he]
    have hF : b.F = a.F := get_att e b a hb he
    cases hg : a.g with
    | none => rfl
    | some g =>
      cases hh : a.heard5 with
      | none => rfl
      | some h =>
        have hr' : rd q.1 = some (g, h) := by
          rw [hr, psiAtt_at e a he, hg, hh]
          rfl
        show inAt c g h a.F = inAt c g h u.F
        exact inAt_one (hQ q u g h hok hu hr') (hF ▸ go.1) (hF ▸ goesOn_K go c.iU3)
  | _ =>
    have e1 : psiAtt e = none := by
      unfold psiAtt
      rw [he]
    rw [e1]
    cases hx : P.inOf (P.seatCO c) c e with
    | none => rfl
    | some x =>
      obtain ⟨a, ha⟩ := att_of_inOf hx
      rw [he] at ha
      cases ha

/-- readersOfK's own function of the runs' input. -/
def readersOfIn (x : P.Runs.In × ℕ) : (ℕ → ℕ → Option Aff) × (ℕ → Option Aff) :=
  let at_ (place col : ℕ) : Option Aff :=
    (P.Runs.gather x.2 (P.Runs.u3at x.1 place col)).map (·.1)
  (fun e col => at_ (if e == 0 then x.1.t.tBit0 else x.1.t.tBit1) col,
    fun col => at_ x.1.t.tPin col)

/-- keysOfK's own function of the padding's input and the runs' input. -/
def keysOfIn (pd : Option P.Runs.PadIn) (x : P.Runs.In × ℕ) : Option (Array Aff) :=
  pd.bind fun k3 => (P.Runs.firstRun x.1 x.2).bind fun w => P.Runs.keysRun x.1 k3 w.2

/-- Attention's readers of the planes' matrix, off q. -/
def attReadersQ (q : α × Option Pub9) : Option ((ℕ → ℕ → Option Aff) × (ℕ → Option Aff)) :=
  (inQ rd c q).map readersOfIn

/-- Attention's key forms, off q. -/
def attKeysQ (q : α × Option Pub9) : Option (Array Aff) :=
  (inQ rd c q).bind (keysOfIn ((rd q.1).map fun gh => P.padOfO gh.1.shape))

theorem attReaders_off_q {q : α × Option Pub9} {e : S} (hf : Fx9 φ Ok q e) :
    P.readersOfK (P.seatCO c) c e = attReadersQ rd c q := by
  show (P.inOf (P.seatCO c) c e).map readersOfIn = _
  rw [inOf_off_q φ Ok rd c hrd hQ hf]
  rfl

theorem attKeys_off_q {q : α × Option Pub9} {e : S} (hf : Fx9 φ Ok q e) :
    P.keysOfK (P.seatCO c) c e = attKeysQ rd c q := by
  have h0 : P.keysOfK (P.seatCO c) c e =
      (P.inOf (P.seatCO c) c e).bind (keysOfIn ((P.seatCO c).pad e)) := rfl
  rw [h0, inOf_off_q φ Ok rd c hrd hQ hf]
  unfold attKeysQ
  cases hx : inQ rd c q with
  | none => rfl
  | some x =>
    have hr : rd q.1 = psiAtt e := by rw [← hf.2.1, hrd]
    obtain ⟨gh, hgh, -⟩ := Option.bind_eq_some_iff.1 hx
    have hp : (P.seatCO c).pad e = (rd q.1).map fun gh => P.padOfO gh.1.shape := by
      rw [hgh]
      rw [hr] at hgh
      cases he : e.here with
      | att a =>
        rw [psiAtt_at e a he] at hgh
        obtain ⟨g, hg, h2⟩ := Option.bind_eq_some_iff.1 hgh
        obtain ⟨h, -, rfl⟩ := Option.map_eq_some_iff.1 h2
        have hp0 : (P.seatCO c).pad e = a.g.map fun (g : Forest.Heard) => P.padOfO g.shape := by
          unfold P.seatCO
          simp only [he]
        rw [hp0, hg]
        rfl
      | _ =>
        unfold psiAtt at hgh
        rw [he] at hgh
        cases hgh
    rw [hp]

end att

/-! ## 3 The head -/

section head
variable (kap : α → Option Seen) (iU3 : ℕ)

/-- The head's three further reads, off q: the tables and "opened" off φ's share, the number of
columns off the snapshot's ledger. -/
def headPlanesQ (q : α × Option Pub9) : Option (PlaneRead → ℕ → Option Aff) :=
  (kap q.1).bind fun z => q.2.bind fun u =>
    if z.opened = true then
      z.t.bind fun tt => ((u.F.trees[iU3]?).map (·.K)).bind fun K =>
        if K == 0 then none else some (planeEntry tt.tab iU3 K)
    else none

/-- The head's readers of the planes' matrix, off q. -/
def headReadersQ (q : α × Option Pub9) : Option ((ℕ → ℕ → Option Aff) × (ℕ → Option Aff)) :=
  (headPlanesQ kap iU3 q).map fun at_ =>
    (fun e col => at_ (if e == 0 then .bits0 else .bits1) col, at_ .pin)

variable (hkap : ∀ e, kap (φ e) = seenOf e)
include hkap

theorem headPlanes_off_q {q : α × Option Pub9} {e : S} (hf : Fx9 φ Ok q e) :
    planesAt iU3 e = headPlanesQ kap iU3 q := by
  obtain ⟨-, hφ, u, b, hu, hb, go⟩ := hf
  have hk : kap q.1 = seenOf e := by rw [← hφ, hkap]
  unfold headPlanesQ
  rw [hk, hu]
  cases he : e.here with
  | head o =>
    obtain ⟨-, -, -, -, -, hF⟩ := get_head e b hb o he o.F
    have hK := goesOn_K go iU3
    rw [hF] at hK
    have hs : seenOf e =
        some ⟨o.x, o.squaresP, o.t, o.opened, o.lookHeard, e.out.reply, e.req⟩ := by
      unfold seenOf
      rw [he]
    rw [hs]
    show _ = if o.opened = true then
      o.t.bind fun tt => ((u.F.trees[iU3]?).map (·.K)).bind fun K =>
        if K == 0 then none else some (planeEntry tt.tab iU3 K) else none
    rw [← hK]
    unfold planesAt S.fork?
    rw [he]
    by_cases ho : o.opened = true
    · simp only [ho, if_true]
      cases o.t with
      | none => rfl
      | some tt => cases o.F.trees[iU3]? <;> rfl
    · simp only [ho, if_false, Bool.false_eq_true]
  | _ =>
    have hs : seenOf e = none := by
      unfold seenOf
      rw [he]
    rw [hs]
    unfold planesAt
    rw [he]
    rfl

theorem headReaders_off_q {q : α × Option Pub9} {e : S} (hf : Fx9 φ Ok q e) :
    callerReaders (planesAt iU3) e = headReadersQ kap iU3 q := by
  unfold callerReaders headReadersQ
  rw [headPlanes_off_q φ Ok kap iU3 hkap hf]

end head

/-! ## 4 CallerFormsQ's field read, at the two callers -/

section tops
variable (rd : α → Option (Forest.Heard × P.Heard)) (A : Attention.Plan)
  (hrd : ∀ e, rd (φ e) = psiAtt e)
  (hQ : ∀ q u g h, Ok q → q.2 = some u → rd q.1 = some (g, h) → K5OkAt (P.parCOf A) g.zk h u.F)
include hrd hQ

/-- **Attention, "planes": the bits' forms.** -/
theorem att_read_bits (i : ℕ × ℕ) (q : α × Option Pub9) (e : S) (he : Fx9 φ Ok q e) :
    bitOf (P.readersOfO A) e i.1 i.2 = bitQ (attReadersQ rd (P.parCOf A)) i q :=
  read_bits φ Ok (fun _ _ h => attReaders_off_q φ Ok rd (P.parCOf A) hrd hQ h) i q e he

/-- **Attention, "planes": the pin's forms.** -/
theorem att_read_pin (col : ℕ) (q : α × Option Pub9) (e : S) (he : Fx9 φ Ok q e) :
    pinOf (P.readersOfO A) e col = pinQ (attReadersQ rd (P.parCOf A)) col q :=
  read_pin φ Ok (fun _ _ h => attReaders_off_q φ Ok rd (P.parCOf A) hrd hQ h) col q e he

/-- **Attention, "join": the key forms.** -/
theorem att_read_keys (k : ℕ) (q : α × Option Pub9) (e : S) (he : Fx9 φ Ok q e) :
    (keysOf (P.keysOfO A) e).getD k (Aff.ofConst zeroE) = keyQ (attKeysQ rd (P.parCOf A)) k q :=
  read_keys φ Ok (fun _ _ h => attKeys_off_q φ Ok rd (P.parCOf A) hrd hQ h) k q e he

end tops

section topsHead
variable (kap : α → Option Seen) (iU3 : ℕ) (hkap : ∀ e, kap (φ e) = seenOf e)
include hkap

/-- **The head, "planes": the bits' forms.** -/
theorem head_read_bits (i : ℕ × ℕ) (q : α × Option Pub9) (e : S) (he : Fx9 φ Ok q e) :
    bitOf (callerReaders (planesAt iU3)) e i.1 i.2 = bitQ (headReadersQ kap iU3) i q :=
  read_bits φ Ok (fun _ _ h => headReaders_off_q φ Ok kap iU3 hkap h) i q e he

/-- **The head, "planes": the pin's forms.** -/
theorem head_read_pin (col : ℕ) (q : α × Option Pub9) (e : S) (he : Fx9 φ Ok q e) :
    pinOf (callerReaders (planesAt iU3)) e col = pinQ (headReadersQ kap iU3) col q :=
  read_pin φ Ok (fun _ _ h => headReaders_off_q φ Ok kap iU3 hkap h) col q e he

end topsHead

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.read_bits
#print axioms VerifiableInference.OnPublicFiles.read_pin
#print axioms VerifiableInference.OnPublicFiles.read_keys
#print axioms VerifiableInference.OnPublicFiles.inOf_off_q
#print axioms VerifiableInference.OnPublicFiles.attReaders_off_q
#print axioms VerifiableInference.OnPublicFiles.attKeys_off_q
#print axioms VerifiableInference.OnPublicFiles.headPlanes_off_q
#print axioms VerifiableInference.OnPublicFiles.headReaders_off_q
#print axioms VerifiableInference.OnPublicFiles.att_read_bits
#print axioms VerifiableInference.OnPublicFiles.att_read_pin
#print axioms VerifiableInference.OnPublicFiles.att_read_keys
#print axioms VerifiableInference.OnPublicFiles.head_read_bits
#print axioms VerifiableInference.OnPublicFiles.head_read_pin
