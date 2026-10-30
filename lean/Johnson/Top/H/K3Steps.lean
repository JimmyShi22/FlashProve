-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3Steps.lean: the kind "lookup" (K3): ITS SHARE OF A LINK's FRAME: what its block's
decision and its runs of claims leave standing, and what they only let grow. Statements and proofs.

A law on the kind speaks of several moments of one link. Between them every block and every run has
to leave what was heard, and may only lead the ledger to a later one. Here is what K3's own block,
at either of its two seats, and K3's own runs owe to that, WITH NO TEST ON THE VIEW's WORDS AND NO
PREMISE ON THE LEDGER's SIZES IN FRONT: the matter needs neither.

Main names:
  `grows_lkPad`: the flat function of the lookup's messages (OnBytes/K/Kc/FlatHear.lean) leads to a
    later ledger wherever it returns; with the like for its pieces and for Fl.owe, Fl.slot,
    Fl.roundsIn. By the class Grows (OnBytes/Desc/First/FlGrows.lean).
  `KeepsLedger fork s s'`: a ledger in front is followed by a later one (OnBytes.PscRun.Later, which
    hands on the arrays' sizes). `KeepsHeard hd s s'`: what hd reads in front it reads behind.
  `Frame fork hd s s'`: both; reflexive and transitive. `Frame.carries`: it gives "what was heard
    stands; a ledger with its sizes is followed by a later one with its sizes", at the order
    Fo.Later (OnBytes/Tie/Pv/Lookup/Forest/FoForm.lean).
  `decide_frame`: of K3.block's decide, at any seat that reads back the ledger that it lays, for any
    reader hd that the seat's put leaves where nothing is heard yet.
  `objects_frame`, `guests_frame`, `join_frame`, `planes_frame`: of the runs of claims: at any seat
    at which a ledger that is laid by the mark is the one that is read (hmf): no other law on the
    seat, so AT EVERY TYPE OF CLAIMS. `planes_marks`: what "planes" lays.
  `block_runs_frame`: of every run in K3.block's own list; its list behind the batching is empty.
  `calls_*`, `digits_*`: all of these at the two seats of Johnson/Desc/First/Look/K3Seat.lean, each
    for BOTH readings of "heard" (the calls': S.lookHeard?; the digits': the smallness test's
    record's field), with the one ledger S.fork?.

Limits. One direction: from a yes. A block that refuses all has these for nothing. Of other kinds'
blocks and runs, and of the batching, nothing is said. A tie of records: no error term. Of the
program `verify-on-bytes` only plain counterparts of its routines, on a ledger and a tape, are named
(lkPad and its pieces): no routine in a context.
Not claimed: anything on soundness, on an honest prover or on hiding.

-/
import Johnson.Top.H.K3LedgerKeeps
import Johnson.Top.H.K3KeySizes
import Johnson.Top.H.K3BlockKeeps
import OnBytes.Desc.First.FlGrows
import OnBytes.Tie.Pv.Lookup.Forest.FoForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Desc.First.Grow
open VerifiableInference.Desc (named need)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits joinRun planesRun Readers)

/-! ## The flat function of the lookup's messages leads to a later ledger -/

section Grows
variable {α β γ : Type}

theorem grows_take {f : Fork → Option (α × Fork)}
    (h : ∀ F x, f F = some x → OnBytes.PscRun.Later F x.2) : Grows (Fl.take f) :=
  ⟨fun {F t a G u} e => by
    unfold Fl.take at e
    cases hf : f F with
    | none => simp [hf] at e
    | some x =>
      simp only [hf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨_, rfl, _⟩ := e
      exact h F x hf⟩

instance grows_slot : Grows Fl.slot := by
  unfold Fl.slot
  infer_instance

instance grows_owe (w : String) : Grows (Fl.owe w) := by
  unfold Fl.owe
  exact grows_take fun F x e => by
    obtain rfl := Option.some.inj e
    exact OnBytes.PscRun.owe_later F w

instance grows_fold (f : β → γ → Fl β) [∀ s a, Grows (f s a)] (l : List γ) (s : β) :
    Grows (l.foldlM f s) := grows_foldlM (fun _ _ => inferInstance) l s

instance grows_roundsIn (form : RoundForm) (p : Psc) (zs : List (E × Nat)) :
    Grows (Fl.roundsIn form p zs) := by
  unfold Fl.roundsIn
  exact grows_foldlM (fun s z => by grows) zs _

instance grows_lkDraws (h : Forest.Shape) : Grows (lkDraws h) := by
  unfold lkDraws
  grows

instance grows_lkTieStep (a : E) (s : Forest.TieStep) (j : Nat) : Grows (lkTieStep a s j) := by
  unfold lkTieStep
  grows

instance grows_lkTie (a : E) : Grows (lkTie a) := by
  unfold lkTie
  grows

instance grows_lkLevel (s : Forest.Descent) (mu : Nat) (order : List Nat) :
    Grows (lkLevel s mu order) := by
  unfold lkLevel
  grows

/-- **The lookup's messages lead to a later ledger.** -/
instance grows_lkPad (calls : Array Call) (pub : Array Nat) (lid : Nat) :
    Grows (lkPad calls pub lid) := by
  unfold lkPad
  grows

end Grows

/-! ## The frame -/

section Frame
variable {T Γ : Type}

/-- A ledger in front is followed by a later one. -/
def KeepsLedger (fork : T → Option Fork) (s s' : T) : Prop :=
  ∀ F, fork s = some F → ∃ F', fork s' = some F' ∧ OnBytes.PscRun.Later F F'

/-- What hd reads in front it reads behind. -/
def KeepsHeard (hd : T → Option Γ) (s s' : T) : Prop := ∀ g, hd s = some g → hd s' = some g

/-- Both. -/
def Frame (fork : T → Option Fork) (hd : T → Option Γ) (s s' : T) : Prop :=
  KeepsHeard hd s s' ∧ KeepsLedger fork s s'

theorem Frame.refl (fork : T → Option Fork) (hd : T → Option Γ) (s : T) : Frame fork hd s s :=
  ⟨fun _ h => h, fun F h => ⟨F, h, OnBytes.PscRun.Later.refl F⟩⟩

theorem Frame.trans {fork : T → Option Fork} {hd : T → Option Γ} {a b c : T}
    (h1 : Frame fork hd a b) (h2 : Frame fork hd b c) : Frame fork hd a c :=
  ⟨fun g h => h2.1 g (h1.1 g h), fun F h => by
    obtain ⟨G, e1, l1⟩ := h1.2 F h
    obtain ⟨H, e2, l2⟩ := h2.2 G e1
    exact ⟨H, e2, l1.trans l2⟩⟩

theorem toFo {F G : Fork} (h : OnBytes.PscRun.Later F G) : _root_.Fo.Later F G :=
  ⟨h.next, h.ns, h.keep⟩

/-- What was heard stands; a ledger with its sizes is followed by a later one with its sizes. -/
theorem Frame.carries {fork : T → Option Fork} {hd : T → Option Γ} {s s' : T}
    (h : Frame fork hd s s') :
    (∀ g, hd s = some g → hd s' = some g) ∧
      ∀ F, fork s = some F → OnBytes.PscRun.Sized F →
        ∃ F', fork s' = some F' ∧ _root_.Fo.Later F F' ∧ OnBytes.PscRun.Sized F' :=
  ⟨h.1, fun F hF hS => by
    obtain ⟨F', e, l⟩ := h.2 F hF
    exact ⟨F', e, toFo l, l.sized hS⟩⟩

end Frame

/-! ## The block's decision and the runs, at any seat -/

section Seat
variable {T Cl Γ : Type}

/-- **decide.** hd: any reader that the seat's put leaves where the seat has heard nothing yet. -/
theorem decide_frame (seat : Seat T Cl) (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
    (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest T Cl)) (hk : SeatKeeps seat)
    (hd : T → Option Γ)
    (hput : ∀ s g G x, seat.heard s = none → hd s = some x → hd (seat.put s g G) = some x)
    (s s' : T) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (h : (Desc.K3.block seat piece laid before p guests).decide s rs cols = .ok s') :
    Frame seat.fork hd s s' := by
  obtain ⟨F, F', g, t, hF, hn, hl, rfl⟩ :=
    decide_lkPad seat piece laid before p guests s s' rs cols h
  refine ⟨fun x hx => hput s g F' x hn hx, fun F0 hF0 => ?_⟩
  obtain rfl : F = F0 := Option.some.inj (hF.symm.trans hF0)
  exact ⟨F', hk s g F' (by rw [hF]; rfl) hn, Grows.later hl⟩

/-- The seat's own reading of "heard": nothing is heard in front of a yes. -/
theorem decide_frame_own (seat : Seat T Cl) (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
    (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest T Cl)) (hk : SeatKeeps seat)
    (s s' : T) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (h : (Desc.K3.block seat piece laid before p guests).decide s rs cols = .ok s') :
    Frame seat.fork seat.heard s s' :=
  decide_frame seat piece laid before p guests hk seat.heard
    (fun _ _ _ _ hn hx => by rw [hn] at hx; cases hx) s s' rs cols h

/-- A ledger that is laid by the seat's mark, later than the one in front. -/
theorem mark_frame (seat : Seat T Cl)
    (hmf : ∀ s F G, seat.fork s = some F → seat.fork (seat.mark s G) = some G)
    (hd : T → Option Γ) (hmark : ∀ s F G, seat.fork s = some F → hd (seat.mark s G) = hd s)
    (s : T) (F G : Fork)
    (hF : seat.fork s = some F) (hl : OnBytes.PscRun.Later F G) :
    Frame seat.fork hd s (seat.mark s G) :=
  ⟨fun x hx => by rw [hmark s F G hF]; exact hx, fun F0 hF0 => by
    obtain rfl : F = F0 := Option.some.inj (hF.symm.trans hF0)
    exact ⟨G, hmf s F G hF, hl⟩⟩

/-- **"objects".** -/
theorem objects_frame (seat : Seat T Cl)
    (hmf : ∀ s F G, seat.fork s = some F → seat.fork (seat.mark s G) = some G)
    (hd : T → Option Γ) (hmark : ∀ s F G, seat.fork s = some F → hd (seat.mark s G) = hd s)
    (n : ℕ) (s s' : T) (cl : List Cl) (hrun : objectsRun seat n s = .ok (cl, s')) :
    Frame seat.fork hd s s' := by
  unfold objectsRun at hrun
  rw [named_bind] at hrun
  obtain ⟨F, hF, hrun⟩ := hrun
  rw [named_bind] at hrun
  obtain ⟨g, _, hrun⟩ := hrun
  have e3 : (g.rows.toList.map seat.claim, seat.mark s (F.paid g.owedObjects)) = (cl, s') :=
    Except.ok.inj hrun
  obtain ⟨_, rfl⟩ := Prod.mk.inj e3
  exact mark_frame seat hmf hd hmark s F _ hF (OnBytes.PscRun.paid_later F _)

/-- **"guests"**: the record is handed back as it came. -/
theorem guests_frame (fork : T → Option Fork) (hd : T → Option Γ)
    (guests : List (Desc.First.Look.Guest T Cl)) (s s' : T) (cl : List Cl)
    (hrun : named "K3 guests: a guest refuses"
      ((guests.mapM fun (g : Desc.First.Look.Guest T Cl) => g.form s).map fun l => (l, s)) =
        .ok (cl, s')) : Frame fork hd s s' := by
  cases hm : guests.mapM fun (g : Desc.First.Look.Guest T Cl) => g.form s with
  | none =>
    rw [hm] at hrun
    cases hrun
  | some l =>
    rw [hm] at hrun
    have e : (l, s) = (cl, s') := Except.ok.inj hrun
    obtain ⟨_, rfl⟩ := Prod.mk.inj e
    exact Frame.refl fork hd s

theorem joinRun_reads (seat : Seat T Cl) (keys : T → Option (Array Aff)) {n : ℕ} {s s' : T}
    {cl : List Cl} (hrun : joinRun seat keys n s = .ok (cl, s')) :
    ∃ F g, seat.fork s = some F ∧ seat.heard s = some g := by
  unfold joinRun at hrun
  rw [named_bind] at hrun
  obtain ⟨F, hF, hrun⟩ := hrun
  rw [named_bind] at hrun
  obtain ⟨g, hg, _⟩ := hrun
  exact ⟨F, g, hF, hg⟩

/-- **"join".** -/
theorem join_frame (seat : Seat T Cl)
    (hmf : ∀ s F G, seat.fork s = some F → seat.fork (seat.mark s G) = some G)
    (hd : T → Option Γ) (hmark : ∀ s F G, seat.fork s = some F → hd (seat.mark s G) = hd s)
    (keys : T → Option (Array Aff)) (n : ℕ) (s s' : T) (cl : List Cl)
    (hrun : joinRun seat keys n s = .ok (cl, s')) : Frame seat.fork hd s s' := by
  obtain ⟨F, g, hF, hg⟩ := joinRun_reads seat keys hrun
  obtain ⟨_, _, _, _, rfl⟩ := joinRun_cut seat keys hF hg hrun
  exact mark_frame seat hmf hd hmark s F _ hF (OnBytes.PscRun.paid_later F _)

theorem planesRun_reads (seat : Seat T Cl) (lm : ℕ) (readers : Readers T) {n : ℕ} {s s' : T}
    {cl : List Cl} (hrun : planesRun seat lm readers n s = .ok (cl, s')) :
    ∃ F g, seat.fork s = some F ∧ seat.heard s = some g := by
  unfold planesRun at hrun
  rw [named_bind] at hrun
  obtain ⟨F, hF, hrun⟩ := hrun
  rw [named_bind] at hrun
  obtain ⟨g, hg, _⟩ := hrun
  exact ⟨F, g, hF, hg⟩

/-- "planes" lays, by the seat's mark, a ledger that is later than the one in front. The proof is
that of planes_later (Johnson/Top/H/K3LedgerKeeps.lean) less what its last line takes from a law on
the seat. -/
theorem planes_marks (seat : Seat T Cl) (lm : ℕ) (readers : Readers T) {n : ℕ} {s s' : T}
    {cl : List Cl} {F : Fork} {g : Forest.Heard} (hf : seat.fork s = some F)
    (hg : seat.heard s = some g) (hrun : planesRun seat lm readers n s = .ok (cl, s')) :
    ∃ G, s' = seat.mark s G ∧ OnBytes.PscRun.Later F G := by
  obtain ⟨r, rows, G, u, _, h1, _, rfl⟩ := planesRun_cut seat lm readers hf hg hrun
  obtain ⟨_, row, p', h2, _⟩ := Fo.Tp.planeClaims_run g lm _ _ (fun _ _ => quiet_need _)
    (fun _ => quiet_need _) F G [] u rows h1
  obtain ⟨-, -, -, -, -, hG, -, -⟩ := Fo.Tp.pscRow_ok _ _ _ _ _ _ _ _ _ h2
  exact ⟨_, rfl, (OnBytes.PscRun.hideRun_keeps hG).trans (OnBytes.PscRun.paid_later G _)⟩

/-- **"planes".** -/
theorem planes_frame (seat : Seat T Cl)
    (hmf : ∀ s F G, seat.fork s = some F → seat.fork (seat.mark s G) = some G)
    (hd : T → Option Γ) (hmark : ∀ s F G, seat.fork s = some F → hd (seat.mark s G) = hd s)
    (lm : ℕ) (readers : Readers T) (n : ℕ) (s s' : T) (cl : List Cl)
    (hrun : planesRun seat lm readers n s = .ok (cl, s')) : Frame seat.fork hd s s' := by
  obtain ⟨F, g, hF, hg⟩ := planesRun_reads seat lm readers hrun
  obtain ⟨G, rfl, l0⟩ := planes_marks seat lm readers hF hg hrun
  exact mark_frame seat hmf hd hmark s F G hF l0

/-- **Every run of claims in K3.block's own list.** -/
theorem block_runs_frame (seat : Seat T Cl)
    (hmf : ∀ s F G, seat.fork s = some F → seat.fork (seat.mark s G) = some G)
    (hd : T → Option Γ) (hmark : ∀ s F G, seat.fork s = some F → hd (seat.mark s G) = hd s)
    (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest T Cl)) :
    ∀ c ∈ (Desc.K3.block seat piece laid before p guests).claims, ∀ n s cl s',
      c.2 n s = .ok (cl, s') → Frame seat.fork hd s s' := by
  intro c hc n s cl s' hrun
  have hc' : c ∈ [("objects", objectsRun seat),
      ("guests", fun (_ : ℕ) (s : T) => named "K3 guests: a guest refuses"
        ((guests.mapM fun (g : Desc.First.Look.Guest T Cl) => g.form s).map fun l => (l, s)))] := hc
  rcases List.mem_cons.mp hc' with rfl | h2
  · exact objects_frame seat hmf hd hmark n s s' cl hrun
  · rw [List.mem_singleton] at h2
    subst h2
    exact guests_frame seat.fork hd guests s s' cl hrun

/-- K3.block has no run behind the batching. -/
theorem block_after_nil (seat : Seat T Cl) (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
    (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest T Cl)) :
    (Desc.K3.block seat piece laid before p guests).after = [] := rfl

end Seat

/-! ## At the two seats of a proof file's link, for both readings of "heard" -/

section AtS
variable {Cl : Type}

/-- The digits' reading of "heard". -/
abbrev tlHeard (s : S) : Option Forest.Heard := s.tl?.bind (·.heard)

theorem calls_decide_calls (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (s s' : S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (h : (Desc.K3.block (seatCalls claim) piece laid before p guests).decide s rs cols = .ok s') :
    Frame S.fork? S.lookHeard? s s' :=
  decide_frame_own (seatCalls claim) piece laid before p guests (seatCalls_keeps claim) s s' rs
    cols h

theorem calls_decide_digits (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (s s' : S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (h : (Desc.K3.block (seatCalls claim) piece laid before p guests).decide s rs cols = .ok s') :
    Frame S.fork? tlHeard s s' :=
  decide_frame (seatCalls claim) piece laid before p guests (seatCalls_keeps claim) tlHeard
    (fun s g G _ _ hx => (calls_keeps_digits claim claim s g G).trans hx) s s' rs cols h

theorem digits_decide_digits (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (s s' : S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (h : (Desc.K3.block (seatDigits claim) piece laid before p guests).decide s rs cols = .ok s') :
    Frame S.fork? tlHeard s s' :=
  decide_frame_own (seatDigits claim) piece laid before p guests (seatDigits_keeps claim) s s' rs
    cols h

theorem digits_decide_calls (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (s s' : S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (h : (Desc.K3.block (seatDigits claim) piece laid before p guests).decide s rs cols = .ok s') :
    Frame S.fork? S.lookHeard? s s' :=
  decide_frame (seatDigits claim) piece laid before p guests (seatDigits_keeps claim) S.lookHeard?
    (fun s g G _ _ hx => (digits_keeps_calls claim claim s g G).trans hx) s s' rs cols h

/-- At either seat the mark is putFork, which leaves both readings. -/
theorem mark_calls (claim : Aff → Cl) (s : S) (F G : Fork) (_ : S.fork? s = some F) :
    S.lookHeard? (s.putFork G) = S.lookHeard? s := mark_keeps_calls claim s G

theorem mark_digits (claim : Aff → Cl) (s : S) (F G : Fork) (_ : S.fork? s = some F) :
    tlHeard (s.putFork G) = tlHeard s := mark_keeps_digits claim s G

end AtS

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.grows_lkPad
#print axioms VerifiableInference.OnPublicFiles.decide_frame
#print axioms VerifiableInference.OnPublicFiles.block_runs_frame
#print axioms VerifiableInference.OnPublicFiles.join_frame
#print axioms VerifiableInference.OnPublicFiles.planes_frame
#print axioms VerifiableInference.OnPublicFiles.calls_decide_digits
#print axioms VerifiableInference.OnPublicFiles.digits_decide_calls
