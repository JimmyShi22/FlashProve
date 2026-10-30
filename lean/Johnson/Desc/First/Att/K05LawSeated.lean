-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05LawSeated.lean: KIND K5's LAW IN ONE STATEMENT AT A BLOCK THAT REFUSES
MORE THAN k5AtN's: at the form in which a description seats the kind's block: behind a guard on
marks, under a name and a place, behind a guard on the reply's seat.

Why. K05_law_one_guard (Att/K05LawGuard.lean) speaks of blk, what k5AtN returns. A description does
not seat blk: it seats blk inside wrappers that say yes only where blk does, with the same record.
The rule of composition has one rule for all such wrappers (goodIn_narrow,
Johnson/Desc/Sound/MergeNarrow.lean): a block that refuses more owes no
more, and what its yes adds may be promised behind it. Here that rule is called at K5's law.

Main names:
  `narrows_of_underR`: the one bridge: the library's Block.UnderR
    (Johnson/Desc/Sound/SeatGuardChain.lean) is the rule's Block.Narrows. That file's guarded_underR
    and Block.UnderR.trans are called, not typed anew.
  `markGuard b`, `marked_underR`: b with a refusal behind its decide where the record bears a mark;
    it stands under b, and every record that it returns bears no mark (`marked_clean`).
  `K05_law_one_narrow`: **the law at every block B' that narrows blk**, with what B''s yes gives of
    the record (G) added to the promise behind. `K05_law_one_under`: the same from B'.UnderR blk.
  `seatedN`, `K05_law_one_seated`: the law at Block.guarded same but { markGuard { blk with planOk
    := ok' } with name := n, place := pc }, with "no mark" behind.
THE FORM seatedN IS BY READING: it is what the text that makes the proof file's description lays at
an attention link's third hearing place, as read at file and line;
its guard on marks is written out here (markGuard) and
that text's own constant is not named. That a description's entry IS seatedN … at these letters is
not shown here. ONE WAY ONLY: a law of the guarded block says nothing of the bare one. The rule
makes no block complete: a guard that refuses an honest run passes it as any other. All that
Att/K05LawGuard.lean's head says of what is left, of D and rad, and of emptiness holds here.
No soundness of the protocol is claimed: the premises named are not shown.
Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.First.Att.K05LawGuard
import Johnson.Desc.Sound.MergeNarrow
import Johnson.Desc.Sound.SeatGuardChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc

variable {S Cl : Type}

/-- **The one bridge**: the library's "b' has b's rounds, and where b' says yes b says the same yes"
(Block.UnderR, Johnson/Desc/Sound/SeatGuardChain.lean) is the rule of composition's Block.Narrows.
-/
theorem narrows_of_underR {b' b : Block S Cl} (h : b'.UnderR b) : b'.Narrows b := ⟨h.1, h.2⟩

end VerifiableInference.Desc

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel
open VerifiableInference.Desc.First.Look (Sent attCaller attSg JAtt AttOK enMask lookAt)
open VerifiableInference.Desc.Sound (Frame Piece goodIn_narrow bind_narrows)
open VerifiableInference.Desc (Claim RoundAsG Block Place narrows_of_underR guarded_underR)

/-- A block with a refusal behind its decide where the record bears a mark. To the letter the text
of
guardMark in Frames1.lean (lines 53 to 58 of the text that was read), which a
file
of the library cannot import. -/
def markGuard {Cl : Type} (b : Block First.S Cl) : Block First.S Cl :=
  { b with decide := fun s rs gs =>
      (b.decide s rs gs).bind fun t =>
        match t.failed with
        | none => .ok t
        | some m => .error ("marked: " ++ m) }

theorem marked_underR {Cl : Type} (b : Block First.S Cl) : (markGuard b).UnderR b :=
  have h := bind_narrows b (fun _ t => match t.failed with
    | none => .ok t
    | some m => .error ("marked: " ++ m)) (by
      intro _ t t' h
      dsimp only at h
      cases hf : t.failed with
      | none => rw [hf] at h; exact (Except.ok.inj h).symm
      | some m => rw [hf] at h; cases h)
  ⟨h.1, h.2⟩

/-- Every record that it returns bears no mark. -/
theorem marked_clean {Cl : Type} (b : Block First.S Cl) (s : First.S) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (s' : First.S)
    (h : (markGuard b).decide s rs gs = .ok s') : s'.failed = none := by
  have h' : ((b.decide s rs gs).bind fun t =>
      match t.failed with
      | none => .ok t
      | some m => .error ("marked: " ++ m)) = .ok s' := h
  cases hd : b.decide s rs gs with
  | error w => rw [hd] at h'; cases h'
  | ok t =>
    rw [hd] at h'
    have h'' : (match t.failed with
      | none => (.ok t : Except String First.S)
      | some m => .error ("marked: " ++ m)) = .ok s' := h'
    cases hf : t.failed with
    | none =>
      rw [hf] at h''
      rw [← Except.ok.inj h'']
      exact hf
    | some m => rw [hf] at h''; cases h''

open Classical in
/-- **THE LAW AT EVERY BLOCK THAT NARROWS blk.** -/
theorem K05_law_one_narrow {W Cl : Type} {Fr : Frame} (claim : Aff → Cl) {Wv : Verify.Public}
    (hP : PlanIs Wv) (h4 : Wv.p4 = true) (g : ℕ) (before : List (ℕ × ℕ))
    (blk : VerifiableInference.Desc.Block First.S Claim)
    (hblk : k5AtN Wv (2 * g + 1) g before = some blk) (hok : blk.planOk = true)
    (hG : k5GuardN Wv (2 * g + 1) g = true) {a : Attention.Plan} (ha : Wv.A[g]? = some a)
    {x : VerifiableInference.Desc.First.Look.Place} (hx : lookAt Wv (2 * g + 1) false = some x) (D : Sent)
    (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
    (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)) → Cb.Gl.E) (ns base : ℕ)
    (ds : List RDT) (hds : List.Forall₂ RoundAsG ds (rounds (parO Wv (2 * g + 1) a before)))
    (tj : OnBytes.K.Kc.Tape)
    (x0 : First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)))
    (yOf : First.S × Fr.E.Str → Ex.Str) (gOf : First.S × Fr.E.Str → Forest.Heard)
    (pl : ℕ → ℕ → JAtt x.ns a.seam.tl) (on : First.S × Fr.E.Str → Prop)
    (I : PinItemP Fr seatSO base W (attSg x D rad).Msg) (Rd : Rides Fr base)
    (R' : First.S × Fr.E.Str → W → Prop)
    (On : K5AtOn x a.seam.tl D rad claim (parO Wv (2 * g + 1) a before) ns base x0 gOf pl on I Rd)
    (Bh : K5Behind x a.seam.tl D rad Ex Wp α a (parO Wv (2 * g + 1) a before) ns base a.nW (plannedK a)
      (padOfO a.fs) tj gOf on I R')
    (B' : Block First.S Claim) (hN : B'.Narrows blk) (G : First.S → Prop)
    (hGd : ∀ s rs gs s', B'.decide s rs gs = .ok s' → G s') :
    (⟨B', base, ds, [], fun _ _ w => w, Err.cap 128 (uLT (ckP .two) ds)⟩ :
        Piece (ckP .two) Fr First.S Claim W).GoodIn
      on (fun b => (LaidBehind Fr seatSO (parO Wv (2 * g + 1) a before) base on b ∧ Rd.q (Rd.rq b.1) b.2) ∧
        G b.1)
      (fun a' w => ((closedOf (attBase x a.S a.seam.tl D rad)
          (attLin x a.S a.seam.tl D rad Ex Wp α ns
            (numsPlan (parO Wv (2 * g + 1) a before).own (x.F.next + Forest.elems x.fs))) ns
          (numsPlan (parO Wv (2 * g + 1) a before).own (x.F.next + Forest.elems x.fs))).own
          (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a') (I.part w)) R' :=
  goodIn_narrow ⟨blk, base, ds, [], fun _ _ w => w, Err.cap 128 (uLT (ckP .two) ds)⟩ B' hN G hGd _ _
    _ _ (K05_law_one_guard claim hP h4 g before blk hblk hok hG ha hx D rad Ex Wp α ns base ds hds tj x0 yOf gOf pl on I Rd R' On Bh)

open Classical in
/-- **The same from the library's relation.** -/
theorem K05_law_one_under {W Cl : Type} {Fr : Frame} (claim : Aff → Cl) {Wv : Verify.Public}
    (hP : PlanIs Wv) (h4 : Wv.p4 = true) (g : ℕ) (before : List (ℕ × ℕ))
    (blk : VerifiableInference.Desc.Block First.S Claim)
    (hblk : k5AtN Wv (2 * g + 1) g before = some blk) (hok : blk.planOk = true)
    (hG : k5GuardN Wv (2 * g + 1) g = true) {a : Attention.Plan} (ha : Wv.A[g]? = some a)
    {x : VerifiableInference.Desc.First.Look.Place} (hx : lookAt Wv (2 * g + 1) false = some x) (D : Sent)
    (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
    (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)) → Cb.Gl.E) (ns base : ℕ)
    (ds : List RDT) (hds : List.Forall₂ RoundAsG ds (rounds (parO Wv (2 * g + 1) a before)))
    (tj : OnBytes.K.Kc.Tape)
    (x0 : First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)))
    (yOf : First.S × Fr.E.Str → Ex.Str) (gOf : First.S × Fr.E.Str → Forest.Heard)
    (pl : ℕ → ℕ → JAtt x.ns a.seam.tl) (on : First.S × Fr.E.Str → Prop)
    (I : PinItemP Fr seatSO base W (attSg x D rad).Msg) (Rd : Rides Fr base)
    (R' : First.S × Fr.E.Str → W → Prop)
    (On : K5AtOn x a.seam.tl D rad claim (parO Wv (2 * g + 1) a before) ns base x0 gOf pl on I Rd)
    (Bh : K5Behind x a.seam.tl D rad Ex Wp α a (parO Wv (2 * g + 1) a before) ns base a.nW (plannedK a)
      (padOfO a.fs) tj gOf on I R')
    (B' : Block First.S Claim) (hU : B'.UnderR blk) (G : First.S → Prop)
    (hGd : ∀ s rs gs s', B'.decide s rs gs = .ok s' → G s') :
    (⟨B', base, ds, [], fun _ _ w => w, Err.cap 128 (uLT (ckP .two) ds)⟩ :
        Piece (ckP .two) Fr First.S Claim W).GoodIn
      on (fun b => (LaidBehind Fr seatSO (parO Wv (2 * g + 1) a before) base on b ∧ Rd.q (Rd.rq b.1) b.2) ∧
        G b.1)
      (fun a' w => ((closedOf (attBase x a.S a.seam.tl D rad)
          (attLin x a.S a.seam.tl D rad Ex Wp α ns
            (numsPlan (parO Wv (2 * g + 1) a before).own (x.F.next + Forest.elems x.fs))) ns
          (numsPlan (parO Wv (2 * g + 1) a before).own (x.F.next + Forest.elems x.fs))).own
          (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a') (I.part w)) R' :=
  K05_law_one_narrow claim hP h4 g before blk hblk hok hG ha hx D rad Ex Wp α ns base ds hds tj x0 yOf
    gOf pl on I Rd R' On Bh B' (narrows_of_underR hU) G hGd

/-- The form in which a description seats the kind's block, by reading. -/
def seatedN (same : First.S → First.S → Bool) (but : Place → Bool) (n : String) (pc : Place)
    (ok' : Bool) (blk : Block First.S Claim) : Block First.S Claim :=
  Block.guarded same but { markGuard { blk with planOk := ok' } with name := n, place := pc }

theorem seatedN_underR (same : First.S → First.S → Bool) (but : Place → Bool) (n : String)
    (pc : Place) (ok' : Bool) (blk : Block First.S Claim) :
    (seatedN same but n pc ok' blk).UnderR blk :=
  (guarded_underR same but _).trans
    (Block.UnderR.trans (b := markGuard { blk with planOk := ok' }) ⟨rfl, fun _ _ _ _ e => e⟩
      ((marked_underR _).trans ⟨rfl, fun _ _ _ _ e => e⟩))

theorem seatedN_clean (same : First.S → First.S → Bool) (but : Place → Bool) (n : String)
    (pc : Place) (ok' : Bool) (blk : Block First.S Claim) (s : First.S) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (s' : First.S)
    (h : (seatedN same but n pc ok' blk).decide s rs gs = .ok s') : s'.failed = none :=
  marked_clean { blk with planOk := ok' } s rs gs s'
    ((guarded_underR same but
      { markGuard { blk with planOk := ok' } with name := n, place := pc }).2 s rs gs s' h)

open Classical in
/-- **THE LAW AT THE SEATED FORM**, with "no mark" behind. -/
theorem K05_law_one_seated {W Cl : Type} {Fr : Frame} (claim : Aff → Cl) {Wv : Verify.Public}
    (hP : PlanIs Wv) (h4 : Wv.p4 = true) (g : ℕ) (before : List (ℕ × ℕ))
    (blk : VerifiableInference.Desc.Block First.S Claim)
    (hblk : k5AtN Wv (2 * g + 1) g before = some blk) (hok : blk.planOk = true)
    (hG : k5GuardN Wv (2 * g + 1) g = true) {a : Attention.Plan} (ha : Wv.A[g]? = some a)
    {x : VerifiableInference.Desc.First.Look.Place} (hx : lookAt Wv (2 * g + 1) false = some x) (D : Sent)
    (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
    (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)) → Cb.Gl.E) (ns base : ℕ)
    (ds : List RDT) (hds : List.Forall₂ RoundAsG ds (rounds (parO Wv (2 * g + 1) a before)))
    (tj : OnBytes.K.Kc.Tape)
    (x0 : First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)))
    (yOf : First.S × Fr.E.Str → Ex.Str) (gOf : First.S × Fr.E.Str → Forest.Heard)
    (pl : ℕ → ℕ → JAtt x.ns a.seam.tl) (on : First.S × Fr.E.Str → Prop)
    (I : PinItemP Fr seatSO base W (attSg x D rad).Msg) (Rd : Rides Fr base)
    (R' : First.S × Fr.E.Str → W → Prop)
    (On : K5AtOn x a.seam.tl D rad claim (parO Wv (2 * g + 1) a before) ns base x0 gOf pl on I Rd)
    (Bh : K5Behind x a.seam.tl D rad Ex Wp α a (parO Wv (2 * g + 1) a before) ns base a.nW (plannedK a)
      (padOfO a.fs) tj gOf on I R')
    (same : First.S → First.S → Bool) (but : Place → Bool) (n : String) (pc : Place) (ok' : Bool) :
    (⟨seatedN same but n pc ok' blk, base, ds, [], fun _ _ w => w,
        Err.cap 128 (uLT (ckP .two) ds)⟩ : Piece (ckP .two) Fr First.S Claim W).GoodIn
      on (fun b => (LaidBehind Fr seatSO (parO Wv (2 * g + 1) a before) base on b ∧ Rd.q (Rd.rq b.1) b.2) ∧
        b.1.failed = none)
      (fun a' w => ((closedOf (attBase x a.S a.seam.tl D rad)
          (attLin x a.S a.seam.tl D rad Ex Wp α ns
            (numsPlan (parO Wv (2 * g + 1) a before).own (x.F.next + Forest.elems x.fs))) ns
          (numsPlan (parO Wv (2 * g + 1) a before).own (x.F.next + Forest.elems x.fs))).own
          (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a') (I.part w)) R' :=
  K05_law_one_under claim hP h4 g before blk hblk hok hG ha hx D rad Ex Wp α ns base ds hds tj x0 yOf gOf pl on I Rd R' On Bh _ (seatedN_underR same but n pc ok' blk)
    (fun s => s.failed = none) (seatedN_clean same but n pc ok' blk)

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.narrows_of_underR
#print axioms VerifiableInference.Desc.First.Att.P.marked_underR
#print axioms VerifiableInference.Desc.First.Att.P.marked_clean
#print axioms VerifiableInference.Desc.First.Att.P.K05_law_one_narrow
#print axioms VerifiableInference.Desc.First.Att.P.K05_law_one_under
#print axioms VerifiableInference.Desc.First.Att.P.seatedN_underR
#print axioms VerifiableInference.Desc.First.Att.P.seatedN_clean
#print axioms VerifiableInference.Desc.First.Att.P.K05_law_one_seated
