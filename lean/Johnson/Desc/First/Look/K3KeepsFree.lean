-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3KeepsFree.lean: THE KIND "LOOKUP" (K3) HANDS "FREE ABOVE" ON: from a
ledger that has its sizes and in which nothing at or above the next slot is filled, a yes of the
kind's decide leaves a ledger of which the same holds. Statements and proofs. And so AT THE OUTPUT
HEAD's LINK's LOOKUP ON THE CALLS: the end theorem with "free above" beside "what the lookup left".

Why. The table of joints' public item "freeAbove m" (Johnson/Desc/First/Borders.lean: every slot
from the ledger's next free number on is free) is made in front of the lookup on the calls and asked
behind it. The table books it as KEPT past the lookup. But the lookup TURNS the ledger: so it does
not ride by "the record is as it was but for …": it wants a law of the kind. "No block makes room:
each hands it on."

  PadExact.freeAbove: by which slots are filled behind a hearing (PadExact,
    Johnson/Top/H/Keep/PadExact.lean): those that were, and some of the lookup's own, all below the
    new next slot.
  decide_freeAbove: of K3.block's decide, AT EVERY SEAT at which the ledger that the hearing lays is
    the one that is read (SeatKeeps).
  FreeAt fork s: the record's ledger is there, has its sizes, and is free above its next slot.
  via_freeAt: of K3.Law.blockVia's decide at the calls' seat, where its test on the plan says yes:
    FreeAt in front gives FreeAt behind.
  leftAt_freeAt: A SECOND ROAD, off the sharp promise alone: K3LeftAt at Q := "free above" gives
    FreeAt of the same record: by two fields of the library's PadLeft.
  leftAt_cEnd: what K3LeftAt says of the form left for the join: it names no entry of a virtual row;
    its slots are filled in the ledger in hand and lie below the number of slots.
  k3_head_free_at: k3_head_left_at (Johnson/Desc/First/Look/K3HeadLeft.lean) at I, I' := FreeAt AND
    AT THE TOKEN's READER FILLED (tok := the record's replyTok?): two premises fewer (hTok, hKeep).

Limits. Marks alone: nothing on what lies under a slot. That the table's item is filled with FreeAt
(or with a Bool that gives it) is nobody's yet: the walk's own Bool reads the slots below the
ledger's number of slots alone; FreeAbove speaks of all numbers; under "has its sizes" the two are
meant to be one: not shown here. Those of K3HeadLeft.lean.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3HeadLeft
import Johnson.Top.H.Keep.PadExact
import Johnson.Top.H.K3SeatFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Fo.Tp
open OnBytes OnBytes.Model OnBytes.PscRun

/-- **Behind a hearing nothing at or above the new next slot is filled**, where nothing at or above
the old one was. -/
theorem PadExact.freeAbove {h : Forest.Shape} {F F' : Fork} {g : Forest.Heard}
    (P : PadExact h F F' g) (hA : FreeAbove F) : FreeAbove F' := fun j hj hf => by
  rw [P.next] at hj
  exact ((P.marks j).1 hf).elim (hA j (by omega)) fun y => absurd y.2.1 (by omega)

end Fo.Tp

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open OnBytes.PscRun (Sized FreeAbove)
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Kinds.Head.Law (HeadAdr headLay headRider HeadOK head_says)

/-- **The kind's decide hands "free above" on.** -/
theorem decide_freeAbove {S Cl : Type} (seat : Desc.K3.Seat S Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (hk : SeatKeeps seat) {s s' : S} {rs : List Fmt.RoundView} {cols : List (List (ℕ × List UInt64))}
    {F : Fork} (hF : seat.fork s = some F) (hS : Sized F) (hA : FreeAbove F)
    (hd : (Desc.K3.block seat piece laid before p guests).decide s rs cols = .ok s') :
    ∃ F', seat.fork s' = some F' ∧ Sized F' ∧ FreeAbove F' := by
  obtain ⟨F1, x, e1, hn, rfl, hE⟩ := decide_exact seat piece laid before p guests s s' rs cols hd
  obtain rfl : F = F1 := Option.some.inj (hF.symm.trans e1)
  obtain ⟨E, hL⟩ := hE hS
  have hsome : (seat.fork s).isSome = true := by rw [hF]; rfl
  exact ⟨x.2, hk s x.1 x.2 hsome hn, hL.sized hS, E.freeAbove hA⟩

/-- The record's ledger is there, has its sizes, and is free above its next slot. -/
def FreeAt {S : Type} (fork : S → Option Fork) (s : S) : Prop :=
  ∃ F, fork s = some F ∧ Sized F ∧ FreeAbove F

/-- **At the block with the hearing exchanged, at the calls' seat.** -/
theorem via_freeAt {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (P : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
    (hplan : (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) piece laid before P guests).planOk =
      true)
    (s : Desc.First.S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (s' : Desc.First.S)
    (h : (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) piece laid before P guests).decide s rs
      cols = .ok s') (hI : FreeAt (Desc.K3.seatCalls claim).fork s) :
    FreeAt (Desc.K3.seatCalls claim).fork s' := by
  obtain ⟨F, hF, hS, hA⟩ := hI
  exact decide_freeAbove (Desc.K3.seatCalls claim) piece laid before P guests
    (seatCalls_keeps claim) hF hS hA (Desc.K3.Law.blockVia_decide hplan h)

/-- **A second road, off the sharp promise alone** (a reader's pointer): what the lookup left, at Q
:= "free above", holds that the ledger in hand has its sizes and is free above: by two fields of the
library's PadLeft (next; beyond). -/
theorem leftAt_freeAt {S : Type} (fork : S → Option Fork) (heard : S → Option Forest.Heard)
    (h : Forest.Shape) (lm first : ℕ) (s : S) (hL : K3LeftAt fork heard h lm first FreeAbove s) :
    FreeAt fork s := by
  obtain ⟨F, F', g, rs, hA, -, hK, -, hF'⟩ := hL
  refine ⟨F', hF', hK.padLeft.fit, fun j hj hf => ?_⟩
  rw [hK.padLeft.next] at hj
  exact hA j (by omega) ((hK.padLeft.beyond j hj).1 hf)

/-- **What the sharp promise says of the form left for the join**: every slot that it names is
filled in the ledger in hand and lies below the number of slots. -/
theorem leftAt_cEnd {S : Type} (fork : S → Option Fork) (heard : S → Option Forest.Heard)
    (h : Forest.Shape) (lm first : ℕ) (Q : Fork → Prop) (s : S)
    (hL : K3LeftAt fork heard h lm first Q s) :
    ∃ F' g, fork s = some F' ∧ heard s = some g ∧ g.cEnd.ents = #[] ∧ FilledA F' g.cEnd := by
  obtain ⟨F, F', g, rs, -, -, hK, hg, hF'⟩ := hL
  exact ⟨F', g, hF', hg, hK.cEndEnts, hK.cEndFilled⟩

variable [Desc.Kinds.Head.Sizes] [Desc.Kinds.Head.Policy] [Desc.Kinds.Head.Request]

section
variable {Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  {X : Verify.Public} {adr : HeadAdr} {x : Desc.First.Look.Place} {tl : HTailF2}
  {D : Desc.First.Look.Sent} {rad : OracleShape → ℕ} {oW : Cb.OMsg Cb.Gl.E}
  {wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E} {nr nc floor : ℕ}
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
    Option ((attSg x D rad).om i).Smp)
  (smpW : Desc.First.S → Option oW.Smp) (strW : Fr.E.Str → oW.Str)
  (msgW : Desc.Wit Cells Tok MsgT → oW.Msg) (Q : Fork → Prop)

local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x

/-- **THE END THEOREM AT THE HEAD's LINK OF A PUBLIC RECORD, WITH WHAT THE LOOKUP LEFT AND "FREE
ABOVE" BESIDE.** THE TOKEN's READER IS FILLED: the record's own replyTok?: so hTok is no premise
here (k3_head_tok pays it), and hKeep none (via_freeAt). -/
theorem k3_head_free_at (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S))
    (codes : Codes) (shape : Params.ReqShape) (a : Desc.Place)
    (B B' : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (hN : B'.Narrows B)
    (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)) (hp : p.b = below B')
    (hx : Desc.Kinds.Head.Law.headAt X = some x)
    (hl : a.link = some (headLink X)) (hpc : a.piece = Desc.K3.pieceAt X (headLink X) false)
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w)
    (hB : Desc.Kinds.Head.Law.headB floor x.fs = true)
    (hpl : (Forest.planeCols x.fs x.lm).toBool = true)
    (hr : (theP).entries.isSome = true) (hR : List.Forall₂ SameAs p.ds (theP).rounds)
    (hcap : p.err = Err.cap 128 (uLT (ckP .two) p.ds))
    (hsmp : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent theP
      []).planOk = true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece
      laid sent theP []).decide s rs cols = .ok s' → smp s' = smp s)
    (hsmpW : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent theP
      []).planOk = true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece
      laid sent theP []).decide s rs cols = .ok s' → smpW s' = smpW s)
    (hstrW : ∀ y (τ : Tr (uLT (ckP .two) p.ds)),
      strW (behind (ckP .two) Fr p.base p.ds y τ) = strW y)
    (hseat : ∀ i, (seatT i).1 < p.base) (σ₀ : (attSg x D rad).Smp) (σW₀ : oW.Smp) :
    p.GoodIn
      (HeadOnQ G x D rad oW seatT smp smpW strW (·.replyTok?) (Desc.K3.seatCalls claim).fork
        (OwnIs D x.link) Q (FreeAt (Desc.K3.seatCalls claim).fork))
      (HeadOnQ' G x D rad oW seatT smp smpW strW (·.replyTok?) (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard (OwnIs D x.link) Q
        (FreeAt (Desc.K3.seatCalls claim).fork))
      (HeadFront G adr x tl D rad oW wOf nr nc seatT arr smp smpW strW msgW
        fun s => s.replyTok?.getD 0)
      (HeadBehind G adr x tl D rad oW wOf nr nc seatT arr smp smpW strW msgW
        (fun s => s.replyTok?.getD 0) (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard) :=
  k3_head_left_at (floor := floor) G seatT arr smp smpW strW msgW (·.replyTok?) Q _ _ claim readers
    codes shape a B B' h hOk hN p hp hx hl hpc hback hext hB hpl hr hR hcap hsmp hsmpW
    (fun sent laid hplan s rs cols s' hd =>
      k3_head_tok claim a.piece laid sent theP [] hplan s s' rs cols hd)
    (fun sent laid hplan s rs cols s' hd =>
      via_freeAt claim a.piece laid sent theP [] hplan s rs cols s' hd)
    hstrW hseat σ₀ σW₀

end

end VerifiableInference.OnPublicFiles

#print axioms Fo.Tp.PadExact.freeAbove
#print axioms VerifiableInference.OnPublicFiles.decide_freeAbove
#print axioms VerifiableInference.OnPublicFiles.via_freeAt
#print axioms VerifiableInference.OnPublicFiles.leftAt_freeAt
#print axioms VerifiableInference.OnPublicFiles.leftAt_cEnd
#print axioms VerifiableInference.OnPublicFiles.k3_head_free_at
