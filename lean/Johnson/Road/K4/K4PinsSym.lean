-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsSym.lean: TWO READINGS OF THE COMMITTED SYMBOLS OFF ONE WITNESS ARE ONE, UNDER
A CONDITION ON PUBLIC LETTERS ALONE. The one: the reading of the caller of the lookup on a link's
calls (`symAt`, Johnson/Desc/First/Look/K3CallerAtt.lean: through `seatCalls` over `sigListCalls`),
at the tuple out of the pinned part (Johnson/Road/K4/K4PinsRead.lean): of it K4's value's matrices
are made. The other: `Meaning.symAt` (Johnson/Goal/Meaning/HidSeat.lean: by the message's number,
its main row and its place), at the messages as a segment reads them (`readAt`,
Johnson/Desc/Sound/ReadAt.lean): of it "what the prover hides" is made. Definitions and theorems, by
unfolding. No draw, no count.

  `readAt_tuple`: what the tuple out of a pinned part holds at a seat that lies in a main table: the
    entry of the table at the member's seat.
  `symU`: the caller's symbol at matrix μ, row of symbols r, column c, these three as plain numbers.
  `SymsOne A tl arr N k sz seat'`: **THE CONDITION, ON PUBLIC LETTERS ALONE**: at every matrix μ,
    row of symbols r and column c of the sizes sz: `seatCalls` FINDS a seat for the cell (r, c) of
    the array that tl names for μ; the seat lies in a main table of the caller's list; its row and
    place are those that seat' μ r c names; and THE tenant that `readAt` finds in segment k's group
    for the number that seat' μ r c names IS the seat of that member of the caller's list. "There
    is" on both sides: no side may be silent.
  **`sym_one`**: under `SitsIn` and `SymsOne`: `symU` at the pinned part of a witness w is
    `Meaning.symAt sz seat' (readAt … k w)`, at every μ, r, c of the sizes.
  `not_symsOne_of_nil`: THE CONDITION CAN FAIL: where the caller's list is empty (a link that the
    request has not) and the sizes have one symbol, it is false. (`SitsIn` holds there for nothing.)

OBJECT: none of its own. USER: Johnson/Road/K4/K4PinsIdn.lean. LETTERS, filled by nobody: every
field of `PinPlan`, tl, arr, ms, N, m, the segment k, the sizes sz, the seats seat'.

Limits. K04_law IS NOT PROVED BY THIS. `SymsOne` AND `SitsIn` ARE PREMISES: NEITHER HAS RUN AT A
PLAN. WHO COULD PAY `SymsOne`: a run on the plan: every clause compares public numbers. IT SPEAKS OF
EVERY SYMBOL: at the full size a walk over all of them is long: an array is laid in a few dozen
blocks (Johnson/Desc/First/Look/K3CallerLaid.lean has a test by blocks for "every address has a seat
that fits"): a test by blocks for the whole condition is written nowhere. It is no Bool here: each
clause is decidable, no decision procedure is laid. Nothing ties k, m and the caller's link. That sz
is the size that tl names (`szOf tl`) is not asked here.
-/
import Johnson.Road.K4.K4PinsRead
import Johnson.Desc.Sound.ReadAt
import Johnson.Goal.Meaning.HidSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4
open Johnson.Pack
open OnBytes.Model (HTailF2)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.Look (Sent sigListCalls seatCalls valAt finOf_some)
open VerifiableInference.Desc.Sound (Mem MsgT InMsg memTab seatTab)
open Cb.Pv.Tail (Size)

/-- What the tuple out of a pinned part holds at a seat that lies in a main table. -/
theorem readAt_tuple {Cells : Type} (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
    (seatT : Fin l.length → ℕ × ℕ) (t : PinM Cells) (s : VerifiableInference.Desc.First.Look.Seat)
    (hk : s.msg < l.length) (hm : s.mask = false) (hr : s.row < (l.get ⟨s.msg, hk⟩).1.mainRows)
    (hp : s.place < (pMain cs (l.get ⟨s.msg, hk⟩).1).ell) :
    VerifiableInference.Desc.First.Look.readAt cs l (tupleOf cs l seatT t) s =
      some (t.1 (seatT ⟨s.msg, hk⟩) false s.row s.place) := by
  unfold VerifiableInference.Desc.First.Look.readAt
  rw [dif_pos hk, if_neg (by rw [hm]; exact Bool.false_ne_true), finOf_some hr, finOf_some hp]
  rfl

variable {Cells : Type} (A : PinPlan Cells) (tl : HTailF2)

/-- The caller's symbol, at plain numbers. -/
def symU (t : PinM Cells) (μ r c : ℕ) : Cb.Gl.E :=
  (valAt A.D.codes (sigListCalls A.D A.rad A.link) (seatCalls A.D A.link) (A.tuple t)
    (.cell (tl.gtTree.getD μ 0) r c)).getD 0

/-- **The condition, on public letters alone.** -/
def SymsOne (arr : ℕ → ℕ → ℕ) (N : Numbers) (k : ℕ) (sz : Size)
    (seat' : Fin sz.NM → ℕ → ℕ → ℕ × ℕ × ℕ) : Prop :=
  ∀ (μ : Fin sz.NM) (r : Fin (Alg.symRows (sz.m μ))) (c : Fin (sz.k μ)),
    ∃ (s : VerifiableInference.Desc.First.Look.Seat)
      (hk : s.msg < (sigListCalls A.D A.rad A.link).length),
      seatCalls A.D A.link (.cell (tl.gtTree.getD μ.val 0) r.val c.val) = some s ∧
      s.mask = false ∧
      s.row < ((sigListCalls A.D A.rad A.link).get ⟨s.msg, hk⟩).1.mainRows ∧
      s.place < (pMain A.D.codes ((sigListCalls A.D A.rad A.link).get ⟨s.msg, hk⟩).1).ell ∧
      (seat' μ r.val c.val).2 = (s.row, s.place) ∧
      ((N.group k).find? fun x => arr x.1 x.2 == (seat' μ r.val c.val).1) =
        some (A.seatT ⟨s.msg, hk⟩)

variable {Tok : Type} (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers) (m k : ℕ) (sz : Size)
  (seat' : Fin sz.NM → ℕ → ℕ → ℕ × ℕ × ℕ)

/-- **The two readings of the committed symbols are one**, under `SitsIn` and `SymsOne`. -/
theorem sym_one (hs : SitsIn (sigListCalls A.D A.rad A.link) A.seatT ms N m)
    (h1 : SymsOne A tl arr N k sz seat') (w : Wit Cells Tok MsgT) (μ : Fin sz.NM)
    (r : Fin (Alg.symRows (sz.m μ))) (c : Fin (sz.k μ)) :
    symU A tl (partOf A.D.codes arr ms N m w) μ.val r.val c.val =
      Meaning.symAt sz seat' (VerifiableInference.Desc.Sound.readAt A.D.codes arr ms N k w) μ r
        c := by
  obtain ⟨s, hk, e1, hm, hr, hp, e2, e3⟩ := h1 μ r c
  obtain ⟨hx, u, hu, hsh⟩ := hs ⟨s.msg, hk⟩
  have hin : InMsg A.D.codes (u.1.l.get u.2).1 false s.row s.place := by
    rw [hsh]
    unfold InMsg
    rw [if_neg (by decide)]
    exact ⟨hr, hp⟩
  have L1 : symU A tl (partOf A.D.codes arr ms N m w) μ.val r.val c.val =
      memTab A.D.codes arr w u false s.row s.place := by
    unfold symU valAt
    rw [e1]
    show (VerifiableInference.Desc.First.Look.readAt A.D.codes _
      (tupleOf A.D.codes _ A.seatT (partOf A.D.codes arr ms N m w)) s).getD 0 = _
    rw [readAt_tuple A.D.codes _ A.seatT _ s hk hm hr hp, Option.getD_some,
      partOf_in A.D.codes arr ms N m w hx hu false s.row s.place hin]
  have R1 : Meaning.symAt sz seat' (VerifiableInference.Desc.Sound.readAt A.D.codes arr ms N k w)
      μ r c = memTab A.D.codes arr w u false s.row s.place := by
    show VerifiableInference.Desc.Sound.readAt A.D.codes arr ms N k w (seat' μ r.val c.val).1 false
      (seat' μ r.val c.val).2.1 (seat' μ r.val c.val).2.2 = _
    unfold VerifiableInference.Desc.Sound.readAt
    rw [e3, e2]
    show seatTab A.D.codes arr ms w (A.seatT ⟨s.msg, hk⟩) false s.row s.place = _
    unfold seatTab
    rw [show (ms.find? fun y => decide (VerifiableInference.Desc.Sound.seatOf y =
      A.seatT ⟨s.msg, hk⟩)) = some u from hu]
  rw [L1, R1]

/-- **The condition can fail**: at an empty list, where the sizes have a symbol. -/
theorem not_symsOne_of_nil (h : (sigListCalls A.D A.rad A.link).length = 0) (μ : Fin sz.NM)
    (r : Fin (Alg.symRows (sz.m μ))) (c : Fin (sz.k μ)) : ¬ SymsOne A tl arr N k sz seat' :=
  fun H => by
    obtain ⟨s, hk, _⟩ := H μ r c
    omega

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.readAt_tuple
#print axioms OnBytes.Road.K4.sym_one
#print axioms OnBytes.Road.K4.not_symsOne_of_nil
