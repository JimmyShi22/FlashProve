-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/SitsLaw.lean: THE LAW OF THE CODE SWITCH AT A SEATED BLOCK AS ONE NAMED
SENTENCE, with every premise that is left in it, by name; for the row that says where the kind's
block sits in a written description.

Main names:
  `K02LawOf r p B enter leave`: r: the typed record of the place (`SwRow`, Row.lean); p: the place's
    numbers; B: the seated block, at any type of claims; (enter, leave): its door. THE SENTENCE: for
    every frame, all letters and all readings that meet the premises listed next, the reduction of
    the piece at `below B` (`seatedAt`, SeatedAt.lean) leads, on the statements at which enter lets
    in a record t with on (t, ·), to: there are t, t' with enter a.1 = .ok t, leave a.1 t' = .ok
    a'.1 and `K2Q` at (t, a.2), (t', a'.2); at errors that are shares of at most 2⁻¹ ^ target.
  THE PREMISES THAT ARE LEFT, one by one: r.ok and r.writtenOK (two tests with code on the typed
    record: tests on the plan) · the letters X, the two maps of names iJ, iQ, the words' reading ρ ·
    two written rounds with the block's declared entries, each of its name's kind · hon (trivial at
    every caller so far) · hpr: no collision at the stored samples' seeds, at the open old messages
    and at the kept messages' slots; the carried joint's own condition · `LawAfter` at the piece's
    own shown columns (paid by `lawAfter_of`, AfterAt.lean, from `CallerAt`, `lin_at`, `FrontOn` and
    the columns) · `Rides` and `FrontNums` (BehindPaid.lean).
  `k02LawOf_of`: it holds wherever `P2At r p` (P2At.lean; at a lot's numbers: `p2At_frame`,
    NumsAt.lean), B declares the kind's rounds, and B sits on the kind's block `K2.codeSwitchKind p`, at any
    type of claims, behind the door (`SeatStep`, SeatedAt.lean). By `k2_leads_seated`.
Limits. A SENTENCE WITH PREMISES: at a real place none of them is shown but `P2At`; together they
are met at made-up toys alone (Toy/), there at the kind's block itself, not at a seated one. What
enter and leave keep of what the law reads is not said. Those of SeatedAt.lean. It is no soundness
of the protocol. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.SeatedAt
import Johnson.Top.H0.K2Caller.NumsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.Sound (Frame Piece below)
open VerifiableInference.Desc.First.K2Hands
open _root_.Run (ckP)
open scoped ENNReal

/-- **The law of the code switch at a seated block, with every premise that is left, by name.** r:
    the
typed record of the place; p: the place's numbers; B: the seated block; (enter, leave): its door. -/
def K02LawOf {Cl : Type} (r : SwRow) (p : K2.P2) (B : Block Rec Cl)
    (enter : Rec → Except String Rec) (leave : Rec → Rec → Except String Rec) : Prop :=
  ∀ (F : Frame) (W W' : Type) (h : r.ok = true) (_hW : r.writtenOK = true)
    (X : Letters r (r.ok_says h))
    (iJ : ((rowsAt r (r.ok_says h) X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r (r.ok_says h) X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
    (d₁ d₂ : RDT) (ρ : WordsOf (selZ X iJ iQ) d₁)
    (_he : [d₁, d₂].map (·.entry) = (K2.rounds p).map (·.entry))
    (_hk : ∀ d ∈ [d₁, d₂], Fmt.kindOf d.entry.name = some d.kind) (base : ℕ)
    (ext : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → W → W)
    (strs : Rec × F.E.Str → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).Ex.Str)
    (inX : Rec → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).X) (on : Rec × F.E.Str → Prop)
    (_hon : ∀ a, on a → (Cb.Pv.SendLocRide.inJ (selZ X iJ iQ)).on (lawFa X iJ iQ strs inX a))
    (_hpr : ∀ a, on a → ((Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).S.over
      (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).A).on (lawFa X iJ iQ strs inX a))
    (_hA : LawAfter X iJ iQ d₁ d₂ ρ p strs inX (shownP X iJ iQ d₁ d₂ ρ p base ext) on)
    (n0 : ℕ) (b₀ : TB X iJ iQ) (oldB : Rec × F.E.Str → (selZ X iJ iQ).sw.S₀.Smp)
    (strB : Rec × F.E.Str → (selLoc X iJ iQ).S.ext.Str)
    (carB : Rec × F.E.Str → X.St₀ × X.E₀.Str)
    (_hR : Rides (W := W) X iJ iQ d₁ d₂ ρ p base ext strs inX on oldB strB carB)
    (_hN : FrontNums (F := F) (r := r) p n0 on)
    (ext' : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → W' → W'),
    (seatedAt (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext) B ext').ior.red.Leads
      (fun a => ∃ t, enter a.1 = .ok t ∧ on (t, a.2))
      (fun a a' => ∃ t t', enter a.1 = .ok t ∧ leave a.1 t' = .ok a'.1 ∧
        K2Q X iJ iQ p strs inX (fbOf X iJ iQ n0 b₀ oldB strB carB) (t, a.2) (t', a'.2))
      (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).err ∧
    Err.Below (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).err ((2 : ℝ≥0∞)⁻¹ ^ r.set.target)

/-- **It holds wherever the place's numbers are the typed record's and B sits on the kind's block.**
    -/
theorem k02LawOf_of {Cl Cl₀ : Type} {r : SwRow} {p : K2.P2} {B : Block Rec Cl}
    {enter : Rec → Except String Rec} {leave : Rec → Rec → Except String Rec} (hp : P2At r p)
    (hr : B.rounds = (K2.codeSwitchKind (Cl := Cl₀) p).rounds)
    (hs : SeatStep B (K2.codeSwitchKind (Cl := Cl₀) p) enter leave) : K02LawOf r p B enter leave :=
  fun _ _ _ h hW X iJ iQ d₁ d₂ ρ he hk base ext strs inX on hon hpr hA n0 b₀ oldB strB carB hR hN
      ext' =>
    k2_leads_seated h hW X iJ iQ d₁ d₂ ρ (k2Wr_of hp he hk) p base ext strs inX on hon hpr hA n0 b₀
      oldB strB carB hR hN B enter leave hr hs ext'

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.k02LawOf_of
