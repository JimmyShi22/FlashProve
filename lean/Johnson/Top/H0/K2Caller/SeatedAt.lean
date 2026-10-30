-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/SeatedAt.lean: FROM THE KIND's BLOCK TO A BLOCK THAT SITS ON IT: a law
(`Reduction.Leads`, Johnson/Desc/Plain/Leads.lean) of the piece at a block K is a law of the piece
at every block B that sits on K behind a door (enter, leave), read through the door. General in the
two blocks, their records and their types of claims; then called at the code switch.

WHY. In a written description the code switch's block does not stand bare: at the finish a quiet
block is joined in front of it and one behind; at the head and at a link's first place one behind;
all under another name and place, another type of claims and a guard. So the seated block hands the
kind's block another record than it was handed, and hands on another than the kind's block made: no
equation of decisions holds, and `Block.Under` fails. What holds is the clause at the step: wherever
B's step says yes, the door lets in, K's step says yes at the same rounds and columns and takes as
many columns, and the way out gives B's record.

Main names:
  `SeatStep B K enter leave`: that clause. It is, to the letter, the field `step` of the structure
    `Sits` (K12/Law/Sits.lean), which this file
    does not import: whoever holds `Sits B K enter leave` hands over its fields rounds and step.
  `below_step`, `shown_congr`, `seat_below`: the clause passes the test on words (`below`,
    Johnson/Desc/Sound/ChainRule.lean).
  `seat_chain`: the clause at the fold of the one block (`chainAt`).
  `seatedAt q B ext`: the piece at `below B` over the stretch, the base and the errors of a piece q.
  `seated_out`: where the piece at the seated block puts out, the door lets in, q puts out at what
    came in, the way out gives the seated piece's record; the oracles behind are the same.
  `seated_leads`: THE DOOR: from `q.ior.red.Leads on Q q.err`: the seated piece's reduction leads,
    on the statements a at which enter a.1 = .ok t and on (t, a.2), to: there are t, t' with enter
    a.1 = .ok t, leave a.1 t' = .ok a'.1 and Q (t, a.2) (t', a'.2); at the same errors.
  `K2Q`: what `k2_leads_read` (BehindPaid.lean) leads to, under a name. `k2_leads_seated`:
    `seated_leads` at `k2Piece` and `k2_leads_read`, with `Err.Below` at 2⁻¹ ^ target; the kind's
    block may stand at any type of claims: its step does not hang on it.
Limits. ONE DIRECTION: from B's yes to K's. That a written description's list holds such a B is not
said here. The law still speaks of the record t that the door lets in and the record t' that the
kind's block makes: what enter and leave keep of what the law reads (the statement, the book, the
group's rows) is not said here. Those of BehindPaid.lean. It is no soundness of the protocol. On
hiding nothing.

-/
import Johnson.Top.H0.K2Caller.BehindPaid
import Johnson.Desc.Sound.FoldHeardProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Block Claim noDigest chainAt viewWordsBelowPrime foldBlocks OpenedColumn step_iff)
open VerifiableInference.Desc.Sound (Frame Piece below)
open VerifiableInference.Desc.First.K2Hands
open _root_.Run (ckP)
open scoped ENNReal

/-! ### Sitting at the step, under the test on words -/

section
variable {S T Cl Cl' : Type}

/-- B sits on K behind a door (enter, leave): the clause at the step. -/
def SeatStep (B : Block S Cl) (K : Block T Cl') (enter : S → Except String T)
    (leave : S → T → Except String S) : Prop :=
  ∀ (ft : ℕ) (s s' : S) (rs : List Fmt.RoundView) (cols : List Col) (k : ℕ),
    B.step ft s rs cols = .ok (s', k) →
      ∃ t t', enter s = .ok t ∧ K.step ft t rs cols = .ok (t', k) ∧ leave s t' = .ok s'

theorem below_step (b : Block S Cl) (ft : ℕ) (s s' : S) (rs : List Fmt.RoundView) (cols : List Col)
    (k : ℕ) : (below b).step ft s rs cols = .ok (s', k) ↔
      viewWordsBelowPrime ⟨rs.map noDigest, ((b.shown ft rs cols).flatMap id).map fun c => (0, c.1, c.2)⟩ = true
          ∧
        b.step ft s rs cols = .ok (s', k) := by
  rw [step_iff, step_iff]
  show (b.Fits ft rs cols ∧ (if viewWordsBelowPrime ⟨rs.map noDigest,
                  ((b.shown ft rs cols).flatMap id).map fun c => (0, c.1, c.2)⟩ = true
      then b.decide s (rs.map noDigest) (b.shown ft rs cols)
      else .error _) = .ok s' ∧ k = (b.want ft rs).length) ↔ _
  by_cases hk : viewWordsBelowPrime ⟨rs.map noDigest,
                  ((b.shown ft rs cols).flatMap id).map fun c => (0, c.1, c.2)⟩ = true
  · rw [if_pos hk]
    exact ⟨fun h => ⟨hk, h⟩, fun h => h.2⟩
  · rw [if_neg hk]
    exact ⟨fun h => (nomatch h.2.1), fun h => absurd h.1 hk⟩

theorem shown_congr {B : Block S Cl} {K : Block T Cl'} (hr : B.rounds = K.rounds) (ft : ℕ)
    (rs : List Fmt.RoundView) (cols : List Col) : B.shown ft rs cols = K.shown ft rs cols := by
  unfold Block.shown Block.want
  rw [hr]

/-- The clause passes the test on words. -/
theorem seat_below {B : Block S Cl} {K : Block T Cl'} {enter : S → Except String T}
    {leave : S → T → Except String S} (hr : B.rounds = K.rounds) (h : SeatStep B K enter leave) :
    SeatStep (below B) (below K) enter leave := by
  intro ft s s' rs cols k hs
  obtain ⟨hk, hb⟩ := (below_step B ft s s' rs cols k).1 hs
  obtain ⟨t, t', h1, h2, h3⟩ := h ft s s' rs cols k hb
  rw [shown_congr hr] at hk
  exact ⟨t, t', h1, (below_step K ft t t' rs cols k).2 ⟨hk, h2⟩, h3⟩

/-- The clause at the fold of the one block. -/
theorem seat_chain (n' n : String) {B : Block S Cl} {K : Block T Cl'}
    {enter : S → Except String T} {leave : S → T → Except String S} (hr : B.rounds = K.rounds)
    (h : SeatStep B K enter leave) {ft : ℕ} {s e : S} {v : Fmt.View}
    (hc : chainAt n' ft [B] s v = .ok e) :
    ∃ t t', enter s = .ok t ∧ chainAt n ft [K] t v = .ok t' ∧ leave s t' = .ok e := by
  have F := VerifiableInference.Desc.chainAtOk hc
  simp only [foldBlocks, List.splitAt_eq] at F
  split at F
  next => exact nomatch F
  next hlen =>
    split at F
    next => exact nomatch F
    next s' k hst =>
      obtain ⟨t, t', h1, h2, h3⟩ := h ft s s' _ _ k hst
      have e1 : s' = e := congrArg Prod.fst (Except.ok.inj F)
      have e2 : (v.rounds.drop B.rounds.length, v.opened.drop k) = (([], []) :
          List Fmt.RoundView × List Col) := congrArg Prod.snd (Except.ok.inj F)
      refine ⟨t, t', h1, ?_, e1 ▸ h3⟩
      have F' : foldBlocks ft [K] t v.rounds v.opened = .ok (t', [], []) := by
        simp only [foldBlocks, List.splitAt_eq]
        rw [← hr, if_neg hlen, h2]
        show (Except.ok (t', v.rounds.drop B.rounds.length, v.opened.drop k) :
          Except String (T × List Fmt.RoundView × List Col)) = _
        rw [e2]
      unfold chainAt
      rw [F']
      rfl

/-! ### At a piece -/

variable {F : Frame} {W W' : Type}

/-- The piece at the seated block, over the stretch, the base and the errors of a piece q. -/
def seatedAt (q : Piece (ckP .two) F T Cl' W) (B : Block S Cl)
    (ext : S × F.E.Str → Tr (uLT (ckP .two) q.ds) → W' → W') : Piece (ckP .two) F S Cl W' :=
  ⟨below B, q.base, q.ds, [], ext, q.err⟩

theorem toOpt {α : Type} {x : Except String α} {a : α} (h : x.toOption = some a) : x = .ok a := by
  cases x with
  | error e => exact absurd h (by simp [Except.toOption])
  | ok y =>
    have : y = a := by simpa [Except.toOption] using h
    rw [this]

/-- **Where the piece at the seated block puts out, the door lets in, the piece q puts out at what
came in, and the way out gives the seated piece's record; the oracles behind are the same.** -/
theorem seated_out (q : Piece (ckP .two) F T Cl' W) (K : Block T Cl') (hq : q.b = below K)
    (hback : q.back = []) (B : Block S Cl) (enter : S → Except String T)
    (leave : S → T → Except String S) (hr : B.rounds = K.rounds) (h : SeatStep B K enter leave)
    (ext : S × F.E.Str → Tr (uLT (ckP .two) q.ds) → W' → W') (a a' : S × F.E.Str)
    (τ : Tr (uLT (ckP .two) q.ds)) (ho : (seatedAt q B ext).ior.red.out a τ = some a') :
    ∃ t t', enter a.1 = .ok t ∧ q.ior.red.out (t, a.2) τ = some (t', a'.2) ∧
      leave a.1 t' = .ok a'.1 := by
  have h1 : (if sTests (ckP .two) q.stage a.2 τ = true
      then (seatedAt q B ext).run a.1 (sView (ckP .two) q.stage a.2 τ) else none).map
        (fun xo => (xo, q.ior.imp a.2 τ)) = some a' := ho
  obtain ⟨s', h2, h3⟩ := Option.map_eq_some_iff.1 h1
  split at h2
  · rename_i ht
    have h4 : (chainAt (below B).name F.ft [below B] a.1
        ⟨(sView (ckP .two) q.stage a.2 τ).rounds ++ [],
          (sView (ckP .two) q.stage a.2 τ).opened⟩).toOption = some s' := h2
    obtain ⟨t, t', e1, e2, e3⟩ := seat_chain (below B).name q.b.name (B := below B) (K := below K)
      hr (seat_below hr h) (toOpt h4)
    subst h3
    refine ⟨t, t', e1, ?_, e3⟩
    show (if sTests (ckP .two) q.stage a.2 τ = true
      then q.run t (sView (ckP .two) q.stage a.2 τ) else none).map
        (fun xo => (xo, q.ior.imp a.2 τ)) = some (t', q.ior.imp a.2 τ)
    rw [if_pos ht]
    show ((chainAt q.b.name F.ft [q.b] t
        ⟨(sView (ckP .two) q.stage a.2 τ).rounds ++ q.back,
          (sView (ckP .two) q.stage a.2 τ).opened⟩).toOption).map _ = _
    rw [hback, hq] at *
    rw [e2]
    rfl
  · exact absurd h2 (by simp)

/-- **A law of the piece q is a law of the piece at the seated block**, read through the door. -/
theorem seated_leads (q : Piece (ckP .two) F T Cl' W) (K : Block T Cl') (hq : q.b = below K)
    (hback : q.back = []) (B : Block S Cl) (enter : S → Except String T)
    (leave : S → T → Except String S) (hr : B.rounds = K.rounds) (h : SeatStep B K enter leave)
    (ext : S × F.E.Str → Tr (uLT (ckP .two) q.ds) → W' → W')
    (on : T × F.E.Str → Prop) (Q : T × F.E.Str → T × F.E.Str → Prop)
    (L : q.ior.red.Leads on Q q.err) :
    (seatedAt q B ext).ior.red.Leads (fun a => ∃ t, enter a.1 = .ok t ∧ on (t, a.2))
      (fun a a' => ∃ t t', enter a.1 = .ok t ∧ leave a.1 t' = .ok a'.1 ∧ Q (t, a.2) (t', a'.2))
      q.err := by
  rintro a ⟨t, ht, hon⟩
  refine Doomed.mono _ _ ?_ (L (t, a.2) hon)
  intro τ hτ a' ha'
  obtain ⟨t₁, t', e1, e2, e3⟩ := seated_out q K hq hback B enter leave hr h ext a a' τ ha'
  obtain rfl : t = t₁ := Except.ok.inj (ht.symm.trans e1)
  exact ⟨t, t', ht, e3, hτ _ e2⟩

end

section
variable {F : Frame} {r : SwRow} {H : r.OK} (X : Letters r H)
  (iJ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
  (p : K2.P2)
  (strs : Rec × F.E.Str → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).Ex.Str)
  (inX : Rec → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).X)

/-- **What the law of the code switch leads to** (`k2_leads_read`'s own words, under a name): every
witness of what stands behind, at the record behind and the reading fb of the statement behind,
gives the relation in front at the witness handed back, and the kept messages' decodings. -/
def K2Q (fb : Rec × F.E.Str → TB X iJ iQ) (a a' : Rec × F.E.Str) : Prop :=
  ∀ wt, lawRb X iJ iQ p F.E.Str a (a'.1, fb a') wt →
    ((Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).S.over
      (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).A).relR (lawFa X iJ iQ strs inX a)
        (selBk X iJ iQ wt) ∧
    ∀ k : (selHd X iJ iQ).K,
      ((selHd X iJ iQ).o k).decW ((selHd X iJ iQ).sW k (lawFa X iJ iQ strs inX a).2.1.1)
          ((lawFa X iJ iQ strs inX a).1.1.1.2 k) =
        some ((selHd X iJ iQ).msg (cutSel r.cs r.l iJ iQ (selNew X iJ iQ wt)).1 k)

end

set_option maxHeartbeats 2000000 in
/-- **The law of the code switch at a seated block**: B sits on the kind's block `K2.codeSwitchKind p` behind a
door (enter, leave); the statement in front is read through enter, the statement behind through
leave. -/
theorem k2_leads_seated {F : Frame} {W W' Cl Cl₀ : Type} {r : SwRow} (h : r.ok = true)
    (hW : r.writtenOK = true) (X : Letters r (r.ok_says h))
    (iJ : ((rowsAt r (r.ok_says h) X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r (r.ok_says h) X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
    (d₁ d₂ : RDT) (ρ : WordsOf (selZ X iJ iQ) d₁) (w : K2Wr r d₁ d₂) (p : K2.P2) (base : ℕ)
    (ext : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → W → W)
    (strs : Rec × F.E.Str → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).Ex.Str)
    (inX : Rec → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).X) (on : Rec × F.E.Str → Prop)
    (hon : ∀ a, on a → (Cb.Pv.SendLocRide.inJ (selZ X iJ iQ)).on (lawFa X iJ iQ strs inX a))
    (hpr : ∀ a, on a → ((Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).S.over
      (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).A).on (lawFa X iJ iQ strs inX a))
    (hA : LawAfter X iJ iQ d₁ d₂ ρ p strs inX (shownP X iJ iQ d₁ d₂ ρ p base ext) on)
    (n0 : ℕ) (b₀ : TB X iJ iQ) (oldB : Rec × F.E.Str → (selZ X iJ iQ).sw.S₀.Smp)
    (strB : Rec × F.E.Str → (selLoc X iJ iQ).S.ext.Str)
    (carB : Rec × F.E.Str → X.St₀ × X.E₀.Str)
    (hR : Rides (W := W) X iJ iQ d₁ d₂ ρ p base ext strs inX on oldB strB carB)
    (hN : FrontNums (F := F) (r := r) p n0 on)
    (B : Block Rec Cl) (enter : Rec → Except String Rec) (leave : Rec → Rec → Except String Rec)
    (hr : B.rounds = (K2.codeSwitchKind (Cl := Cl₀) p).rounds)
    (hs : SeatStep B (K2.codeSwitchKind (Cl := Cl₀) p) enter leave)
    (ext' : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → W' → W') :
    (seatedAt (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext) B ext').ior.red.Leads
      (fun a => ∃ t, enter a.1 = .ok t ∧ on (t, a.2))
      (fun a a' => ∃ t t', enter a.1 = .ok t ∧ leave a.1 t' = .ok a'.1 ∧
        K2Q X iJ iQ p strs inX (fbOf X iJ iQ n0 b₀ oldB strB carB) (t, a.2) (t', a'.2))
      (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).err ∧
    Err.Below (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).err ((2 : ℝ≥0∞)⁻¹ ^ r.set.target) := by
  have L := k2_leads_read h hW X iJ iQ d₁ d₂ ρ w p base ext strs inX on hon hpr hA n0 b₀ oldB strB
    carB hR hN
  have L1 : (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).ior.red.Leads on
      (K2Q X iJ iQ p strs inX (fbOf X iJ iQ n0 b₀ oldB strB carB))
      (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).err := L.1
  have hs' : SeatStep B (K2.codeSwitchKind (Cl := Claim) p) enter leave := hs
  exact ⟨seated_leads (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext) (K2.codeSwitchKind p) rfl rfl B enter leave
    hr hs' ext' on (K2Q X iJ iQ p strs inX (fbOf X iJ iQ n0 b₀ oldB strB carB)) L1, L.2⟩

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.seat_below
#print axioms VerifiableInference.Desc.First.K2Caller.seat_chain
#print axioms VerifiableInference.Desc.First.K2Caller.seated_out
#print axioms VerifiableInference.Desc.First.K2Caller.seated_leads
#print axioms VerifiableInference.Desc.First.K2Caller.k2_leads_seated
