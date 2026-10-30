-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/CandYes.lean: **"THE ONE ROW THAT IS OWED", WITH THE PIECE's OWN YES HANDED TO
THE SEAM.** Statements and proofs. `TestGivesCand` speaks under the piece's yes; the elder tool
`cand_of_leads` (Game.lean) has that yes in its hand and does not pass it on: so whoever pays the
seam ("the kind's one tuple gives candidates in the row's letters") had to take from the PROMISE
what the block's own yes says for certain (the batched rows lie within the group; the layout's
numbers; …). Here the seam's payer gets the yes.
  `cand_of_leads_yes`: the tool, for every piece: `cand_of_leads` with "∀ τ b, p.ior.red.out a τ =
    some b →" in front of the seam's conclusion. The elder form follows from it.
  `k12_cand_atY` | `k12_cand_atOY`: `k12_cand_at` | `k12_cand_atO` (GameCandAt.lean) so: made by a
    program out of their texts: the premise on the seam and one call turn, nothing else.
  `rowTwo_cand_gameY`: `rowTwo_cand_game` (RowTwoGame.lean) so: at the last chain's block 2: the
    seam has the yes of that row's own piece among its premises.
THE RIDER. The seam grows WEAKER as a debt (it has one premise more): a block that says no to all
has it for nothing, as it has the whole row; one that says yes to all hands its payer a yes that
says nothing: the payer must then find the candidates without it.
Limits: those of GameCandAt.lean and RowTwoGame.lean. NO SOUNDNESS IS CLAIMED.

-/
import Johnson.Desc.K12.Coin.RowTwoGame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open VerifiableInference.OnPublicFiles.Last (pieceTwoX candN)
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0 codes_of_johOk)
open H2K.First (batOneOk)
open Johnson.Pack (sigOf)

section
variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {A Cells Tok : Type} (arr : ℕ → ℕ → ℕ)
  (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  {C : PQ.CK} {Fr : Frame} {Cl : Type}

/-- **The tool, with the yes handed on.** -/
theorem cand_of_leads_yes (p : Piece C Fr A Cl (Wit Cells Tok MsgT)) (mine : List Mem)
    (on on' : A × Fr.E.Str → Prop) (ins outs : A × Fr.E.Str → Wit Cells Tok MsgT → Prop)
    (onK R : A × Fr.E.Str → Prop)
    (hg : p.ior.red.Leads onK (fun a _ => R a) p.err)
    (hon : ∀ a, on a → Promised cs G smp mine a.1 (strsOf Fr a.2) → onK a)
    (hkeep : ∀ a τ b, on a → Promised cs G smp mine a.1 (strsOf Fr a.2) →
      p.ior.red.out a τ = some b → on' b)
    (hseam : SeatsFit cs G mine → Fenced p.base mine →
      ∀ a, on a → Promised cs G smp mine a.1 (strsOf Fr a.2) → R a →
        ∀ τ b, p.ior.red.out a τ = some b → ∀ w, outs b w →
          ∃ c : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg,
            (∀ x ∈ mine, CandAt cs G smp x a.1 (strsOf Fr a.2) (c x)) ∧
              ∀ w', LaidBy cs arr mine c w w' → ins a w') :
    TestGivesCand cs G arr smp p mine on on' ins outs := by
  intro hS hF a ha hp
  exact Doomed.mono _ _
    (fun τ hτ b hb =>
      ⟨hkeep a τ b ha hp hb, fun w hw => hseam hS hF a ha hp (hτ b hb) τ b hb w hw⟩)
    (hg a (hon a ha hp))

end

section
variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {P S Cl' Cells Tok : Type}
  (arr : ℕ → ℕ → ℕ)
  (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)

/-- **The row's end at a piece that a description holds**, first arm, the seam under the piece's
yes. -/
theorem k12_cand_atY (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT)
    (dt : List RDT) (e : ℕ) (r : Fmt.M1.Stage → ℕ)
    (p : Piece (ckP .two) F (P × S) Cl' (Wit Cells Tok MsgT))
    (hb : Alike (held (P := P) ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave)) p.b)
    (h0 : p.back = []) (hbase : p.base = base) (hds : p.ds = dB :: dt)
    (herr : HEq p.err ((e, errJ π r dt) : Err (uLT (ckP .two) (dB :: dt))))
    (hB : PlaceB F π num base dB dt = true) (hnum : ∀ n, num (.own (π.nums.free + n)) = base + n)
    (hj : johOk π r = true) (hb1 : batOneOk π = true)
    (hle : batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e)
    (mine : List Mem) (on on' : (P × S) × F.E.Str → Prop)
    (ins outs : (P × S) × F.E.Str → Wit Cells Tok MsgT → Prop)
    (hon : ∀ a, on a → Promised cs G smp mine a.1 (strsOf F a.2) →
      ∀ t, enter a.1.2 = .ok t → FirstOpens π num no base t)
    (hkeep : ∀ a τ b, on a → Promised cs G smp mine a.1 (strsOf F a.2) →
      p.ior.red.out a τ = some b → on' b)
    (hseam : SeatsFit cs G mine → Fenced p.base mine →
      ∀ a, on a → Promised cs G smp mine a.1 (strsOf F a.2) →
        (∃ t, enter a.1.2 = .ok t ∧ QN π (NTuple F π no (fun s => r s.st) rd) (t, a.2)) →
        ∀ τ b, p.ior.red.out a τ = some b → ∀ w, outs b w →
          ∃ c : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg,
            (∀ x ∈ mine, CandAt cs G smp x a.1 (strsOf F a.2) (c x)) ∧
              ∀ w', LaidBy cs arr mine c w w' → ins a w') :
    TestGivesCand cs G arr smp p mine on on' ins outs := by
  have hl : likeOk π (dB :: dt) = true := by
    simp only [PlaceB, Bool.and_eq_true] at hB
    exact hB.1.1.1.1.2
  have hA := atPlace_of F π num _ _ _ _ _ base dB dt _ hB (codes_of_johOk r π hj) hnum
    (bears_errJ π r dB dt (like_of_ok π _ hl))
  have hg := k12_game_alike P S Cl' enter leave F (Wit Cells Tok MsgT) π num no _ _ _ _ _ rd base
    dB dt e (errJ π r dt) r p hb h0 hbase hds herr hA (fun _ => rfl) hj hb1 hle
  exact cand_of_leads_yes cs G arr smp p mine on on' ins outs _
    (fun a => ∃ t, enter a.1.2 = .ok t ∧ QN π (NTuple F π no (fun s => r s.st) rd) (t, a.2))
    (Reduction.Leads.conseq hg (fun _ h => h)
      (fun _ _ _ _ _ q => by obtain ⟨⟨t, _, h1, _, h3⟩, _⟩ := q; exact ⟨t, h1, h3⟩))
    hon hkeep hseam

/-- **The row's end at a piece that a description holds**, second arm, the seam under the piece's
yes. -/
theorem k12_cand_atOY (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT)
    (dt : List RDT) (e : ℕ) (r : Fmt.M1.Stage → ℕ)
    (p : Piece (ckP .two) F (P × S) Cl' (Wit Cells Tok MsgT))
    (hb : Alike (held (P := P) ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave)) p.b)
    (h0 : p.back = []) (hbase : p.base = base) (hds : p.ds = dB :: dt)
    (herr : HEq p.err ((e, errJ π r dt) : Err (uLT (ckP .two) (dB :: dt))))
    (hB : PlaceOwnB F π num base dB dt = true) (hnum : ∀ n, num (.own (π.nums.free + n)) = base + n)
    (hj : johOk π r = true) (hb1 : batOneOk π = true)
    (hle : batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e)
    (mine : List Mem) (on on' : (P × S) × F.E.Str → Prop)
    (ins outs : (P × S) × F.E.Str → Wit Cells Tok MsgT → Prop)
    (hon : ∀ a, on a → Promised cs G smp mine a.1 (strsOf F a.2) →
      ∀ t, enter a.1.2 = .ok t → FirstOpensOwn π num no base t)
    (hkeep : ∀ a τ b, on a → Promised cs G smp mine a.1 (strsOf F a.2) →
      p.ior.red.out a τ = some b → on' b)
    (hseam : SeatsFit cs G mine → Fenced p.base mine →
      ∀ a, on a → Promised cs G smp mine a.1 (strsOf F a.2) →
        (∃ t, enter a.1.2 = .ok t ∧ QN π (NTuple F π no (fun s => r s.st) rd) (t, a.2)) →
        ∀ τ b, p.ior.red.out a τ = some b → ∀ w, outs b w →
          ∃ c : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg,
            (∀ x ∈ mine, CandAt cs G smp x a.1 (strsOf F a.2) (c x)) ∧
              ∀ w', LaidBy cs arr mine c w w' → ins a w') :
    TestGivesCand cs G arr smp p mine on on' ins outs := by
  have hl : likeOk π (dB :: dt) = true := by
    simp only [PlaceOwnB, Bool.and_eq_true] at hB
    exact hB.1.1.1.1.2
  have hA := atPlaceOwn_of F π num _ _ _ _ _ base dB dt _ hB (codes_of_johOk r π hj) hnum
    (bears_errJ π r dB dt (like_of_ok π _ hl))
  obtain ⟨hP, h1, hlog⟩ := own_pays π (fun s => r s.st) r (fun _ => rfl) hj hb1 dB dt hA.like
  have hg := k12_game_alikeO P S Cl' enter leave F (Wit Cells Tok MsgT) π num no _ _ _ _ _ rd base
    dB dt e _ (errJ π r dt) p hb h0 hbase hds herr hA hP h1 hlog hle
  exact cand_of_leads_yes cs G arr smp p mine on on' ins outs _
    (fun a => ∃ t, enter a.1.2 = .ok t ∧ QN π (NTuple F π no (fun s => r s.st) rd) (t, a.2))
    (Reduction.Leads.conseq hg (fun _ h => h)
      (fun _ _ _ _ _ q => by obtain ⟨⟨t, _, h1, _, h3⟩, _⟩ := q; exact ⟨t, h1, h3⟩))
    hon hkeep hseam

end

section
variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {Pp S₃ Cl Cells Tok : Type}
  (arr : ℕ → ℕ → ℕ)
  (smp : Pp × S₃ → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)

/-- **The one row that is owed, at block 2 of the last chain, with the game paid, THE SEAM UNDER
THE PIECE's YES.** -/
theorem rowTwo_cand_gameY (Fr : Frame) (π : P12) (base : ℕ) (dB : RDT) (dt : List RDT) (e₀ : ℕ)
    (εt : Err (uLT (ckP .two) dt)) (enter : S₃ → Except String T12)
    (leave : S₃ → T12 → Except String S₃) (mine : List Mem)
    (on on' : (Pp × S₃) × Fr.E.Str → Prop)
    (ins : (Pp × S₃) × Fr.E.Str → Wit Cells Tok MsgT → Prop) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (rd : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ)
    (x : (Pp × S₃) × Fr.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dt)) → Wit Cells Tok MsgT →
      Wit Cells Tok MsgT)
    (hB : PlaceB Fr π num base dB dt = true) (hnum : ∀ n, num (.own (π.nums.free + n)) = base + n)
    (hj : johOk π r = true) (hb1 : batOneOk π = true)
    (hle : batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e₀) (hε : Err.le (errJ π r dt) εt)
    (opens : ∀ a t, on a → Promised cs G smp mine a.1 (strsOf Fr a.2) → enter a.1.2 = .ok t →
      FirstOpens π num no base t)
    (seam : ∀ a t st rest G0 Ly D τ b, on a → Promised cs G smp mine a.1 (strsOf Fr a.2) →
      enter a.1.2 = .ok t → Fixes π t st rest G0 Ly D →
      NTuple Fr π no (fun s => r s.st) rd (t, a.2) st rest G0 Ly D →
      (pieceTwoX (Cl := Cl) Fr π base dB dt e₀ εt enter leave x).ior.red.out a τ = some b →
      candN cs G arr smp Fr mine ins a)
    (behind : ∀ a τ b, on a → Promised cs G smp mine a.1 (strsOf Fr a.2) →
      (pieceTwoX (Cl := Cl) Fr π base dB dt e₀ εt enter leave x).ior.red.out a τ = some b → on' b)
    (outs : (Pp × S₃) × Fr.E.Str → Wit Cells Tok MsgT → Prop) :
    TestGivesCand cs G arr smp (pieceTwoX (Cl := Cl) Fr π base dB dt e₀ εt enter leave x) mine on
      on' ins outs := by
  refine cand_mono_err cs G arr smp _ base (dB :: dt) [] x (e₀, errJ π r dt) (e₀, εt)
    ⟨Nat.le_refl _, hε⟩ mine on on' ins outs ?_
  refine k12_cand_atY cs G arr smp enter leave Fr π num no rd base dB dt e₀ r _
    (alike_of (alike_lift _ _ (alike_below (alike_inside enter leave
      (K12.k12_alike guardedProximityTestParts π))))) rfl rfl rfl HEq.rfl hB hnum hj hb1 hle mine on on' ins outs
    (fun a ha hp t ht => opens a t ha hp ht) (fun a τ b ha hp hb => behind a τ b ha hp hb) ?_
  intro _ _ a ha hp hq τ b hb w _
  obtain ⟨t, ht, st, rest, G0, Ly, D, hf, hN⟩ := hq
  obtain ⟨c, hc, hi⟩ := seam a t st rest G0 Ly D τ b ha hp ht hf hN hb
  exact ⟨c, hc, fun w' hw' => hi w w' hw'⟩

end

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.cand_of_leads_yes
#print axioms VerifiableInference.Desc.K12.Coin.k12_cand_atY
#print axioms VerifiableInference.Desc.K12.Coin.k12_cand_atOY
#print axioms VerifiableInference.Desc.K12.Coin.rowTwo_cand_gameY
