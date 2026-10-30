-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/GameLabelsAt.lean: **THE ROW's END WITH NOTHING PROMISED OF THE RECORD, AND
THE NEW FORM TRIED AGAINST THE TWO SILLY VERIFIERS** (first arm). Definitions, statements and
proofs.

GameLabels.lean numbers the book's places by the labels of the trees that stand there: so the game's
promise is empty. Here:
  `SeatSeamsV`: GameCand.lean's seams of letters, at that numbering.
  `k12_cand_atV`: FOR a piece p over P × S, at any type of claims, whose block is alike to `held` of
    the proximity test's seat: PUBLIC: `PlaceB` · the numbering's equation · `johOk` · `batOneOk` ·
    e at least the batching's count · `labelsPubB`; OF THE ROW's LETTERS: hkeep · `SeatSeamsV`; THEN
    `TestGivesCand` (Johnson/Desc/Sound/WordsLaw.lean), to the letter. GameCandAt.lean's third
    letter, "the row's promises give `FirstOpens`", IS GONE.
  `GameAtHeldV`: the new form as a sentence on any piece over P × S. `k12_has_heldV`: the law says
    just this.
  `yesAll_not_heldV`: a piece with small errors that puts out at every transcript from a statement
    whose door in gives a record without the group has not the form. `yesAll_shut_heldV`: nor one
    that does so from a statement at which the door in REFUSES. (With an empty promise the form
    bites at every statement.) `noAll_has_heldV`: **a piece that never puts out has the form.**
Limits: those of GameLabels.lean and GameCand.lean. NO SOUNDNESS IS CLAIMED. hkeep and the seams are
paid nowhere here. No trial stands at a first-arm record WITH the group.

-/
import Johnson.Desc.K12.Coin.GameLabels
import Johnson.Desc.K12.Coin.GameCandAt
import Johnson.Desc.K12.Coin.GameHeldChecks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0 codes_of_johOk)
open H2K.First (batOneOk)
open Johnson.Pack (sigOf)

section
variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {A Cells Tok : Type} (arr : ℕ → ℕ → ℕ)
  (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)

/-- **The seams of letters at a seat, the book's places numbered by their trees' labels.** -/
def SeatSeamsV (enter : A → Except String T12) (F : Frame) (π : P12) (nl : ℕ → ℕ) (rad : Sg → ℕ)
    (rd : ℕ → ℕ) (base : ℕ) (mine : List Mem) (on : A × F.E.Str → Prop)
    (ins outs : A × F.E.Str → Wit Cells Tok MsgT → Prop) : Prop :=
  SeatsFit cs G mine → Fenced base mine →
    ∀ a, on a → Promised cs G smp mine a.1 (strsOf F a.2) →
      (∃ t, enter a.1 = .ok t ∧ QN π (NTuple F π (nuOf π nl t) rad rd) (t, a.2)) →
      ∀ b w, outs b w →
        ∃ c : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg,
          (∀ x ∈ mine, CandAt cs G smp x a.1 (strsOf F a.2) (c x)) ∧
            ∀ w', LaidBy cs arr mine c w w' → ins a w'

end

section
variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {P S Cl' Cells Tok : Type}
  (arr : ℕ → ℕ → ℕ)
  (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)

/-- **The row's end at a piece that a description holds: nothing is promised of the record.** -/
theorem k12_cand_atV (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (nl : ℕ → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT)
    (dt : List RDT) (e : ℕ) (r : Fmt.M1.Stage → ℕ)
    (p : Piece (ckP .two) F (P × S) Cl' (Wit Cells Tok MsgT))
    (hb : Alike (held (P := P) ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave)) p.b)
    (h0 : p.back = []) (hbase : p.base = base) (hds : p.ds = dB :: dt)
    (herr : HEq p.err ((e, errJ π r dt) : Err (uLT (ckP .two) (dB :: dt))))
    (hB : PlaceB F π num base dB dt = true) (hnum : ∀ n, num (.own (π.nums.free + n)) = base + n)
    (hj : johOk π r = true) (hb1 : batOneOk π = true)
    (hle : batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e)
    (hpl : labelsPubB π num nl base = true)
    (mine : List Mem) (on on' : (P × S) × F.E.Str → Prop)
    (ins outs : (P × S) × F.E.Str → Wit Cells Tok MsgT → Prop)
    (hkeep : ∀ a τ b, on a → Promised cs G smp mine a.1 (strsOf F a.2) →
      p.ior.red.out a τ = some b → on' b)
    (hseam : SeatSeamsV cs G arr smp (fun a : P × S => enter a.2) F π nl (fun s => r s.st) rd
      p.base mine on ins outs) :
    TestGivesCand cs G arr smp p mine on on' ins outs := by
  have hl : likeOk π (dB :: dt) = true := by
    simp only [PlaceB, Bool.and_eq_true] at hB
    exact hB.1.1.1.1.2
  have hA := atPlace_of F π num _ _ _ _ _ base dB dt _ hB (codes_of_johOk r π hj) hnum
    (bears_errJ π r dB dt (like_of_ok π _ hl))
  have hg := k12_game_alikeV P S Cl' enter leave F (Wit Cells Tok MsgT) π num nl _ _ _ _ _ rd base
    dB dt e (errJ π r dt) r p hb h0 hbase hds herr hA (fun _ => rfl) hj hb1 hle
    (labelsPub_of_B hpl)
  exact cand_of_leads cs G arr smp p mine on on' ins outs _
    (fun a => ∃ t, enter a.1.2 = .ok t ∧
      QN π (NTuple F π (nuOf π nl t) (fun s => r s.st) rd) (t, a.2))
    (Reduction.Leads.conseq hg (fun _ h => h)
      (fun _ _ _ _ _ q => by obtain ⟨⟨t, _, h1, _, h3⟩, _⟩ := q; exact ⟨t, h1, h3⟩))
    (fun _ _ _ => trivial) hkeep hseam

end

section
variable {P S Cl' W : Type} (enter : S → Except String T12) (leave : S → T12 → Except String S)
  (F : Frame) (π : P12) (nl : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ)
  (p : Piece (ckP .two) F (P × S) Cl' W)

/-- **The new form**: nothing promised; the numbering off the record. -/
def GameAtHeldV : Prop :=
  p.ior.red.Leads (fun _ => True)
    (fun a b => (∃ t t', enter a.1.2 = .ok t ∧ leave a.1.2 t' = .ok b.1.2 ∧
      QN π (NTuple F π (nuOf π nl t) rad rd) (t, a.2)) ∧ b.1 = (a.1.1, b.1.2)) p.err

/-- **Yes to all**, at a record without the group. -/
theorem yesAll_not_heldV (x : (P × S) × F.E.Str) (t : T12) (ht : enter x.1.2 = .ok t)
    (hg : t.st.groups[t.g]? = none) (hyes : ∀ τ, ∃ b, p.ior.red.out x τ = some b)
    (hs : Small p.err) : ¬ GameAtHeldV enter leave F π nl rad rd p := by
  intro h
  refine not_doomed_false _ _ hs (Doomed.mono _ _ (fun τ hτ => ?_) (h x trivial))
  obtain ⟨b, hb⟩ := hyes τ
  obtain ⟨⟨t', _, e1, _, q⟩, _⟩ := hτ b hb
  obtain rfl : t = t' := Except.ok.inj (ht.symm.trans e1)
  exact qn_no_group π _ (t, x.2) hg q

/-- **Yes to all**, where the door in refuses. -/
theorem yesAll_shut_heldV (x : (P × S) × F.E.Str) (w : String) (ht : enter x.1.2 = .error w)
    (hyes : ∀ τ, ∃ b, p.ior.red.out x τ = some b) (hs : Small p.err) :
    ¬ GameAtHeldV enter leave F π nl rad rd p := by
  intro h
  refine not_doomed_false _ _ hs (Doomed.mono _ _ (fun τ hτ => ?_) (h x trivial))
  obtain ⟨b, hb⟩ := hyes τ
  obtain ⟨⟨t', _, e1, _, _⟩, _⟩ := hτ b hb
  rw [ht] at e1
  cases e1

/-- **No to all.** -/
theorem noAll_has_heldV (hno : ∀ a τ, p.ior.red.out a τ = none) :
    GameAtHeldV enter leave F π nl rad rd p :=
  fun a _ => Doomed.of_forall _ _ fun τ b hb => by rw [hno a τ] at hb; cases hb

end

/-- The law says just the form. -/
theorem k12_has_heldV (P S Cl' : Type) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ)
    (nl : ℕ → ℕ) (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT)
    (dt : List RDT) (e : ℕ) (εt : Err (uLT (ckP .two) dt)) (r : Fmt.M1.Stage → ℕ)
    (p : Piece (ckP .two) F (P × S) Cl' W)
    (hb : Alike (held (P := P) ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave)) p.b)
    (h0 : p.back = []) (hbase : p.base = base) (hds : p.ds = dB :: dt)
    (herr : HEq p.err ((e, εt) : Err (uLT (ckP .two) (dB :: dt))))
    (hA : AtPlace F π num L mC mS mW rad base dB dt εt) (hr : ∀ s, rad s = r s.st)
    (hj : johOk π r = true) (hb1 : batOneOk π = true)
    (hle : batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e) (hpl : LabelsPub π num nl base) :
    GameAtHeldV enter leave F π nl rad rd p :=
  k12_game_alikeV P S Cl' enter leave F W π num nl L mC mS mW rad rd base dB dt e εt r p hb h0
    hbase hds herr hA hr hj hb1 hle hpl

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.k12_cand_atV
#print axioms VerifiableInference.Desc.K12.Coin.yesAll_not_heldV
#print axioms VerifiableInference.Desc.K12.Coin.yesAll_shut_heldV
#print axioms VerifiableInference.Desc.K12.Coin.noAll_has_heldV
#print axioms VerifiableInference.Desc.K12.Coin.k12_has_heldV
