-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyRows2225At.lean: rows 2.2 and 2.5 of the key file's table
of joints (Johnson/RunOne/KeyRows2225.lean: keeps₂_send2 | keeps₂_send5) at the two written rounds
of a sending, the chance paid by the sending kind's files' own law: send_goodIn
(Johnson/Desc/K1/Law/GoodSend3.lean) called as it lies at T := P₂ × St₂, stOf := the shared chain's
own statement, On := on₂ … 2 | 5, and at its own letter On' := «the statement has just 2 | 4
messages», which is proved here from the promise's half (never True).
After owed10_of (Johnson/Top/Fire/Code/Row10House.lean).
On emptiness: as KeyRows2225.lean's head: no member of on₂ … 2 | 5 is shown.
Object: sendPiece b base d₁ d₂ P₁.coordinates e: by rfl pieceOf b base [d₁, d₂] [] ⟨the identity,
the written errors at e⟩ · user: keepsAt_of_law₂ (keeps_same raises the errors): the fields r2_2 |
r2_5 · letters: the tables'; the sending kind's P₁ radP e fOf fIn; New.
  shape₂_at3 | shape₂_at6   behind the sendings the statement has just 2 | 4 messages (out of the
    book-keeping)
  keeps₂_send2_at | keeps₂_send5_at   the rows
Left, each with its payer and its kind of «∀»: the sending kind's eleven (hC · h1 · hS · hpl ·
hE · hP · hz · hl64 · he · hf with fOf | fIn): as at row 1.0: K1's files at the key file's numbers
(paid_key_at_scope: the key file's nineteen sendings) and KeySendBelow.lean's below_send; hS
[bare ∀ under the block's yes]: K14's sendAt holds K1's decideSend (SendGood.lean) + held_decide
· hl · hbase · hG · hnew · yes: KeyRows2225.lean's head · tieS [under «just n messages» and Sealed
at the message outright: 0 | 2 | 3]: tie_of_sealReads at oOf := that number · hlen | hk: the
place sends two messages, the sampled one(s) at 0 | 0 and 1: public.
Nothing on soundness by itself.
-/
import Johnson.RunOne.KeyRows2225
import Johnson.Desc.K1.Law.GoodSend3

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat
open OnBytes.Slice hiding ofF tabOf
open _root_.Run.PQ (CK)
open _root_.Run (ckP)
open _root_.Iop (Reduction Err)
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Plain
    VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K1 (Par condPort IsSend sendPiece send_goodIn Sealed shapeAt shapesOf
    sampledAt errPort)
open Johnson.Pack (portOmZ)

theorem shape₂_at3 (S : LinShape) (a : Nat) (d : St₂) (h : LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a
    3 d) = true) : d.st.oracles.size = 2 := by
  simp only [LKFU.Shape23.ok, LKFU.Shape23.shape₂, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true] at h
  obtain ⟨_, c2, _⟩ := h
  simpa using c2

theorem shape₂_at6 (S : LinShape) (a : Nat) (d : St₂) (h : LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a
    6 d) = true) : d.st.oracles.size = 4 := by
  simp only [LKFU.Shape23.ok, LKFU.Shape23.shape₂, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true] at h
  obtain ⟨_, c2, _⟩ := h
  simpa using c2

section
variable {XI Cells M Smp Rec Cl W : Type} (F : FileDescription XI) (Fr₂ : Frame)
  (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (at_ : Where)
  (S : LinShape) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad a : Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)

/-- **ROW 2.2, the chance paid by the sending kind's files' law.** -/
theorem keeps₂_send2_at (b : Block (P₂ × St₂) Cl) (base : Nat) (d₁ d₂ : RDT)
    -- THE SENDING KIND's LAW's OWN PREMISES (Johnson/Desc/K1/Law/GoodSend3.lean: send_goodIn), BY
    -- NAME
    (P₁ : Par) (radP : Nat → Nat) (hC : condPort P₁ radP = true) (h1 : P₁.seeds = 1)
    (hS : IsSend P₁ (fun z : P₂ × St₂ => z.2.st) b)
    (hpl : PlainDraws (_root_.Fmt.dsOf d₁.entry d₁.kind)) (hE : nE (_root_.Fmt.dsOf d₁.entry
        d₁.kind) = P₁.coordinates + 1)
    (hP : nP (_root_.Fmt.dsOf d₁.entry d₁.kind) = 0) (hz : IsNZ (_root_.Fmt.dsOf d₁.entry d₁.kind)
        P₁.coordinates) (hl64 : d₁.entry.logN ≤ 64)
    (e : Nat) (he : errPort P₁ radP ≤ e)
    (fOf : Fr₂.E.Str → ∀ k, (portOmZ P₁.codes (shapeAt P₁ k) (radP k.val)).Str)
    (fIn : Fr₂.E.Str → (wT d₁).Msg → ∀ k, (portOmZ P₁.codes (shapeAt P₁ k) (radP k.val)).Str)
    (hf : ∀ y τ, fOf ((sendPiece (W := W) (F := Fr₂) b base d₁ d₂ P₁.coordinates e).ior.imp y τ) =
        fIn y τ.1)
    -- THE ROW's
    (hl : ∀ z rs gs z', b.decide z rs gs = .ok z' → z'.1 = z.1 ∧ SentBack z.2 z'.2)
    (hbase : ∀ j ∈ pinned (open₂ 2), (at_ j).1 < base) (hG : SmpGrows G₂)
    (New : Strs → Prop) (hnew : ∀ x τ x', (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 2) x →
        (sendPiece (W := W) (F := Fr₂) b base d₁ d₂ P₁.coordinates e).ior.red.out x τ = some x' →
        New (strsOf Fr₂ x'.2))
    (yes : ∀ z rs gs z' y y', roundsFit b.rounds rs = true → b.decide z (rs.map noDigest) gs = .ok
        z' → StrsStay F at_ (open₂ 2) y y' → New y' →
      onAt F G₂ at_ (meaning₂ S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 2
          d)) (Free₂ F G₂ at_ S K₁ R coll last₁ off₂ 2) (open₂ 2) z y →
      LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 3 z'.2) = true ∧ Free₂ F G₂ at_ S K₁ R coll last₁
          off₂ 3 z' y')
    (hlen : (shapesOf P₁).length = 2) (k₀ : Fin (shapesOf P₁).length) (hk₀ : sampledAt P₁ k₀) (hk :
        k₀.val = 0)
    (tieS : ∀ x' : (P₂ × St₂) × Fr₂.E.Str, x'.1.2.st.oracles.size = 2 →
      Sealed P₁.codes (shapeAt P₁ k₀) (radP k₀.val) (fOf x'.2 k₀) x'.1.2.st 0 →
      hasSmp G₂ (at_ 3).1 (at_ 3).2 x'.1 = true ∧ NoColl F G₂ (at_ 3).1 (at_ 3).2 x'.1 (strsOf Fr₂
          x'.2)) :
    (sendPiece (W := W) (F := Fr₂) b base d₁ d₂ P₁.coordinates e).ior.red.Keeps (on₂ F Fr₂ G₂ at_ S
        K₁ R enc rad a coll last₁ off₂ 2) (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 3) (L₂
        F Fr₂ G₂ at_ S K₁ R enc rad 2) (L₂ F Fr₂ G₂ at_ S K₁ R enc rad 3) (sendPiece (W := W) (F :=
        Fr₂) b base d₁ d₂ P₁.coordinates e).err :=
  keeps₂_send2 F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ (sendPiece (W := W) (F := Fr₂) b base
      d₁ d₂ P₁.coordinates e) hl hbase hG New hnew yes _ (fun _ _ => True) (fun _ _ => True)
    (send_goodIn P₁ radP hC h1 b (fun z => z.2.st) hS base d₁ d₂ hpl hE hP hz hl64 e he fOf fIn hf
        (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 2)
      (fun x' => x'.1.2.st.oracles.size = 2) (fun _ _ => True) (fun _ _ => True)
      (fun x τ x' hx hb => by
      have hd := piece_decides_at (sendPiece (W := W) (F := Fr₂) b base d₁ d₂ P₁.coordinates e) x τ
          x' hb
      have hft := (piece_fits_at (sendPiece (W := W) (F := Fr₂) b base d₁ d₂ P₁.coordinates e) x τ
          x' hb).1
      have Hy := strsStay_of_out F Fr₂ at_ (sendPiece (W := W) (F := Fr₂) b base d₁ d₂
          P₁.coordinates e) (open₂ 2) hbase x x' τ hb
      exact shape₂_at3 S a x'.1.2 (yes x.1 _ _ x'.1 _ _ hft hd Hy (hnew x τ x' hx hb) hx).1)
      (fun _ _ _ _ _ _ _ => trivial))
    (fun x' h => tieS x' h.1 (by
      have t := h.2 k₀ hk₀
      have e0 : x'.1.2.st.oracles.size - (shapesOf P₁).length + k₀.val = 0 := by
        have s := h.1
        omega
      rw [e0] at t
      exact t))

/-- **ROW 2.5, the chance paid by the sending kind's files' law.** -/
theorem keeps₂_send5_at {K : Type} [Field K] (ρ : Model.Reading K) (hsame : ∀ x y, R.same x y ↔
    ρ.val x = ρ.val y) (b : Block (P₂ × St₂) Cl) (base : Nat) (d₁ d₂ : RDT)
    -- THE SENDING KIND's LAW's OWN PREMISES (Johnson/Desc/K1/Law/GoodSend3.lean: send_goodIn), BY
    -- NAME
    (P₁ : Par) (radP : Nat → Nat) (hC : condPort P₁ radP = true) (h1 : P₁.seeds = 1)
    (hS : IsSend P₁ (fun z : P₂ × St₂ => z.2.st) b)
    (hpl : PlainDraws (_root_.Fmt.dsOf d₁.entry d₁.kind)) (hE : nE (_root_.Fmt.dsOf d₁.entry
        d₁.kind) = P₁.coordinates + 1)
    (hP : nP (_root_.Fmt.dsOf d₁.entry d₁.kind) = 0) (hz : IsNZ (_root_.Fmt.dsOf d₁.entry d₁.kind)
        P₁.coordinates) (hl64 : d₁.entry.logN ≤ 64)
    (e : Nat) (he : errPort P₁ radP ≤ e)
    (fOf : Fr₂.E.Str → ∀ k, (portOmZ P₁.codes (shapeAt P₁ k) (radP k.val)).Str)
    (fIn : Fr₂.E.Str → (wT d₁).Msg → ∀ k, (portOmZ P₁.codes (shapeAt P₁ k) (radP k.val)).Str)
    (hf : ∀ y τ, fOf ((sendPiece (W := W) (F := Fr₂) b base d₁ d₂ P₁.coordinates e).ior.imp y τ) =
        fIn y τ.1)
    -- THE ROW's
    (hl : ∀ z rs gs z', b.decide z rs gs = .ok z' → z'.1 = z.1 ∧ SentBack z.2 z'.2)
    (hbase : ∀ j ∈ pinned (open₂ 5), (at_ j).1 < base) (hG : SmpGrows G₂)
    (New : Strs → Prop) (hnew : ∀ x τ x', (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 5) x →
        (sendPiece (W := W) (F := Fr₂) b base d₁ d₂ P₁.coordinates e).ior.red.out x τ = some x' →
        New (strsOf Fr₂ x'.2))
    (yes : ∀ z rs gs z' y y', roundsFit b.rounds rs = true → b.decide z (rs.map noDigest) gs = .ok
        z' → StrsStay F at_ (open₂ 5) y y' → New y' →
      onAt F G₂ at_ (meaning₂ S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 5
          d)) (Free₂ F G₂ at_ S K₁ R coll last₁ off₂ 5) (open₂ 5) z y →
      LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 6 z'.2) = true ∧ Free₂ F G₂ at_ S K₁ R coll last₁
          off₂ 6 z' y')
    (hlen : (shapesOf P₁).length = 2) (k₄ k₅ : Fin (shapesOf P₁).length) (hk₄ : sampledAt P₁ k₄)
        (hk₅ : sampledAt P₁ k₅) (h4 : k₄.val = 0) (h5 : k₅.val = 1)
    (tie4 : ∀ x' : (P₂ × St₂) × Fr₂.E.Str, x'.1.2.st.oracles.size = 4 →
      Sealed P₁.codes (shapeAt P₁ k₄) (radP k₄.val) (fOf x'.2 k₄) x'.1.2.st 2 →
      hasSmp G₂ (at_ 4).1 (at_ 4).2 x'.1 = true ∧ NoColl F G₂ (at_ 4).1 (at_ 4).2 x'.1 (strsOf Fr₂
          x'.2))
    (tie5 : ∀ x' : (P₂ × St₂) × Fr₂.E.Str, x'.1.2.st.oracles.size = 4 →
      Sealed P₁.codes (shapeAt P₁ k₅) (radP k₅.val) (fOf x'.2 k₅) x'.1.2.st 3 →
      hasSmp G₂ (at_ 5).1 (at_ 5).2 x'.1 = true ∧ NoColl F G₂ (at_ 5).1 (at_ 5).2 x'.1 (strsOf Fr₂
          x'.2)) :
    (sendPiece (W := W) (F := Fr₂) b base d₁ d₂ P₁.coordinates e).ior.red.Keeps (on₂ F Fr₂ G₂ at_ S
        K₁ R enc rad a coll last₁ off₂ 5) (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 6) (L₂
        F Fr₂ G₂ at_ S K₁ R enc rad 5) (L₂ F Fr₂ G₂ at_ S K₁ R enc rad 6) (sendPiece (W := W) (F :=
        Fr₂) b base d₁ d₂ P₁.coordinates e).err :=
  keeps₂_send5 F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ ρ (sendPiece (W := W) (F := Fr₂) b base
      d₁ d₂ P₁.coordinates e) hl hbase hsame hG New hnew yes _ (fun _ _ => True) (fun _ _ => True)
    (send_goodIn P₁ radP hC h1 b (fun z => z.2.st) hS base d₁ d₂ hpl hE hP hz hl64 e he fOf fIn hf
        (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 5)
      (fun x' => x'.1.2.st.oracles.size = 4) (fun _ _ => True) (fun _ _ => True)
      (fun x τ x' hx hb => by
      have hd := piece_decides_at (sendPiece (W := W) (F := Fr₂) b base d₁ d₂ P₁.coordinates e) x τ
          x' hb
      have hft := (piece_fits_at (sendPiece (W := W) (F := Fr₂) b base d₁ d₂ P₁.coordinates e) x τ
          x' hb).1
      have Hy := strsStay_of_out F Fr₂ at_ (sendPiece (W := W) (F := Fr₂) b base d₁ d₂
          P₁.coordinates e) (open₂ 5) hbase x x' τ hb
      exact shape₂_at6 S a x'.1.2 (yes x.1 _ _ x'.1 _ _ hft hd Hy (hnew x τ x' hx hb) hx).1)
      (fun _ _ _ _ _ _ _ => trivial))
    (fun x' h k hk => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl
      · refine tie4 x' h.1 ?_
        have t := h.2 k₄ hk₄
        have e0 : x'.1.2.st.oracles.size - (shapesOf P₁).length + k₄.val = 2 := by
          have s := h.1
          omega
        rw [e0] at t
        exact t
      · refine tie5 x' h.1 ?_
        have t := h.2 k₅ hk₅
        have e0 : x'.1.2.st.oracles.size - (shapesOf P₁).length + k₅.val = 3 := by
          have s := h.1
          omega
        rw [e0] at t
        exact t)

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.keeps₂_send2_at
#print axioms Johnson.RunOne.KeyRows23.keeps₂_send5_at
