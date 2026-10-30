-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/GoodSendOpen.lean: the law of a sending in the form of the rule of composition,
for a block that goes on behind the round of the seeds in rounds of its own (the answers are items
of a round in which the caller goes on; further rounds may follow): at the written count that bears
the number of the place's bad seeds at the first round, and 0 at all others, the prover has lost
towards: where the block says yes, each message that the sending has sampled is sealed.

Main names:
  seedMapsL, seedMapsL_ok, seedMapsL_pass   the stretch's first written round is read as the typed
               round of one seed; all others are passed by.
  IsSendOpen   a block's yes on a first round and whatever follows holds a yes of the kind's
               decision on that first round and some second; the statement behind the block keeps
               the messages of the decision's; a reader of the record behind returns the number of
               the first new message.
  openPiece    the piece.
  send_goodIn_open   the law, with letters at the borders.
  send_gives_open    the law as one lost game, with the sample read off the statement.

What is not claimed. THE ERRORS ARE 0 AT THE LATER ROUNDS: so the two premises at a yes on the
letters (keep, back) can be met only by conditions and relations that every yes carries; a block
with a law of its own on its later rounds joins that law to send_gives_open at the sum of the
errors. One answer a message. Of blocks that go on none is shown to be in the class. Nothing on
soundness of a protocol, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.GoodSendStays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat OnBytes.Slice
open Johnson.Pack Cb Cb.Ood
open VerifiableInference.Desc (Block noDigest)
open VerifiableInference.Desc.Sound (Frame Piece)

/-- The first written round is read as the typed round of one seed; the others are passed by. -/
noncomputable def seedMapsL (d₁ : RDT) (ds : List RDT) (c : Nat) :
    Maps (d₁ :: ds) [seedRound d₁ c] :=
  .step (RMap.seed (r' := seedRound d₁ c) (fun m => m) c id) (Maps.skips ds)

theorem seedMapsL_ok {d₁ : RDT} (ds : List RDT) {c : Nat}
    (hp : PlainDraws (Fmt.dsOf d₁.entry d₁.kind)) (hE : nE (Fmt.dsOf d₁.entry d₁.kind) = c + 1)
    (hP : nP (Fmt.dsOf d₁.entry d₁.kind) = 0) (hz : IsNZ (Fmt.dsOf d₁.entry d₁.kind) c)
    (hl : d₁.entry.logN ≤ 64) : (seedMapsL d₁ ds c).OK :=
  ⟨RMap.seed_ok _ hp hE hP hz hl Function.injective_id, Maps.ok_skips ds⟩

theorem skips_pass : ∀ (ds : List RDT) (τ : Tr (uLT (ckP .two) ds)), (Maps.skips ds).pass τ = true
  | [], _ => rfl
  | _ :: ds, (_, _, τ) => skips_pass ds τ

theorem seedMapsL_pass (d₁ : RDT) (ds : List RDT) (c : Nat) (τ : Tr (uLT (ckP .two) (d₁ :: ds)))
    (h : passT (ckP .two) (d₁ :: ds) (rhoT (ckP .two) (d₁ :: ds) τ) = true) :
    (seedMapsL d₁ ds c).pass τ = true := by
  obtain ⟨m, c1, τ'⟩ := τ
  have h' : (GChal.pass (b := d₁.entry.work) c1 &&
      passT (ckP .two) ds (rhoT (ckP .two) ds τ')) = true := h
  show (GChal.pass (b := d₁.entry.work) c1 && (Maps.skips ds).pass τ') = true
  rw [(Bool.and_eq_true_iff.1 h').1, skips_pass]
  rfl

variable {T Cl W : Type} {F : Frame}

/-- **A block's yes holds a yes of the kind's decision on its first round and some second.** -/
def IsSendOpen (P : Par) (stOf : T → Statement) (first : T → Nat) (b : Block T Cl) : Prop :=
  ∀ s s' r₁ rs gs, b.decide s (r₁ :: rs) gs = .ok s' →
    ∃ (L : Type) (d d' : DState L) (owed : Option Nat) (ids : Array Nat) (r₂ : Fmt.RoundView),
      decideSend P owed d [r₁, r₂] = .ok (ids, d') ∧ OldMsgs d'.st (stOf s') ∧
        first s' = d.st.oracles.size

/-- The piece that holds such a block at its stretch. -/
noncomputable def openPiece (b : Block T Cl) (base : Nat) (d₁ : RDT) (ds : List RDT)
    (back : List Fmt.RoundView) (c e : Nat) : Piece (ckP .two) F T Cl W :=
  ⟨b, base, d₁ :: ds, back, fun _ _ w => w, (seedMapsL d₁ ds c).err ((e, ()) : Nat × Unit)⟩

/-- **The law of a sending whose block goes on.** -/
theorem send_goodIn_open (P : Par) (rad : Nat → Nat) (hC : condPort P rad = true) (b : Block T Cl)
    (stOf : T → Statement) (first : T → Nat) (hS : IsSendOpen P stOf first b) (base : Nat)
    (d₁ : RDT) (ds : List RDT) (back : List Fmt.RoundView) (he₁ : d₁.entry = seedEntry P)
    (hk₁ : d₁.kind = .seeds) (e : Nat) (he : errPort P rad ≤ e)
    (fOf : F.E.Str → ∀ k, (portOmZ P.codes (shapeAt P k) (rad k.val)).Str)
    (fIn : F.E.Str → (wT d₁).Msg → ∀ k, (portOmZ P.codes (shapeAt P k) (rad k.val)).Str)
    (hf : ∀ y τ,
      fOf ((openPiece (W := W) (F := F) b base d₁ ds back P.coordinates e).ior.imp y τ) =
        fIn y τ.1)
    (On On' : T × F.E.Str → Prop) (R R' : T × F.E.Str → W → Prop)
    (hkeep : ∀ a τ x, On a →
      (openPiece (W := W) (F := F) b base d₁ ds back P.coordinates e).ior.red.out a τ = some x →
      On' x)
    (hback : ∀ a τ x w, On a →
      (openPiece (W := W) (F := F) b base d₁ ds back P.coordinates e).ior.red.out a τ = some x →
      R' x w → R a w) :
    (openPiece (W := W) (F := F) b base d₁ ds back P.coordinates e).GoodIn On
      (fun x => On' x ∧ ∀ k, sampledAt P k →
        Sealed P.codes (shapeAt P k) (rad k.val) (fOf x.2 k) (stOf x.1) (first x.1 + k.val))
      R R' := by
  have h1 := seeds_one P rad hC
  obtain ⟨hp, hE, hP, hz, hl⟩ := seed_draws P h1 d₁ he₁ hk₁
  have hne : Nonempty (Fin P.seeds) := ⟨⟨0, by omega⟩⟩
  refine goodIn_of_count_msg _ _ _ _ _ (seedRound d₁ P.coordinates) e
    (fun _ => (seedMapsL d₁ ds P.coordinates).carry)
    (fun _ => (seedMapsL d₁ ds P.coordinates).fits (seedMapsL_ok ds hp hE hP hz hl) _)
    (fun a m z => BadPort P rad (fIn a.2 m) (fun _ => z)) ?_ ?_
  · intro a m _
    refine Nat.le_trans (cnt_comp_le (fun z (_ : Fin P.seeds) => z) (fun x y h => ?_)
      (BadPort P rad (fIn a.2 m))) (Nat.le_trans (badPort_count P rad hC _) he)
    exact congrFun h hne.some
  · intro a τ x ha hx
    have ht := Desc.K14.Law.piece_tests _ a τ x hx
    simp only [sTests, Bool.and_eq_true] at ht
    have hpass := seedMapsL_pass d₁ ds P.coordinates τ ht.1.1
    obtain ⟨hx2, gs, hdec⟩ := Desc.K14.Law.piece_yes _ a τ x hx
    refine ⟨_, (seedMapsL d₁ ds P.coordinates).tr_of_pass τ hpass, fun hgood => ?_⟩
    refine ⟨⟨hkeep a τ x ha hx, fun k hk => ?_⟩, fun w hw => hback a τ x w ha hx hw⟩
    obtain ⟨m₁, c₁, τ'⟩ := τ
    have hdec' : b.decide a.1 (noDigest (shownAt d₁ m₁ c₁) ::
        (rvT (ckP .two) ds τ' ++ back).map noDigest) gs = .ok x.1 := hdec
    obtain ⟨L, d, d', owed, ids, r₂, hyes, hold, hfirst⟩ := hS _ _ _ _ _ hdec'
    have hread := reads_shown P h1 d₁ hE hz m₁ c₁
    have hlen : ((noDigest (shownAt d₁ m₁ c₁)).drawn.elems.map E.ofTriple).length =
        P.seeds * (P.coordinates + 1) := by
      have hmap := rvOf_els (toRD d₁) (msgRD d₁ m₁) c₁
      have := congrArg List.length hmap
      rw [List.length_map, elemsV_length] at this
      rw [List.length_map, h1, Nat.one_mul]
      exact this.trans hE
    obtain ⟨y, hy⟩ := seedIs_behind_len P rad owed d d' _ _ ids hC hlen hyes _ hread k hk
    rw [hfirst]
    refine ⟨_, y, hy.old hold, fun hcl => hgood ⟨k, hk, ?_⟩⟩
    rw [hx2, hf] at hcl
    exact hcl

/-- **The same as one lost game, with the sample read off the statement**: to be joined, at the sum
of the errors, to the law that the block has on its later rounds. -/
theorem send_gives_open (P : Par) (rad : Nat → Nat) (hC : condPort P rad = true) (b : Block T Cl)
    (stOf : T → Statement) (first : T → Nat) (hS : IsSendOpen P stOf first b) (base : Nat)
    (d₁ : RDT) (ds : List RDT) (back : List Fmt.RoundView) (he₁ : d₁.entry = seedEntry P)
    (hk₁ : d₁.kind = .seeds) (e : Nat) (he : errPort P rad ≤ e)
    (fOf : F.E.Str → ∀ k, (portOmZ P.codes (shapeAt P k) (rad k.val)).Str)
    (fIn : F.E.Str → (wT d₁).Msg → ∀ k, (portOmZ P.codes (shapeAt P k) (rad k.val)).Str)
    (hf : ∀ y τ,
      fOf ((openPiece (W := W) (F := F) b base d₁ ds back P.coordinates e).ior.imp y τ) =
        fIn y τ.1) (a : T × F.E.Str) :
    Doomed (uLT (ckP .two) (d₁ :: ds))
      (openPiece (W := W) (F := F) b base d₁ ds back P.coordinates e).err fun τ =>
        ∀ x, (openPiece (W := W) (F := F) b base d₁ ds back P.coordinates e).ior.red.out a τ =
            some x →
          ∀ k, sampledAt P k → ∃ z,
            smpAt P.codes (shapeAt P k) (rad k.val) (stOf x.1) (first x.1 + k.val) = some z ∧
            ¬ (portOmZ P.codes (shapeAt P k) (rad k.val)).Clash (fOf x.2 k) z.1 := by
  have g := send_goodIn_open (W := W) (F := F) P rad hC b stOf first hS base d₁ ds back he₁ hk₁ e
    he fOf fIn hf (fun _ => True) (fun _ => True) (fun _ _ => True) (fun _ _ => True)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ => trivial)
  refine Doomed.mono _ _ (fun τ hτ x hx k hk => ?_) (g a trivial)
  obtain ⟨ρ, y, hs, hc⟩ := (hτ x hx).1.2 k hk
  obtain ⟨z, h1, h2, _⟩ := smpAt_of _ _ (rad k.val) _ _ ρ y (cond_tie P rad hC k hk) hs
  exact ⟨z, h1, fun hcl => hc ((clash_val _ _ z.1 ρ h2).1 hcl)⟩

/-- A sending that closes its own round of answers is in the class. -/
theorem isSendOpen_of (P : Par) (stOf : T → Statement) (b : Block T Cl) (hS : IsSend P stOf b)
    (hb : ∀ s s' rs gs, b.decide s rs gs = .ok s' → rs.length = 2) :
    IsSendOpen P stOf (fun t => (stOf t).oracles.size - (shapesOf P).length) b := by
  intro s s' r₁ rs gs h
  have hl := hb _ _ _ _ h
  match rs, hl, h with
  | [r₂], _, h =>
    obtain ⟨L, d, d', owed, ids, hyes, hsame, hsize⟩ := hS s s' r₁ r₂ gs h
    refine ⟨L, d, d', owed, ids, r₂, hyes, old_of_same hsame, ?_⟩
    show (stOf s').oracles.size - (shapesOf P).length = d.st.oracles.size
    rw [hsize, size_behind P owed d d' _ _ ids hyes]
    omega

end VerifiableInference.Desc.K1
